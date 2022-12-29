{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module BriskRows.Plugin (plugin) where

import           Control.Applicative ((<|>))
import           Data.Maybe (mapMaybe)

import           GHC.Core.Reduction (Reduction (Reduction))
import qualified GHC.Rename.Names as Rename
import           GHC.Tc.Types.Constraint (Ct)
import qualified GHC.Tc.Types.Constraint as Ct
import           GHC.Plugins (TyCon, (<+>), eqType, text)
import qualified GHC.Plugins as GhcPlugins
import           GHC.Utils.Outputable (ppr)
import           GHC.Driver.Ppr (showSDoc)
import           GHC.Utils.Panic (panicDoc)
import qualified GHC.Core.Predicate as Predicate
import qualified GHC.Core.TyCo.Rep as TyCoRep
import qualified GHC.Tc.Types.Evidence as TcEvidence
import           GHC.Tc.Plugin (TcPluginM)
import qualified GHC.Tc.Plugin as TcPluginM
import           GHC.Tc.Types (TcPluginSolveResult (..))
import qualified GHC.Tc.Types as TcRnTypes
import           GHC.Tc.Utils.TcType (TcKind, TcType)
import qualified GHC.Tc.Utils.TcType as TcType
import qualified GHC.Core.TyCon as TyCon
import           GHC.Types.Unique.FM (unitUFM)

-- | The @brisk-rows@ typechecker plugin
--
-- It adds the following rules.
--
-- * /Reflexive/. A family application @'BriskRows.CmpName' l r@ simplifies to @EQ@ if @l@ and @r@ are equivalent.
--
-- * /Injective/. A Wanted equality between two extensions @rhoL 'BriskRows.:&' nmL 'BriskRows.:=' aL@ and @rhoR :& nmR := aR@ requires @(aL ~ aR, nmL ~ nmR)@ if @rhoL@ and @rhoR@ are already equivalent.
--
-- * /Injective/. A Wanted equality between two extensions @rhoL :& nmL := aL@ and @rhoR :& nmR := aR@ requires @(aL ~ aR, rhoL ~ rhoR)@ if @nmL@ and @nmR@ are already equivalent.
--
-- * /Inverse/. A Wanted equality between an extension @rho :& nm := a@ and a value @Row# [nm1 := a1, nm2 := a2, ..., nmN := aN]@ requires that @a ~ 'BriskRows.Select' nm (Row# ...)@.
--
-- * /Inverse/. A Wanted equality between an extension @rho :& nm := a@ and a value @Row# [nm1 := a1, nm2 := a2, ..., nmN := aN]@ requires that @rho ~ 'BriskRows.Internal.Restrict' nm (Row# ...)@, where 'BriskRows.Internal.Restrict' is a hidden family that removes the column.
--
-- The plugin adds the required constraints except when they are already present (thus avoiding loops) or when they involve the internal type families with codomain 'BriskRows.ROW' (something hasn't yet simplified).
-- It is by no means complete with respect to row type equivalence in general, but it is sufficient in the context of the fundamental staticness required by the @brisk-rows@ types.
plugin :: GhcPlugins.Plugin
plugin = GhcPlugins.defaultPlugin
  { GhcPlugins.pluginRecompile = \_args -> pure GhcPlugins.NoForceRecompile
  , GhcPlugins.tcPlugin        = \_args -> Just TcRnTypes.TcPlugin
      { TcRnTypes.tcPluginInit    = newEnv
      , TcRnTypes.tcPluginStop    = \_ -> pure ()
      , TcRnTypes.tcPluginRewrite = \env@Env{envCmpName} -> unitUFM envCmpName (rewriteCmpName env)
      , TcRnTypes.tcPluginSolve   = \env _evBindsVar gs ws -> do

            doTrace env $ text $ "<<<<<<------"
            doTrace env $ ppr $ gs <> ws
            doTrace env $ text $ "<-----------"

            let recipes = mapMaybe (improve env) ws
            doTrace env $ ppr recipes

            doTrace env $ text "----------->"
            news <- mapM (newConstraint env ws) recipes
            doTrace env $ text $ "------>>>>>>"

            pure $ TcPluginOk [] (concat news)
      }
  }

-----

lookupModule :: String -> TcPluginM.TcPluginM GhcPlugins.Module
lookupModule s = do
    hsc_env <- TcPluginM.getTopEnv

    let mod_nm = GhcPlugins.mkModuleName s
        lu     =
            TcPluginM.findImportedModule mod_nm
          . Rename.renamePkgQual (GhcPlugins.hsc_unit_env hsc_env) mod_nm
    lu (Just $ GhcPlugins.fsLit "this") >>= \case
        TcPluginM.Found _ m -> pure m
        _                   -> lu Nothing >>= \case
            TcPluginM.Found _ m -> pure m
            _                   ->
                panicDoc "Plugin.BriskRows initialization could not find Module " (ppr mod_nm)

lookupTC :: GhcPlugins.Module -> String -> TcPluginM.TcPluginM GhcPlugins.TyCon
lookupTC modul s =
    TcPluginM.lookupOrig modul (GhcPlugins.mkTcOcc s) >>=
    TcPluginM.tcLookupTyCon

lookupDC :: GhcPlugins.TyCon -> String -> TcPluginM.TcPluginM GhcPlugins.DataCon
lookupDC tc s = case dcs of
    [d] -> pure d
    _ -> panicDoc "Plugin.BriskRows initialization could not find DataCon " (ppr s)
  where
    dcs =
        [ dc
        | dc <- TyCon.tyConDataCons tc
        , GhcPlugins.fsLit s ==
            GhcPlugins.occNameFS (GhcPlugins.occName (GhcPlugins.dataConName dc))
        ]

-----

data Env = Env {
    doTrace     :: GhcPlugins.SDoc -> TcPluginM ()
  ,
    envCmpName  :: !TyCon
  ,
    envEQ       :: !TyCon
  ,
    envExtend   :: !TyCon
  ,
    envRestrict :: !TyCon
  ,
    envRow      :: !TyCon
  ,
    envSelect   :: !TyCon
  ,
    envStops    :: [TyCon]
  }

newEnv :: TcPluginM Env
newEnv = do
    doTrace <- pure (\_x -> (pure ())) `asTypeOf` do
      dflags <- TcRnTypes.unsafeTcPluginTcM GhcPlugins.getDynFlags
      pure $ \x -> do
        TcPluginM.tcPluginIO $ putStrLn $ showSDoc dflags x

    modul <- lookupModule "BriskRows.Internal"
    let luTC = lookupTC modul

    envCmpName <- luTC "CmpName"

    envEQ <- luTC "CmpNameEQ"

    envExtend <- luTC "Extend_Row#"

    envRestrict <- luTC "Restrict"

    envRow <- do
      tc <- luTC "ROW"
      GhcPlugins.promoteDataCon <$> lookupDC tc "Row#"
  
    envSelect <- luTC "Select"

    -- We can skip Extend, since it's a type synonym. (TODO and so eqType handles that, right?)
    -- We can skip Extend_Row# since this function is only ever used once we've confirmed it's not an extension.
    envStops <- mapM luTC $ words "Cons Extend_Col Extend_Ordering Restrict_Ordering Restrict"

    pure Env{..}

isExtend :: Env -> TyCon -> Bool
isExtend Env{envExtend} tc = tc == envExtend

isRow :: Env -> TcType -> Bool
isRow Env{envRow} ty = case TcType.tcSplitTyConApp_maybe ty of
    Just (tc, [_k, _v, _cols]) -> envRow == tc
    _                          -> False

isStop :: Env -> TcType -> Bool
isStop Env{envStops} ty = case TcType.tcTyConAppTyCon_maybe ty of
    Just tc -> tc `elem` envStops
    _       -> False

mkRestrict :: Env -> TcKind -> TcKind -> TcType -> TcType -> TcType
mkRestrict Env{envRestrict} k v nm rho = TcType.mkTyConApp envRestrict [k, v, nm, rho]

mkSelect :: Env -> TcKind -> TcKind -> TcType -> TcType -> TcType
mkSelect Env{envSelect} k v nm rho = TcType.mkTyConApp envSelect [k, v, nm, rho]

-----

-- | See 'BriskRows.Internal.CmpName' for the explanation of we implement its reflexivity in the plugin
rewriteCmpName :: Env -> TcRnTypes.RewriteEnv -> [Ct] -> [TcType] -> TcPluginM TcRnTypes.TcPluginRewriteResult
rewriteCmpName env _rwenv _gs args = case args of
  [_k, l, r]
    | l `eqType` r -> pure $ TcRnTypes.TcPluginRewriteTo (Reduction co rhs) []
    | otherwise    -> pure TcRnTypes.TcPluginNoRewrite
  _ -> fail "CmpName wrote arg count!"
  where
    Env{envCmpName, envEQ} = env

    lhs = TcType.mkTyConApp envCmpName args
    rhs = TcType.mkTyConTy envEQ

    co = GhcPlugins.mkUnivCo (TyCoRep.PluginProv "brisk-rows:CmpName.Refl") TyCon.Nominal lhs rhs

-----

data NewEquality = NewEquality !TcType !TcType

data NewCtRecipe = NewCtRecipe !Ct ![NewEquality]

newConstraint :: Env -> [Ct] -> NewCtRecipe -> TcPluginM [Ct]
newConstraint env olds (NewCtRecipe old news) =
    mapMaybe id <$> mapM each news
  where
    isOld :: NewEquality -> Maybe Ct
    isOld =
        foldl (\acc f new -> f new <|> acc new) (\_ -> Nothing)
        [ \(NewEquality l r) ->
            if (eqType l l' && eqType r r') || (eqType l r' && eqType r l')
            then Just old'
            else Nothing
        | old' <- olds
        , Predicate.EqPred Predicate.NomEq l' r' <- [Predicate.classifyPredType $ Ct.ctPred old']
        ]

    each :: NewEquality -> TcPluginM (Maybe Ct)
    each new@(NewEquality l r)
        -- don't emit the equality if it already exists
      | Just ct <- isOld new = do
        doTrace env $ text "SKIPPING" <+> ppr (new, ct)
        pure Nothing
      | otherwise = do
        let loc = Ct.ctLoc old
            eq  = Predicate.mkPrimEqPred l r
        doTrace env $ text "EMITTING" <+> ppr eq
        fmap (Just . Ct.mkNonCanonical) $ TcPluginM.newWanted loc eq

instance GhcPlugins.Outputable NewEquality where
  ppr (NewEquality lhs rhs) = text "NewEquality" <+> ppr (lhs, rhs)

instance GhcPlugins.Outputable NewCtRecipe where
  ppr (NewCtRecipe old news) = text "NewCtRecipe" <+> ppr (old, news)

-----

data Extension =
    -- | @Extend_Row# {k} {v} nm a rho _err@
    Extend !TcKind !TcKind !TcType !TcType !TcType

getExtend :: Env -> TcType -> Maybe Extension
getExtend env ty = case TcType.tcSplitTyConApp_maybe ty of
    Just (tc, [k, v, nm, a, rho, _err])
      | isExtend env tc
      -> Just $ Extend k v nm a rho
    _ -> Nothing

-----

-- | The domain-specific knowledge
--
-- This plugin does not implement any interactions, so we simplify each constraint individually.
--
-- Also, it only does /Improvement/.
-- It does not improve Givens.
-- To improve Derived/Wanteds, it adds missing Deriveds.
--
-- > rho :& nm := l ~ rho :& nm := r   implies/requires   l ~ r
--
-- > rho :& l := a ~ rho :& r := a   implies/requires   l ~ r
--
-- > l :& nm := a ~ r :& nm := a   implies/requires   l ~ r
--
-- > rho :& x := a :& y := b :& ... ~ Row# cols   implies/requires   rho ~ Row# cols :# y :# x, b ~ Select y ..., a ~ Select x ...
improve :: Env -> Ct -> Maybe NewCtRecipe
improve env ct = case ct of
    Ct.CNonCanonical{}
      | Just (TcEvidence.Nominal, lhs, rhs) <- Predicate.getEqPredTys_maybe (Ct.ctPred ct)
      -> NewCtRecipe ct <$> go lhs rhs
    _ -> Nothing
  where

    go lhs rhs = case getExtend env lhs of   -- the LHS will never be the Row#, will it?
      Just ext
        | isRow env rhs
        -> goInverted env ext rhs []

        | Just rext <- getExtend env rhs
        -> goOuterInjectivity ext rext

      _ -> Nothing

-- | Invert extensions to restrictions
--
-- @root :& nmN := aN :& ... :& nm2 := a2 :& nm1 := a1@ equals @Row# [k1 := v1, k2 := v2, ..., kN := vN]@
-- only if @a1 ~ Select nm1 (Row# [k1 ... vN])@, @a2 ~ Select nm2 (Row# [k1 ... vN])@, all the way to @aN ~ Select nmN (Row# [k1 ... vN])@
-- and also @root ~ Restrict nmN (... (Restrict nm2 (Restrict nm1 (Row# [k1 ... vN]))))@.
goInverted :: Env -> Extension -> TcType -> [NewEquality] -> Maybe [NewEquality]
goInverted env ext rhs acc =
    case getExtend env rho of
      Just ext' -> goInverted env ext' rhs' acc'
      Nothing   ->
        -- emit no equalities if the root is one of our internal type families
        if isStop env rho then Nothing else
        Just (NewEquality rho rhs' : acc')
  where
    Extend k v nm a rho = ext

    acc' = NewEquality a (mkSelect env k v nm rhs) : acc

    rhs' = mkRestrict env k v nm rhs

-- | This simple treatment of just one layer suffices for the general
-- definitions in "BriskRows.Internal.RV" etc.
goOuterInjectivity :: Extension -> Extension -> Maybe [NewEquality]
goOuterInjectivity lext rext
    -- kinds must match
  | not $ lk `eqType` rk && lv `eqType` rv = Nothing

    -- if the outermost names are equal, require the images and (recursively) extended rows are too
  | lnm `eqType` rnm   = Just [NewEquality la ra, NewEquality lrho rrho]

    -- if the extended rows are equal, require the outermost names and images are too
  | lrho `eqType` rrho = Just [NewEquality la ra, NewEquality lnm  rnm ]

  | otherwise          = Nothing
  where
    Extend lk lv lnm la lrho = lext
    Extend rk rv rnm ra rrho = rext
