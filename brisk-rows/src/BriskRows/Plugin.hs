{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | This typechecker plugin that rearranges 'BriskRow.ROW' equalities
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
        -> goInv env ext rhs []

        | Just rext <- getExtend env rhs
        -> goInj ext rext

      _ -> Nothing

goInv :: Env -> Extension -> TcType -> [NewEquality] -> Maybe [NewEquality]
goInv env ext rhs acc =
    case getExtend env rho of
      Just ext' -> goInv env ext' rhs' acc'
      Nothing   ->
        if isStop env rho then Nothing else Just (NewEquality rho rhs' : acc')
  where
    Extend k v nm a rho = ext

    acc' = NewEquality a (mkSelect env k v nm rhs) : acc

    rhs' = mkRestrict env k v nm rhs

-- Two out of three is good enough!
--
-- This simple treatment of just one layer suffices for the general definitions
-- in "BriskRows.Internal.RV" etc.
goInj :: Extension -> Extension -> Maybe [NewEquality]
goInj lext rext
  | not $ lk `eqType` rk && lv `eqType` rv                    = Nothing
  | lnm `eqType` rnm && la `eqType` ra                        = Just [NewEquality lrho rrho]
  | lnm `eqType` rnm &&                    lrho `eqType` rrho = Just [NewEquality la   ra  ]
  |                     la `eqType` ra  && lrho `eqType` rrho = Just [NewEquality lnm  rnm ]
  | otherwise                                                 = Nothing
  where
    Extend lk lv lnm la lrho = lext
    Extend rk rv rnm ra rrho = rext
