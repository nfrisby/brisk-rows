{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module BriskRows.Plugin (plugin) where

import           Debug.Trace (trace)

import           Control.Applicative ((<|>))
import           Control.Monad (guard)
import           Data.Functor ((<&>))
-- import           Data.List (find)
import           Data.Maybe (fromMaybe, mapMaybe)

import           GHC.Types.Id.Make (proxyHashId)
import           GHC.Core.Class (Class, classTyCon)
import           GHC.Platform (Platform)
import qualified GHC.Core as Core
import           GHC.Core.Reduction (HetReduction (HetReduction), Reduction (Reduction), reductionReducedType)
import qualified GHC.Rename.Names as Rename
import           GHC.Core.FamInstEnv (FamInstEnvs, normaliseTcApp, topReduceTyFamApp_maybe)
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
-- import           GHC.Core.Unify (typesCantMatch)
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
      , TcRnTypes.tcPluginRewrite = \env@Env{envCmpName, envExtOp = _} ->
          -- NOTE WELL that these rewrites only happen inside of constraints!
          --
          -- TODO confirm that
            unitUFM envCmpName (rewriteCmpName env)
--          <>
--            unitUFM envExt     (rewriteExt   env)
--          <>
--            unitUFM envExtOp   (rewriteExtOp env)
      , TcRnTypes.tcPluginSolve   = \env _evBindsVar gs ws -> do

            doTrace env $ text $ "<<<<<<------"
            doTrace env $ ppr $ gs <> ws
            doTrace env $ text $ "<-----------"

            let existingEqs = foobar (getExistingEq env) (gs ++ ws)
                recipes     = mapMaybe (improve env `uncurry`) existingEqs
            doTrace env $ ppr recipes

            doTrace env $ text "----------->"
            newEqs <- mapM (newEq env ws) recipes
            doTrace env $ text $ "------>>>>>>"

            doTrace env $ text "***---"
            let dictRecipes = mapMaybe (simplifyDict env) ws
            doTrace env $ ppr dictRecipes
            doTrace env $ text "---***"
            (solvedDicts, newDictss) <- fmap unzip $ mapM (newDict env) dictRecipes

            pure $ TcPluginOk (mapMaybe oldEq recipes <> solvedDicts) (concat newEqs <> concat newDictss)
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

lookupId :: GhcPlugins.Module -> String -> TcPluginM.TcPluginM GhcPlugins.Id
lookupId modul s =
    TcPluginM.lookupOrig modul (GhcPlugins.mkVarOcc s) >>=
    TcPluginM.tcLookupId

lookupTC :: GhcPlugins.Module -> String -> TcPluginM.TcPluginM GhcPlugins.TyCon
lookupTC modul s =
    TcPluginM.lookupOrig modul (GhcPlugins.mkTcOcc s) >>=
    TcPluginM.tcLookupTyCon

lookupPDC :: GhcPlugins.TyCon -> String -> TcPluginM.TcPluginM GhcPlugins.TyCon
lookupPDC tc s = case dcs of
    [d] -> pure $ GhcPlugins.promoteDataCon d
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
    doTrace        :: GhcPlugins.SDoc -> TcPluginM ()
  ,
    doTrace_       :: forall a. GhcPlugins.SDoc -> a -> a
  ,
    envAllCols     :: !Class
  ,
    -- | Coercion from KnownLT to its method type at the given @k@, @v@, @nm@, and @rho@.
    envAllColsCo   :: !(TcKind -> TcKind -> TcType -> TcType -> TyCoRep.Coercion)
  ,
    envAllColsHelp :: !TyCon
  ,
    envAllColsExt  :: !GhcPlugins.Id
  ,
    envAssign      :: !TyCon
  ,
    envCmpName     :: !TyCon
  ,
    envEQ          :: !TyCon
  ,
    envEmp         :: !TyCon
  ,
    envExtOp       :: !TyCon
  ,
    envFamInstEnvs :: !FamInstEnvs
  ,
    envGT          :: !TyCon
  ,
    envKnownLT     :: !Class
  ,
    -- | Coercion from KnownLT to its method type at the given @k@, @v@, @nm@, and @rho@.
    envKnownLTCo   :: !(TcKind -> TcKind -> TcType -> TcType -> TyCoRep.Coercion)
  ,
    envKnownLTExt  :: !GhcPlugins.Id
  ,
    envLT          :: !TyCon
  ,
    envRestrict    :: !TyCon
  ,
    envSelect      :: !TyCon
  ,
    envStops       :: [TyCon]
  ,
    envPlatform    :: !Platform
  ,
    envUnfoldExtOp :: !TyCon
  }

newEnv :: TcPluginM Env
newEnv = do
    dflags <- TcRnTypes.unsafeTcPluginTcM GhcPlugins.getDynFlags

    modul <- lookupModule "BriskRows.Internal"
    let luTC = lookupTC modul

    envAllCols <- TyCon.tyConClass_maybe <$> luTC "AllCols" >>= \case
        Just cls -> pure cls
        Nothing  -> panicDoc "Plugin.BriskRows could not find the AllCols class" (text "")

    envAllColsCo <- case TyCon.unwrapNewTyCon_maybe (classTyCon envAllCols) of
        Just (_tvs, _rhs, coax) -> pure $ \k v c rho -> TcEvidence.mkTcUnbranchedAxInstCo coax [k, v, c, rho] []
        Nothing                 -> panicDoc "Plugin.BriskRows could not treat AllCol as a newtype" (text "")

    envAllColsHelp <- luTC "AllColsHelp"
    envAllColsExt  <- lookupId modul "extAllCols"

    envAssign <- do
      tc <- luTC "COL"
      lookupPDC tc ":="

    envCmpName <- luTC "CmpName"

    (envEQ, envGT, envLT) <- do
      tc <- lookupModule "GHC.Types" >>= flip lookupTC "Ordering"

      eq <- lookupPDC tc "EQ"
      gt <- lookupPDC tc "GT"
      lt <- lookupPDC tc "LT"
      pure (eq, gt, lt)

    envEmp <- luTC "ROW" >>= flip lookupPDC "Emp"

    envExtOp  <- luTC ":&"

    envFamInstEnvs <- TcPluginM.getFamInstEnvs

    envKnownLT <- TyCon.tyConClass_maybe <$> luTC "KnownLT" >>= \case
        Just cls -> pure cls
        Nothing  -> panicDoc "Plugin.BriskRows could not find the KnownLT class" (text "")

    envKnownLTCo <- case TyCon.unwrapNewTyCon_maybe (classTyCon envKnownLT) of
        Just (_tvs, _rhs, coax) -> pure $ \k v x rho -> TcEvidence.mkTcUnbranchedAxInstCo coax [k, v, x, rho] []
        Nothing                 -> panicDoc "Plugin.BriskRows could not treat KnownLT as a newtype" (text "")

    envKnownLTExt <- lookupId modul "extKnownLT"

    envPlatform <- TcPluginM.getTargetPlatform

    envRestrict <- luTC "Restrict"

    envSelect <- luTC "Select"

    -- We can skip Extend, since it's a type synonym. (TODO and so eqType handles that, right?)
    -- We can skip Extend_Row# since this function is only ever used once we've confirmed it's not an extension.
    envStops <- mapM luTC $ words "" -- "Cons Extend_Col Extend_Ordering Restrict_Ordering Restrict"

    envUnfoldExtOp <- luTC "UnfoldExtOp"

    pure Env{
              doTrace  = \x -> asTypeOf (pure ()) $ TcPluginM.tcPluginIO $ putStrLn $ showSDoc dflags x
            , doTrace_ = \x -> asTypeOf id $ trace (showSDoc dflags x)
            , ..
            }

isEmp :: Env -> TcType -> Bool
isEmp Env{envEmp} ty = case TcType.tcSplitTyConApp_maybe ty of
    Just (tc, [_k, _v]) -> envEmp == tc
    _                   -> False

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

{-
rewriteExtOp :: Env -> TcRnTypes.RewriteEnv -> [Ct] -> [TcType] -> TcPluginM TcRnTypes.TcPluginRewriteResult
rewriteExtOp env _rwenv _gs args = case args of
  [_k, _v, rho, _col]
    | Just tc' <- TcType.tcTyConAppTyCon_maybe rho
    , (tc' == envEmp || tc' == envRow)
    -> pure $ TcRnTypes.TcPluginRewriteTo (Reduction co rhs) []

    | otherwise
    -> pure TcRnTypes.TcPluginNoRewrite

  _ -> fail ":& wrote arg count!"
  where
    Env{envEmp, envExtOp, envRow, envUnfoldExtOp} = env

    lhs = TcType.mkTyConApp envExtOp       args
    rhs = TcType.mkTyConApp envUnfoldExtOp args

    co = GhcPlugins.mkUnivCo (TyCoRep.PluginProv "brisk-rows:(:&)") TyCon.Nominal lhs rhs

rewriteExt :: Env -> TcRnTypes.RewriteEnv -> [Ct] -> [TcType] -> TcPluginM TcRnTypes.TcPluginRewriteResult
rewriteExt env _rwenv _gs args = case args of
  [_k, _v, _nm, _a, rho]
    | Just tc' <- TcType.tcTyConAppTyCon_maybe rho
    , (tc' == envEmp || tc' == envRow)
    -> pure $ TcRnTypes.TcPluginRewriteTo (Reduction co rhs) []

    | otherwise
    -> pure TcRnTypes.TcPluginNoRewrite

  _ -> fail "Ext wrote arg count!"
  where
    Env{envEmp, envExt, envRow, envUnfoldExt} = env

    lhs = TcType.mkTyConApp envExt       args
    rhs = TcType.mkTyConApp envUnfoldExt args

    co = GhcPlugins.mkUnivCo (TyCoRep.PluginProv "brisk-rows:Ext") TyCon.Nominal lhs rhs
-}

-----

data NewEquality = NewEquality !TcType !TcType

data NewEqRecipe = NewEqRecipe !Ct !MaybeEvTerm ![NewEquality]

data MaybeEvTerm = NothingEvTerm | JustEvTerm !TcEvidence.EvTerm

oldEq :: NewEqRecipe -> Maybe (TcEvidence.EvTerm, Ct)
oldEq (NewEqRecipe old mbEvTerm _news) = case mbEvTerm of
    NothingEvTerm -> Nothing
    JustEvTerm ev -> Just (ev, old)

newEq :: Env -> [Ct] -> NewEqRecipe -> TcPluginM [Ct]
newEq env olds (NewEqRecipe old _mbEvTerm news) =
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

instance GhcPlugins.Outputable NewEqRecipe where
  ppr (NewEqRecipe old mbEvTerm news) = text "NewEqRecipe" <+> ppr (old, ppr mbEvTerm, news)

instance GhcPlugins.Outputable MaybeEvTerm where
  ppr = ppr . \case
      NothingEvTerm -> Nothing
      JustEvTerm ev -> Just ev

-----

data Extension =
    -- | @Extend_Row# {k} {v} nm a rho _err@
    Extend !TcType !(Maybe TcType) !TcKind !TcKind !TcType !TcType !TcType

getExtend :: Env -> TcType -> Maybe Extension
getExtend env ty = case TcType.tcSplitTyConApp_maybe ty of
    Just (tc, args)
{-      | tc == envExtend
      , [k, v, nm, a, rho, _err] <- args
      -> Just $ Extend ty Nothing k v nm a rho
      | tc == envExt
      , [k, v, nm, a, rho] <- args
      -> Just $ Extend ty (Just $ TcType.mkTyConApp envUnfoldExt args) k v nm a rho
-}
      | tc == envExtOp
      , [k, v, rho, col] <- args
      , Just (tc', args') <- TcType.tcSplitTyConApp_maybe col
      , tc' == envAssign
      , [_k, _v, nm, a] <- args'
      -> Just $ Extend ty (Just $ TcType.mkTyConApp envUnfoldExtOp args) k v nm a rho
    _ -> Nothing
  where
    Env{envAssign, envExtOp, envUnfoldExtOp} = env

getExistingEq :: Env -> Ct -> Maybe (Extension, Extension)
getExistingEq env ct = case ct of
    Ct.CNonCanonical{}
      | Just (TcEvidence.Nominal, lhs, rhs) <- Predicate.getEqPredTys_maybe (Ct.ctPred ct)
      , Just lext <- getExtend env lhs
      , Just rext <- getExtend env rhs
      -> Just (lext, rext)
    _ -> Nothing

-----

equal :: Env -> TcType -> TcType -> Bool
equal env x y = Just EQ == cmp env x y

apart :: Env -> TcType -> TcType -> Bool
apart env x y = maybe False (/= EQ) $ cmp env x y

cmp :: Env -> TcType -> TcType -> Maybe Ordering
cmp env =
    \x y -> go $ reductionReducedType $ normaliseTcApp envFamInstEnvs TyCon.Nominal envCmpName [TcType.tcTypeKind x, x, y]
  where
    Env {envCmpName, envEQ, envFamInstEnvs, envGT, envLT} = env

    go ty = case TcType.tcSplitTyConApp_maybe ty of
        Nothing         -> Nothing
        Just (tc, args)
          | tc == envLT -> Just LT
          | tc == envEQ -> Just EQ
          | tc == envGT -> Just GT

          | Just (sigma, body, oversat) <- TyCon.expandSynTyCon_maybe tc args
          -> go $ TcType.substTy (TcType.mkTvSubstPrs sigma) body `TcType.mkAppTys` oversat

          | Just (HetReduction redn _co) <- topReduceTyFamApp_maybe envFamInstEnvs tc args
          -> go $ reductionReducedType redn

          | tc == envCmpName
          , [_k, x, y] <- args
          , eqType x y -> Just EQ

          | otherwise   -> Nothing

-----

data NewDictRecipe =
    -- | @old k v x rho i rho'@
    NewKnownLTRecipe !Ct !TcKind !TcKind !TcType !TcType !Int !TcType
  |
    -- | @old k v c rho columns root@
    NewAllColsRecipe !Ct !TcKind !TcKind !TcType !TcType !Extensions !TcType

instance GhcPlugins.Outputable NewDictRecipe where
  ppr (NewKnownLTRecipe old k v x rho i rho') = text "NewKnownLTRecipe" <+> ppr (old, k, v, x, rho, i, rho')
  ppr (NewAllColsRecipe old k v c rho (Extends assocs) rho') = text "NewKnownLTRecipe" <+> ppr (old, k, v, c, rho, assocs, rho')

simplifyDict :: Env -> Ct -> Maybe NewDictRecipe
simplifyDict env ct = case ct of
    Ct.CDictCan{Ct.cc_class, Ct.cc_tyargs}

      | cc_class == envKnownLT
      , [k, v, x, rho] <- cc_tyargs
      , Just ext <- getExtend env rho
      -> goKnownLT x ext <&> \(i, rho') -> NewKnownLTRecipe ct k v x rho i rho'

      | cc_class == envAllCols
      , [k, v, c, rho] <- cc_tyargs
      , Just ext <- getExtend env rho
      , let (root, exts) = peel env ext
      -> Just $ NewAllColsRecipe ct k v c rho exts root

    _ -> Nothing
  where
    Env{envAllCols, envExtOp, envKnownLT} = env

    goKnownLT :: TcType -> Extension -> Maybe (Int, TcType)
    goKnownLT x ext = ($ recu) $ case cmp env x nm of
        Just o  -> Just . if LT == o then incr else skip
        Nothing -> keep
      where
        Extend _ty _mbNewTy k v nm a rho = ext

        recu = getExtend env rho >>= goKnownLT x

        incr = \case
            Nothing        -> (1, rho)
            Just (i, root) -> (i + 1, root)

        skip = \case
            Nothing        -> (0, rho)
            Just (i, root) -> (i, root)

        keep = \case
            Nothing        -> Nothing
            Just (i, root) -> Just (i + 1, TcType.mkTyConApp envExtOp [k, v, root, nm, a])

newDict :: Env -> NewDictRecipe -> TcPluginM ((TcEvidence.EvTerm, Ct), [Ct])
newDict env = \case

    NewKnownLTRecipe old k v x rho i rho' -> do
        let Env{envKnownLT, envKnownLTCo, envKnownLTExt, envPlatform} = env

        new <- do
            let loc = Ct.ctLoc old
            let ty  = TcType.mkTyConApp (classTyCon envKnownLT) [k, v, x, rho']
            TcPluginM.newWanted loc ty

        let ev =
                 (`GhcPlugins.mkCast` GhcPlugins.mkSymCo (envKnownLTCo k v x rho))
               $ (\inner -> TcEvidence.evId envKnownLTExt `Core.mkTyApps` [k, v, x, rho', rho] `Core.mkApps` [Core.mkIntLit envPlatform (toInteger i), inner])
               $ (`GhcPlugins.mkCast` envKnownLTCo k v x rho')
               $ Ct.ctEvExpr new

        pure ((TcEvidence.EvExpr ev, old), [Ct.mkNonCanonical new])

    NewAllColsRecipe old k v c rho0 (Extends assocs) root -> do
        let Env{envAllCols, envAllColsCo, envAllColsHelp, envAllColsExt, envAssign, envExtOp} = env

        let cons (nm, a) (rho, news, inner) = do
                new <- do
                    let loc = Ct.ctLoc old
                    let ty  = TcType.mkTyConApp envAllColsHelp [k, v, c, nm, a, rho]
                    TcPluginM.newWanted loc ty

                let rho' = TcType.mkTyConApp envExtOp [k, v, rho, TcType.mkTyConApp envAssign [k, v, nm, a]]

                pure $ (,,) rho' (new : news) $
                                    TcEvidence.evId envAllColsExt
                    `Core.mkTyApps` [k, v, c, nm, a, rho]
                    `Core.mkApps`   [Ct.ctEvExpr new]
                    `Core.mkApps`   [ Core.mkTyApps (TcEvidence.evId proxyHashId) [knd, typ] | (knd, typ) <- [(k, nm), (v, a)] ]
                    `Core.mkApps`   [inner]
        new <- do
            let loc = Ct.ctLoc old
            let ty  = TcType.mkTyConApp (classTyCon envAllCols) [k, v, c, root]
            TcPluginM.newWanted loc ty

        (_rho, news, ev) <- foldr
            (\assoc acc -> acc >>= cons assoc)
            (pure (root, [], Ct.ctEvExpr new `GhcPlugins.mkCast` envAllColsCo k v c root))
            assocs
        let et = TcEvidence.EvExpr $ ev `GhcPlugins.mkCast` GhcPlugins.mkSymCo (envAllColsCo k v c rho0)

        pure ((et, old), map Ct.mkNonCanonical (new : news))

-----

-- | The domain-specific knowledge
--
-- This plugin does not implement any interactions, so we simplify each constraint individually.
--
-- Also, it only does /Improvement/.
-- It does not improve Givens.
-- To improve Wanteds, it adds missing Wanteds.
--
-- > rho :& nm := l ~ rho :& nm := r   implies/requires   l ~ r
--
-- > rho :& l := a ~ rho :& r := a   implies/requires   l ~ r
--
-- > l :& nm := a ~ r :& nm := a   implies/requires   l ~ r
--
-- > rho :& x := a :& y := b :& ... ~ Row# cols   implies/requires   rho ~ Row# cols :# y :# x, b ~ Select y ..., a ~ Select x ...
improve :: Env -> Ct -> [(Extension, Extension)] -> Maybe NewEqRecipe
improve env ct existingEqs = case ct of
    Ct.CNonCanonical{}
      | Just (TcEvidence.Nominal, lhs, rhs) <- Predicate.getEqPredTys_maybe (Ct.ctPred ct)
      -> go lhs rhs
    _ -> Nothing
  where

    go lhs rhs = case getExtend env lhs of   -- the LHS will never be the Row#, will it?
      Just lext
        | isEmp env rhs
        -> NewEqRecipe ct NothingEvTerm <$> goInverted env lext rhs []

        | Just rext <- getExtend env rhs
        -> goExtExt env existingEqs ct lext rext

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
    Extend _ty _mbNewTy k v nm a rho = ext

    acc' = NewEquality a (mkSelect env k v nm rhs) : acc

    rhs' = mkRestrict env k v nm rhs

goExtExt :: Env -> [(Extension, Extension)] -> Ct -> Extension -> Extension -> Maybe NewEqRecipe
goExtExt env existingEqs old lext rext
    -- wait for kinds to match
  | not $ lk `eqType` rk && lv `eqType` rv = Nothing

  | otherwise =
        (NewEqRecipe old NothingEvTerm <$> goOuterInjectivity env lext rext)
    <|>
        (       (\(co, eqs) -> NewEqRecipe old (JustEvTerm (TcEvidence.evCoercion co)) eqs)
            <$> (isRearranged env lext rext <|> goUnfold existingEqs lext rext)
        )
  where
    Extend _lb _lty lk lv _lnm _la _lrho = lext
    Extend _rb _rty rk rv _rnm _ra _rrho = rext

-- | This simple treatment of just one layer suffices for the general
-- definitions in "BriskRows.Internal.RV" etc.
goOuterInjectivity :: Env -> Extension -> Extension -> Maybe [NewEquality]
goOuterInjectivity env lext rext
    -- if the outermost names are equal, require the images and (recursively) extended rows are too
  | equal env lnm rnm   = Just [NewEquality la ra, NewEquality lrho rrho]

    -- This is commented out because 'isRearranged' supplants this rule.
{-
    -- if the extended rows are equal, require the outermost names and images are too
  | equal env lrho rrho = Just [NewEquality la ra, NewEquality lnm  rnm ]
-}

  | otherwise = Nothing
  where
    Extend _lb _lty _lk _lv lnm la lrho = lext
    Extend _rb _rty _rk _rv rnm ra rrho = rext

-- | This ensures that unsolved equivalences are not generalized over.
--
-- TODO cleaner way?
goUnfold :: [(Extension, Extension)] -> Extension -> Extension -> Maybe (TcEvidence.TcCoercion, [NewEquality])
goUnfold _existingEqs lext rext
    -- ensure both are expanded
  | Nothing <- lmbNewTy
  , Nothing <- rmbNewTy
  = Nothing

--  , Nothing <- find (eq2 (lext, rext)) existingEqs -} = Just (co, [NewEquality lty rty])

  | otherwise = Just (co, [NewEquality (fromMaybe lty lmbNewTy) (fromMaybe rty rmbNewTy)])
  where
    Extend lty lmbNewTy _lk _lv _lnm _la _lrho = lext
    Extend rty rmbNewTy _rk _rv _rnm _ra _rrho = rext

    _eq2 (ll, lr) (rl, rr) = eqExtension ll rl && eqExtension lr rr

    -- TODO Any way something like floating could make this unsound? If so, any
    -- way to express within this coercion that it depends on the other
    -- equalities?
    co = GhcPlugins.mkUnivCo (TyCoRep.PluginProv "brisk-rows:Perm") TyCon.Nominal lty rty

eqExtension :: Extension -> Extension -> Bool
eqExtension (Extend _ _ lk lv lnm la lrho) (Extend _ _ rk rv rnm ra rrho)
  =  lk   `eqType` rk
  && lv   `eqType` rv
  && lnm  `eqType` rnm
  && la   `eqType` ra
  && lrho `eqType` rrho

-----

foobar :: (a -> Maybe b) -> [a] -> [(a, [b])]
foobar f =
    \xs -> fst $ go id (map f xs) xs
  where
   go acc ys = \case
       []   -> ([], [])
       x:xs -> let (xs', ys') = go (maybe acc (\y -> acc . (y:)) (head ys)) (tail ys) xs
               in ((x, acc ys') : xs', maybe id (:) (head ys) ys')

-----

data Extensions = Extends [(TcType, TcType)]

peel :: Env -> Extension -> (TcType, Extensions)
peel env ext =
    ((nm, a) `cons`) <$> maybe (rho, Extends []) (peel env) (getExtend env rho)
  where
    Extend _b _tc _k _v nm a rho = ext

    cons x (Extends xs) = Extends (x : xs)

pop :: Env -> TcType -> [(TcType, x)]-> Extensions -> Maybe (TcType, Extensions)
pop env needle misses = \case
    Extends []               -> Nothing
    Extends (assoc : assocs)
        -- TODO zonk them?
      | eq  (fst assoc) -> do guard (all (apt . fst) misses); Just (snd assoc, Extends assocs)
      | apt (fst assoc) -> fmap (cons assoc) <$> pop env needle misses (Extends assocs)
      | otherwise       -> Nothing
  where
    cons x (Extends xs) = Extends (x : xs)

    eq  = equal env needle
    apt = apart env needle

-----

-- | Implied smaller equalities and a root-to-root coercion for two equated
-- extensions whose columns names are either merely rearranged or else only one
-- degree of freedom away from that.
--
-- We must use 'typesCantMatch' in 'pop', or else this is unsound. Without
-- 'typesCantMatch', it would simplify @l :& a := Int :& b := Char ~ r :& b :=
-- Int :& a := Char@ to @(l ~ r, Int ~ Char)@. The @l ~ r@ conclusion is sound,
-- but the contradiction is not because the equivalence is satisfiable, eg with
-- @a ~ b@.
isRearranged :: Env -> Extension -> Extension -> Maybe (TcEvidence.TcCoercion, [NewEquality])
isRearranged env lext rext =
    (,) co <$> goAssocs [] [] lassocs0 rassocs0
  where
    eq = equal env

    -- We're solving the equality using this coercion, but we're also adding
    -- new Wanted equalities that ensure this equality will /eventually zonk/
    -- to a mere rearrangement.
    --
    -- TODO Any way something like floating could make this unsound? If so, any
    -- way to express within this coercion that it depends on the other
    -- equalities?
    co = GhcPlugins.mkUnivCo (TyCoRep.PluginProv "brisk-rows:Perm") TyCon.Nominal lty rty

    Extend lty _lmbNewTy _lk _lv _lnm _la _lrho = lext
    Extend rty _rmbNewTy _rk _rv _rnm _ra _rrho = rext

    (lroot, lassocs0) = peel env lext
    (rroot, rassocs0) = peel env rext

    goAssocs acc miss lassocs rassocs = case lassocs of
        Extends []                     -> goDone acc miss rassocs
        Extends ((lnm, la) : lassocs') ->
         case pop env lnm miss rassocs of
             Just (ra, rassocs') -> goAssocs (NewEquality la ra : acc)              miss  (Extends lassocs') rassocs'
             Nothing             -> goAssocs acc                       ((lnm, la) : miss) (Extends lassocs') rassocs

    goDone acc miss rassocs = case let Extends xs = rassocs in (miss, xs) of
        ([], []) ->
            -- The column names are merely rearranged, so this equality
            -- simplifies to requiring the roots are equal.
            pure $ NewEquality lroot rroot : acc

        ([],  _:_) -> Nothing   -- currently ragged
        (_:_, [] ) -> Nothing   -- currently ragged

        ((lnm0, la0) : misses, (rnm0, ra0) : leftovers)
          | not $ eqType lroot rroot      -> Nothing
          | all (eq lnm0 . fst) misses    -> goUni False acc lnm0 (reverse $ la0 : map snd misses   ) (          (rnm0, ra0) : leftovers)
          | all (eq rnm0 . fst) leftovers -> goUni True  acc rnm0 (          ra0 : map snd leftovers) (reverse $ (lnm0, la0) : misses   )
          | otherwise                     -> Nothing

    -- The roots are identical and one side has identical names.
    --
    -- If there's the same number of names on both sides, require all columns
    -- are equal.
    goUni flipped acc lnm las rassocs = case (las, rassocs) of
        ([],  [] ) -> Just acc
        ([],  _:_) -> Nothing   -- currently ragged
        (_:_, [] ) -> Nothing   -- currently ragged

        (la : las', (rnm, ra) : rassocs') -> goUni flipped (mk lnm rnm : mk la ra : acc) lnm las' rassocs'
      where
        mk l r = if flipped then NewEquality r l else NewEquality l r
