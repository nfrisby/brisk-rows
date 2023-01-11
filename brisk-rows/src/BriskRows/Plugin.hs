{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module BriskRows.Plugin (plugin) where

import           Debug.Trace (trace)

import           Control.Monad (ap, foldM, guard)
import           Data.Coerce (coerce)
import           Data.Functor ((<&>))
import qualified Data.List.NonEmpty as NE
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Maybe (mapMaybe)
import           Data.Traversable (forM)

import           GHC.Types.Id.Make (proxyHashId)
import           GHC.Core.Class (Class, classTyCon)
import           GHC.Core.DataCon (dataConWrapId)
import           GHC.Platform (Platform)
import qualified GHC.Core as Core
import           GHC.Core.Make (mkCoreApps)
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
      , TcRnTypes.tcPluginRewrite = \env@Env{envCmpName, envUnsafeExt} ->
          -- NOTE WELL that these rewrites only happen inside of constraints!
          --
          -- TODO confirm that
                unitUFM envCmpName   (\_rwenv _gs args -> pure $ rewriteCmpName env args)
            <>
                unitUFM envUnsafeExt (\_rwenv _gs args -> pure $ rewriteUnsafeExt env args)
      , TcRnTypes.tcPluginSolve   = \env evBindsVar gs ws -> do
            famInstEnvs <- TcPluginM.getFamInstEnvs

            doTrace env $ text $ "\n\n\n==========INCOMING\n"
            doTrace env $ ppr $ gs <> ws

            let gidx          = indexGivens env gs
                given_contras = checkGivens gidx

            -- only work on the Givens if there are no Wanteds
            let cts = if null ws then gs else ws

            doTrace env $ text $ "\n\n\n==========TABLE\n"
            do
                let GivensIndex (RowVarLTs x) (RowVarDefns y) = gidx
                doTrace env $ ppr $ Map.toList $ Map.map Map.keys x
                doTrace env $ ppr $ Map.keys y

            -- TODO properly prevent a Given CEqCan from simplifying itself
            let (irrel_contras, recipes) = mapStep (improve env famInstEnvs (if null ws then GivensIndex (RowVarLTs Map.empty) (RowVarDefns Map.empty) else gidx)) cts

            doTrace env $ text $ "\n\n\n==========IRREL RECIPES\n"
            doTrace env $ ppr recipes

            doTrace env $ text $ "\n\n\n==========NEW IRREL\n"
            newIrrels <- mapM (newIrrel env evBindsVar) recipes

            doTrace env $ text $ "\n\n\n==========CONTRADICTIONS\n"
            doTrace env $ ppr given_contras
            doTrace env $ ppr irrel_contras

            let dictRecipes = mapMaybe (simplifyDict env famInstEnvs gidx) cts
            doTrace env $ text $ "\n\n\n==========DICT RECIPES\n"
            doTrace env $ ppr dictRecipes

            doTrace env $ text $ "\n\n\n==========NEW DICTS\n"
            (solvedDicts, newDictss) <- fmap unzip $ mapM (newDict env evBindsVar) dictRecipes

            pure TcPluginSolveResult {
                tcPluginInsolubleCts = if null given_contras then irrel_contras else given_contras
              ,
                tcPluginSolvedCts    = map (oldIrrel env) recipes ++ solvedDicts
              ,
                tcPluginNewCts       = concat newIrrels ++ concat newDictss
              }
      }
  }


-- | A type making it explicit that we're opting into the non-determistic ordering on 'TcType'
newtype NonDetTcType = NonDetTcType TcType
instance GhcPlugins.Outputable NonDetTcType where ppr (NonDetTcType ty) = ppr ty
instance Eq  NonDetTcType where NonDetTcType l == NonDetTcType r = eqType l r
instance Ord NonDetTcType where compare (NonDetTcType l) (NonDetTcType r) = TcType.nonDetCmpType l r

-- | An index of the 'BriskRows.Internal.KnownLT' Given constraints
newtype RowVarLTs = RowVarLTs (Map NonDetTcType (Map NonDetTcType TcEvidence.EvExpr))

-- | An index of the 'CEqCan's that are elimnating extensions.
--
-- TODO when would it be productive to consider many possible extensions?
newtype RowVarDefns = RowVarDefns (Map NonDetTcType (NE.NonEmpty (Ct, Extension)))

data GivensIndex = GivensIndex RowVarLTs RowVarDefns

indexGivens :: Env -> [Ct] -> GivensIndex
indexGivens env =
    go Map.empty Map.empty
  where
    Env {envAssign, envExtOp, envKnownLT, envKnownLTCo} = env

    go acc_knownLT acc_extEq = \case
        []       -> GivensIndex (RowVarLTs acc_knownLT) (RowVarDefns acc_extEq)
        ct : cts



          | Just (tc, args) <- TcType.tcSplitTyConApp_maybe (Ct.ctPred ct)
          , tc == classTyCon envKnownLT
          , [k, v, nm, rho] <- args
          , Just envExtOp /= TcType.tcTyConAppTyCon_maybe rho

          , let ex   =
                                        Ct.ctEvExpr (Ct.ctEvidence ct)
                    `GhcPlugins.mkCast` envKnownLTCo k v nm rho
                    `mkCoreApps`        [ Core.mkTyApps (TcEvidence.evId proxyHashId) [TcType.tcTypeKind x, x] | x <- [nm, rho] ]
          , let acc' = Map.insertWith Map.union (NonDetTcType rho) (Map.singleton (NonDetTcType nm) ex) acc_knownLT
          -> go acc' acc_extEq cts



          | Ct.CEqCan{Ct.cc_lhs, Ct.cc_rhs} <- ct
          , Ct.TyFamLHS tc args <- cc_lhs

          , tc == envExtOp
          , [k, v, rho, asn] <- args
          , Just (tc', args') <- TcType.tcSplitTyConApp_maybe asn

          , tc' == envAssign
          , [k', v', nm, a] <- args'
          , eqType k k' && eqType v v'

          , let ext  = Extend k v nm a rho
          , let acc' = Map.insertWith (<>) (NonDetTcType cc_rhs) ((,) ct ext NE.:| []) acc_extEq
          -> go acc_knownLT acc' cts



          | otherwise
          -> go acc_knownLT acc_extEq cts

checkGivens :: GivensIndex -> [Ct]
checkGivens gidx =
    go $ map (bounded [] Set.empty) (Map.toList m)
  where
    GivensIndex _rowVarLTs (RowVarDefns m) = gidx

    go = \case
        []     -> []
        xs:xss -> if null xs then go xss else xs

    bounded path visited (rhs, exts) =
        go [ bounded1 path (Set.insert rhs visited) ct ext | (ct, ext) <- NE.toList exts ]

    bounded1 path visited ct ext
        | Set.member rhs' visited
        = path'

        | Just exts' <- Map.lookup rhs' m
        = bounded path' visited (rhs', exts')

        | otherwise = []
      where
        Extend _k _v _nm _a rho = ext

        rhs' = NonDetTcType rho

        path' = ct : path

-----

lookupModule :: String -> TcPluginM GhcPlugins.Module
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

lookupId :: GhcPlugins.Module -> String -> TcPluginM GhcPlugins.Id
lookupId modul s =
    TcPluginM.lookupOrig modul (GhcPlugins.mkVarOcc s) >>=
    TcPluginM.tcLookupId

lookupTC :: GhcPlugins.Module -> String -> TcPluginM GhcPlugins.TyCon
lookupTC modul s =
    TcPluginM.lookupOrig modul (GhcPlugins.mkTcOcc s) >>=
    TcPluginM.tcLookupTyCon

lookupPDC :: GhcPlugins.TyCon -> String -> TcPluginM GhcPlugins.TyCon
lookupPDC tc s = GhcPlugins.promoteDataCon <$> lookupDC tc s

lookupDC :: GhcPlugins.TyCon -> String -> TcPluginM GhcPlugins.DataCon
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
    doTrace           :: GhcPlugins.SDoc -> TcPluginM ()
  ,
    doTrace_          :: forall a. GhcPlugins.SDoc -> a -> a
  ,
    envAbsent         :: !Class
  ,
    envAbsentCon      :: !GhcPlugins.DataCon
  ,
    envAllCols        :: !Class
  ,
    -- | Coercion from KnownLT to its method type at the given @k@, @v@, @nm@, and @rho@.
    envAllColsCo      :: !(TcKind -> TcKind -> TcType -> TcType -> TyCoRep.Coercion)
  ,
    envApart          :: !TyCon
  ,
    envAssign         :: !TyCon
  ,
    envCastAllCols    :: !GhcPlugins.Id
  ,
    envCmpName        :: !TyCon
  ,
    envDict           :: !TyCon
  ,
    envDictCon        :: !GhcPlugins.DataCon
  ,
    envEQ             :: !TyCon
  ,
    envEmp            :: !TyCon
  ,
    envExtOp          :: !TyCon
  ,
    envGT             :: !TyCon
  ,
    envGivenAllCols1  :: !GhcPlugins.Id
  ,
    envGivenAllCols2  :: !GhcPlugins.Id
  ,
    envGivenKnownLT   :: !GhcPlugins.Id
  ,
    envGivenKnownLen  :: !GhcPlugins.Id
  ,
    envKnownLT        :: !Class
  ,
    -- | Coercion from KnownLT to its method type at the given @k@, @v@, @nm@, and @rho@.
    envKnownLTCo      :: !(TcKind -> TcKind -> TcType -> TcType -> TyCoRep.Coercion)
  ,
    envKnownLen       :: !Class
  ,
    -- | Coercion from KnownLen to its method type at the given @k@, @v@, and @rho@.
    envKnownLenCo     :: !(TcKind -> TcKind -> TcType -> TyCoRep.Coercion)
  ,
    envLT             :: !TyCon
  ,
    envPlatform       :: !Platform
  ,
    envROW            :: !TyCon
  ,
    envSem            :: !TyCon
  ,
    envUncastAllCols  :: !GhcPlugins.Id
  ,
    envUnsafeExt      :: !TyCon
  ,
    envWantedAllCols  :: !GhcPlugins.Id
  ,
    envWantedKnownLT  :: !GhcPlugins.Id
  ,
    envWantedKnownLen :: !GhcPlugins.Id
  }

newEnv :: TcPluginM Env
newEnv = do
    dflags <- TcRnTypes.unsafeTcPluginTcM GhcPlugins.getDynFlags

    modul <- lookupModule "BriskRows.Internal"
    let luTC = lookupTC modul

    envAbsent <- TyCon.tyConClass_maybe <$> luTC "Absent" >>= \case
        Just cls -> pure cls
        Nothing  -> panicDoc "Plugin.BriskRows could not find the Absent class" (text "")
    envAbsentCon <- case TyCon.tyConSingleDataCon_maybe (classTyCon envAbsent) of
        Just x  -> pure x
        Nothing -> panicDoc "Plugin.BriskRows could not find the Absent dictonary constructor" (text "")

    envAllCols <- TyCon.tyConClass_maybe <$> luTC "AllCols" >>= \case
        Just cls -> pure cls
        Nothing  -> panicDoc "Plugin.BriskRows could not find the AllCols class" (text "")

    envAllColsCo <- case TyCon.unwrapNewTyCon_maybe (classTyCon envAllCols) of
        Just (_tvs, _rhs, coax) -> pure $ \k v c rho -> TcEvidence.mkTcUnbranchedAxInstCo coax [k, v, c, rho] []
        Nothing                 -> panicDoc "Plugin.BriskRows could not treat AllCol as a newtype" (text "")

    envAssign <- do
      tc <- luTC "COL"
      lookupPDC tc ":="

    envCastAllCols <- lookupId modul "castAllCols"

    envCmpName <- luTC "CmpName"

    envDict <- lookupModule "BriskRows.Sem" >>= flip lookupTC "Dict"
    envDictCon <- lookupDC envDict "Dict"

    (envApart, envEQ) <- do
        tc <- luTC "NameOrdering"
        apart_ <- lookupPDC tc "NameApart"
        eq <- lookupPDC tc "NameEQ"
        pure (apart_, eq)
    (envGT, envLT) <- do
        tc <- luTC "NameApartness"
        gt <- lookupPDC tc "NameGT"
        lt <- lookupPDC tc "NameLT"
        pure (gt, lt)

    envEmp <- luTC "ROW" >>= flip lookupPDC "Emp"

    envExtOp  <- luTC ":&"

    envGivenAllCols1 <- lookupId modul "givenAllCols1"
    envGivenAllCols2 <- lookupId modul "givenAllCols2"
    envGivenKnownLT  <- lookupId modul "givenKnownLT"
    envGivenKnownLen <- lookupId modul "givenKnownLen"

    envKnownLT <- TyCon.tyConClass_maybe <$> luTC "KnownLT" >>= \case
        Just cls -> pure cls
        Nothing  -> panicDoc "Plugin.BriskRows could not find the KnownLT class" (text "")

    envKnownLTCo <- case TyCon.unwrapNewTyCon_maybe (classTyCon envKnownLT) of
        Just (_tvs, _rhs, coax) -> pure $ \k v x rho -> TcEvidence.mkTcUnbranchedAxInstCo coax [k, v, x, rho] []
        Nothing                 -> panicDoc "Plugin.BriskRows could not treat KnownLT as a newtype" (text "")

    envKnownLen <- TyCon.tyConClass_maybe <$> luTC "KnownLen" >>= \case
        Just cls -> pure cls
        Nothing  -> panicDoc "Plugin.BriskRows could not find the KnownLen class" (text "")

    envKnownLenCo <- case TyCon.unwrapNewTyCon_maybe (classTyCon envKnownLen) of
        Just (_tvs, _rhs, coax) -> pure $ \k v rho -> TcEvidence.mkTcUnbranchedAxInstCo coax [k, v, rho] []
        Nothing                 -> panicDoc "Plugin.BriskRows could not treat KnownLT as a newtype" (text "")

    envPlatform <- TcPluginM.getTargetPlatform

    envROW <- luTC "ROW"

    envSem <- lookupModule "BriskRows.Sem" >>= flip lookupTC "Sem"

    envUncastAllCols <- lookupId modul "uncastAllCols"

    envUnsafeExt <- luTC "UnsafeExt"

    envWantedAllCols  <- lookupId modul "wantedAllCols"
    envWantedKnownLT  <- lookupId modul "wantedKnownLT"
    envWantedKnownLen <- lookupId modul "wantedKnownLen"

    pure Env{
              doTrace  = \_ -> pure () -- \x -> TcPluginM.tcPluginIO $ putStrLn $ showSDoc dflags x
            , doTrace_ = \x -> trace (showSDoc dflags x)
            , ..
            }

isEmp :: Env -> TcType -> Bool
isEmp Env{envEmp} ty = case TcType.tcSplitTyConApp_maybe ty of
    Just (tc, [_k, _v]) -> envEmp == tc
    _                   -> False

mkExtensions :: Env -> TcKind -> TcKind -> TcType -> Extensions Outermost -> TcType
mkExtensions env k v root exts =
    case unconsE exts of
        Nothing             -> root
        Just (nm, a, exts') ->
            let asn   = TcType.mkTyConApp envAssign [k, v, nm, a]
                inner = mkExtensions env k v root exts'
            in
            TcType.mkTyConApp envExtOp [k, v, inner, asn]
  where
    Env{envAssign, envExtOp} = env

mkAbsent :: Env -> TcKind -> TcKind -> TcType -> TcType -> TcType
mkAbsent env k v nm rho =
    TcType.mkTyConApp (classTyCon envAbsent) [k, v, nm, rho]
  where
    Env{envAbsent} = env

mkAbsentDict :: Env -> TcKind -> TcKind -> TcType -> TcType -> TcEvidence.EvExpr
mkAbsentDict env k v nm rho =
    TcEvidence.evId (dataConWrapId envAbsentCon) `Core.mkTyApps` [k, v, nm, rho]
  where
    Env{envAbsentCon} = env

-----

-- | See 'BriskRows.Internal.CmpName' for the explanation of we implement its reflexivity in the plugin
rewriteCmpName :: Env -> [TcType] -> TcRnTypes.TcPluginRewriteResult
rewriteCmpName env args = case args of
  [_k, l, r]
    | l `eqType` r -> TcRnTypes.TcPluginRewriteTo (Reduction co rhs) []
  _ -> TcRnTypes.TcPluginNoRewrite
  where
    Env{envCmpName, envEQ} = env

    lhs = TcType.mkTyConApp envCmpName args
    rhs = TcType.mkTyConTy envEQ

    co = GhcPlugins.mkUnivCo (TyCoRep.PluginProv "brisk-rows:CmpName.Refl") TyCon.Nominal lhs rhs

rewriteUnsafeExt :: Env -> [TcType] -> TcRnTypes.TcPluginRewriteResult
rewriteUnsafeExt env args = case args of
  [k, v, nm, a, rho] ->
      let lhs = TcType.mkTyConApp envUnsafeExt args
          asn = TcType.mkTyConApp envAssign [k, v, nm, a]
          rhs = TcType.mkTyConApp envExtOp [k, v, rho, asn]

          co = GhcPlugins.mkUnivCo (TyCoRep.PluginProv "brisk-rows:UnsafeExt") TyCon.Nominal lhs rhs
      in
      TcRnTypes.TcPluginRewriteTo (Reduction co rhs) []
  _ -> TcRnTypes.TcPluginNoRewrite
  where
    Env{envAssign, envExtOp, envUnsafeExt} = env

-----

data OldEquality = OldEquality !TcType !TcType
data NewEquality = NewEquality !TcType !TcType

data NewIrrelRecipe =
    NewAbsentRecipe !Ct !TcKind !TcKind !TcType !TcType !TcType
  |
    NewEqRecipe !Ct !OldEquality ![NewEquality]

oldIrrel :: Env -> NewIrrelRecipe -> (TcEvidence.EvTerm, Ct)
oldIrrel env = \case
    NewAbsentRecipe old k v nm rho _rho' -> case Ct.ctEvidence old of
        Ct.CtGiven{} ->
            -- GHC plugin interface's weird rule: use a Given's own evidence in order to eliminate it.
            let evtm = Ct.ctEvTerm (Ct.ctEvidence old)
            in (evtm, old)
        Ct.CtWanted{} ->
            let evex = mkAbsentDict env k v nm rho
            in (TcEvidence.EvExpr evex, old)
    NewEqRecipe old (OldEquality lhs rhs) _news -> case Ct.ctEvidence old of
        Ct.CtGiven{} ->
            -- GHC plugin interface's weird rule: use a Given's own evidence in order to eliminate it.
            let evtm = Ct.ctEvTerm (Ct.ctEvidence old)
            in (evtm, old)
        Ct.CtWanted{} ->
            let co = GhcPlugins.mkUnivCo (TyCoRep.PluginProv "brisk-rows:Row.Rearrange") TyCon.Nominal lhs rhs
            in (TcEvidence.evCoercion co, old)

newIrrel :: Env -> TcEvidence.EvBindsVar -> NewIrrelRecipe -> TcPluginM [Ct]
newIrrel env evBindsVar = \case
    NewAbsentRecipe old k v nm rho rho' -> do
        let loc = Ct.ctLoc old
            ty  = mkAbsent env k v nm rho'
        ((:[]) . Ct.mkNonCanonical) <$> case Ct.ctEvidence old of
            Ct.CtWanted{} -> TcPluginM.newWanted loc ty
            Ct.CtGiven {} ->
                TcPluginM.newGiven evBindsVar loc ty
              $ mkAbsentDict env k v nm rho
    NewEqRecipe old _oldeq news ->
        forM news $ \(NewEquality lhs rhs) -> do
            let loc = Ct.ctLoc old
                eq  = Predicate.mkPrimEqPred lhs rhs
            doTrace env $ text "EMITTING" <+> ppr eq
            Ct.mkNonCanonical <$> case Ct.ctEvidence old of
                Ct.CtWanted{} -> TcPluginM.newWanted loc eq
                Ct.CtGiven {} ->
                    TcPluginM.newGiven evBindsVar loc eq
                  $ Core.Coercion
                  $ GhcPlugins.mkUnivCo (TyCoRep.PluginProv "brisk-rows:Row.Rearrange") TyCon.Nominal lhs rhs

instance GhcPlugins.Outputable NewEquality where
  ppr (NewEquality lhs rhs) = text "NewEquality" <+> ppr (lhs, rhs)

instance GhcPlugins.Outputable NewIrrelRecipe where
  ppr (NewAbsentRecipe old k v nm rho rho') = text "NewAbsentRecipe" <+> ppr (old, k, v, nm, rho, rho')
  ppr (NewEqRecipe     old _oldeq news) = text "NewEqRecipe" <+> ppr (old, news)

-----

data Extension =
    -- | @Extend_Row# {k} {v} nm a rho _err@
    Extend !TcKind !TcKind !TcType !TcType !TcType

-- | TODO detect cycles and abort with 'Contra' when 'getExtend' is called in a loop
getExtend :: Env -> GivensIndex -> TcType -> Maybe Extension
getExtend env gidx ty
    | Just (tc, args) <- TcType.tcSplitTyConApp_maybe ty
    , tc == envExtOp
    , [k, v, rho, col] <- args
    , Just (tc', args') <- TcType.tcSplitTyConApp_maybe col
    , tc' == envAssign
    , [k', v', nm, a] <- args'
    , eqType k k' && eqType v v'
    = Just $ Extend k v nm a rho

    | Just ((,) _ct ext NE.:| []) <- Map.lookup (NonDetTcType ty) m
    = Just ext

    | otherwise
    = Nothing
  where
    Env{envAssign, envExtOp} = env
    GivensIndex _rowVarLTs (RowVarDefns m) = gidx

-----

equal :: Env -> FamInstEnvs -> TcType -> TcType -> Bool
equal env famInstEnvs x y = Just EQ == cmp env famInstEnvs x y

apart :: Env -> FamInstEnvs -> TcType -> TcType -> Bool
apart env famInstEnvs x y = maybe False (\case NameApart{} -> True; NameEQ -> False) $ cmp_ env famInstEnvs x y

data NameOrdering  = NameEQ | NameApart (Maybe NameApartness)
data NameApartness = NameLT | NameGT

cmp :: Env -> FamInstEnvs -> TcType -> TcType -> Maybe Ordering
cmp env famInstEnvs l r = cmp_ env famInstEnvs l r >>= \case
    NameEQ      -> Just EQ
    NameApart x -> x >>= \case
        NameLT  -> Just LT
        NameGT  -> Just GT

cmp_ :: Env -> FamInstEnvs -> TcType -> TcType -> Maybe NameOrdering
cmp_ env famInstEnvs =
    \x y -> go $ reductionReducedType $ normaliseTcApp famInstEnvs TyCon.Nominal envCmpName [TcType.tcTypeKind x, x, y]
  where
    Env {envApart, envCmpName, envEQ, envGT, envLT} = env

    go ty = case TcType.tcSplitTyConApp_maybe ty of
        Nothing         -> Nothing
        Just (tc, args)
          | tc == envEQ -> Just NameEQ

          | tc == envApart
          , [ty'] <- args
          -> Just $ NameApart $ go' ty'

          | Just ty' <- step tc args
          -> go ty'

          | tc == envCmpName
          , [_k, x, y] <- args
          , eqType x y
          -> Just NameEQ

          | otherwise
          -> Nothing

    go' ty = case TcType.tcSplitTyConApp_maybe ty of
        Nothing         -> Nothing
        Just (tc, args)
          | tc == envLT -> Just NameLT
          | tc == envGT -> Just NameGT

          | Just ty' <- step tc args
          -> go' ty'

          | otherwise
          -> Nothing

    step tc args
        | Just (sigma, body, oversat) <- TyCon.expandSynTyCon_maybe tc args
        = Just $ TcType.substTy (TcType.mkTvSubstPrs sigma) body `TcType.mkAppTys` oversat

        | Just (HetReduction redn _co) <- topReduceTyFamApp_maybe famInstEnvs tc args
        = Just $ reductionReducedType redn

        | otherwise
        = Nothing

-----

data NewDictRecipe =
    -- | @old k v x rho i rho'@
    NewKnownLTRecipe !Ct !TcKind !TcKind !TcType !TcType !Int !TcType
  |
    -- | @old k v rho i rho'@
    NewKnownLenRecipe !Ct !TcKind !TcKind !TcType !Int !TcType
  |
    -- | @old k v c rho extracts rho'@
    --
    -- The extracts are the columns that have a decided order wrt every other
    -- column in the row and an in-scope 'KnownLT' wrt to the row's root.
    NewAllColsRecipe !Ct !TcKind !TcKind !TcType !TcType (DirectedList Innermost (TcType, TcType, KnownLtInt)) !TcType

instance GhcPlugins.Outputable NewDictRecipe where
  ppr (NewKnownLTRecipe  old k v x rho i        rho') = text "NewKnownLTRecipe"  <+> ppr (old, k, v, x, rho, i,                           rho')
  ppr (NewKnownLenRecipe old k v   rho i        rho') = text "NewKnownLenRecipe" <+> ppr (old, k, v,    rho, i,                           rho')
  ppr (NewAllColsRecipe  old k v c rho extracts rho') = text "NewAllColsRecipe"  <+> ppr (old, k, v, c, rho, forgetDirectedList extracts, rho')

simplifyDict :: Env -> FamInstEnvs -> GivensIndex -> Ct -> Maybe NewDictRecipe
simplifyDict env famInstEnvs gidx ct = case ct of
    Ct.CDictCan{Ct.cc_class, Ct.cc_tyargs}

      | cc_class == envKnownLT
      , [k, v, x, rho] <- cc_tyargs
      , Just ext <- getExtend env gidx rho
      -> goKnownLT x ext <&> \(i, rho') -> NewKnownLTRecipe ct k v x rho i rho'

      | cc_class == envKnownLen
      , [k, v, rho] <- cc_tyargs
      , Just ext <- getExtend env gidx rho
      -> Just $ let (rho', i) = goKnownLen ext in NewKnownLenRecipe ct k v rho i rho'

      | cc_class == envAllCols
      , [k, v, c, rho] <- cc_tyargs
      , Just ext <- getExtend env gidx rho
      , let (root, exts) = peel env gidx ext
      -> goAllCols k v root nil nilE (revE exts) <&> \(extracts, rho') -> NewAllColsRecipe ct k v c rho extracts rho'

    _ -> Nothing
  where
    Env{envAllCols, envExtOp, envKnownLT, envKnownLen} = env

    goKnownLT :: TcType -> Extension -> Maybe (Int, TcType)
    goKnownLT x ext = ($ recu) $ case cmp env famInstEnvs nm x of
        Just o  -> Just . if LT == o then incr else skip
        Nothing -> keep
      where
        Extend k v nm a rho = ext

        recu = getExtend env gidx rho >>= goKnownLT x

        incr = \case
            Nothing        -> (1, rho)
            Just (i, root) -> (i + 1, root)

        skip = \case
            Nothing        -> (0, rho)
            Just (i, root) -> (i, root)

        keep = \case
            Nothing        -> Nothing
            Just (i, root) -> Just (i + 1, TcType.mkTyConApp envExtOp [k, v, root, nm, a])

    goKnownLen :: Extension -> (TcType, Int)
    goKnownLen ext =
        (+1) <$> case getExtend env gidx rho of
            Nothing   -> (rho, 0)
            Just rho' -> goKnownLen rho'
      where
        Extend _k _v _nm _a rho = ext

    goAllCols ::
         TcKind
      -> TcKind
      -> TcType
      -> DirectedList Innermost (TcType, TcType, KnownLtInt)
      -> Extensions Innermost
      -> Extensions Outermost
      -> Maybe (DirectedList Innermost (TcType, TcType, KnownLtInt), TcType)
    goAllCols k v root hits misses =
        (. unconsE) $ \case
            Nothing -> if null (forgetDirectedList hits) then Nothing else Just (hits, mkExtensions env k v root (revE misses))

            Just (nm, a, exts)
              | Just evex <- knownLtRoot   env             gidx nm root
              , Just i    <- knownLtMisses env famInstEnvs      nm misses
              , not new_misses
              -> goAllCols k v root (cons (nm, a, KnownLtInt i evex) hits') misses' exts

              | otherwise
              -> goAllCols k v root hits' (consE (nm, a) misses') exts
              where
                (new_misses, misses', hits') = cmpPartition env famInstEnvs fst3 fstsnd3 bump nm misses hits
      where
        bump (nm, a, KnownLtInt i evex) = (nm, a, KnownLtInt (i+1) evex)

-----

-- | Data about a column being extracted from a row
--
-- The expr is of type @Int#@.
--
-- The 'Int' is the number of other columns in the original row that are less
-- than this column and either not being extracted or else more inner than is
-- this column in the row type itself.
--
-- The following example motivates ignoring columns that are more outer than
-- this column in the row type itself.
--
-- Original row: rho + a + b + c + d.
--
-- Suppose we are extracting b and c (eg decided all comparisons except a vs d)
--
-- New row: rho + a + d
--
-- For a Wanted AllCols, we should first insert b into the dictionary for the
-- new row, since it might be equal to c and c was more outer than b.
--
-- For a Given AllCols, we should first delete c from the old row, since it
-- might be equal to b and b was more inner than c.
data KnownLtInt = KnownLtInt !Int !TcEvidence.EvExpr

instance GhcPlugins.Outputable KnownLtInt where
  ppr (KnownLtInt i evex) = text "KnownLtInt" <+> ppr (i, evex)

fst3 :: (a, b, c) -> a
fst3 = \(x, _, _) -> x

fstsnd3 :: (a, b, c) -> (a, b)
fstsnd3 = \(x, y, _) -> (x, y)

knownLtRoot :: Env -> GivensIndex -> TcType -> TcType -> Maybe TcEvidence.EvExpr
knownLtRoot env gidx nm root
  | isEmp env root = Just $ Core.mkIntLit envPlatform 0
  | otherwise      = Map.lookup (NonDetTcType root) m >>= Map.lookup (NonDetTcType nm)
  where
    Env{envPlatform} = env
    GivensIndex (RowVarLTs m) _rowVarDefns = gidx

cmpPartition ::
     Env
  -> FamInstEnvs
  -> (a -> TcType) -> (a -> (TcType,TcType)) -> (a -> a)
  -> TcType
  -> Extensions Innermost
  -> DirectedList Innermost a
  -> (Bool, Extensions Innermost, DirectedList Innermost a)
cmpPartition env famInstEnvs prj cnv bump x (Extends misses) hits =
    (new_misses, Extends misses', hits')
  where
    (new_misses, misses', hits') = cmpPartition_ env famInstEnvs prj cnv bump x misses hits

cmpPartition_ ::
     Env
  -> FamInstEnvs
  -> (a -> TcType) -> (a -> b) -> (a -> a)
  -> TcType
  -> DirectedList Innermost b
  -> DirectedList Innermost a
  -> (Bool, DirectedList Innermost b, DirectedList Innermost a)
cmpPartition_ env famInstEnvs prj cnv bump x =
    \misses hits -> go False misses (nil @Outermost) hits
  where
    go flag misses hits = (. uncons) $ \case
        Nothing      -> (flag, misses, unrevDL hits)
        Just (y, ys) -> case cmp env famInstEnvs x (prj y) of
            Nothing -> go True (cnv y `cons` misses)          hits  ys
            Just LT -> let !y' = bump y in
                       go flag               misses  (cons y' hits) ys
            Just EQ -> go flag               misses  (cons y  hits) ys
            Just GT -> go flag               misses  (cons y  hits) ys

knownLtMisses :: Env -> FamInstEnvs -> TcType -> Extensions leftmost -> Maybe Int
knownLtMisses env famInstEnvs x =
    fmap sum . traverse each . forgetDirectedList . forgetExtensions
  where
    each (miss_nm, _) = cmp env famInstEnvs miss_nm x <&> \case
        LT -> 1
        EQ -> 0
        GT -> 0

-----

newDict :: Env -> TcEvidence.EvBindsVar -> NewDictRecipe -> TcPluginM ((TcEvidence.EvTerm, Ct), [Ct])
newDict env evBindsVar = \case

    NewKnownLTRecipe old k v x rho i rho' -> case Ct.ctEvidence old of
        Ct.CtGiven{} -> do
            let Env{envGivenKnownLT, envKnownLT, envKnownLTCo, envPlatform} = env

            new <- do
                let loc = Ct.ctLoc old
                let ty  = TcType.mkTyConApp (classTyCon envKnownLT) [k, v, x, rho']
                TcPluginM.newGiven evBindsVar loc ty $
                     (`GhcPlugins.mkCast` GhcPlugins.mkSymCo (envKnownLTCo k v x rho'))
                   $ (\older -> TcEvidence.evId envGivenKnownLT `Core.mkTyApps` [k, v, x, rho, rho'] `mkCoreApps` [Core.mkIntLit envPlatform (toInteger i), older])
                   $ (`GhcPlugins.mkCast` envKnownLTCo k v x rho)
                   $ Ct.ctEvExpr (Ct.ctEvidence old)

            -- GHC plugin interface's weird rule: use a Given's own evidence in order to eliminate it.
            let evtm = Ct.ctEvTerm (Ct.ctEvidence old)
            pure ((evtm, old), [Ct.mkNonCanonical new])
        Ct.CtWanted{} -> do
            let Env{envKnownLT, envKnownLTCo, envPlatform, envWantedKnownLT} = env

            new <- do
                let loc = Ct.ctLoc old
                let ty  = TcType.mkTyConApp (classTyCon envKnownLT) [k, v, x, rho']
                TcPluginM.newWanted loc ty

            let ev =
                     (`GhcPlugins.mkCast` GhcPlugins.mkSymCo (envKnownLTCo k v x rho))
                   $ (\newer -> TcEvidence.evId envWantedKnownLT `Core.mkTyApps` [k, v, x, rho', rho] `mkCoreApps` [Core.mkIntLit envPlatform (toInteger i), newer])
                   $ (`GhcPlugins.mkCast` envKnownLTCo k v x rho')
                   $ Ct.ctEvExpr new

            pure ((TcEvidence.EvExpr ev, old), [Ct.mkNonCanonical new])

    NewKnownLenRecipe old k v rho i rho' -> case Ct.ctEvidence old of
        Ct.CtGiven{} -> do
            let Env{envGivenKnownLen, envKnownLen, envKnownLenCo, envPlatform} = env

            new <- do
                let loc = Ct.ctLoc old
                let ty  = TcType.mkTyConApp (classTyCon envKnownLen) [k, v, rho']
                TcPluginM.newGiven evBindsVar loc ty $
                     (`GhcPlugins.mkCast` GhcPlugins.mkSymCo (envKnownLenCo k v rho'))
                   $ (\older -> TcEvidence.evId envGivenKnownLen `Core.mkTyApps` [k, v, rho, rho'] `mkCoreApps` [Core.mkIntLit envPlatform (toInteger i), older])
                   $ (`GhcPlugins.mkCast` envKnownLenCo k v rho)
                   $ Ct.ctEvExpr (Ct.ctEvidence old)

            -- GHC plugin interface's weird rule: use a Given's own evidence in order to eliminate it.
            let evtm = Ct.ctEvTerm (Ct.ctEvidence old)
            pure ((evtm, old), [Ct.mkNonCanonical new])
        Ct.CtWanted{} -> do
            let Env{envKnownLen, envKnownLenCo, envPlatform, envWantedKnownLen} = env

            new <- do
                let loc = Ct.ctLoc old
                let ty  = TcType.mkTyConApp (classTyCon envKnownLen) [k, v, rho']
                TcPluginM.newWanted loc ty

            let ev =
                     (`GhcPlugins.mkCast` GhcPlugins.mkSymCo (envKnownLenCo k v rho))
                   $ (\newer -> TcEvidence.evId envWantedKnownLen `Core.mkTyApps` [k, v, rho', rho] `mkCoreApps` [Core.mkIntLit envPlatform (toInteger i), newer])
                   $ (`GhcPlugins.mkCast` envKnownLenCo k v rho')
                   $ Ct.ctEvExpr new

            pure ((TcEvidence.EvExpr ev, old), [Ct.mkNonCanonical new])

    NewAllColsRecipe old k v c rho extracts rho' -> case Ct.ctEvidence old of
        Ct.CtGiven{} -> do
            let Env{envAllCols, envAllColsCo, envDict, envDictCon, envGivenAllCols1, envGivenAllCols2, envPlatform, envSem} = env

            let snoc (news, older) (nm, a, KnownLtInt i evex) = do
                    new <- do
                        let loc = Ct.ctLoc old
                        let ty  = TcType.mkTyConApp envSem  [k, v, TcType.constraintKind, c, nm, a]
                        case_bndr <- TcPluginM.newEvVar $ TcType.mkTyConApp envDict [ty]
                        bndr      <- TcPluginM.newEvVar ty
                        let scrut =
                                                TcEvidence.evId envGivenAllCols1
                                `Core.mkTyApps` [k, v, c, nm, a]
                                `mkCoreApps`    [ Core.mkTyApps (TcEvidence.evId proxyHashId) [knd, typ] | (knd, typ) <- [(k, nm), (v, a)] ]
                                `mkCoreApps`    [Core.mkIntLit envPlatform (toInteger i), evex, older]
                        -- retrieve the payload of the Dict
                        TcPluginM.newGiven evBindsVar loc ty $
                            Core.Case scrut case_bndr ty
                                [Core.Alt
                                     (Core.DataAlt envDictCon)
                                     [bndr]
                                     (TcEvidence.evId bndr)
                                ]

                    pure $ (,) (new : news) $
                                        TcEvidence.evId envGivenAllCols2
                        `Core.mkTyApps` [k, v, c]
                        `mkCoreApps`    [Core.mkIntLit envPlatform (toInteger i), evex, older]

            -- This processes the outermost extract first. See Haddock of
            -- 'KnownLtInt' and 'NewAllColsRecipe' to confirm that and
            -- understand why it's important.
            (news, evex) <- foldM
                snoc
                ([], mkCastAllCols env k v c rho $ Ct.ctEvExpr $ Ct.ctEvidence old)
                (forgetDirectedList $ revDL extracts `asTypeOf` nil @Outermost)

            new <- do
                let loc = Ct.ctLoc old
                let ty  = TcType.mkTyConApp (classTyCon envAllCols) [k, v, c, rho']
                TcPluginM.newGiven evBindsVar loc ty $
                                        mkUncastAllCols env k v c rho' evex
                    `GhcPlugins.mkCast` GhcPlugins.mkSymCo (envAllColsCo k v c rho')

            -- GHC plugin interface's weird rule: use a Given's own evidence in order to eliminate it.
            let evtm = Ct.ctEvTerm (Ct.ctEvidence old)
            pure ((evtm, old), map Ct.mkNonCanonical (new : news))
        Ct.CtWanted{} -> do
            let Env{envAllCols, envAllColsCo, envPlatform, envSem, envWantedAllCols} = env

            let snoc (news, newer) (nm, a, KnownLtInt i evex) = do
                    new <- do
                        let loc = Ct.ctLoc old
                        let ty  = TcType.mkTyConApp envSem [k, v, TcType.constraintKind, c, nm, a]
                        TcPluginM.newWanted loc ty

                    pure $ (,) (new : news) $
                                        TcEvidence.evId envWantedAllCols
                        `Core.mkTyApps` [k, v, c, nm, a]
                        `mkCoreApps`    [Ct.ctEvExpr new]
                        `mkCoreApps`    [ Core.mkTyApps (TcEvidence.evId proxyHashId) [knd, typ] | (knd, typ) <- [(k, nm), (v, a)] ]
                        `mkCoreApps`    [Core.mkIntLit envPlatform (toInteger i), evex, newer]
            new <- do
                let loc = Ct.ctLoc old
                let ty  = TcType.mkTyConApp (classTyCon envAllCols) [k, v, c, rho']
                TcPluginM.newWanted loc ty

            -- This processes the innermost extract first. See Haddock of
            -- 'KnownLtInt' and 'NewAllColsRecipe' to confirm that and
            -- understand why it's important.
            (news, evex) <- foldM
                snoc
                ([], mkCastAllCols env k v c rho' (Ct.ctEvExpr new))
                (forgetDirectedList $ extracts `asTypeOf` nil @Innermost)
            let evtm = TcEvidence.EvExpr $ mkUncastAllCols env k v c rho evex `GhcPlugins.mkCast` GhcPlugins.mkSymCo (envAllColsCo k v c rho)

            pure ((evtm, old), map Ct.mkNonCanonical (new : news))

mkCastAllCols :: Env -> TcKind -> TcKind -> TcType -> TcType -> TcEvidence.EvExpr -> TcEvidence.EvExpr
mkCastAllCols env k v c rho evex =
                    TcEvidence.evId envCastAllCols
    `Core.mkTyApps` [k, v, c, rho]
    `mkCoreApps`    [evex, prx]
  where
    Env{envCastAllCols, envROW} = env

    prx = TcEvidence.evId proxyHashId `Core.mkTyApps` [envROW `TcType.mkTyConApp` [k, v], rho]

mkUncastAllCols :: Env -> TcKind -> TcKind -> TcType -> TcType -> TcEvidence.EvExpr -> TcEvidence.EvExpr
mkUncastAllCols env k v c rho evex =
                    TcEvidence.evId envUncastAllCols
    `Core.mkTyApps` [k, v, c, rho]
    `mkCoreApps`    [evex]
  where
    Env{envUncastAllCols} = env

-----

mapStep :: (a -> Step b) -> [a] -> ([a], [b])
mapStep f =
    go [] []
  where
    go contras steps = \case
        []   -> (contras, steps)
        x:xs -> case f x of
            Contra -> go (x : contras)      steps  xs
            NoStep -> go      contras       steps  xs
            Step y -> go      contras  (y : steps) xs

data Step a = Contra | NoStep | Step a

instance Functor Step where
  fmap f = \case
      Contra -> Contra
      NoStep -> NoStep
      Step a -> Step (f a)
instance Applicative Step where
  pure  = Step
  (<*>) = ap
instance Monad Step where
  x >>= k = case x of
      Contra -> Contra
      NoStep -> NoStep
      Step a -> k a

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
improve :: Env -> FamInstEnvs -> GivensIndex -> Ct -> Step NewIrrelRecipe
improve env famInstEnvs gidx ct

    | Just (tc, args) <- TcType.tcSplitTyConApp_maybe ty
    , tc == classTyCon envAbsent
    , [k, v, nm, rho] <- args
    , Just ext <- getExtend env gidx rho
    = goAbsent k v nm False (nilE @Innermost) ext <&> \rho' -> NewAbsentRecipe ct k v nm rho rho'

    | Just (TcEvidence.Nominal, lhs, rhs) <- Predicate.getEqPredTys_maybe ty
    = goEq lhs rhs

    | otherwise = NoStep
  where
    Env{envAbsent} = env

    ty = Ct.ctPred ct

    goEq lhs rhs = case (getExtend env gidx lhs, getExtend env gidx rhs) of
        (Nothing,   Nothing  ) -> NoStep
        (Just ext,  Nothing  ) -> if isEmp env rhs || eqType (fst (peel env gidx ext)) rhs then Contra else NoStep
        (Nothing,   Just ext ) -> if isEmp env lhs || eqType lhs (fst (peel env gidx ext)) then Contra else NoStep
        (Just lext, Just rext) ->
            -- wait for kinds to match
            if not (sameKinds lext rext) then NoStep else
            NewEqRecipe ct (OldEquality lhs rhs) <$> isRearranged env famInstEnvs gidx lext rext

    sameKinds :: Extension -> Extension -> Bool
    sameKinds lext rext =
        eqType lk rk && eqType lv rv
      where
        Extend lk lv _lnm _la _lrho = lext
        Extend rk rv _rnm _ra _rrho = rext

    goAbsent k0 v0 x hit acc ext
        -- wait for kinds to match
        | not (eqType k0 k && eqType v0 v) = NoStep
        | equal env famInstEnvs x nm       = Contra
        | apart env famInstEnvs x nm       = recu True                acc
        | otherwise                        = recu hit  (consE (nm, a) acc)
      where
        Extend k v nm a rho = ext

        recu hit' acc' = case getExtend env gidx rho of
            Nothing   -> if not hit' then NoStep else Step $ mkExtensions env k v rho (revE acc')
            Just ext' -> goAbsent k0 v0 x hit' acc' ext'

-----

newtype DirectedList (leftmost :: Leftmost) a = DirectedList {forgetDirectedList :: [a]}

nil :: forall leftmost {a}. DirectedList leftmost a
nil = DirectedList []

cons :: a -> DirectedList leftmost a -> DirectedList leftmost a
cons x (DirectedList xs) = DirectedList (x : xs)

uncons :: DirectedList leftmost a -> Maybe (a, DirectedList leftmost a)
uncons (DirectedList xs) = case xs of
    []    -> Nothing
    x:xs' -> Just (x, DirectedList xs')

data Leftmost = Innermost | Rev Leftmost
type Outermost = Rev Innermost

unrevDL :: DirectedList (Rev leftmost) a -> DirectedList leftmost a
unrevDL (DirectedList assocs) = DirectedList (reverse assocs)

revDL :: DirectedList leftmost a -> DirectedList (Rev leftmost) a
revDL (DirectedList assocs) = DirectedList (reverse assocs)

newtype Extensions (leftmost :: Leftmost) = Extends {forgetExtensions :: DirectedList leftmost (TcType, TcType)}

unconsE :: Extensions leftmost -> Maybe (TcType, TcType, Extensions leftmost)
unconsE (Extends (DirectedList xs)) = case xs of
    []          -> Nothing
    (nm, a):xs' -> Just (nm, a, Extends (DirectedList xs'))

revrevE :: Extensions leftmost -> Extensions (Rev (Rev leftmost))
revrevE = coerce

revE :: Extensions leftmost -> Extensions (Rev leftmost)
revE (Extends assocs) = Extends (revDL assocs)

nilE :: forall leftmost. Extensions leftmost
nilE = Extends (DirectedList [])

consE :: (TcType, TcType) -> Extensions leftmost -> Extensions leftmost
consE x (Extends assocs) = Extends (cons x assocs)

len :: Extensions leftmost -> Int
len (Extends (DirectedList xs)) = length xs

-- | Zero or more 'getExtend' calls
peel :: Env -> GivensIndex -> Extension -> (TcType, Extensions Innermost)
peel env gidx = peel_ env gidx (nilE @Innermost)

peel_ :: Env -> GivensIndex -> Extensions Innermost -> Extension -> (TcType, Extensions Innermost)
peel_ env gidx acc ext =
    case getExtend env gidx rho of
        Nothing   -> (rho, acc')
        Just ext' -> peel_ env gidx acc' ext'
  where
    Extend _k _v nm a rho = ext

    acc' = consE (nm, a) acc

-- | Pluck out the shallowest column that is equal to the given name and on
-- both sides of the equivalence under only extensions that are apart from the
-- given name
pop :: Env -> FamInstEnvs -> GivensIndex -> TcType -> [(TcType, x)] -> Extensions leftmost -> Maybe (TcType, Extensions leftmost)
pop env famInstEnvs gidx needle misses = (. unconsE) $ \case
    Nothing            -> Nothing
    Just (nm, a, exts)
        -- TODO zonk them?
      | eq  nm    -> do guard (all (apt . fst) misses); Just (a, exts)
      | apt nm    -> fmap (consE (nm, a)) <$> pop env famInstEnvs gidx needle misses exts
      | otherwise -> Nothing
  where
    eq  = equal env famInstEnvs needle
    apt = apart env famInstEnvs needle

-- | Decompose commutative rearrangements by repeatedly calling 'pop'
--
-- Also, after the popping is done, if (a) one of side of the remnants is just
-- the replication of a single name, (b) the roots are matched or at least one
-- is 'Emp', and (c) the extensions are the same length, then unify the columns
-- via a zip and also unify the roots.
isRearranged :: Env -> FamInstEnvs -> GivensIndex -> Extension -> Extension -> Step [NewEquality]
isRearranged env famInstEnvs gidx lext rext =
    go [] (revE lexts0) (nilE @Innermost) (revE rexts0)
  where
    (lroot, lexts0) = peel env gidx lext
    (rroot, rexts0) = peel env gidx rext

    Extend lk lv _lnm _la _lrho = lext
    Extend rk rv _rnm _ra _rrho = rext

    same    = eqType lroot rroot
    matched = isEmp env lroot || isEmp env rroot || same

    go :: [NewEquality] -> Extensions Outermost -> Extensions Innermost -> Extensions Outermost -> Step [NewEquality]
    go neweqs lexts rmisses = (. unconsE) $ \case
        Just (rnm, ra, rexts') -> case pop env famInstEnvs gidx rnm (forgetDirectedList (forgetExtensions rmisses)) lexts of
            Nothing           -> go neweqs                       lexts (consE (rnm, ra) rmisses) rexts'
            Just (la, lexts') -> go (NewEquality la ra : neweqs) lexts'                 rmisses  rexts'

        Nothing
            | isEmp env rroot, len rmisses < len lexts
            -> Contra

            | isEmp env lroot, len lexts < len rmisses
            -> Contra

            -- If the roots match, all the remaining rights are equal and the
            -- same length as the remaining lefts, then all the names must be
            -- the same.
            | matched
            , Just (rnm, ras) <- checkMono env famInstEnvs rmisses
            , Just acc <- zipper neweqs (\acc (lnm, la) ra -> NewEquality lnm rnm : NewEquality la ra : acc) (forgetExtensions lexts) ras
            -> Step $ if same then acc else NewEquality lroot rroot : acc

            -- ditto, reflected
            | matched
            , Just (lnm, las) <- checkMono env famInstEnvs lexts
            , Just acc <- zipper neweqs (\acc la (rnm, ra) -> NewEquality lnm rnm : NewEquality la ra : acc) las (forgetExtensions (revrevE rmisses))
            -> Step $ if same then acc else NewEquality lroot rroot : acc

            | null neweqs
            -> NoStep

            | same, len lexts /= len rmisses
            -> Contra

            | otherwise
            -> Step $
                  NewEquality (mkExtensions env lk lv lroot lexts)
                              (mkExtensions env rk rv rroot (revE rmisses))
                : neweqs

checkMono :: Env -> FamInstEnvs -> Extensions leftmost -> Maybe (TcType, DirectedList (Rev leftmost) TcType)
checkMono env famInstEnvs =
    (. unconsE) $ \case
        Nothing            -> Nothing
        Just (nm, a, exts) -> go nm (DirectedList [a]) exts
  where
    go x acc = (. unconsE) $ \case
        Nothing            -> Just (x, acc)
        Just (nm, a, exts) -> if equal env famInstEnvs x nm then go x (cons a acc) exts else Nothing

zipper :: [c] -> ([c] -> a -> b -> [c]) -> DirectedList leftmost a -> DirectedList leftmost b -> Maybe [c]
zipper acc f (DirectedList xs) (DirectedList ys) = zipper_ acc f xs ys

zipper_ :: [c] -> ([c] -> a -> b -> [c]) -> [a] -> [b] -> Maybe [c]
zipper_ acc f xs ys = case (xs, ys) of
    ([],    []   ) -> Just acc
    (x:xs', y:ys') -> zipper_ (f acc x y) f xs' ys'
    _              -> Nothing   -- ragged
