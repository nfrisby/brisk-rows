{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | This typechecker plugin allows the user to ignore the distinction between @Insert@ and @Delete@.
module BriskRows.Internal.Plugin (plugin) where

import           Control.Applicative ((<|>))
import           Data.Coerce (coerce)
import           Data.Functor (void)
import           Data.Maybe (mapMaybe)

import           Constraint (Ct)
import qualified Constraint as Ct
import           GhcPlugins (TyCon, Type)
import qualified GhcPlugins
import           Outputable (ppr, showSDocDump)
import           Panic (panicDoc)
import qualified Predicate
import qualified TcEvidence
import           TcPluginM (TcPluginM, newDerived, newGiven)
import qualified TcPluginM
import           TcRnTypes (TcPluginResult (..))
import qualified TcRnTypes
import qualified TcType
import qualified TyCoRep
import qualified TyCon
import           UniqDFM (plusUDFM)
import           VarEnv (DTyVarEnv)
import qualified VarEnv as VE
import           VarSet (DTyVarSet)
import qualified VarSet as VS

plugin :: GhcPlugins.Plugin
plugin = GhcPlugins.defaultPlugin
  { GhcPlugins.tcPlugin = \_ -> Just TcRnTypes.TcPlugin
      { TcRnTypes.tcPluginInit  = newEnv
      , TcRnTypes.tcPluginSolve = \env gs ds ws -> do

            asTypeOf (pure ()) $ do
                dflags <- TcRnTypes.unsafeTcPluginTcM GhcPlugins.getDynFlags
                TcPluginM.tcPluginIO $ putStrLn $ showSDocDump dflags $ ppr $ gs <> ds <> ws

            fmap (TcPluginOk [] . concat) $ mapM newConstraint $ improve env gs ds ws

      , TcRnTypes.tcPluginStop  = \_ -> pure ()
      }
  }

-----

lookupModule :: String -> TcPluginM.TcPluginM GhcPlugins.Module
lookupModule s = do
    let mod_nm = GhcPlugins.mkModuleName s
        lu     = TcPluginM.findImportedModule mod_nm
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
    envDelete :: !TyCon
  ,
    envInsert :: !TyCon
  ,
    envLookup :: !TyCon
  ,
    envRow    :: !TyCon
  }

mkDelete :: Env -> Type -> Type -> Type -> Type
mkDelete Env{envDelete} nm row err = TcType.mkTyConApp envDelete [nm, row, err]

mkInsert :: Env -> Type -> Type -> Type -> Type -> Type
mkInsert Env{envInsert} nm a row err = TcType.mkTyConApp envInsert [nm, a, row, err]

mkLookup :: Env -> Type -> Type -> Type
mkLookup Env{envLookup} nm row = TcType.mkTyConApp envLookup [nm, row]

isDelete :: Env -> TyCon -> Bool
isDelete Env{envDelete} tc = tc == envDelete

isInsert :: Env -> TyCon -> Bool
isInsert Env{envInsert} tc = tc == envInsert

getRow :: Env -> Type -> Maybe Type
getRow Env{envRow} ty = case TcType.tcSplitTyConApp_maybe ty of
    Just (tc, [cols])
      | envRow == tc
      -> Just cols
    _ -> Nothing

newEnv :: TcPluginM Env
newEnv = do
    modul <- lookupModule "BriskRows.Internal"
    let luTC = lookupTC modul

    envDelete <- luTC "DeleteRow"
    envInsert <- luTC "InsertRow"
    envLookup <- luTC "Lookup"

    rowTC <- luTC "ROW"
    let luDC s = GhcPlugins.promoteDataCon <$> lookupDC rowTC s

    envRow  <- luDC "Row"

    pure Env{..}

-----

data NewEquality = NewEquality !Type !Type

-- | An old 'Ct' and its LHS and RHS
data OldEqCt = OldEqCt !Ct !Type !Type

data NewCtRecipe = NewCtRecipe !OldEqCt ![NewEquality]

newConstraint :: NewCtRecipe -> TcPluginM [Ct]
newConstraint (NewCtRecipe (OldEqCt old oldl oldr) news) =
    mapM each news
  where
    each :: NewEquality -> TcPluginM Ct
    each (NewEquality l r) = do
        let loc = Ct.ctLoc old
            eq  = Predicate.mkPrimEqPred l r
        fmap Ct.mkNonCanonical $
          if not (Ct.isGivenCt old) then newDerived loc eq else do
            let mkU   = GhcPlugins.mkUnivCo (TyCoRep.PluginProv "brisk-rows") TcEvidence.Nominal
                oldco = TyCoRep.CoVarCo (Ct.ctEvId old)
                newco = mkU l oldl `TyCoRep.TransCo` oldco `TyCoRep.TransCo` mkU oldr r
            newGiven loc eq (GhcPlugins.Coercion newco)

-----

data FamApp a =
    -- | @DeleteRow nm row@
    Delete !Type !a !Type
  |
    -- | @InsertRow nm a row err@
    Insert !Type !Type !a !Type
  deriving (Functor)

getDelete :: Env -> Type -> Maybe (FamApp Type)
getDelete Env{envDelete} ty = case TcType.tcSplitTyConApp_maybe ty of
    Just (tc, [nm, row, err])
      | envDelete == tc
      -> Just $ Delete nm row err
    _ -> Nothing

getInsert :: Env -> Type -> Maybe (FamApp Type)
getInsert Env{envInsert} ty = case TcType.tcSplitTyConApp_maybe ty of
    Just (tc, [nm, a, row, err])
      | envInsert == tc
      -> Just $ Insert nm a row err
    _ -> Nothing

-----

data Fsk a = Fsk !TcType.TcTyVar !(FamApp a)
  deriving (Functor)

fskVar :: Fsk a -> TcType.TcTyVar
fskVar (Fsk tv _a) = tv

-- | Those @fsk@s that are an application of 'Delete' or 'Insert'
newtype FskMap a = FskMap (DTyVarEnv (Fsk a))
  deriving (Functor)

lookupFsk :: TcType.TcTyVar -> FskMap a -> Maybe (FamApp a)
lookupFsk tv (FskMap env) = case VE.lookupDVarEnv env tv of
    Nothing            -> Nothing
    Just (Fsk _tv app) -> Just app

extendFsk :: FskMap a -> Fsk a -> FskMap a
extendFsk fskMap fsk = flip coerce fskMap $ \x -> VE.extendDVarEnv x (fskVar fsk) fsk

mkFskMap :: Env -> [Ct] -> FskMap Type
mkFskMap env =
    foldl snoc (FskMap VE.emptyDVarEnv)
  where
    snoc :: FskMap Type -> Ct -> FskMap Type
    snoc !acc = \case
        Ct.CFunEqCan { Ct.cc_fun = tc, Ct.cc_tyargs = args, Ct.cc_fsk = tv }

          | isDelete env tc
          , [nm, row, err] <- args
          ->
          extendFsk acc $ Fsk tv $ Delete nm row err

          | isInsert env tc
          , [nm, a, row, err] <- args
          ->
          extendFsk acc $ Fsk tv $ Insert nm a row err

        _ -> acc

-----

data FamApps = FamApp !(FamApp FamApps) | Root !Type

forget :: Env -> FamApps -> Type
forget env = \case
    Root ty                      -> ty
    FamApp (Delete nm   app err) -> mkDelete env nm   (forget env app) err
    FamApp (Insert nm a app err) -> mkInsert env nm a (forget env app) err

invertEq :: Env -> Type -> FamApp FamApps -> [NewEquality]
invertEq =
    \env rhs -> go env rhs . FamApp
  where
    -- For example
    --
    -- > Delete x   (Delete y   row) ~ Row cols   implies/requires   row ~ Insert y (Lookup y row) (Insert x (Lookup x (Delete y row)) (Row cols))
    --
    -- > Insert x a (Insert y b row) ~ Row cols   implies/requires   row ~ Delete y (Delete x (Row cols))
    --                                                                 a ~ Lookup x (Row cols)
    --                                                                 b ~ Lookup y (Delete x (Row cols))
    go :: Env -> Type -> FamApps -> [NewEquality]
    go env acc = \case
        Root ty                      -> [NewEquality ty acc]
        FamApp (Delete nm   app err) ->
            go env (mkInsert env nm (mkLookup env nm (forget env app)) acc err) app
        FamApp (Insert nm a app err) ->
            NewEquality a (mkLookup env nm acc)   -- TODO optimize acc here?
          : go env (mkDelete env nm acc err) app

-----

-- TODO the solver loop would handle it just fine if we only ever inverted the outermost equality
--
-- > Delete x (Delete y row) ~ Row cols   implies/requires   Delete y row ~ Insert x (Lookup x (Delete y row)) (Row cols)
--
-- And that would let us drastically simplify 'narrowFskMap'.
-- As it is, this is just an optimization to avoid multiple trips around the solver loop.
-- I suppose that might be important? Or maybe it's actually a pessimization!

data NarrowingState = NarrowingState !DTyVarSet !(DTyVarEnv (FskMap ())) !(FskMap FamApps)

-- | Drop those @fsk@s that are a composition of 'FamApp's ultimately applied to @Row@
--
-- This prevents an infinite solver loop.
narrowFskMap :: Env -> FskMap Type -> FskMap FamApps
narrowFskMap env fskMap0 =
    finish
  $ foldl
      snoc
      (NarrowingState VS.emptyDVarSet VE.emptyDVarEnv (FskMap VE.emptyDVarEnv))
  $ VE.dVarEnvElts
  $ coerce fskMap0
  where
    get :: FamApp a -> a
    get = \case
        Delete _nm    row _err -> row
        Insert _nm _a row _err -> row

    snoc :: NarrowingState -> Fsk Type -> NarrowingState
    snoc (NarrowingState stop pending stuck) (Fsk tv app)

      -- directly stopped, aka applied to @Row@
      | Just _cols <- getRow env (get app)
      = stopper

      -- is applied to a 'FamApp'
      | Just roottv <- TcType.tcGetTyVar_maybe (get app)
      , Just{}      <- lookupFsk tv fskMap0
      =
        -- transitively stopped
        if VS.elemDVarSet tv stop then stopper else

        case lookupFsk tv stuck of

          -- transitively stuck
          Just apps -> stucker $ FamApp apps <$ app

          -- pending
          Nothing   ->
              NarrowingState
                  stop
                  (VE.extendDVarEnv_C plus pending roottv (one $ Fsk tv $ void app))
                  stuck

      -- directly stuck
      | otherwise
      = stucker $ Root <$> app

      where
        stopper =
            NarrowingState
                (VS.extendDVarSet stop tv)
                (VE.delDVarEnv pending tv)
                stuck

        stucker :: FamApp FamApps -> NarrowingState
        stucker app' =
            NarrowingState
                stop
                (VE.delDVarEnv pending tv)
          $ maybe id (plus . set app') (VE.lookupDVarEnv pending tv)
          $ extendFsk stuck (Fsk tv app')

    plus :: forall a. FskMap a -> FskMap a -> FskMap a
    plus = coerce $ plusUDFM @(Fsk a)

    one :: Fsk () -> FskMap ()
    one fsk = coerce $ VE.unitDVarEnv (fskVar fsk) fsk

    -- replace the root fsk with something better
    set :: FamApp FamApps -> FskMap () -> FskMap FamApps
    set app' = fmap $ \() -> FamApp app'

    -- we never learned more about the root fsk, so put it back
    reset :: FskMap () -> FskMap FamApps
    reset =
        coerce
      $ VE.mapDVarEnv
      $ \(Fsk tv app) ->
            Fsk tv
          $ fmap (\() -> Root (TyCoRep.mkTyVarTy tv))
          $ app

    -- keep the stuck things and anything still pending
    --
    -- TODO is pending always null here?
    finish :: NarrowingState -> FskMap FamApps
    finish (NarrowingState _stop pending stuck) =
        VE.foldDVarEnv (plus . reset) stuck pending

-----

-- | The domain-specific knowledge
--
-- This plugin does not implement any intersections, so we simplify each constraint individually.
--
-- Also, it only does /Improvement/.
-- To improve givens, it adds any implied Givens that aren't already present.
-- To improve derived/wanteds, it adds Deriveds that aren't already present.
--
-- > ... Insert nm a row ~ Row cols   implies/requires   row ~ Delete nm ... (Row cols)   and   a ~ Lookup nm (Row cols)
--
-- > ... Delete nm row   ~ Row cols   implies/requires   row ~ Insert nm (Lookup nm row) ... (Row cols)
--
-- TODO it should also support the ambiguity check by encoding the (partial) injectivity properties:
--
-- > Insert nm a l ~ Insert nm b r   implies    l ~ r and a ~ b
--
-- > Delete nm   l ~ Delete nm   r   implies    l ~ r
--
-- > Insert l1 l2 row ~ Insert r1 r2 row   implies    l1 ~ r1 and l2 ~ r2
improve :: Env -> [Ct] -> [Ct] -> [Ct] -> [NewCtRecipe]
improve env gs ds ws
  | null ws   = mapMaybe improve1' gs
  | otherwise = mapMaybe improve1' (ds <> ws)
  where
    -- ws is un-flattened :/
    fskMap = narrowFskMap env $ mkFskMap env $ gs <> ds

    improve1' ct = improve1 env <$> parse env fskMap ct

improve1 :: Env -> Parsed ->  NewCtRecipe
improve1 env (Parsed old app) =
    NewCtRecipe old $ invertEq env rhs app
  where
    OldEqCt _ct _lhs rhs = old

-----

data Parsed = Parsed !OldEqCt !(FamApp FamApps)

-- | Parse a Ct that we might act upon
--
-- According to <https://gitlab.haskell.org/ghc/ghc/-/wikis/plugins/type-checker>:
--
-- During simplification of givens:
-- The deriveds and wanteds lists will be empty.
-- The givens will be flat, un-zonked, and inert.
--
-- During solving of wanteds:
-- The givens and deriveds will be flat, un-zonked, and inert.
-- The wanteds will be unflattened and zonked.
--
-- TODO where do I need to zonk things in Givens/Deriveds?
parse :: Env -> FskMap FamApps -> Ct -> Maybe Parsed
parse env fskMap ct = case ct of

    Ct.CTyEqCan {
        Ct.cc_eq_rel = Predicate.NomEq
      ,
        Ct.cc_rhs = rhs
      ,
        Ct.cc_tyvar = tv
      }
      | Just _cols <- getRow env rhs
      , Just app <- lookupFsk tv fskMap
      ->
      Just $ Parsed (OldEqCt ct (TyCoRep.mkTyVarTy tv) rhs) app

    Ct.CNonCanonical{}
      | Just (TcEvidence.Nominal, lhs, rhs) <- Predicate.getEqPredTys_maybe (Ct.ctPred ct)
      , Just _cols <- getRow env rhs
      , Just app   <- getFamApps env fskMap lhs
      ->
      Just $ Parsed (OldEqCt ct lhs rhs) app

    _ -> Nothing

getFamApps :: Env -> FskMap FamApps -> Type -> Maybe (FamApp FamApps)
getFamApps env fskMap ty =
        (fmap (fmap inside) $ getDelete env ty <|> getInsert env ty)
    <|>
        tyfamapp
  where
    inside :: Type -> FamApps
    inside arg = maybe (Root arg) FamApp $ getFamApps env fskMap arg

    -- The typechecker plugin docs imply this one isn't necessary.
    -- But I also vaguely recall it being necessary anyway :grimace:.
    tyfamapp = TcType.tcGetTyVar_maybe ty >>= flip lookupFsk fskMap
