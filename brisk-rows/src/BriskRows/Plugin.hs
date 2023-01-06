{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module BriskRows.Plugin (plugin) where

import           Control.Applicative ((<|>))
import           Control.Monad (guard)
-- import           Data.List (find)
import           Data.Maybe (fromMaybe, mapMaybe)

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
import           GHC.Core.Unify (typesCantMatch)
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
      , TcRnTypes.tcPluginRewrite = \env@Env{envCmpName, envExt, envExtOp} ->
          -- NOTE WELL that these rewrites only happen inside of constraints!
          --
          -- TODO confirm that
            unitUFM envCmpName (rewriteCmpName env)
          <>
            unitUFM envExt     (rewriteExt   env)
          <>
            unitUFM envExtOp   (rewriteExtOp env)
      , TcRnTypes.tcPluginSolve   = \env _evBindsVar gs ws -> do

            doTrace env $ text $ "<<<<<<------"
            doTrace env $ ppr $ gs <> ws
            doTrace env $ text $ "<-----------"

            let existingEqs = foobar (getExistingEq env) (gs ++ ws)
                recipes     = mapMaybe (improve env `uncurry`) existingEqs
            doTrace env $ ppr recipes

            doTrace env $ text "----------->"
            news <- mapM (newConstraint env ws) recipes
            doTrace env $ text $ "------>>>>>>"

            pure $ TcPluginOk (mapMaybe oldConstraint recipes) (concat news)
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
    doTrace        :: GhcPlugins.SDoc -> TcPluginM ()
  ,
    envAssign      :: !TyCon
  ,
    envCmpName     :: !TyCon
  ,
    envEQ          :: !TyCon
  ,
    envEmp         :: !TyCon
  ,
    envExt         :: !TyCon
  ,
    envExtOp       :: !TyCon
  ,
    envExtend      :: !TyCon
  ,
    envRestrict    :: !TyCon
  ,
    envRow         :: !TyCon
  ,
    envSelect      :: !TyCon
  ,
    envStops       :: [TyCon]
  ,
    envUnfoldExt   :: !TyCon
  ,
    envUnfoldExtOp :: !TyCon
  }

newEnv :: TcPluginM Env
newEnv = do
    doTrace <- pure (\_x -> (pure ())) `asTypeOf` do
      dflags <- TcRnTypes.unsafeTcPluginTcM GhcPlugins.getDynFlags
      pure $ \x -> do
        TcPluginM.tcPluginIO $ putStrLn $ showSDoc dflags x

    modul <- lookupModule "BriskRows.Internal"
    let luTC = lookupTC modul

    envAssign <- do
      tc <- luTC "COL"
      GhcPlugins.promoteDataCon <$> lookupDC tc ":="

    envCmpName <- luTC "CmpName"

    envEQ <- luTC "CmpNameEQ"

    envEmp <- luTC "Emp"

    envExt    <- luTC "Ext"
    envExtOp  <- luTC ":&"
    envExtend <- luTC "Extend_Row#"

    envRestrict <- luTC "Restrict"

    envRow <- do
      tc <- luTC "ROW"
      GhcPlugins.promoteDataCon <$> lookupDC tc "Row#"
  
    envSelect <- luTC "Select"

    -- We can skip Extend, since it's a type synonym. (TODO and so eqType handles that, right?)
    -- We can skip Extend_Row# since this function is only ever used once we've confirmed it's not an extension.
    envStops <- mapM luTC $ words "Cons Extend_Col Extend_Ordering Restrict_Ordering Restrict"

    envUnfoldExt   <- luTC "UnfoldExt"
    envUnfoldExtOp <- luTC "UnfoldExtOp"

    pure Env{..}

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

rewriteExtOp :: Env -> TcRnTypes.RewriteEnv -> [Ct] -> [TcType] -> TcPluginM TcRnTypes.TcPluginRewriteResult
rewriteExtOp env _rwenv _gs args = case args of
  [_k, _v, rho, _col]
    | Just (tc', _) <- TcType.tcSplitTyConApp_maybe rho
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
    | Just (tc', _) <- TcType.tcSplitTyConApp_maybe rho
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

-----

data NewEquality = NewEquality !TcType !TcType

data NewCtRecipe = NewCtRecipe !Ct !MaybeEvTerm ![NewEquality]

data MaybeEvTerm = NothingEvTerm | JustEvTerm !TcEvidence.EvTerm

oldConstraint :: NewCtRecipe -> Maybe (TcEvidence.EvTerm, Ct)
oldConstraint (NewCtRecipe old mbEvTerm _news) = case mbEvTerm of
    NothingEvTerm -> Nothing
    JustEvTerm ev -> Just (ev, old)

newConstraint :: Env -> [Ct] -> NewCtRecipe -> TcPluginM [Ct]
newConstraint env olds (NewCtRecipe old _mbEvTerm news) =
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
  ppr (NewCtRecipe old mbEvTerm news) = text "NewCtRecipe" <+> ppr (old, ppr mbEvTerm, news)

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
      | tc == envExtend
      , [k, v, nm, a, rho, _err] <- args
      -> Just $ Extend ty Nothing k v nm a rho
      | tc == envExt
      , [k, v, nm, a, rho] <- args
      -> Just $ Extend ty (Just $ TcType.mkTyConApp envUnfoldExt args) k v nm a rho
      | tc == envExtOp
      , [k, v, rho, col] <- args
      , Just (tc', args') <- TcType.tcSplitTyConApp_maybe col
      , tc' == envAssign
      , [_k, _v, nm, a] <- args'
      -> Just $ Extend ty (Just $ TcType.mkTyConApp envUnfoldExtOp args) k v nm a rho
    _ -> Nothing
  where
    Env{envAssign, envExt, envExtOp, envExtend, envUnfoldExt, envUnfoldExtOp} = env

getExistingEq :: Env -> Ct -> Maybe (Extension, Extension)
getExistingEq env ct = case ct of
    Ct.CNonCanonical{}
      | Just (TcEvidence.Nominal, lhs, rhs) <- Predicate.getEqPredTys_maybe (Ct.ctPred ct)
      , Just lext <- getExtend env lhs
      , Just rext <- getExtend env rhs
      -> Just (lext, rext)
    _ -> Nothing

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
improve :: Env -> Ct -> [(Extension, Extension)] -> Maybe NewCtRecipe
improve env ct existingEqs = case ct of
    Ct.CNonCanonical{}
      | Just (TcEvidence.Nominal, lhs, rhs) <- Predicate.getEqPredTys_maybe (Ct.ctPred ct)
      -> go lhs rhs
    _ -> Nothing
  where

    go lhs rhs = case getExtend env lhs of   -- the LHS will never be the Row#, will it?
      Just lext
        | isRow env rhs
        -> NewCtRecipe ct NothingEvTerm <$> goInverted env lext rhs []

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

goExtExt :: Env -> [(Extension, Extension)] -> Ct -> Extension -> Extension -> Maybe NewCtRecipe
goExtExt env existingEqs old lext rext
    -- wait for kinds to match
  | not $ lk `eqType` rk && lv `eqType` rv = Nothing

  | otherwise =
        (NewCtRecipe old NothingEvTerm <$> goOuterInjectivity lext rext)
    <|>
        (       (\(co, eqs) -> NewCtRecipe old (JustEvTerm (TcEvidence.evCoercion co)) eqs)
            <$> (isRearranged env lext rext <|> goUnfold existingEqs lext rext)
        )
  where
    Extend _lb _lty lk lv _lnm _la _lrho = lext
    Extend _rb _rty rk rv _rnm _ra _rrho = rext

-- | This simple treatment of just one layer suffices for the general
-- definitions in "BriskRows.Internal.RV" etc.
goOuterInjectivity :: Extension -> Extension -> Maybe [NewEquality]
goOuterInjectivity lext rext
    -- if the outermost names are equal, require the images and (recursively) extended rows are too
  | lnm `eqType` rnm   = Just [NewEquality la ra, NewEquality lrho rrho]

    -- This is commented out because 'isRearranged' supplants this rule.
{-
    -- if the extended rows are equal, require the outermost names and images are too
  | lrho `eqType` rrho = Just [NewEquality la ra, NewEquality lnm  rnm ]
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

pop :: TcType -> [(TcType, x)]-> Extensions -> Maybe (TcType, Extensions)
pop needle misses = \case
    Extends []               -> Nothing
    Extends (assoc : assocs)
        -- TODO zonk them?
      | eqType needle (fst assoc) -> do guard (all (apart . fst) misses); Just (snd assoc, Extends assocs)
      | apart         (fst assoc) -> fmap (cons assoc) <$> pop needle misses (Extends assocs)
      | otherwise                 -> Nothing
  where
    cons x (Extends xs) = Extends (x : xs)

    apart nm = typesCantMatch [(needle, nm)]

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
         case pop lnm miss rassocs of
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
          | not $ eqType lroot rroot          -> Nothing
          | all (eqType lnm0 . fst) misses    -> goUni False acc lnm0 (reverse $ la0 : map snd misses   ) (          (rnm0, ra0) : leftovers)
          | all (eqType rnm0 . fst) leftovers -> goUni True  acc rnm0 (          ra0 : map snd leftovers) (reverse $ (lnm0, la0) : misses   )
          | otherwise                         -> Nothing

    -- The roots are identical and one side has identical names.
    --
    -- If there's the same number of names on both sides, require all columns
    -- are equal.
    goUni flipped acc lnm las rassocs = case (las, rassocs) of
        ([],  [] ) -> Just acc
        ([],  _:_) -> Nothing   -- currently ragged
        (_:_, [] ) -> Nothing   -- currently ragged

        (la : las', (rnm, ra) : rassocs') -> goUni flipped (newEq lnm rnm : newEq la ra : acc) lnm las' rassocs'
      where
        newEq l r = if flipped then NewEquality r l else NewEquality l r
