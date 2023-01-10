{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -fplugin=BriskRows.Plugin #-}

{-# OPTIONS_HADDOCK not-home #-}

module BriskRows.Internal.RVtf (
    -- * Records
    AllCols,
    Rcd (Rcd#),
    del#,
    dicts#,
    emp,
    idxs,
    ins#,
    natro#,
    prj#,
    prjAt,
    pur#,
    -- * Variants
    Vrt (Vrt),
    abd,
    cas#,
    idxFromVrt,
    inj#,
    injAt,
    vrtFromIdx,
    wkn#,
    -- * Both
    NoSplat,
    Splat (splat#),
    asFldOf,
    toFields,
    idFldOf#,
    lacking#,
    splat,
    ) where

import qualified Data.Foldable as Foldable
import           Data.Kind (Constraint, Type)
import qualified Data.Sequence as Sq
import           GHC.Exts (Any, Proxy#, proxy#)
import           GHC.TypeLits (ErrorMessage (Text, (:<>:), (:$$:), ShowType))
import           GHC.Types (Int (I#))
import           Unsafe.Coerce (unsafeCoerce)

import qualified BriskRows.Idx as Idx
import           BriskRows.Internal
import           BriskRows.Sem

-----

row# :: rv (rho :: ROW k v) -> Proxy# rho
row# _ = proxy#

knownLT :: KnownLT nm rho => Proxy# nm -> Proxy# rho -> Int
knownLT = \nm rho -> I# (knownLT# nm rho)

-----

-- | A record
newtype Rcd (fld :: Fld k v Type) (rho :: ROW k v) =
    -- | INVARIANT Same order as the row
    Rcd# (Sq.Seq (Sem fld Any Any))

emp :: forall {k} {v} fld. Rcd fld (Emp :: ROW k v)
emp = Rcd# Sq.empty

-- | Extend the record's row by inserting another field
ins# :: KnownLT nm rho => Proxy# nm -> Sem fld nm a -> Rcd fld rho -> Rcd fld (rho :& nm := a)
ins# = \nm a rcd ->
    let rho     = row# rcd
        Rcd# sq = rcd
    in
    Rcd# $ Sq.insertAt (knownLT nm rho) (unsafeCoerce a) sq

-- | Restrict the record's row by deleting a field
del# :: KnownLT nm rho => Proxy# nm -> Rcd fld (rho :& nm := a) -> Rcd fld rho
del# = \nm rcd ->
    let Rcd# sq = rcd
        rcd'    = Rcd# $ Sq.deleteAt (knownLT nm (row# rcd')) sq
    in
    rcd'

-- | Project a value out of the record
prj# :: forall {nm} {rho} {fld} {a}. KnownLT nm rho => Proxy# nm -> Rcd fld (rho :& nm := a) -> Sem fld nm a
prj# = \nm rcd -> prjAt (Idx.idx# nm (proxy# @rho)) rcd

-----

{-
class KnownLen rho => AllCols (c :: Fld k v Constraint) (rho :: ROW k v)
  where
    dicts# :: Proxy# c -> Rcd (Con Dict `App` c) rho

instance AllCols c (Row# '[]) where dicts# = \_c -> emp

instance (Sem c nm a, AllCols c (Row# cols)) => AllCols c (Row# (nm := a ': cols)) where
  dicts# = \_c ->
      let Rcd# sq = dicts# proxy# :: Rcd (Con Dict `App` c) (Row# cols)
      in Rcd# $ unsafeCoerce (Dict :: Dict (Sem c nm a)) Sq.<| sq
-}

dicts# :: forall k v (c :: Fld k v Constraint) {rho :: ROW k v}.
     AllCols c rho
  => Proxy# c
  -> Rcd (Con Dict `App` c) rho
dicts# c = Rcd# $ anyDicts# c (proxy# @rho)

pur# :: forall fld {rho}. AllCols (Con CTop) rho => Proxy# fld -> (forall nm a. Proxy# nm -> Proxy# a -> Sem fld nm a) -> Rcd fld rho
pur# = \fld f ->
    natro#
        (proxy# @(Con Dict `App` Con CTop))
        fld
        (\nm a _dict -> f nm a)
        (dicts# (proxy# @(Con CTop)))

-----

-- | A variant
data Vrt :: Fld k v Type -> ROW k v -> Type where
    Vrt :: {-# UNPACK #-} !(Idx.Idx nm a rho) -> !(Sem fld nm a) -> Vrt fld rho

-- | An absurd value, since an empty variant is an empty type
abd :: forall fld {ans}. Vrt fld Emp -> ans
abd = error "Vrt.abd"

-- | Extend a variant continuation's row by adding another case
cas# ::
     KnownLT nm rho
  => Proxy# nm
  -> (Sem fld nm a             -> ans)
  -> (Vrt fld rho              -> ans)
  -> (Vrt fld (rho :& nm := a) -> ans)
cas# = \nm f g (Vrt idx x) ->
    case Idx.nrw# nm idx of
        Left Idx.ReflKV -> f x
        Right idx'      -> g $ Vrt idx' x

-- | Restrict a variant continuation's row by weakening it no longer handle a specific case
wkn# :: KnownLT nm rho => Proxy# nm -> (Vrt fld (rho :& nm := a) -> ans) -> (Vrt fld rho -> ans)
wkn# = \nm f (Vrt idx x) -> f $ Vrt (Idx.wdn# nm idx) x

-- | Inject a value into the variant
inj# :: forall {nm} {rho} {fld} {a}. KnownLT nm rho => Proxy# nm -> Sem fld nm a -> Vrt fld (rho :& nm := a)
inj# = \nm a ->
    let idx = Idx.idx# nm (proxy# @rho)
    in
    injAt idx a


-----

idxFromVrt :: Vrt (Con (Idx.EqualsKV nm a) `App` Nam `App` Img) rho -> Idx.Idx nm a rho
idxFromVrt = \(Vrt idx Idx.ReflKV) -> idx

vrtFromIdx :: Idx.Idx nm a rho -> Vrt (Con (Idx.EqualsKV nm a) `App` Nam `App` Img) rho
vrtFromIdx = \idx -> Vrt idx Idx.ReflKV

injAt :: Idx.Idx nm a rho -> Sem fld nm a -> Vrt fld rho
injAt = Vrt

prjAt :: Idx.Idx nm a rho -> Rcd fld rho -> Sem fld nm a
prjAt idx rcd =
    let Rcd#    sq = rcd
        Idx.Idx i  = idx
    in
    unsafeCoerce $ Sq.index sq i

-- | Each field has type @'Idx.Idx' nm a rho@
idxs :: forall {rho}. AllCols (Con CTop) rho => Rcd (Con Idx.Idx `App` Nam `App` Img `App` Con rho) rho
idxs =
    let len = Sq.length $ anyDicts# (proxy# @(Con CTop)) (proxy# @rho)
        rcd = Rcd# $ Sq.fromFunction len Idx.Idx
    in
    rcd

{-
-- | Each field is of type @'Vrt2' ('Con' ('EqualsKV' nm a) '``App``' 'Nam' '``App``' 'Img') rho@
vrts ::
     KnownLen rho
  => Rcd
       (Con Vrt2
                -- ie Con (EqualsKV nm a) `App` Nam `App` Img
          `App` (Con App `App` (Con App `App` (Con Con `App` (Con EqualsKV `App` Nam `App` Img)) `App` Con Nam) `App` Con Img)
          `App` Con rho
       )
       rho
vrts =
    let rcd = Rcd# $ Sq.fromFunction (I# (knownLen# (row# rcd))) $ \i -> Vrt2 (Idx.Idx i) (unsafeCoerce ReflKV)
    in
    rcd
-}

-----

infix 2 `asFldOf`

asFldOf :: t (fld :: Fld k v Type) (rho1 :: ROW k v) -> u fld rho2 -> t fld rho1
asFldOf = \x _y -> x

idFldOf# :: Proxy# fld -> t (fld :: Fld k v Type) (rho :: ROW k v) -> t fld rho
idFldOf# = \_f x -> x

lacking# :: Absent nm rho => Proxy# nm -> t rho -> t rho
lacking# = \_nm -> id

-----

class Fmap (rv :: Fld k v Type -> ROW k v -> Type) where
  natro# :: Proxy# fld1 -> Proxy# fld2 -> (forall nm a. Proxy# nm -> Proxy# a -> Sem fld1 nm a -> Sem fld2 nm a) -> rv fld1 rho -> rv fld2 rho

instance Fmap Rcd where
  natro# = \_fld1 _fld2 f (Rcd# sq) -> Rcd# $ f (proxy# @Any) (proxy# @Any) <$> sq

instance Fmap Vrt where
  natro# = \_fld1 _fld2 f (Vrt idx x) ->
      let kidx# :: Idx.Idx nm a rho -> Proxy# nm
          kidx# _ = proxy#

          vidx# :: Idx.Idx nm a rho -> Proxy# a
          vidx# _ = proxy#
      in
      Vrt idx (f (kidx# idx) (vidx# idx) x)

-----

infixl 4 `splat`

-- | Combine a 'Rcd' or 'Vrt' with a 'Rcd' or 'Vrt'
--
-- Combining two 'Rcd' gives a 'Rcd'.
-- Combining a 'Rcd' and a 'Vrt' gives a 'Vrt'.
-- Combining two 'Vrt' gives a @'Maybe' 'Vrt'@.
splat ::
  forall {l} {r} {fld1} {fld2} {rho}.
    Splat (TypeErr (NoSplat l r)) l r
 => l (fld1 :->: fld2) rho
 -> r fld1 rho
 -> SplatF l r fld2 rho
splat = splat# (proxy# @(TypeErr (NoSplat l r)))

type NoSplat l r =
    Text "Each `splat' argument must be either Rcd or Vrt, but at least one of these types is neither:" :$$: (Text "        " :<>: ShowType l) :$$: (Text "    and " :<>: ShowType r)

type family SplatF (l :: Fld k v Type -> ROW k v -> Type) (r :: Fld k v Type -> ROW k v -> Type) (fld :: Fld k v Type) (rho :: ROW k v) :: Type
  where
    SplatF Rcd Rcd fld rho =        Rcd fld rho
    SplatF Rcd Vrt fld rho =        Vrt fld rho
    SplatF Vrt Rcd fld rho =        Vrt fld rho
    SplatF Vrt Vrt fld rho = Maybe (Vrt fld rho)

class Splat (err :: Err) (l :: Fld k v Type -> ROW k v -> Type) (r :: Fld k v Type -> ROW k v -> Type) where splat# :: Proxy# err -> l (fld1 :->: fld2) rho -> r fld1 rho -> SplatF l r fld2 rho

instance Splat err Rcd Rcd where splat# = \_err (Rcd# l)     (Rcd# r)     -> Rcd# $ Sq.zipWith unsafeCoerce l r
instance Splat err Rcd Vrt where splat# = \_err rcd          (Vrt idx r)  -> Vrt idx (prjAt idx rcd $ r)
instance Splat err Vrt Rcd where splat# = \_err (Vrt idx l)  rcd          -> Vrt idx (l $ prjAt idx rcd)
instance Splat err Vrt Vrt where splat# = \_err (Vrt idxL l) (Vrt idxR r) -> case Idx.compareIdx idxL idxR of Idx.EQ' Idx.ReflKV -> Just $ Vrt idxL (l r); _ -> Nothing

-----

-- | Projecting fields out of a homogenous 'Rcd' or 'Vrt'
--
-- A 'Rcd' gives a list (ordered by 'CmpName' and most-recent as leftmost for collisions).
-- A 'Vrt' gives a single value.
toFields ::
  forall {t} {rho} {a}.
    ToFields (TypeErr (NoToFields t)) t
 => t (Con a) rho
 -> ToFieldsF t a
toFields = toFields# (proxy# @(TypeErr (NoToFields t)))

type NoToFields (t :: Fld k v Type -> ROW k v -> Type) =
    Text "The argument of `toFields` must be either Rcd or Vrt, but this type is neither:" :$$: (Text "        " :<>: ShowType t)

type family ToFieldsF (t :: Fld k v Type -> ROW k v -> Type) (a :: Type) :: Type
  where
    ToFieldsF Rcd a = [a]
    ToFieldsF Vrt a = a

class ToFields (err :: Err) t where toFields# :: Proxy# err -> t (Con a) rho -> ToFieldsF t a

instance ToFields err Rcd where toFields# = \_err (Rcd# sq)    -> unsafeCoerce `map` Foldable.toList sq
instance ToFields err Vrt where toFields# = \_err (Vrt _idx x) -> x
