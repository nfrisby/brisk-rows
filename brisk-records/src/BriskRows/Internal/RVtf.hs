{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
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
    ins#,
    natro#,
    prj#,
    pur#,
    -- * Variants
    Vrt (Vrt#),
    abd,
    cas#,
    inj#,
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
import           GHC.Prim (Int#, (+#), (-#))
import           GHC.TypeLits (ErrorMessage (Text, (:<>:), (:$$:), ShowType))
import           GHC.Types (Int (I#))
import           Unsafe.Coerce (unsafeCoerce)

import           BriskRows.Internal
import           BriskRows.Internal.Sem

-----

row# :: rOW (rho :: ROW k v) -> Proxy# rho
row# _ = proxy#

vrtRow# :: (t fld (rho :: ROW k v) -> ans) -> Proxy# rho
vrtRow# _ = proxy#

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
--
-- See 'Select'.
prj# :: KnownLT nm rho => Proxy# nm -> Rcd fld rho -> Sem fld nm (Select nm rho)
prj# = \nm rcd ->
    let rho     = row# rcd
        Rcd# sq = rcd
    in
    unsafeCoerce $ Sq.index sq (knownLT nm rho)

-----

class KnownLen rho => AllCols (c :: Fld k v Constraint) (rho :: ROW k v)
  where
    dicts# :: Proxy# c -> Rcd (Con Dict `App` c) rho

instance AllCols c (Row# '[]) where dicts# = \_c -> emp

instance (Sem c nm a, AllCols c (Row# cols)) => AllCols c (Row# (nm := a ': cols)) where
  dicts# = \_c ->
      let Rcd# sq = dicts# proxy# :: Rcd (Con Dict `App` c) (Row# cols)
      in Rcd# $ unsafeCoerce (Dict :: Dict (Sem c nm a)) Sq.<| sq

pur# :: forall fld {rho}. KnownLen rho => Proxy# fld -> (forall nm a. Sem fld nm a) -> Rcd fld rho
pur# = \_fld f -> Rcd# $ Sq.replicate (I# (knownLen# (proxy# @rho))) (f @Any @Any)

-----

-- | A variant
data Vrt (fld :: Fld k v Type) (rho :: ROW k v) =
    -- | INVARIANT The integer is the value's index in the row
    --
    -- For the most-recently added column of a given name, this tag is
    -- equivalent to 'knownLT#'. See 'Row#'.
    Vrt# !(Sem fld Any Any) Int#

-- | An absurd value, since an empty variant is an empty type
abd :: forall fld {ans}. Vrt fld Emp -> ans
abd = error "Vrt.abd"

-- | Extend a variant continuation's row by adding another case
cas# :: KnownLT nm rho => Proxy# nm -> (Sem fld nm a -> ans) -> (Vrt fld rho -> ans) -> (Vrt fld (rho :& nm := a) -> ans)
cas# = \nm f g vrt ->
    let rho          = vrtRow# g
        !(Vrt# a i#) = vrt
    in
    case compare (I# i#) (knownLT nm rho) of
      LT -> g $ Vrt# a i#        
      EQ -> unsafeCoerce f a   -- the nm column is the first thing in rho :& nm that's not less than nm
      GT -> g $ Vrt# a (i# -# 1#)

-- | Restrict a variant continuation's row by weakening it no longer handle a specific case
wkn# :: KnownLT nm rho => Proxy# nm -> (Vrt fld (rho :& nm := a) -> ans) -> (Vrt fld rho -> ans)
wkn# = \nm f vrt ->
    let rho          = row# vrt
        !(Vrt# a i#) = vrt
    in
    case compare (I# i#) (knownLT nm rho) of
      LT -> f $ Vrt# a  i#
      EQ -> f $ Vrt# a (i# +# 1#)   -- the new nm column is the first thing in rho :& nm that's not less than nm
      GT -> f $ Vrt# a (i# +# 1#)

-- | Inject a value into the variant
--
-- See 'Select'.
inj# :: KnownLT nm rho => Proxy# nm -> Sem fld nm (Select nm rho) -> Vrt fld rho
inj# = \nm a ->
    let vrt = Vrt# (unsafeCoerce a) (knownLT# nm (row# vrt))
    in
    vrt

-----

infix 2 `asFldOf`

asFldOf :: t (fld :: Fld k v Type) (rho1 :: ROW k v) -> u fld rho2 -> t fld rho1
asFldOf = \x _y -> x

idFldOf# :: Proxy# fld -> t (fld :: Fld k v Type) (rho :: ROW k v) -> t fld rho
idFldOf# = \_f x -> x

lacking# :: Absent nm rho => Proxy# nm -> t rho -> t rho
lacking# = \_nm -> id

-----

class Fmap rv where
  natro# :: Proxy# fld1 -> Proxy# fld2 -> (forall nm a. Sem fld1 nm a -> Sem fld2 nm a) -> rv fld1 rho -> rv fld2 rho

instance Fmap Rcd where
  natro# = \_fld1 _fld2 f (Rcd# sq) -> Rcd# $ f @Any @Any <$> sq

instance Fmap Vrt where
  natro# = \_fld1 _fld2 f (Vrt# a i) -> Vrt# (f @Any @Any a) i

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

instance Splat err Rcd Rcd where splat# = \_err (Rcd# l)    (Rcd# r)    -> Rcd# $ Sq.zipWith unsafeCoerce l r
instance Splat err Rcd Vrt where splat# = \_err (Rcd# l)    (Vrt# r i#) -> Vrt# (Sq.index l (I# i#) `unsafeCoerce` r) i#
instance Splat err Vrt Rcd where splat# = \_err (Vrt# l i#) (Rcd# r)    -> Vrt# (Sq.index r (I# i#) `unsafeCoerce` l) i#
instance Splat err Vrt Vrt where splat# = \_err (Vrt# l l#) (Vrt# r r#) -> if I# l# /= I# r# then Nothing else Just $ Vrt# (l `unsafeCoerce` r) l#

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

instance ToFields err Rcd where toFields# = \_err (Rcd# sq ) -> unsafeCoerce `map` Foldable.toList sq
instance ToFields err Vrt where toFields# = \_err (Vrt# x _) -> unsafeCoerce x
