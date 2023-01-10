{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -fplugin=BriskRows.Plugin #-}

{-# OPTIONS_HADDOCK not-home #-}

module BriskRows.Internal.RV (
    -- * Records
    Rcd (Rcd),
    del#,
    emp,
    ins#,
    prj#,
    -- * Variants
    Vrt (Vrt),
    abd,
    cas#,
    inj#,
    wkn#,
    -- * Both
    AllMonoid,
    AllSemigroup,
    lacking#,
    pur,
    Splat (splat#),
    SplatF,
    splat,
    ) where

import           Data.Kind (Type)
import           GHC.Exts (Proxy#, proxy#)

import qualified BriskRows.Fields as Fields
import           BriskRows.Internal
import qualified BriskRows.Internal.RVf as RVf
import qualified BriskRows.Internal.RVtf as RVtf
import qualified BriskRows.Sem as Sem

-----

-- | A record
newtype Rcd (rho :: ROW k Type) = Rcd (RVf.Rcd Fields.I rho)

-- | The empty record
emp :: forall {k}. Rcd (Emp :: ROW k Type)
emp = Rcd $ RVf.emp

-- | Extend the record's row by inserting another field
ins# :: forall {nm} {rho} {a}. KnownLT nm rho => Proxy# nm -> a -> Rcd rho -> Rcd (rho :& nm := a)
ins# = \nm a (Rcd rcd) -> Rcd $ RVf.ins# nm (Fields.I a) rcd

-- | Restrict the record's row by deleting a field
del# :: forall {nm} {rho} {a}. KnownLT nm rho => Proxy# nm -> Rcd (rho :& nm := a) -> Rcd rho
del# = \nm (Rcd rcd) -> Rcd $ RVf.del# nm rcd

-- | Project a value out of the record
prj# :: forall {nm} {rho} {a}. KnownLT nm rho => Proxy# nm -> Rcd (rho :& nm := a) -> a
prj# = \nm (Rcd rcd) -> Fields.unI $ RVf.prj# nm rcd

-----

-- | A variant
newtype Vrt (rho :: ROW k Type) = Vrt (RVf.Vrt Fields.I rho)

-- | An absurd value, since an empty variant is an empty type
abd :: forall {ans}. Vrt Emp -> ans
abd = error "Vrt.abd"

-- | Extend a variant continuation's row by adding another case
cas# :: forall {nm} {rho} {a} {ans}. KnownLT nm rho => Proxy# nm -> (a -> ans) -> (Vrt rho -> ans) -> (Vrt (rho :& nm := a) -> ans)
cas# = \nm f g (Vrt vrt) -> RVf.cas# nm (f . Fields.unI) (g . Vrt) vrt

-- | Restrict a variant continuation's row by weakening it no longer handle a specific case
wkn# :: forall {nm} {rho} {a} {ans}. KnownLT nm rho => Proxy# nm -> (Vrt (rho :& nm := a) -> ans) -> (Vrt rho -> ans)
wkn# = \nm f (Vrt vrt) -> RVf.wkn# nm (f . Vrt) vrt

-- | Inject a value into the variant
inj# :: forall {nm} {rho} {a}. KnownLT nm rho => Proxy# nm -> a -> Vrt (rho :& nm := a)
inj# = \nm a -> Vrt $ RVf.inj# nm (Fields.I a)

-----

-- | Require the name is 'Absent' from the row
lacking# :: forall {nm} {rho} {rv}. Absent nm rho => Proxy# nm -> rv rho -> rv rho
lacking# = \_nm -> id

-----

class    Monoid v => ImgIsMonoid k v
instance Monoid v => ImgIsMonoid k v

-- | Every image in the row is an instance of 'Monoid'
class    (AllCols (Sem.Con Sem.CTop) rho, RVf.AllCols ImgIsMonoid rho) => AllMonoid (rho :: ROW k Type)
instance (AllCols (Sem.Con Sem.CTop) rho, RVf.AllCols ImgIsMonoid rho) => AllMonoid  rho

-- | Use 'mempty' for each field
pur :: forall {rho}. AllMonoid rho => Rcd rho
pur = Rcd $
    RVf.pur# proxy# (Fields.A $ \Fields.D -> Fields.I mempty)
  `RVf.splat`
    RVf.dicts# (proxy# @ImgIsMonoid)

infixl 4 `splat`

class    Semigroup v => ImgIsSemigroup k v
instance Semigroup v => ImgIsSemigroup k v

-- | Every image in the row is an instance of 'Semigroup'
class    (AllCols (Sem.Con Sem.CTop) rho, RVf.AllCols ImgIsSemigroup rho) => AllSemigroup (rho :: ROW k Type)
instance (AllCols (Sem.Con Sem.CTop) rho, RVf.AllCols ImgIsSemigroup rho) => AllSemigroup  rho

-- | Combine one 'Rcd' or 'Vrt' with another, via '<>'
splat ::
  forall {l} {r} {rho}.
    (AllSemigroup rho, Splat (TypeErr (RVtf.NoSplat l r)) l r)
 => l rho
 -> r rho
 -> SplatF l r rho
splat = splat# (proxy# @(TypeErr (RVtf.NoSplat l r)))

-- | The result shape of 'splat'
--
-- It's 'Rcd' if both are 'Rcd's, it's @'Maybe' 'Vrt'@ if both are 'Vrt's, and it's
-- 'Vrt' if it's one of each.
type family SplatF (l :: ROW k Type -> Type) (r :: ROW k Type -> Type) (rho :: ROW k Type) :: Type
  where
    SplatF Rcd Rcd rho =        Rcd rho
    SplatF Rcd Vrt rho =        Vrt rho
    SplatF Vrt Rcd rho =        Vrt rho
    SplatF Vrt Vrt rho = Maybe (Vrt rho)

class Splat (err :: Err) (l :: ROW k Type -> Type) (r :: ROW k Type -> Type)
  where
    splat# :: (AllCols (Sem.Con Sem.CTop) rho, RVf.AllCols ImgIsSemigroup rho) => Proxy# err -> l rho -> r rho -> SplatF l r rho

combo :: (Fields.D ImgIsSemigroup Fields.:->: Fields.I Fields.:->: Fields.I Fields.:->: Fields.I) k v
combo = Fields.A $ \Fields.D -> Fields.A $ \(Fields.I l') -> Fields.A $ \(Fields.I r') -> Fields.I $ l' <> r'

instance Splat err Rcd Rcd where splat# = \_err (Rcd l) (Rcd r) ->      Rcd $ RVf.pur# proxy# combo `RVf.splat` RVf.dicts# (proxy# @ImgIsSemigroup) `RVf.splat` l `RVf.splat` r
instance Splat err Rcd Vrt where splat# = \_err (Rcd l) (Vrt r) ->      Vrt $ RVf.pur# proxy# combo `RVf.splat` RVf.dicts# (proxy# @ImgIsSemigroup) `RVf.splat` l `RVf.splat` r
instance Splat err Vrt Rcd where splat# = \_err (Vrt l) (Rcd r) ->      Vrt $ RVf.pur# proxy# combo `RVf.splat` RVf.dicts# (proxy# @ImgIsSemigroup) `RVf.splat` l `RVf.splat` r
instance Splat err Vrt Vrt where splat# = \_err (Vrt l) (Vrt r) -> fmap Vrt $ RVf.pur# proxy# combo `RVf.splat` RVf.dicts# (proxy# @ImgIsSemigroup) `RVf.splat` l `RVf.splat` r
