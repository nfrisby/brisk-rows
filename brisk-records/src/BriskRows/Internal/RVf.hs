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

{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -fplugin=BriskRows.Plugin #-}

{-# OPTIONS_HADDOCK not-home #-}

module BriskRows.Internal.RVf (
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
    asFldOf,
    idFldOf#,
    lacking#,
    splat,
    ) where

import           Data.Kind (Type)
import           GHC.Exts (Proxy#, proxy#)

import           BriskRows.Fields
import           BriskRows.Internal
import qualified BriskRows.Internal.RVtf as RVtf
import qualified BriskRows.Internal.Sem as Sem

-----

-- | A record
newtype Rcd (fld :: k -> v -> Type) (rho :: ROW k v) =
    Rcd (RVtf.Rcd (Sem.Con fld `Sem.App` Sem.Nam `Sem.App` Sem.Img) rho)

emp :: Rcd fld (Emp :: ROW k v)
emp = Rcd RVtf.emp

-- | Extend the record's row by inserting another field
ins# :: KnownLT nm rho => Proxy# nm -> fld nm a -> Rcd fld rho -> Rcd fld (rho :& nm := a)
ins# = \nm a (Rcd rcd) -> Rcd $ RVtf.ins# nm a rcd

-- | Restrict the record's row by deleting a field
del# :: KnownLT nm rho => Proxy# nm -> Rcd fld (rho :& nm := a) -> Rcd fld rho
del# = \nm (Rcd rcd) -> Rcd $ RVtf.del# nm rcd

-- | Project a value out of the record
--
-- See 'Select'.
prj# :: KnownLT nm rho => Proxy# nm -> Rcd fld rho -> fld nm (Select nm rho)
prj# = \nm (Rcd rcd) -> RVtf.prj# nm rcd

-----

-- | A variant
data Vrt (fld :: k -> v -> Type) (rho :: ROW k v) =
    Vrt (RVtf.Vrt (Sem.Con fld `Sem.App` Sem.Nam `Sem.App` Sem.Img) rho)

-- | An absurd value, since an empty variant is an empty type
abd :: Vrt fld Emp -> ans
abd = error "Vrt.abd"

-- | Extend a variant continuation's row by adding another case
cas# :: KnownLT nm rho => Proxy# nm -> (fld nm a -> ans) -> (Vrt fld rho -> ans) -> (Vrt fld (rho :& nm := a) -> ans)
cas# = \nm fld g (Vrt vrt) -> RVtf.cas# nm fld (g . Vrt) vrt

-- | Restrict a variant continuation's row by weakening it no longer handle a specific case
wkn# :: KnownLT nm rho => Proxy# nm -> (Vrt fld (rho :& nm := a) -> ans) -> (Vrt fld rho -> ans)
wkn# = \nm fld (Vrt vrt) -> RVtf.wkn# nm (fld . Vrt) vrt

-- | Inject a value into the variant
--
-- See 'Select'.
inj# :: KnownLT nm rho => Proxy# nm -> fld nm (Select nm rho) -> Vrt fld rho
inj# = \nm a -> Vrt $ RVtf.inj# nm a

-----

infix 2 `asFldOf`

asFldOf :: t (fld :: k -> v -> Type) (rho1 :: ROW k v) -> u fld rho2 -> t fld rho1
asFldOf = \x _y -> x

idFldOf# :: Proxy# fld -> t (fld :: k -> v -> Type) (rho :: ROW k v) -> t fld rho
idFldOf# = \_f x -> x

lacking# :: Absent nm rho => Proxy# nm -> t rho -> t rho
lacking# = RVtf.lacking#

-----

splat ::
  forall {l} {r} {fld1} {fld2} {rho}.
    Splat (TypeErr (RVtf.NoSplat l r)) l r
 => l (fld1 :->: fld2) rho
 -> r fld1 rho
 -> SplatF l r fld2 rho
splat = splat# (proxy# @(TypeErr (RVtf.NoSplat l r)))

type family SplatF (l :: (k -> v -> Type) -> ROW k v -> Type) (r :: (k -> v -> Type) -> ROW k v -> Type) (fld :: k -> v -> Type) (rho :: ROW k v) :: Type
  where
    SplatF Rcd Rcd fld rho =        Rcd fld rho
    SplatF Rcd Vrt fld rho =        Vrt fld rho
    SplatF Vrt Rcd fld rho =        Vrt fld rho
    SplatF Vrt Vrt fld rho = Maybe (Vrt fld rho)

class Splat (err :: Err) (l :: (k -> v -> Type) -> ROW k v -> Type) (r :: (k -> v -> Type) -> ROW k v -> Type)
  where
    splat# :: Proxy# err -> l (fld1 :->: fld2) rho -> r fld1 rho -> SplatF l r fld2 rho

type Lift fld = Sem.Con fld `Sem.App` Sem.Nam `Sem.App` Sem.Img

unwrap ::
     Sem.Sem (Lift (fld1 :->: fld2)) k v
  -> Sem.Sem
       (Lift fld1 Sem.:->: Lift fld2)
       k
       v
unwrap = unA

instance Splat err Rcd Rcd where splat# = \err (Rcd l) (Rcd r) -> Rcd $ RVtf.splat# err (RVtf.natro# proxy# proxy# unwrap l) r
instance Splat err Rcd Vrt where splat# = \err (Rcd l) (Vrt r) -> Vrt $ RVtf.splat# err (RVtf.natro# proxy# proxy# unwrap l) r
instance Splat err Vrt Rcd where splat# = \err (Vrt l) (Rcd r) -> Vrt $ RVtf.splat# err (RVtf.natro# proxy# proxy# unwrap l) r
instance Splat err Vrt Vrt where splat# = \err (Vrt l) (Vrt r) -> Vrt <$> RVtf.splat# err (RVtf.natro# proxy# proxy# unwrap l) r
