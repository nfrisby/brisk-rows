{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
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
    ) where

import           Data.Kind (Type)
import           GHC.Exts (Proxy#)

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
