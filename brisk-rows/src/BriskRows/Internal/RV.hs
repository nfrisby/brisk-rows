{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -fplugin=BriskRows.Plugin #-}

{-# OPTIONS_HADDOCK -not-home #-}

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
    lacking#,
    ) where

import           Data.Kind (Type)
import           GHC.Exts (Proxy#)

import           BriskRows.Fields (I (I), unI)
import           BriskRows.Internal
import qualified BriskRows.Internal.RVf as RVf

-----

-- | A record
newtype Rcd (rho :: ROW k Type) = Rcd (RVf.Rcd I rho)

emp :: Rcd (Emp :: ROW k Type)
emp = Rcd $ RVf.emp

-- | Extend the record's row by inserting another field
ins# :: KnownLT nm rho => Proxy# nm -> a -> Rcd rho -> Rcd (rho :& nm := a)
ins# = \nm a (Rcd rcd) -> Rcd $ RVf.ins# nm (I a) rcd

-- | Restrict the record's row by deleting a field
del# :: KnownLT nm rho => Proxy# nm -> Rcd (rho :& nm := a) -> Rcd rho
del# = \nm (Rcd rcd) -> Rcd $ RVf.del# nm rcd

-- | Project a value out of the record
--
-- See 'Select'.
prj# :: KnownLT nm rho => Proxy# nm -> Rcd rho -> Select nm rho
prj# = \nm (Rcd rcd) -> unI $ RVf.prj# nm rcd

-----

-- | A variant
newtype Vrt (rho :: ROW k Type) = Vrt (RVf.Vrt I rho)

-- | An absurd value, since an empty variant is an empty type
abd :: Vrt Emp -> ans
abd = error "Vrt.abd"

-- | Extend a variant continuation's row by adding another case
cas# :: KnownLT nm rho => Proxy# nm -> (a -> ans) -> (Vrt rho -> ans) -> (Vrt (rho :& nm := a) -> ans)
cas# = \nm f g (Vrt vrt) -> RVf.cas# nm (f . unI) (g . Vrt) vrt

-- | Restrict a variant continuation's row by weakening it no longer handle a specific case
wkn# :: KnownLT nm rho => Proxy# nm -> (Vrt (rho :& nm := a) -> ans) -> (Vrt rho -> ans)
wkn# = \nm f (Vrt vrt) -> RVf.wkn# nm (f . Vrt) vrt

-- | Inject a value into the variant
--
-- See 'Select'.
inj# :: KnownLT nm rho => Proxy# nm -> Select nm rho -> Vrt rho
inj# = \nm a -> Vrt $ RVf.inj# nm (I a)

-----

lacking# :: Absent nm rho => Proxy# nm -> t rho -> t rho
lacking# = \_nm -> id
