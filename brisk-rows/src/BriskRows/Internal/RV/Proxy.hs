{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_HADDOCK -not-home #-}

module BriskRows.Internal.RV.Proxy (
    -- * Records
    delPP,
    insP,
    prjP,
    -- * Variants
    casP,
    injP,
    wknPP,
    -- * Both
    lackingP,
    ) where

import           GHC.Exts (Proxy#, proxy#)
import           GHC.TypeLits (Symbol)

import           BriskRows.Internal
import           BriskRows.Internal.RV

-----

symbol# :: symbol (nm :: Symbol) -> Proxy# nm
symbol# _ = proxy#

type# :: proxy a -> Proxy# a
type# _ = proxy#

-----

-- | Alias of 'ins#'
insP :: KnownLT nm rho => proxy nm -> a -> Rcd rho -> Rcd (rho :& nm := a)
insP = \nm -> ins# (symbol# nm)

-- | Alias of 'del##'
delPP :: KnownLT nm rho => symbol nm -> proxy a -> Rcd (rho :& nm := a) -> Rcd rho
delPP = \nm a -> del## (symbol# nm) (type# a)

-- | Alias of 'prj#'
prjP :: KnownLT nm rho => proxy nm -> Rcd rho -> Select nm rho
prjP = \nm -> prj# (symbol# nm)

-----

-- | Alias of 'cas#'
casP :: KnownLT nm rho => proxy nm -> (a -> ans) -> (Vrt rho -> ans) -> (Vrt (rho :& nm := a) -> ans)
casP = \nm -> cas# (symbol# nm)

-- | Alias of 'wkn##'
wknPP :: KnownLT nm rho => symbol nm -> proxy a -> (Vrt (rho :& nm := a) -> ans) -> (Vrt rho -> ans)
wknPP = \nm a -> wkn## (symbol# nm) (type# a)

-- | Alias of 'inj#'
injP :: KnownLT nm rho => proxy nm -> Select nm rho -> Vrt rho
injP = \nm -> inj# (symbol# nm)

-----

-- | Alias of 'lacking#'
lackingP :: Absent nm rho => symbol nm -> f rho -> f rho
lackingP = \nm -> lacking# (symbol# nm)
