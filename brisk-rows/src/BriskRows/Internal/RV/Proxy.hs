{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fplugin=BriskRows.Plugin #-}

{-# OPTIONS_HADDOCK -not-home #-}

module BriskRows.Internal.RV.Proxy (
    -- * Records
    delP,
    insP,
    prjP,
    -- * Variants
    casP,
    injP,
    wknP,
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

-----

-- | Alias of 'ins#'
insP :: KnownLT nm rho => proxy nm -> a -> Rcd rho -> Rcd (rho :& nm := a)
insP = \nm -> ins# (symbol# nm)

-- | Alias of 'del#'
delP :: KnownLT nm rho => symbol nm -> Rcd (rho :& nm := a) -> Rcd rho
delP = \nm -> del# (symbol# nm)

-- | Alias of 'prj#'
prjP :: KnownLT nm rho => proxy nm -> Rcd rho -> Select nm rho
prjP = \nm -> prj# (symbol# nm)

-----

-- | Alias of 'cas#'
casP :: KnownLT nm rho => proxy nm -> (a -> ans) -> (Vrt rho -> ans) -> (Vrt (rho :& nm := a) -> ans)
casP = \nm -> cas# (symbol# nm)

-- | Alias of 'wkn##'
wknP :: KnownLT nm rho => symbol nm -> (Vrt (rho :& nm := a) -> ans) -> (Vrt rho -> ans)
wknP = \nm -> wkn# (symbol# nm)

-- | Alias of 'inj#'
injP :: KnownLT nm rho => proxy nm -> Select nm rho -> Vrt rho
injP = \nm -> inj# (symbol# nm)

-----

-- | Alias of 'lacking#'
lackingP :: Absent nm rho => symbol nm -> f rho -> f rho
lackingP = \nm -> lacking# (symbol# nm)
