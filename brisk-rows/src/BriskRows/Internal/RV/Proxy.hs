{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
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

import           BriskRows.Internal
import           BriskRows.Internal.RV

-----

name# :: name (nm :: k) -> Proxy# nm
name# _ = proxy#

-----

-- | Alias of 'ins#'
insP :: KnownLT nm rho => proxy nm -> a -> Rcd rho -> Rcd (rho :& nm := a)
insP = \nm -> ins# (name# nm)

-- | Alias of 'del#'
delP :: KnownLT nm rho => name nm -> Rcd (rho :& nm := a) -> Rcd rho
delP = \nm -> del# (name# nm)

-- | Alias of 'prj#'
prjP :: KnownLT nm rho => proxy nm -> Rcd rho -> Select nm rho
prjP = \nm -> prj# (name# nm)

-----

-- | Alias of 'cas#'
casP :: KnownLT nm rho => proxy nm -> (a -> ans) -> (Vrt rho -> ans) -> (Vrt (rho :& nm := a) -> ans)
casP = \nm -> cas# (name# nm)

-- | Alias of 'wkn##'
wknP :: KnownLT nm rho => name nm -> (Vrt (rho :& nm := a) -> ans) -> (Vrt rho -> ans)
wknP = \nm -> wkn# (name# nm)

-- | Alias of 'inj#'
injP :: KnownLT nm rho => proxy nm -> Select nm rho -> Vrt rho
injP = \nm -> inj# (name# nm)

-----

-- | Alias of 'lacking#'
lackingP :: Absent nm rho => name nm -> f rho -> f rho
lackingP = \nm -> lacking# (name# nm)
