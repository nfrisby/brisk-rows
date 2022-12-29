{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fplugin=BriskRows.Plugin #-}

{-# OPTIONS_HADDOCK not-home #-}

module BriskRows.Internal.RVf.Proxy (
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
import           BriskRows.Internal.RVf

-----

name# :: name (nm :: k) -> Proxy# nm
name# _ = proxy#

-----

-- | Alias of 'ins#'
insP :: KnownLT nm rho => proxy nm -> f nm a -> Rcd f rho -> Rcd f (rho :& nm := a)
insP = \nm -> ins# (name# nm)

-- | Alias of 'del#'
delP :: KnownLT nm rho => name nm -> Rcd f (rho :& nm := a) -> Rcd f rho
delP = \nm -> del# (name# nm)

-- | Alias of 'prj#'
prjP :: KnownLT nm rho => proxy nm -> Rcd f rho -> f nm (Select nm rho)
prjP = \nm -> prj# (name# nm)

-----

-- | Alias of 'cas#'
casP :: KnownLT nm rho => proxy nm -> (f nm a -> ans) -> (Vrt f rho -> ans) -> (Vrt f (rho :& nm := a) -> ans)
casP = \nm -> cas# (name# nm)

-- | Alias of 'wkn#'
wknP :: KnownLT nm rho => name nm -> (Vrt f (rho :& nm := a) -> ans) -> (Vrt f rho -> ans)
wknP = \nm -> wkn# (name# nm)

-- | Alias of 'inj#'
injP :: KnownLT nm rho => proxy nm -> f nm (Select nm rho) -> Vrt f rho
injP = \nm -> inj# (name# nm)

-----

-- | Alias of 'lacking#'
lackingP :: Absent nm rho => name nm -> t rho -> t rho
lackingP = \nm -> lacking# (name# nm)
