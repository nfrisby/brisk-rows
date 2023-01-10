{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fplugin=BriskRows.Plugin #-}

{-# OPTIONS_HADDOCK not-home #-}

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

name# :: forall {k} {proxy} {nm}. proxy (nm :: k) -> Proxy# nm
name# _ = proxy#

-----

-- | Alias of 'ins#'
insP :: forall {nm} {rho} {proxy} {a}. KnownLT nm rho => proxy nm -> a -> Rcd rho -> Rcd (rho :& nm := a)
insP = \nm -> ins# (name# nm)

-- | Alias of 'del#'
delP :: forall {nm} {rho} {proxy} {a}. KnownLT nm rho => proxy nm -> Rcd (rho :& nm := a) -> Rcd rho
delP = \nm -> del# (name# nm)

-- | Alias of 'prj#'
prjP :: forall {nm} {a} {rho} {proxy}. KnownLT nm rho => proxy nm -> Rcd (rho :& nm := a) -> a
prjP = \nm -> prj# (name# nm)

-----

-- | Alias of 'cas#'
casP :: forall {nm} {rho} {proxy} {a} {ans}. KnownLT nm rho => proxy nm -> (a -> ans) -> (Vrt rho -> ans) -> (Vrt (rho :& nm := a) -> ans)
casP = \nm -> cas# (name# nm)

-- | Alias of 'wkn#'
wknP :: forall {nm} {rho} {proxy} {a} {ans}. KnownLT nm rho => proxy nm -> (Vrt (rho :& nm := a) -> ans) -> (Vrt rho -> ans)
wknP = \nm -> wkn# (name# nm)

-- | Alias of 'inj#'
injP :: forall {nm} {a} {rho} {proxy}. KnownLT nm rho => proxy nm -> a -> Vrt (rho :& nm := a)
injP = \nm -> inj# (name# nm)

-----

-- | Alias of 'lacking#'
lackingP :: forall {rv} {nm} {rho} {proxy}. Absent nm rho => proxy nm -> rv rho -> rv rho
lackingP = \nm -> lacking# (name# nm)
