{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fplugin=BriskRows.Plugin #-}

{-# OPTIONS_HADDOCK -not-home #-}

module BriskRows.Internal.RV.Ambiguous (
    -- * Records
    del,
    ins,
    prj,
    -- * Variants
    cas,
    inj,
    wkn,
    -- * Both
    lacking,
    ) where

import           GHC.Exts (proxy#)

import           BriskRows.Internal
import           BriskRows.Internal.RV

-----

-- | Alias of 'ins#'
ins :: forall nm a rho. KnownLT nm rho => a -> Rcd rho -> Rcd (rho :& nm := a)
ins = ins# (proxy# @nm)

-- | Alias of 'del#'
del :: forall nm a rho. KnownLT nm rho => Rcd (rho :& nm := a) -> Rcd rho
del = del# (proxy# @nm)

-- | Alias of 'prj#'
prj :: forall nm rho. KnownLT nm rho => Rcd rho -> Select nm rho
prj = prj# (proxy# @nm)

-----

-- | Alias of 'cas#'
cas :: forall nm a rho ans. KnownLT nm rho => (a -> ans) -> (Vrt rho -> ans) -> (Vrt (rho :& nm := a) -> ans)
cas = cas# (proxy# @nm)

-- | Alias of 'wkn#'
wkn :: forall nm a rho ans. KnownLT nm rho => (Vrt (rho :& nm := a) -> ans) -> (Vrt rho -> ans)
wkn = wkn# (proxy# @nm)

-- | Alias of 'inj#'
inj :: forall nm rho. KnownLT nm rho => Select nm rho -> Vrt rho
inj = inj# (proxy# @nm)

-----

-- | Alias of 'lacking#'
lacking :: forall nm rho f. Absent nm rho => f rho -> f rho
lacking = lacking# (proxy# @nm)
