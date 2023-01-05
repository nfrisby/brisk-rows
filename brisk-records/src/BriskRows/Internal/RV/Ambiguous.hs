{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fplugin=BriskRows.Plugin #-}

{-# OPTIONS_HADDOCK not-home #-}

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
ins :: forall nm {a} {rho}. KnownLT nm rho => a -> Rcd rho -> Rcd (rho :& nm := a)
ins = ins# (proxy# @nm)

-- | Alias of 'del#'
del :: forall nm {a} {rho}. KnownLT nm rho => Rcd (rho :& nm := a) -> Rcd rho
del = del# (proxy# @nm)

-- | Alias of 'prj#'
prj :: forall nm {a} {rho}. (KnownLT nm rho, Found a ~ Find nm rho) => Rcd rho -> a
prj = prj# (proxy# @nm)

-- prj :: forall nm {a} {rho}. KnownLT nm (rho :& nm := a) => Rcd (rho :& nm := a) -> a


-----

-- | Alias of 'cas#'
cas :: forall nm {a} {rho} {ans}. KnownLT nm rho => (a -> ans) -> (Vrt rho -> ans) -> (Vrt (rho :& nm := a) -> ans)
cas = cas# (proxy# @nm)

-- | Alias of 'wkn#'
wkn :: forall nm {a} {rho} {ans}. KnownLT nm rho => (Vrt (rho :& nm := a) -> ans) -> (Vrt rho -> ans)
wkn = wkn# (proxy# @nm)

-- | Alias of 'inj#'
inj :: forall nm {a} {rho}. (KnownLT nm rho, Found a ~ Find nm rho) => a -> Vrt rho
inj = inj# (proxy# @nm)

-- inj :: forall nm {a} {rho}. KnownLT nm (rho :& nm := a) => a -> Vrt (rho :& nm := a)

-----

-- | Alias of 'lacking#'
lacking :: forall nm {rho} {rv}. Absent nm rho => rv rho -> rv rho
lacking = lacking# (proxy# @nm)
