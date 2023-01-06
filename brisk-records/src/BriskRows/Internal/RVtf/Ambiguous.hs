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

module BriskRows.Internal.RVtf.Ambiguous (
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
import           BriskRows.Internal.RVtf
import           BriskRows.Sem

-----

-- | Alias of 'ins#'
ins :: forall nm {a} {rho} {f}. KnownLT nm rho => Sem f nm a -> Rcd f rho -> Rcd f (rho :& nm := a)
ins = ins# (proxy# @nm)

-- | Alias of 'del#'
del :: forall nm {a} {rho} {f}. KnownLT nm rho => Rcd f (rho :& nm := a) -> Rcd f rho
del = del# (proxy# @nm)

-- | Alias of 'prj#'
prj :: forall nm {a} {rho} {f}. (KnownLT nm rho, Found a ~ Find nm rho) => Rcd f rho -> Sem f nm a
prj = prj# (proxy# @nm)

-- prj :: forall nm {a} {rho} {f}. KnownLT nm (rho :& nm := a) => Rcd f (rho :& nm := a) -> Sem f nm a

-----

-- | Alias of 'cas#'
cas :: forall nm {a} {rho} {f} {ans}. KnownLT nm rho => (Sem f nm a -> ans) -> (Vrt f rho -> ans) -> (Vrt f (rho :& nm := a) -> ans)
cas = cas# (proxy# @nm)

-- | Alias of 'wkn#'
wkn :: forall nm {a} {rho} {f} {ans}. KnownLT nm rho => (Vrt f (rho :& nm := a) -> ans) -> (Vrt f rho -> ans)
wkn = wkn# (proxy# @nm)

-- | Alias of 'inj#'
inj :: forall nm {a} {rho} {f}. (KnownLT nm rho, Found a ~ Find nm rho) => Sem f nm a -> Vrt f rho
inj = inj# (proxy# @nm)

-- inj :: forall nm {a} {rho} {f}. KnownLT nm (rho :& nm := a) => Sem f nm a -> Vrt f (rho :& nm := a)

-----

-- | Alias of 'lacking#'
lacking :: forall nm {rho} {t} {f}. Absent nm rho => t f rho -> t f rho
lacking = lacking# (proxy# @nm)
