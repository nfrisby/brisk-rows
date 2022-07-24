{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fplugin=BriskRows.Plugin #-}

{-# OPTIONS_HADDOCK -not-home #-}

module BriskRows.Internal.RV.Operators (
    -- * Records
    (.*),
    (./),
    -- * Variants
    (.+),
    (.-),
    -- * Both
    Name (Name),
    col,
    ) where

import           GHC.OverloadedLabels
import           GHC.TypeLits (Symbol)
import           GHC.Types (type (~~))

import           BriskRows.Internal
import           BriskRows.Internal.RV
import           BriskRows.Internal.RV.Proxy

-----

data Name (nm :: k) = Name
instance (k ~ Symbol, sym1 ~~ sym2) => IsLabel sym1 (Name (sym2 :: k)) where fromLabel = Name

col :: forall nm a. a -> COL (Name nm) a
col = \a -> Name := a

-----

infixl 5 .*

-- | Alias of 'ins#'
(.*) :: KnownLT nm rho => Rcd rho -> COL (Name nm) a -> Rcd (rho :& nm := a)
rcd .* nm := a = insP nm a rcd

infixl 5 ./

-- | Alias of 'del#'
(./) :: KnownLT nm rho => Rcd (rho :& nm := a) -> Name nm -> Rcd rho
rcd ./ nm = delP nm rcd

-----

infixl 5 .+

-- | Alias of 'cas#'
(.+) :: KnownLT nm rho => (Vrt rho -> ans) -> COL (Name nm) (a -> ans) -> (Vrt (rho :& nm := a) -> ans)
g .+ nm := f = casP nm f g

infixl 5 .-

-- | Alias of 'wkn#'
(.-) :: KnownLT nm rho => (Vrt (rho :& nm := a) -> ans) -> Name nm -> (Vrt rho -> ans)
g .- nm = wknP nm g
