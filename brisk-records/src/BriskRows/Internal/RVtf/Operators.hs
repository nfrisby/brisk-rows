{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fplugin=BriskRows.Plugin #-}

{-# OPTIONS_HADDOCK not-home #-}

module BriskRows.Internal.RVtf.Operators (
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

import           BriskRows.Internal
import           BriskRows.Internal.RV.Operators (Name (Name), col)
import           BriskRows.Internal.RVtf
import           BriskRows.Internal.RVtf.Proxy
import           BriskRows.Internal.Sem

-----

infixl 5 .*

-- | Alias of 'ins#'
(.*) :: KnownLT nm rho => Rcd f rho -> COL (Name nm) (Sem f nm a) -> Rcd f (rho :& nm := a)
rcd .* nm := a = insP nm a rcd

infixl 5 ./

-- | Alias of 'del#'
(./) :: KnownLT nm rho => Rcd f (rho :& nm := a) -> Name nm -> Rcd f rho
rcd ./ nm = delP nm rcd

-----

infixl 5 .+

-- | Alias of 'cas#'
(.+) :: KnownLT nm rho => (Vrt f rho -> ans) -> COL (Name nm) (Sem f nm a -> ans) -> (Vrt f (rho :& nm := a) -> ans)
g .+ nm := f = casP nm f g

infixl 5 .-

-- | Alias of 'wkn#'
(.-) :: KnownLT nm rho => (Vrt f (rho :& nm := a) -> ans) -> Name nm -> (Vrt f rho -> ans)
g .- nm = wknP nm g
