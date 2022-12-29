{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fplugin=BriskRows.Plugin #-}

{-# OPTIONS_HADDOCK not-home #-}

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

-- | A 'Data.Proxy.Proxy' isomorph with a more specific name and an instance of 'IsLabel'
--
-- This enables expressions such as @'BriskRows.RV.emp' '.*' #foo 'BriskRows.:=' True '.*' #bar 'BriskRows.:=' 3@ when using @-XOverloadedLabels@.
data Name nm where    -- omitting the k variable so that it has /inferred/ visibility
  Name :: forall {nm}. Name nm

instance (k ~ Symbol, sym1 ~~ sym2) => IsLabel sym1 (Name (sym2 :: k)) where fromLabel = Name

-- | A 'COL' constructor that adds a 'Name' wrapper
--
-- This enables expressions such as @'emp' '.*' 'col' \@Int True '.*' 'col' \@Char Nothing@ when using @-XTypeApplications@ instead of @-XOverloadedLabels@.
col :: forall nm {a}. a -> COL (Name nm) a
col = \a -> Name := a

-----

infixl 5 .*

-- | Alias of 'ins#'
(.*) :: forall {nm} {rho} {a}. KnownLT nm rho => Rcd rho -> COL (Name nm) a -> Rcd (rho :& nm := a)
rcd .* nm := a = insP nm a rcd

infixl 5 ./

-- | Alias of 'del#'
(./) :: forall {nm} {rho} {a}. KnownLT nm rho => Rcd (rho :& nm := a) -> Name nm -> Rcd rho
rcd ./ nm = delP nm rcd

-----

infixl 5 .+

-- | Alias of 'cas#'
(.+) :: forall {nm} {rho} {a} {ans}. KnownLT nm rho => (Vrt rho -> ans) -> COL (Name nm) (a -> ans) -> (Vrt (rho :& nm := a) -> ans)
g .+ nm := f = casP nm f g

infixl 5 .-

-- | Alias of 'wkn#'
(.-) :: forall {nm} {rho} {a} {ans}. KnownLT nm rho => (Vrt (rho :& nm := a) -> ans) -> Name nm -> (Vrt rho -> ans)
g .- nm = wknP nm g
