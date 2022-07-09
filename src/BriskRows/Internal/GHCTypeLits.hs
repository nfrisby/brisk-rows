{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Compat layer for some definitions recently added to "GHC.TypeLits"
module BriskRows.Internal.GHCTypeLits (
    module BriskRows.Internal.GHCTypeLits,
    module GHC.TypeLits,
  ) where

import           Data.Type.Equality ((:~:)(Refl))
import           GHC.Exts (Proxy#)
import           GHC.TypeLits
import           Unsafe.Coerce (unsafeCoerce)

-- | adapted from base-4.16.0.0
data OrderingI a b where
  LTI :: CmpSymbol a b ~ LT => OrderingI a b
  EQI :: CmpSymbol a a ~ EQ => OrderingI a a
  GTI :: CmpSymbol a b ~ GT => OrderingI a b

-- | adapted from base-4.16.0.0
cmpSymbol :: forall l r. (KnownSymbol l, KnownSymbol r)
          => Proxy# l -> Proxy# r -> OrderingI l r
cmpSymbol l r = case compare (symbolVal' l) (symbolVal' r) of
  EQ -> case unsafeCoerce (Refl, Refl) :: (EQ :~: CmpSymbol l r, l :~: r) of (Refl, Refl) -> EQI
  LT -> case unsafeCoerce Refl         :: (LT :~: CmpSymbol l r         ) of Refl         -> LTI
  GT -> case unsafeCoerce Refl         :: (GT :~: CmpSymbol l r         ) of Refl         -> GTI
