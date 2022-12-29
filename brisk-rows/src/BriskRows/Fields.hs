{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module BriskRows.Fields (
  -- * Field structure combinators
  A (A, A#, AP), (:->:), unA, unA#, unAP,
  C (C, C#, CP), (:.:), unC, unC#, unCP,
  D (D, D#, DP), withD, withD#, withDP,
  E, unE, unE#, unEP,
  I (I, I#, IP), unI, unI#, unIP, withI, withI#, withIP,
  K (K, K#, KP), unK, unK#, unKP, withK, withK#, withKP,
  P (P, P#, PP), (:*:), unP, unP#, unPP,
  S (L, L#, LP, R, R#, RP), (:+:), unS, unS#, unSP,
  N (N, N#, NP), unN, unN#, unNP,
  V (V, V#, VP), unV, unV#, unVP,
  U (U, U#, UP), unU, unU#, unUP,
  Y (Y, Y#, YP), unY, unY#, unYP,
  ) where

import           Data.Proxy (Proxy (Proxy))
import           GHC.Exts (Proxy#, proxy#)
import           GHC.Generics (Generic)

-----

-- We can TypeApplication this without supplying the kind argument
proxyP :: Proxy a
proxyP = Proxy

-----

-- | Identity (just the value)
newtype I k v = I v
  deriving (Eq, Generic, Ord, Show)

pattern I# :: forall k v. Proxy# k -> v -> I k v
pattern I# k v <- I v@((\_ -> proxy# @k) -> k)
  where
    I# _ v = I v

pattern IP :: forall k v. Proxy k -> v -> I k v
pattern IP k v <- I v@((\_ -> proxyP @k) -> k)
  where
    IP _ v = I v

{-# COMPLETE I# #-}
{-# COMPLETE IP #-}

unI :: I k v -> v
unI = \(I v) -> v

unI# :: Proxy# k -> I k v -> v
unI# = \_k -> unI

unIP :: proxy k -> I k v -> v
unIP = \_k -> unI

withI :: forall k v ans. (v -> ans) -> I k v -> ans
withI = \f (I v) -> f v

withI# :: forall k v ans. Proxy# k -> (v -> ans) -> I k v -> ans
withI# = \_k -> withI

withIP :: forall k v ans proxy. proxy k -> (v -> ans) -> I k v -> ans
withIP = \_k -> withI

-----

-- | Constant
newtype K b k v = K b
  deriving (Eq, Generic, Ord, Show)

pattern K# :: forall b k v. Proxy# k -> Proxy# v -> b -> K b k v
pattern K# k v b <- K b@((\_ -> proxy# @k) -> k@((\_ -> proxy# @v) -> v))
  where
    K# _ _ b = K b

pattern KP :: forall b k v. Proxy k -> Proxy v -> b -> K b k v
pattern KP k v b <- K b@((\_ -> proxyP @k) -> k@((\_ -> proxyP @v) -> v))
  where
    KP _ _ b = K b

{-# COMPLETE K# #-}
{-# COMPLETE KP #-}

unK :: K b k v -> b
unK = \(K b) -> b

unK# :: Proxy# k -> K b k v -> b
unK# = \_k -> unK

unKP :: proxy k -> K b k v -> b
unKP = \_k -> unK

withK :: forall k v b ans. (b -> ans) -> K b k v -> ans
withK = \f (K b) -> f b

withK# :: forall k v b ans. Proxy# k -> Proxy# v -> (b -> ans) -> K b k v -> ans
withK# = \_k _v -> withK

withKP :: forall k v b ans proxy. proxy k -> proxy v -> (b -> ans) -> K b k v -> ans
withKP = \_k _v -> withK

-----

-- | Arrow
newtype A f g k v = A (f k v -> g k v)

infixr 0 :->:
type (:->:) = A

pattern A# :: forall f g k v. Proxy# k -> Proxy# v -> (f k v -> g k v) -> A f g k v
pattern A# k v fn <- A fn@((\_ -> proxy# @k) -> k@((\_ -> proxy# @v) -> v))
  where
    A# _ _ fn = A fn

pattern AP :: forall f g k v. Proxy k -> Proxy v -> (f k v -> g k v) -> A f g k v
pattern AP k v fn <- A fn@((\_ -> proxyP @k) -> k@((\_ -> proxyP @v) -> v))
  where
    AP _ _ fn = A fn

{-# COMPLETE A# #-}
{-# COMPLETE AP #-}

unA :: A f g k v -> f k v -> g k v
unA = \(A fn) -> fn

unA# :: Proxy# k -> A f g k v -> f k v -> g k v
unA# = \_k -> unA

unAP :: proxy k -> A f g k v -> f k v -> g k v
unAP = \_k -> unA

-----

-- | Composition, providing the name to both
newtype C f g k v = C (f k (g k v))
  deriving (Generic)

deriving instance Eq   (f k (g k v)) => Eq   (C f g k v)
deriving instance Ord  (f k (g k v)) => Ord  (C f g k v)
deriving instance Read (f k (g k v)) => Read (C f g k v)
deriving instance Show (f k (g k v)) => Show (C f g k v)

infixr 9 :.:
type (:.:) = C

pattern C# :: forall f g k v. Proxy# k -> Proxy# v -> f k (g k v) -> C f g k v
pattern C# k v fg <- C fg@((\_ -> proxy# @k) -> k@((\_ -> proxy# @v) -> v))
  where
    C# _ _ fg = C fg

pattern CP :: forall f g k v. Proxy k -> Proxy v -> f k (g k v) -> C f g k v
pattern CP k v fg <- C fg@((\_ -> proxyP @k) -> k@((\_ -> proxyP @v) -> v))
  where
    CP _ _ fg = C fg

{-# COMPLETE C# #-}
{-# COMPLETE CP #-}

unC :: C f g k v -> f k (g k v)
unC = \(C fg) -> fg

unC# :: Proxy# k -> C f g k v -> f k (g k v)
unC# = \_k -> unC

unCP :: Proxy k -> C f g k v -> f k (g k v)
unCP = \_k -> unC

-----

-- | Dictionary
data D c k v = c k v => D# (Proxy# c) (Proxy# k) (Proxy# v)

pattern D :: forall c k v. () => c k v => D c k v
pattern D <- D# _ _ _
  where
    D = D# (proxy# @c) (proxy# @k) (proxy# @v)

pattern DP :: forall c k v. () => c k v => Proxy c -> Proxy k -> Proxy v -> D c k v
pattern DP c k v <- D# ((\_ -> proxyP @c) -> c) ((\_ -> proxyP @k) -> k) ((\_ -> proxyP @v) -> v)
  where
    DP _c _k _v = D# (proxy# @c) (proxy# @k) (proxy# @v)

{-# COMPLETE D #-}
{-# COMPLETE DP #-}

withD :: D c k v -> (c k v => ans) -> ans
withD = \D#{} k -> k

withD# :: Proxy# c -> Proxy# k -> D c k v -> (c k v => ans) -> ans
withD# = \_c _k -> withD

withDP :: proxyc c -> proxyk k -> D c k v -> (c k v => ans) -> ans
withDP = \_c _k -> withD

-----

-- | Product
data P l r k v = P (l k v) (r k v)
  deriving (Eq, Generic, Ord, Read, Show)

infixr 7 :*:
type (:*:) = P

pattern P# :: forall l r k v. Proxy# k -> Proxy# v -> l k v -> r k v -> P l r k v
pattern P# k v l r <- P l r@((\_ -> proxy# @k) -> k@((\_ -> proxy# @v) -> v))
  where
    P# _ _ l r = P l r

pattern PP :: forall l r k v. Proxy k -> Proxy v -> l k v -> r k v -> P l r k v
pattern PP k v l r <- P l r@((\_ -> proxyP @k) -> k@((\_ -> proxyP @v) -> v))
  where
    PP _ _ l r = P l r

{-# COMPLETE P# #-}
{-# COMPLETE PP #-}

unP :: P l r k v -> (l k v, r k v)
unP = \(P l r) -> (l, r)

unP# :: Proxy# k -> P l r k v -> (l k v, r k v)
unP# = \_k -> unP

unPP :: proxy k -> P l r k v -> (l k v, r k v)
unPP = \_k -> unP

-----

-- | Sum
data S l r k v = L (l k v) | R (r k v)
  deriving (Eq, Generic, Ord, Read, Show)

infixr 6 :+:
type (:+:) = S

pattern L# :: forall l r k v. Proxy# k -> Proxy# v -> l k v -> S l r k v
pattern L# k v l <- L l@((\_ -> proxy# @k) -> k@((\_ -> proxy# @v) -> v))
  where
    L# _ _ l = L l

pattern R# :: forall l r k v. Proxy# k -> Proxy# v -> r k v -> S l r k v
pattern R# k v r <- R r@((\_ -> proxy# @k) -> k@((\_ -> proxy# @v) -> v))
  where
    R# _ _ r = R r

pattern LP :: forall l r k v. Proxy k -> Proxy v -> l k v -> S l r k v
pattern LP k v l <- L l@((\_ -> proxyP @k) -> k@((\_ -> proxyP @v) -> v))
  where
    LP _ _ l = L l

pattern RP :: forall l r k v. Proxy k -> Proxy v -> r k v -> S l r k v
pattern RP k v r <- R r@((\_ -> proxyP @k) -> k@((\_ -> proxyP @v) -> v))
  where
    RP _ _ r = R r

{-# COMPLETE L#, R# #-}
{-# COMPLETE L#, RP #-}
{-# COMPLETE LP, R# #-}
{-# COMPLETE LP, RP #-}

unS :: S l r k v -> l k v `Either` r k v
unS = \case
    L l -> Left  l
    R r -> Right r

unS# :: Proxy# k -> S l r k v -> l k v `Either` r k v
unS# = \_k -> unS

unSP :: proxy k -> S l r k v -> l k v `Either` r k v
unSP = \_k -> unS

-----

-- | Apply to just the name
newtype N f k v = N (f k)
  deriving (Eq, Generic, Ord, Show)

pattern N# :: forall f k v. Proxy# k -> Proxy# v -> f k -> N f k v
pattern N# k v f <- N f@((\_ -> proxy# @k) -> k@((\_ -> proxy# @v) -> v))
  where
    N# _ _ f = N f

pattern NP :: forall f k v. Proxy k -> Proxy v -> f k -> N f k v
pattern NP k v f <- N f@((\_ -> proxyP @k) -> k@((\_ -> proxyP @v) -> v))
  where
    NP _ _ f = N f

{-# COMPLETE N# #-}
{-# COMPLETE NP #-}

unN :: N f k v -> f k
unN = \(N f) -> f

unN# :: Proxy# k -> N f k v -> f k
unN# = \_k -> unN

unNP :: proxy k -> N f k v -> f k
unNP = \_k -> unN

-----

-- | Apply to just the value
newtype V f k v = V (f v)
  deriving (Eq, Generic, Ord, Show)

pattern V# :: forall f k v. Proxy# k -> Proxy# v -> f v -> V f k v
pattern V# k v f <- V f@((\_ -> proxy# @k) -> k@((\_ -> proxy# @v) -> v))
  where
    V# _ _ f = V f

pattern VP :: forall f k v. Proxy k -> Proxy v -> f v -> V f k v
pattern VP k v f <- V f@((\_ -> proxyP @k) -> k@((\_ -> proxyP @v) -> v))
  where
    VP _ _ f = V f

{-# COMPLETE V# #-}
{-# COMPLETE VP #-}

unV :: V f k v -> f v
unV = \(V f) -> f

unV# :: Proxy# k -> V f k v -> f v
unV# = \_k -> unV

unVP :: proxy k -> V f k v -> f v
unVP = \_k -> unV

-----

-- | Unit
data U k v = U
  deriving (Eq, Generic, Ord, Show)

pattern U# :: forall k v. Proxy# k -> Proxy# v -> U k v
pattern U# k v <- _u@((\_ -> proxy# @k) -> k@((\_ -> proxy# @v) -> v))
  where
    U# _ _ = U

pattern UP :: forall k v. Proxy k -> Proxy v -> U k v
pattern UP k v <- ((\u -> (u, proxyP @k, proxyP @v)) -> (U, k, v))
  where
    UP _ _ = U

{-# COMPLETE U# #-}
{-# COMPLETE UP #-}

unU :: U k v -> ()
unU = \U -> ()

unU# :: Proxy# k -> U k v -> ()
unU# = \_k -> unU

unUP :: proxy k -> U k v -> ()
unUP = \_k -> unU

-----

-- | Empty
data E k v
  deriving (Eq, Generic, Ord, Show)

unE :: E k v -> r
unE = \case {}

unE# :: Proxy# k -> E k v -> r
unE# = \_k -> unE

unEP :: proxy k -> E k v -> r
unEP = \_k -> unE

-----

-- | Join
newtype Y f fk fv k v = Y (f (fk k v) (fv k v))
  deriving (Generic)

deriving instance Eq   (f (fk k v) (fv k v)) => Eq   (Y f fk fv k v)
deriving instance Ord  (f (fk k v) (fv k v)) => Ord  (Y f fk fv k v)
deriving instance Read (f (fk k v) (fv k v)) => Read (Y f fk fv k v)
deriving instance Show (f (fk k v) (fv k v)) => Show (Y f fk fv k v)

pattern Y# :: forall f fk fv k v. Proxy# k -> Proxy# v -> f (fk k v) (fv k v) -> Y f fk fv k v
pattern Y# k v f <- Y f@((\_ -> proxy# @k) -> k@((\_ -> proxy# @v) -> v))
  where
    Y# _ _ f = Y f

pattern YP :: forall f fk fv k v. Proxy k -> Proxy v -> f (fk k v) (fv k v) -> Y f fk fv k v
pattern YP k v f <- Y f@((\_ -> proxyP @k) -> k@((\_ -> proxyP @v) -> v))
  where
    YP _ _ f = Y f

{-# COMPLETE Y# #-}
{-# COMPLETE YP #-}

unY :: Y f fk fv k v -> f (fk k v) (fv k v)
unY = \(Y f) -> f

unY# :: Proxy# k -> Y f fk fv k v -> f (fk k v) (fv k v)
unY# = \_k -> unY

unYP :: proxy k -> Y f fk fv k v -> f (fk k v) (fv k v)
unYP = \_k -> unY
