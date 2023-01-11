{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fplugin=BriskRows.Plugin #-}

module BriskRows.Demo (
  -- * Record type
  TIP,
  -- ** Constructors
  pattern (:*),
  pattern Nil,
  -- ** Auxiliary
  Val,
  -- ** Re-exports
  module BriskRows,
  ) where

import           Data.Kind (Type)
import           GHC.Exts (proxy#)
import           GHC.Records (HasField(getField))
import           GHC.TypeLits (Symbol)

import           BriskRows
import           BriskRows.RV            (Name (Name))
import qualified BriskRows.RVtf          as RVtf
import           BriskRows.Internal      (UnsafeExt)
import           BriskRows.Internal.RVtf (dicts#, pur#, splat, toFields)
import qualified BriskRows.Sem           as Sem

-----

data family Val (nm :: Symbol)

-----

type SemFld = Sem.Con Val `Sem.App` Sem.Nam :: Sem.Fld Symbol () Type
newtype TIP (rho :: ROW Symbol ()) = TIP (RVtf.Rcd SemFld rho)

pattern Nil :: TIP Emp
pattern Nil <- !_
  where
    Nil = TIP RVtf.emp

{-# COMPLETE Nil #-}

infixl 5 :*

pattern (:*) :: forall {rho} nm. KnownLT nm rho => () => TIP rho -> Val nm -> TIP (rho :& nm := '())
pattern (:*) rcd cl <- (uncol -> (,) rcd cl)
  where
    TIP rcd :* cl = TIP (rcd RVtf..* Name := cl)

{-# COMPLETE (:*) #-}

uncol :: forall nm rho. KnownLT nm rho => TIP (rho :& nm := '()) -> (TIP rho, Val nm)
uncol = \(TIP rcd) -> (TIP $ RVtf.del @nm rcd, RVtf.prj @nm rcd)

-----

instance (rho ~ UnsafeExt nm '() inner, KnownLT nm rho, a ~ Val nm) => HasField nm (TIP rho) a where
  getField (TIP rcd) = getField @nm rcd

-----

instance (KnownLen rho, AllCols (Sem.Con Show `Sem.App` (Sem.Con Val `Sem.App` Sem.Nam)) rho) => Show (TIP rho) where showsPrec = showsPrecTIP

showsPrecTIP :: forall {rho}. (KnownLen rho, AllCols (Sem.Con Show `Sem.App` SemFld) rho) => Int -> TIP rho -> ShowS
showsPrecTIP = \p (TIP rcd) ->
    showParen (p > 5)
  $ foldr
      (\fld acc -> acc . showString " :* " . fld)
      (showString "Nil")
      (toFields $ f `splat` dicts# proxy# `splat` rcd :: [ShowS])
  where
    f :: RVtf.Rcd
        (         Sem.Con Sem.Dict `Sem.App` (Sem.Con Show `Sem.App` SemFld)
         Sem.:->: SemFld
         Sem.:->: Sem.Con ShowS
        )
        rho
    f = pur# proxy# (\_nm _a Sem.Dict -> showsPrec 5)

-----

instance (KnownLen rho, AllCols (Sem.Con Eq `Sem.App` (Sem.Con Val `Sem.App` Sem.Nam)) rho) => Eq (TIP rho) where (==) = eqTIP

eqTIP :: forall {rho}. (KnownLen rho, AllCols (Sem.Con Eq `Sem.App` SemFld) rho) => TIP rho -> TIP rho -> Bool
eqTIP = \(TIP ls) (TIP rs) ->
    and $ toFields $ f `splat` dicts# proxy# `splat` ls `splat` rs
  where
    f :: RVtf.Rcd
        (         Sem.Con Sem.Dict `Sem.App` (Sem.Con Eq `Sem.App` SemFld)
         Sem.:->: SemFld
         Sem.:->: SemFld
         Sem.:->: Sem.Con Bool
        )
        rho
    f = pur# proxy# (\_nm _a Sem.Dict -> (==))

-----

{-

data instance Val "xy"    = XY !Int !Int       deriving (Show, Eq)
data instance Val "dir"   = LeftD | RightD     deriving (Show, Eq)
data instance Val "color" = Red | Green | Blue deriving (Show, Eq)

-- I compared and contrasted the Core of these four to determine that there was
-- a problem in the AllCols evidence the plugin generates.

_argsA :: TIP (Emp :& "xy" := '() :& "dir" := '())
_argsA = Nil :* XY 1 2 :* LeftD

_argsB :: TIP (Emp :& "dir" := '() :& "xy" := '())
_argsB = Nil :* LeftD :* XY 1 2

_dictsA :: RVtf.Rcd (Sem.Con Sem.Dict `Sem.App` (Sem.Con Show `Sem.App` SemFld)) (Emp :& "xy" := '() :& "dir" := '())
_dictsA = dicts# (proxy# @(Sem.Con Show `Sem.App` SemFld))

_dictsB :: RVtf.Rcd (Sem.Con Sem.Dict `Sem.App` (Sem.Con Show `Sem.App` SemFld)) (Emp :& "dir" := '() :& "xy" := '())
_dictsB = dicts# (proxy# @(Sem.Con Show `Sem.App` SemFld))

-}
