{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Now that 'ROW' is a newtype, the user will only be able to violate its invariant via an unsafe import. That's acceptable.
--
-- Re-combining 'Rcd' and 'Seq' and an acceptable reliance on strictness via 'cons' has eliminated the noisy 'KnownRow' constraint.
--
-- The key problem with this module is its inscrutable type errors.
--
-- > extend (proxy# @"Hi") () $ extend (proxy# @"Hi") () $ emp
--
-- gives
--
-- > No instance for (ExtendCase 'EQ "Hi" () '[])
--
-- which is qualitatively less helpful than
--
-- > Cannot Insert already-present column: "Hi"
--
-- See "BriskRows.Motivation.Stage4".

module BriskRows.Motivation.Stage3 (module BriskRows.Motivation.Stage3) where

import           Data.Kind (Type)
import           GHC.Exts (Proxy#, proxy#)
import           GHC.TypeLits (CmpSymbol, Symbol)

-----

infix 7 :::
data COL = Symbol ::: Type

-- | INVARIANT the 'Col'umn names are strictly ascending wrt 'CmpSymbol'
newtype ROW = Row [COL]

type Nil = Row '[]

-----

data Rcd :: ROW -> Type where
  -- | REQUIREMENT @nm@ is less than the first column in @cols@ according to 'CmpSymbol'
  Cons :: Proxy# nm -> a -> Rcd (Row cols) -> Rcd (Row (nm ::: a ': cols))
  Nil  ::                                     Rcd (Row '[])

emp :: Rcd Nil
emp = Nil

-----

-- | We carefully define 'InsertLeast' so that it reduces to an application of 'Row' only if its argument did.
--
-- In other words, 'InsertLeast' is " strict ".
--
-- REQUIREMENT @x@ is less than the first column in @row@ according to 'CmpSymbol'
type family InsertLeast (x :: Symbol) (xv :: Type) (row :: ROW) :: ROW where
  InsertLeast x xv (Row cols) = Row (x ::: xv ': cols)

-- | REQUIREMENT @nm@ is less than the first column in @cols@ according to 'CmpSymbol'
cons :: Proxy# nm -> a -> Rcd row -> Rcd (InsertLeast nm a row)
cons nm a rcd =
    case rcd of
      Nil    -> Cons nm a rcd
      Cons{} -> Cons nm a rcd

{- -- this could soundly replace cons, which I think might improve the final GHC Core of the program

data ProofRow :: ROW -> Type where
  ProofRow :: ProofRow (Row cols)

proofDelete :: forall nm cols ans. Remove nm (Row cols) => Proxy# nm -> Proxy# (Row cols) -> (forall cols'. Delete nm (Row cols) ~ Row cols' => ans) -> ans
proofDelete _nm _row k =
    -- safe by definition of Delete and Remove
    let _ = needConstraint @(Remove nm (Row cols)) in
    case unsafeCoerce (ProofRow @'[]) :: ProofRow (Delete nm (Row cols)) of ProofRow -> k

proofInsert :: forall nm a cols ans. Extend nm (Row cols) => Proxy# nm -> Proxy# a -> Proxy# (Row cols) -> (forall cols'. Insert nm a (Row cols) ~ Row cols' => ans) -> ans
proofInsert _nm _a _row k =
    -- safe by definition of Insert and Extend
    let _ = needConstraint @(Extend nm (Row cols)) in
    case unsafeCoerce (ProofRow @'[]) :: ProofRow (Insert nm a (Row cols)) of ProofRow -> k
-}

-----

type family Lookup (nm :: Symbol) (row :: ROW) :: Type where
  Lookup nm (Row (x ::: xv ': cols)) = LookupCase (CmpSymbol nm x) nm x xv cols

type family LookupCase (o :: Ordering) (nm :: Symbol) (x :: Symbol) (xv :: Type) (cols :: [COL]) :: Type where
  LookupCase EQ nm x xv cols = xv
  LookupCase GT nm x xv cols = Lookup nm (Row cols)

class    Project (nm :: Symbol) (row :: ROW) where

  project                        :: Proxy# nm -> Rcd row -> Lookup nm row

instance ProjectCase (CmpSymbol nm x) nm cols =>
         Project nm (Row (x ::: xv ': cols)) where

  project nm (Cons x xv rcd)      = projectCase (proxy# @(CmpSymbol nm x)) nm x xv rcd

class    ProjectCase (o :: Ordering) (nm :: Symbol) (cols :: [COL]) where

  projectCase                    :: Proxy# o -> Proxy# nm -> Proxy# x -> xv -> Rcd (Row cols) -> LookupCase o nm x xv cols

instance ProjectCase EQ nm cols where

  projectCase _eq _nm _x  xv _rcd = xv

instance Project nm (Row cols) =>
         ProjectCase GT nm cols where

  projectCase _gt  nm _x _xv  rcd = project nm rcd

-----

type family Insert (nm :: Symbol) (a :: Type) (row :: ROW) :: ROW where
  Insert nm a (Row '[])                = Row '[nm ::: a]
  Insert nm a (Row (x ::: xv ': cols)) = InsertCase (CmpSymbol nm x) nm a x xv cols

type family InsertCase (o :: Ordering) (nm :: Symbol) (a :: Type) (x :: Symbol) (xv :: Type) (cols :: [COL]) :: ROW where
  InsertCase LT nm a x xv cols = Row (nm ::: a ': x ::: xv ': cols)
  InsertCase GT nm a x xv cols = InsertLeast x xv (Insert nm a (Row cols))

class    Extend (nm :: Symbol) (row :: ROW) where

  extend                      :: Proxy# nm -> a -> Rcd row -> Rcd (Insert nm a row)

instance Extend nm (Row '[]) where

  extend nm a Nil              = Cons nm a Nil

instance ExtendCase (CmpSymbol nm x) nm cols =>
         Extend nm (Row (x ::: xv ': cols)) where

  extend nm a (Cons x xv rcd)  = extendCase (proxy# @(CmpSymbol nm x)) nm a x xv rcd

class    ExtendCase (o :: Ordering) (nm :: Symbol) (cols :: [COL]) where

  extendCase                  :: Proxy# o -> Proxy# nm -> a -> Proxy# x -> xv -> Rcd (Row cols) -> Rcd (InsertCase o nm a x xv cols)

instance ExtendCase LT nm cols where

  extendCase _eq nm a x xv rcd = Cons nm a $ Cons x xv rcd

instance Extend nm (Row cols) =>
         ExtendCase GT nm cols where

  extendCase _gt nm a x xv rcd = cons x xv $ extend nm a rcd

-----

type family Delete (nm :: Symbol) (row :: ROW) :: ROW where
  Delete nm (Row (x ::: xv ': cols)) = DeleteCase (CmpSymbol nm x) nm x xv cols

type family DeleteCase (o :: Ordering) (nm :: Symbol) (x :: Symbol) (xv :: Type) (cols :: [COL]) :: ROW where
  DeleteCase EQ nm x xv cols = Row cols
  DeleteCase GT nm x xv cols = InsertLeast x xv (Delete nm (Row cols))

class    Remove (nm :: Symbol) (row :: ROW) where

  remove                       :: Proxy# nm -> Rcd row -> Rcd (Delete nm row)

instance RemoveCase (CmpSymbol nm x) nm cols =>
         Remove nm (Row (x ::: xv ': cols)) where

  remove nm (Cons x xv rcd)     = removeCase (proxy# @(CmpSymbol nm x)) nm x xv rcd

class    RemoveCase (o :: Ordering) (nm :: Symbol) (cols :: [COL]) where

  removeCase                   :: Proxy# o -> Proxy# nm -> Proxy# x -> xv -> Rcd (Row cols) -> Rcd (DeleteCase o nm x xv cols)

instance RemoveCase EQ nm cols where

  removeCase _eq _nm _x _xv rcd = rcd

instance Remove nm (Row cols) =>
         RemoveCase GT nm cols where

  removeCase _gt  nm  x  xv rcd = cons x xv $ remove nm rcd
