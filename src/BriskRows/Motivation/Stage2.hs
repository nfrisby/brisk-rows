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
-- The key problem with this module is the noisy 'KnownRow' constraint.
--
-- See "BriskRows.Motivation.Stage3".

module BriskRows.Motivation.Stage2 (module BriskRows.Motivation.Stage2) where

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

data Seq :: [COL] -> Type where
  Cons :: Proxy# nm -> a -> Seq cols -> Seq (nm ::: a ': cols)
  Nil  ::                               Seq '[]

newtype Rcd (row :: ROW) = Rcd (Seq (ForgetRow row))

fromSorted :: Seq cols -> Rcd (Row cols)
fromSorted = Rcd

type family ForgetRow (row :: ROW) :: [COL] where
  ForgetRow (Row cols) = cols

emp :: Rcd Nil
emp = Rcd Nil

-----

-- | We carefully define 'InsertLeast' so that it reduces to an application of 'Row' only if its argument did.
--
-- In other words, 'InsertLeast' is " strict ".
type family InsertLeast (x :: Symbol) (xv :: Type) (row :: ROW) :: ROW where
  InsertLeast x xv (Row cols) = Row (x ::: xv ': cols)

class    KnownRow (row :: ROW) where

  extendLeast              :: Proxy# nm -> a -> Rcd row -> Rcd (InsertLeast nm a row)

instance KnownRow (Row cols) where

  extendLeast nm a (Rcd sq) = Rcd (Cons nm a sq)

-----

type family Lookup (nm :: Symbol) (row :: ROW) :: Type where
  Lookup nm (Row (x ::: xv ': cols)) = LookupCase (CmpSymbol nm x) nm x xv cols

type family LookupCase (o :: Ordering) (nm :: Symbol) (x :: Symbol) (xv :: Type) (cols :: [COL]) :: Type where
  LookupCase EQ nm x xv cols = xv
  LookupCase GT nm x xv cols = Lookup nm (Row cols)

class         Project (nm :: Symbol) (row :: ROW) where

  project                        :: Proxy# nm -> Rcd row -> Lookup nm row

instance (    ProjectCase (CmpSymbol nm x) nm cols
         ) => Project nm (Row (x ::: xv ': cols)) where

  project nm (Rcd (Cons x xv sq)) = projectCase (proxy# @(CmpSymbol nm x)) nm x xv sq

class         ProjectCase (o :: Ordering) (nm :: Symbol) (cols :: [COL]) where

  projectCase                    :: Proxy# o -> Proxy# nm -> Proxy# x -> xv -> Seq cols -> LookupCase o nm x xv cols

instance      ProjectCase EQ nm cols where

  projectCase _eq _nm _x  xv _sq  = xv

instance (    Project nm (Row cols)
         ) => ProjectCase GT nm cols where

  projectCase _gt  nm _x _xv  sq  = project nm (fromSorted sq)

-----

type family Insert (nm :: Symbol) (a :: Type) (row :: ROW) :: ROW where
  Insert nm a (Row '[])                = Row '[nm ::: a]
  Insert nm a (Row (x ::: xv ': cols)) = InsertCase (CmpSymbol nm x) nm a x xv cols

type family InsertCase (o :: Ordering) (nm :: Symbol) (a :: Type) (x :: Symbol) (xv :: Type) (cols :: [COL]) :: ROW where
  InsertCase LT nm a x xv cols = Row (nm ::: a ': x ::: xv ': cols)
  InsertCase GT nm a x xv cols = InsertLeast x xv (Insert nm a (Row cols))

class         Extend (nm :: Symbol) (a :: Type) (row :: ROW) where

  extend                          :: Proxy# nm -> a -> Rcd row -> Rcd (Insert nm a row)

instance      Extend nm a (Row '[]) where

  extend nm a (Rcd Nil           ) = Rcd (Cons nm a Nil)

instance (    ExtendCase (CmpSymbol nm x) nm a cols
         ) => Extend nm a (Row (x ::: xv ': cols)) where

  extend nm a (Rcd (Cons x xv sq)) = extendCase (proxy# @(CmpSymbol nm x)) nm a x xv sq

class         ExtendCase (o :: Ordering) (nm :: Symbol) (a :: Type) (cols :: [COL]) where

  extendCase                      :: Proxy# o -> Proxy# nm -> a -> Proxy# x -> xv -> Seq cols -> Rcd (InsertCase o nm a x xv cols)

instance      ExtendCase LT nm a cols where

  extendCase _eq nm a x xv sq      = Rcd $ Cons nm a $ Cons x xv sq

instance (    Extend nm a (Row cols)
         ,    KnownRow (Insert nm a (Row cols))
         ) => ExtendCase GT nm a cols where

  extendCase _gt nm a x xv sq      = extendLeast x xv $ extend nm a (fromSorted sq)

-----

type family Delete (nm :: Symbol) (row :: ROW) :: ROW where
  Delete nm (Row (x ::: xv ': cols)) = DeleteCase (CmpSymbol nm x) nm x xv cols

type family DeleteCase (o :: Ordering) (nm :: Symbol) (x :: Symbol) (xv :: Type) (cols :: [COL]) :: ROW where
  DeleteCase EQ nm x xv cols = Row cols
  DeleteCase GT nm x xv cols = InsertLeast x xv (Delete nm (Row cols))

class    Remove (nm :: Symbol) (row :: ROW) where

  remove                        :: Proxy# nm -> Rcd row -> Rcd (Delete nm row)

instance ( RemoveCase (CmpSymbol nm x) nm cols
         ) => Remove nm (Row (x ::: xv ': cols)) where

  remove nm (Rcd (Cons x xv sq)) = removeCase (proxy# @(CmpSymbol nm x)) nm x xv sq

class    RemoveCase (o :: Ordering) (nm :: Symbol) (cols :: [COL]) where

  removeCase                    :: Proxy# o -> Proxy# nm -> Proxy# x -> xv -> Seq cols -> Rcd (DeleteCase o nm x xv cols)

instance RemoveCase EQ nm cols where

  removeCase _eq _nm _x _xv sq   = fromSorted sq

instance ( Remove nm (Row cols)
         , KnownRow (Delete nm (Row cols))
         ) =>
         RemoveCase GT nm cols where

  removeCase _gt  nm  x  xv sq   = extendLeast x xv $ remove nm (fromSorted sq)
