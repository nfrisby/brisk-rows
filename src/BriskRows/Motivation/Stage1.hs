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

-- | The key problem with this module is that it's trivial for the user to
-- accidentally violate the 'ROW' invariant.
--
-- See "BriskRows.Motivation.Stage2".

module BriskRows.Motivation.Stage1 (module BriskRows.Motivation.Stage1) where

import           Data.Kind (Type)
import           GHC.Exts (Proxy#, proxy#)
import           GHC.TypeLits (CmpSymbol, Symbol)

-----

infix 7 :::
data COL = Symbol ::: Type

-- | INVARIANT the 'Col'umn names are strictly ascending wrt 'CmpSymbol'
type ROW = [COL]

type Nil = '[] :: ROW

-----

data Rcd :: ROW -> Type where
  -- | REQUIREMENT @nm@ is less than the first column in @cols@ according to 'CmpSymbol'
  Cons :: Proxy# nm -> a -> Rcd row -> Rcd (nm ::: a ': row)
  Nil  ::                              Rcd '[]

emp :: Rcd Nil
emp = Nil

-----

type family Lookup (nm :: Symbol) (row :: ROW) :: Type where
  Lookup nm (x ::: xv ': row) = LookupCase (CmpSymbol nm x) nm x xv row

type family LookupCase (o :: Ordering) (nm :: Symbol) (x :: Symbol) (xv :: Type) (row :: ROW) :: Type where
  LookupCase EQ nm x xv row = xv
  LookupCase GT nm x xv row = Lookup nm row

class         Project (nm :: Symbol) (row :: ROW) where

  project                        :: Proxy# nm -> Rcd row -> Lookup nm row

instance (    ProjectCase (CmpSymbol nm x) nm row
         ) => Project nm (x ::: xv ': row) where

  project nm (Cons x xv rcd)      = projectCase (proxy# @(CmpSymbol nm x)) nm x xv rcd

class         ProjectCase (o :: Ordering) (nm :: Symbol) (row :: ROW) where

  projectCase                    :: Proxy# o -> Proxy# nm -> Proxy# x -> xv -> Rcd row -> LookupCase o nm x xv row

instance      ProjectCase EQ nm row where

  projectCase _eq _nm _x  xv _rcd = xv

instance (    Project nm row
         ) => ProjectCase GT nm row where

  projectCase _gt  nm _x _xv  rcd = project nm rcd

-----

type family Insert (nm :: Symbol) (a :: Type) (row :: ROW) :: ROW where
  Insert nm a '[]               = '[nm ::: a]
  Insert nm a (x ::: xv ': row) = InsertCase (CmpSymbol nm x) nm a x xv row

type family InsertCase (o :: Ordering) (nm :: Symbol) (a :: Type) (x :: Symbol) (xv :: Type) (row :: ROW) :: ROW where
  InsertCase LT nm a x xv row = nm ::: a ': x ::: xv ': row
  InsertCase GT nm a x xv row = x ::: xv ': Insert nm a row

class         Extend (nm :: Symbol) (row :: ROW) where

  extend                      :: Proxy# nm -> a -> Rcd row -> Rcd (Insert nm a row)

instance      Extend nm '[] where

  extend nm a Nil              = Cons nm a Nil

instance (    ExtendCase (CmpSymbol nm x) nm row
         ) => Extend nm (x ::: xv ': row) where

  extend nm a (Cons x xv rcd)  = extendCase (proxy# @(CmpSymbol nm x)) nm a x xv rcd

class         ExtendCase (o :: Ordering) (nm :: Symbol) (row :: ROW) where

  extendCase                  :: Proxy# o -> Proxy# nm -> a -> Proxy# x -> xv -> Rcd row -> Rcd (InsertCase o nm a x xv row)

instance      ExtendCase LT nm row where

  extendCase _eq nm a x xv rcd = Cons nm a $ Cons x xv rcd

instance (    Extend nm row
         ) => ExtendCase GT nm row where

  extendCase _gt nm a x xv rcd = Cons x xv $ extend nm a rcd

-----

type family Delete (nm :: Symbol) (row :: ROW) :: ROW where
  Delete nm (x ::: xv ': row) = DeleteCase (CmpSymbol nm x) nm x xv row

type family DeleteCase (o :: Ordering) (nm :: Symbol) (x :: Symbol) (xv :: Type) (row :: ROW) :: ROW where
  DeleteCase EQ nm x xv row = row
  DeleteCase GT nm x xv row = x ::: xv ': Delete nm row

class         Remove (nm :: Symbol) (row :: ROW) where

  remove                       :: Proxy# nm -> Rcd row -> Rcd (Delete nm row)

instance (    RemoveCase (CmpSymbol nm x) nm row
         ) => Remove nm (x ::: xv ': row) where

  remove nm (Cons x xv rcd)     = removeCase (proxy# @(CmpSymbol nm x)) nm x xv rcd

class         RemoveCase (o :: Ordering) (nm :: Symbol) (row :: ROW) where

  removeCase                   :: Proxy# o -> Proxy# nm -> Proxy# x -> xv -> Rcd row -> Rcd (DeleteCase o nm x xv row)

instance      RemoveCase EQ nm row where

  removeCase _eq _nm _x _xv rcd = rcd

instance (    Remove nm row
         ) => RemoveCase GT nm row where

  removeCase _gt  nm  x  xv rcd = Cons x xv $ remove nm rcd
