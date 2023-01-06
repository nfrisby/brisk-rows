{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_HADDOCK not-home #-}

-- | The structure of fields in "BriskRows.RVtf".
--
-- This is an alternative to "BriskRows.Fields". The principal difference is
-- that the 'Sem' family prevents the field structure from being preserved in
-- the values themselves.
module BriskRows.Sem (
    -- * Structure
    Fld (Con, App, Nam, Img),
    Sem,
    -- * Constraints
    CAnd,
    CTop,
    Dict (Dict),
    -- * Abbreviations
    (:&&:),
    (:*:),
    (:->:),
    ) where

import           GHC.Types (Constraint, Type)

-----

-- | Interpet a 'Fld' as an actual type, given the column name and image
type family Sem (fld :: Fld k v t) (nm :: k) (a :: v) :: t
  where
    Sem (Con c)    nm  a = c
    Sem (App f x)  nm  a = (Sem f nm a) (Sem x nm a)
    Sem Nam        nm _a = nm
    Sem Img       _nm  a = a

-----

infixl 9 `App`

-- | An expression for the common structure of a record's fields
data Fld :: Type -> Type -> Type -> Type
  where
    -- | A constant type, indepenent of the column
    Con :: t -> Fld k v t
    -- | Apply one 'Fld' to another
    App :: Fld k v (x -> t) -> Fld k v x -> Fld k v t
    -- | The type of the name in this column
    Nam :: Fld k v k
    -- | The type of the image in this column
    Img :: Fld k v v

-----

infixr 1 :*:
type l :*: r = Con (,) `App` l `App` r

infixr 3 :&&:
type l :&&: r = Con CAnd `App` l `App` r

infixr 0 :->:
type l :->: r = Con (->) `App` l `App` r

-----

-- | TODO use constraints library?
data Dict :: Constraint -> Type
  where
    Dict :: c => Dict c

-- | Conjuction
class    (l, r) => CAnd l r
instance (l, r) => CAnd l r

-- | True
class    CTop
instance CTop
