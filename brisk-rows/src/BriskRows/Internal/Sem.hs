{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_HADDOCK not-home #-}

module BriskRows.Internal.Sem (
    (:&:),
    (:*:),
    (:->:),
    CAnd,
    CTop,
    Dict (Dict),
    Fld (Con, App, Nam, Img),
    Sem,
    ) where

import           GHC.Types (Constraint, Type)

type family Sem (fld :: Fld k v t) (nm :: k) (a :: v) :: t
  where
    Sem (Con c)    nm  a = c
    Sem (App f x)  nm  a = (Sem f nm a) (Sem x nm a)
    Sem Nam        nm _a = nm
    Sem Img       _nm  a = a

infixl 9 `App`

data Fld :: Type -> Type -> Type -> Type
  where
    Con :: t -> Fld k v t
    App :: Fld k v (x -> t) -> Fld k v x -> Fld k v t
    Nam :: Fld k v k
    Img :: Fld k v v

infixr 1 :*:
type l :*: r = Con (,) `App` l `App` r

infixr 3 :&:
type l :&: r = Con CAnd `App` l `App` r

infixr 0 :->:
type l :->: r = Con (->) `App` l `App` r

data Dict :: Constraint -> Type
  where
    Dict :: c => Dict c

class    (l, r) => CAnd l r
instance (l, r) => CAnd l r

class    CTop
instance CTop
