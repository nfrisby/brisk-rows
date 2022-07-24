{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-redundant-constraints #-}

{-# OPTIONS_HADDOCK -not-home #-}

module BriskRows.Internal (
    -- * Row types
    COL ((:=)),
    ROW (Row#),
    Emp,
    Extend, (:&),
    Select,
    -- * Row type constraints
    KnownLT (knownLT#),
    Lacks,
    Absent,
    ) where

import           Data.Kind (Type)
import           GHC.Exts (Proxy#, proxy#)
import           GHC.Prim (Int#, (+#))
import           GHC.TypeLits (CmpSymbol, Symbol)
import           GHC.TypeLits (ErrorMessage (Text, (:<>:), (:$$:), ShowType), TypeError)

-----

-- | A distinguished data kind for the 'Assert'-like argument
data Err = NoErr

-- This indirection is enough to disarm the errors while GHC compiles this module
type family TypeErr (err :: ErrorMessage) :: Err where TypeErr err = TypeError err

type Incomparable (nm :: Symbol) (x :: Symbol) =
    Text "These names are incomparable! " :$$: (Text "        " :<>: ShowType nm) :$$: (Text "    and " :<>: ShowType x)

type NotFound (nm :: Symbol) = Text "This column is not in the row! " :<>: ShowType nm

type NotAbsent (nm :: Symbol) = Text "This column is not absent in the row! " :<>: ShowType nm

type AbstractROW (rho :: ROW) = Text "This row is not concrete! " :<>: ShowType rho

type AbstractCOL (col :: COL) = Text "This column is not concrete! " :<>: ShowType col

-----

data COL = Symbol := Type

-- | The kind of a row type
data ROW =
    -- | INVARIANT Non-descending, according to 'CmpSymbol'
    --
    -- Of multiple columns with the same name, the leftmost is the most recently added.
    -- See 'Lacks'.
    Row# [COL]

-- | The empty row
type Emp = Row# '[]

type family Cons
    (  nm :: Symbol )
    (   a :: Type   )
    ( rho :: ROW    )
          :: ROW
  where
    Cons nm a (Row# cols) = Row# (nm := a ': cols)

-----
{-
-- | How many columns in the row are less than @nm@ according to 'CmpSymbol'
type family CountLT
    ( nm  :: Symbol )
    ( rho :: ROW    )
          :: N
  where
    CountLT nm (Row# '[]             ) = Z
    CountLT nm (Row# (x := b ': cols)) = CountLT_Ordering (Incomparable nm x) (CmpSymbol nm x) nm cols

type family CountLT_Ordering
    (  err :: Err      )
    (    o :: Ordering )
    (   nm :: Symbol   )
    ( cols :: [COL]    )
           :: N
  where
    CountLT_Ordering err LT nm cols =    CountLT nm (Row# cols)
    CountLT_Ordering err EQ nm cols =    CountLT nm (Row# cols)
    CountLT_Ordering err GT nm cols = S (CountLT nm (Row# cols))

data N = Z | S N

-- | The demoted natural
class KnownN (n :: N) where knownN# :: Proxy# n -> I#

instance             KnownN  Z    where knownN# = \_n -> 0#
instance KnownN n => KnownN (S n) where knownN# = \_n -> 1# +# knownN# (proxy# :: Proxy# n)
-}

-- | Key data enabling methods on records, variants, etc
--
-- See 'Lacks'.
class KnownLT (nm :: Symbol) (rho :: ROW)
  where
    -- | The number of lesser columns in the row, according to 'CmpSymbol'
    knownLT# :: Proxy# nm -> Proxy# rho -> Int#

instance KnownLT nm (Row# '[])
  where
    knownLT# = \_nm _rho -> 0#

instance
    KnownLT_Ordering (TypeErr (Incomparable nm x)) (CmpSymbol nm x) nm cols
 => KnownLT nm (Row# (x := b ': cols))
  where
    knownLT# = \nm _rho ->
        knownLT_Ordering
          (proxy# :: Proxy# (TypeErr (Incomparable nm x)))
          (proxy# :: Proxy# (CmpSymbol nm x))
          nm
          (proxy# :: Proxy# cols)

class
    KnownLT_Ordering
      (  err :: Err      )
      (    o :: Ordering )
      (   nm :: Symbol   )
      ( cols :: [COL]    )
  where
    knownLT_Ordering :: Proxy# err -> Proxy# o -> Proxy# nm -> Proxy# cols -> Int#

instance KnownLT_Ordering err LT nm cols
  where
    knownLT_Ordering = \_err _o _nm _cols -> 0#

instance KnownLT_Ordering err EQ nm cols
  where
    knownLT_Ordering = \_err _o _nm _cols -> 0#

instance
    KnownLT nm (Row# cols)
 => KnownLT_Ordering err GT nm cols
  where
    knownLT_Ordering = \_err _o nm _cols -> 1# +# knownLT# nm (proxy# :: Proxy# (Row# cols))

-----

-- | The traditional row polymorphism constraint
--
-- 'KnownLT' alone, without 'Absent', is sufficient for Leijen's [Extensible
-- records with scoped
-- labels](https://www.microsoft.com/en-us/research/publication/extensible-records-with-scoped-labels/).
--
-- To ensure every column name is unique in every row, use 'Lacks'/'Absent'
-- ubiquitously.
type Lacks nm rho = (Absent nm rho, KnownLT nm rho)

-- | There is no such column in the row
--
-- See 'Lacks'.
class Absent (nm :: Symbol) (rho :: ROW)

instance Absent nm (Row# '[])

instance
    Absent_Ordering (TypeErr (Incomparable nm x)) (CmpSymbol nm x) nm cols
 => Absent nm (Row# (x := b ': cols))

class Absent_Ordering (err :: Err) (o :: Ordering) (nm :: Symbol) (cols :: [COL])

instance Absent_Ordering err LT nm cols

instance TypeError (NotAbsent nm) => Absent_Ordering err EQ nm cols

instance Absent nm (Row# cols) => Absent_Ordering err GT nm cols

-----

type family Extend_Col (err :: Err) (col :: COL) (rho :: ROW) :: ROW
  where
    Extend_Col err (nm := a) rho = Extend_Row# nm a rho (TypeErr (AbstractROW rho))

-- We intentionally put the @err@ argument after the @rho@ argument, so that GHC renders the deeper error
type family Extend_Row#
    (  nm :: Symbol )
    (   a :: Type   )
    ( rho :: ROW    )
    ( err :: Err    )
          :: ROW
  where
    Extend_Row# nm a (Row# '[]             ) err = Row# '[nm := a]
    Extend_Row# nm a (Row# (x := b ': cols)) err = Extend_Ordering (TypeErr (Incomparable nm x)) (CmpSymbol nm x) nm a x b cols

type family Extend_Ordering
    (  err :: Err      )
    (    o :: Ordering )
    (   nm :: Symbol   )
    (    a :: Type     )
    (    x :: Symbol   )
    (    b :: Type     )
    ( cols :: [COL]    )
           :: ROW
  where
    Extend_Ordering err LT nm a x b cols = Cons nm a (Cons x b (Row# cols))
    Extend_Ordering err EQ nm a x b cols = Cons nm a (Cons x b (Row# cols))
    Extend_Ordering err GT nm a x b cols = Cons x b (Extend_Row# nm a (Row# cols) NoErr)

-----

-- Restriction is essentially an implementation detail of the typechecker plugin, not exposed to the user

type family Restrict (nm :: Symbol) (rho :: ROW) :: ROW
  where
    Restrict nm (Row# '[]             ) = TypeError (NotFound nm)
    Restrict nm (Row# (x := b ': cols)) = Restrict_Ordering (TypeErr (Incomparable nm x)) (CmpSymbol nm x) nm x b cols

type family Restrict_Ordering
    (  err :: Err      )
    (    o :: Ordering )
    (   nm :: Symbol   )
    (    x :: Symbol   )
    (    b :: Type     )
    ( cols :: [COL]    )
           :: ROW
  where
    Restrict_Ordering err LT nm x b cols = TypeError (NotFound nm)
    Restrict_Ordering err EQ nm x b cols = Row# cols
    Restrict_Ordering err GT nm x b cols = Cons x b (Restrict nm (Row# cols))

-----

-- | The type of this column in the row
--
-- If this multiple columns have the same name, it selects the type of the
-- leftmost column. See 'Row#'.
type family Select (nm :: Symbol) (rho :: ROW) :: Type
  where
    Select nm (Row# '[]             ) = TypeError (NotFound nm)
    Select nm (Row# (x := b ': cols)) = Select_Ordering (TypeErr (Incomparable nm x)) (CmpSymbol nm x) nm x b cols

type family Select_Ordering
    (  err :: Err      )
    (    o :: Ordering )
    (   nm :: Symbol   )
    (    x :: Symbol   )
    (    b :: Type     )
    ( cols :: [COL]    )
           :: Type
  where
    Select_Ordering err LT nm x b cols = TypeError (NotFound nm)
    Select_Ordering err EQ nm x b cols = b
    Select_Ordering err GT nm x b cols = Select nm (Row# cols)

-----

-- | Extend the row by inserting the given column
type Extend nm a rho = Extend_Row# nm a rho (TypeErr (AbstractROW rho))

infixl 5 :&

-- | Operator alias of 'Extend'
type row :& col = Extend_Col (TypeErr (AbstractCOL col)) col row
