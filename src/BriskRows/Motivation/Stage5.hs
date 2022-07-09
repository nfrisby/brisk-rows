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
-- The introduction of 'TE.TypeError' to complete the type families' definitions has improved the type error messages.
--
-- The addition of pervasive 'AssertLikeError' arguments has prevented the use of the library with abstract rows or column names, thereby preventing GHC from inferring illegible types filled with implementation details.

module BriskRows.Motivation.Stage5 (module BriskRows.Motivation.Stage5) where

import           Data.Kind (Type)
import           GHC.Exts (Proxy#, proxy#)
import           GHC.TypeLits (CmpSymbol, Symbol)
import qualified GHC.TypeLits as TE

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

-- | We add an argument of this kind to every type family and class.
--
-- If GHC cannot reduce the user's code's constraints, then it will find a 'TE.TypeError' lingering in the irreduced constraints, and render that for the user.
--
-- This prevents the user from ever seeing a " No instance for " etc message or an inferred type involving our type classes.
-- They are still free to write their own contexts, if they'd like.
--
-- I've consistently placed it as the last argument of the families/classes.
-- This seems to cause GHC to render the error from the innermost application (eg the root type variable instead of the nested applications of row combinators to it).
type AssertLikeError = Type

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

proofInsert :: forall nm a cols ans. ExtendRow nm a (Row cols) => Proxy# nm -> Proxy# a -> Proxy# (Row cols) -> (forall cols'. Insert nm a (Row cols) ~ Row cols' => ans) -> ans
proofInsert _nm _a _row k =
    -- safe by definition of Insert and Extend
    let _ = needConstraint @(ExtendRow nm a (Row cols)) in
    case unsafeCoerce (ProofRow @'[]) :: ProofRow (Insert nm a (Row cols)) of ProofRow -> k
-}

-----

-- | Writing 'TE.TypeError' directly in the signature of eg 'extendConcrete' causes GHC to error with the message when type-checking this module!
type family DelayedTypeError (msg :: TE.ErrorMessage) :: Type where
   DelayedTypeError msg = TE.TypeError msg

type AbstractError (fun :: Symbol) (row :: ROW) = DelayedTypeError (TE.Text "BriskRows." TE.:<>: TE.Text fun TE.:<>: TE.Text " must be applied to a concrete row, but its argument is abstract:" TE.:$$: TE.Text "    " TE.:<>: TE.ShowType row)

type IncomparableError (nm :: Symbol) (x :: Symbol) = DelayedTypeError (TE.Text "BriskRows.* only supports orderable column names, but these two could not be compared:" TE.:$$: TE.Text "        " TE.:<>: TE.ShowType nm TE.:$$: TE.Text "    and " TE.:<>: TE.ShowType x)

-----

type family Lookup (nm :: Symbol) (row :: ROW) :: Type where
  Lookup nm (Row '[]               ) = TE.TypeError (TE.Text "Cannot Lookup absent column: " TE.:<>: TE.ShowType nm)
  Lookup nm (Row (x ::: xv ': cols)) = LookupCase (CmpSymbol nm x) nm x xv cols (IncomparableError nm x)

type family LookupCase (o :: Ordering) (nm :: Symbol) (x :: Symbol) (xv :: Type) (cols :: [COL]) (err :: Type) :: Type where
  LookupCase LT nm x xv cols err = TE.TypeError (TE.Text "Cannot Lookup absent column: " TE.:<>: TE.ShowType nm)
  LookupCase EQ nm x xv cols err = xv
  LookupCase GT nm x xv cols err = Lookup nm (Row cols)

class    Project (nm :: Symbol) (row :: ROW) where

  project                        :: Proxy# nm -> Rcd row -> Lookup nm row

instance ProjectCase (CmpSymbol nm x) nm cols (IncomparableError nm x) =>
         Project nm (Row (x ::: xv ': cols)) where

  project nm (Cons x xv rcd)      = projectCase (proxy# @(CmpSymbol nm x)) (proxy# @(IncomparableError nm x)) nm x xv rcd

class    ProjectCase (o :: Ordering) (nm :: Symbol) (cols :: [COL]) (err :: AssertLikeError) where

  projectCase                    :: Proxy# o -> Proxy# err -> Proxy# nm -> Proxy# x -> xv -> Rcd (Row cols) -> LookupCase o nm x xv cols err

instance ProjectCase EQ nm cols err where

  projectCase _eq _err _nm _x  xv _rcd = xv

instance Project nm (Row cols) =>
         ProjectCase GT nm cols err where

  projectCase _gt _err  nm _x _xv  rcd = project nm rcd

-----

type family InsertRow (nm :: Symbol) (a :: Type) (row :: ROW) (err :: AssertLikeError) :: ROW where
  InsertRow nm a (Row '[])                err = Row '[nm ::: a]
  InsertRow nm a (Row (x ::: xv ': cols)) err = InsertCase (CmpSymbol nm x) nm a x xv cols (IncomparableError nm x)

type family InsertCase (o :: Ordering) (nm :: Symbol) (a :: Type) (x :: Symbol) (xv :: Type) (cols :: [COL]) (err :: AssertLikeError) :: ROW where
  InsertCase LT nm a x xv cols err = Row (nm ::: a ': x ::: xv ': cols)
  InsertCase EQ nm a x xv cols err = TE.TypeError (TE.Text "Cannot InsertRow already-present column: " TE.:<>: TE.ShowType nm)
  InsertCase GT nm a x xv cols err = InsertLeast x xv (InsertRow nm a (Row cols) ())

class    ExtendRow (nm :: Symbol) (row :: ROW) (err :: AssertLikeError) where

  extendRow                           :: Proxy# err -> Proxy# nm -> a -> Rcd row -> Rcd (InsertRow nm a row err)

instance ExtendRow nm (Row '[]) err_ where

  extendRow _err nm a Nil              = Cons nm a Nil

instance ExtendCase (CmpSymbol nm x) nm cols (IncomparableError nm x) =>
         ExtendRow nm (Row (x ::: xv ': cols)) err_ where

  extendRow _err nm a (Cons x xv rcd)  =
       extendCase
          (proxy# @(CmpSymbol nm x))
          (proxy# @(IncomparableError nm x))
          nm a x xv rcd

class    ExtendCase (o :: Ordering) (nm :: Symbol) (cols :: [COL]) (err :: AssertLikeError) where

  extendCase                       :: Proxy# o -> Proxy# err -> Proxy# nm -> a -> Proxy# x -> xv -> Rcd (Row cols) -> Rcd (InsertCase o nm a x xv cols err)

instance ExtendCase LT nm cols err where

  extendCase _eq _err nm a x xv rcd = Cons nm a $ Cons x xv rcd

instance ExtendRow nm (Row cols) () =>
         ExtendCase GT nm cols err where

  extendCase _gt _err nm a x xv rcd = cons x xv $ extendRow (proxy# @()) nm a rcd

-----

type Insert nm a row = InsertRow nm a row (AbstractError "Insert" row)

extend ::
 forall nm a row.
    ExtendRow nm row (AbstractError "extendConcrete" row)
 => Proxy# nm
 -> a
 -> Rcd row
 -> Rcd (InsertRow nm a row (AbstractError "extendConcrete" row))
extend = extendRow (proxy# @(AbstractError "extendConcrete" row))

-----

type family DeleteRow (nm :: Symbol) (row :: ROW) (err :: AssertLikeError) :: ROW where
  DeleteRow nm (Row '[]               ) err = TE.TypeError (TE.Text "Cannot Delete already-absent column: " TE.:<>: TE.ShowType nm)
  DeleteRow nm (Row (x ::: xv ': cols)) err = DeleteCase (CmpSymbol nm x) nm x xv cols (IncomparableError nm x)

type family DeleteCase (o :: Ordering) (nm :: Symbol) (x :: Symbol) (xv :: Type) (cols :: [COL]) (err :: AssertLikeError) :: ROW where
  DeleteCase LT nm x xv cols err = TE.TypeError (TE.Text "Cannot Delete already-absent column: " TE.:<>: TE.ShowType nm)
  DeleteCase EQ nm x xv cols err = Row cols
  DeleteCase GT nm x xv cols err = InsertLeast x xv (DeleteRow nm (Row cols) ())

class    RemoveRow (nm :: Symbol) (row :: ROW) (err :: AssertLikeError) where

  removeRow                         :: Proxy# err -> Proxy# nm -> Rcd row -> Rcd (DeleteRow nm row err)

instance RemoveCase (CmpSymbol nm x) nm cols (IncomparableError nm x) =>
         RemoveRow nm (Row (x ::: xv ': cols)) err where

  removeRow _err nm (Cons x xv rcd)  =
      removeCase
        (proxy# @(CmpSymbol nm x))
        (proxy# @(IncomparableError nm x))
        nm x xv rcd

class    RemoveCase (o :: Ordering) (nm :: Symbol) (cols :: [COL]) (err :: AssertLikeError) where

  removeCase                        :: Proxy# o -> Proxy# err -> Proxy# nm -> Proxy# x -> xv -> Rcd (Row cols) -> Rcd (DeleteCase o nm x xv cols err)

instance RemoveCase EQ nm cols err where

  removeCase _eq _err _nm _x _xv rcd = rcd

instance RemoveRow nm (Row cols) () =>
         RemoveCase GT nm cols err where

  removeCase _gt _err  nm  x  xv rcd = cons x xv $ removeRow (proxy# @()) nm rcd

-----

type Delete nm row = DeleteRow nm row (AbstractError "Delete" row)

remove ::
 forall nm row.
    RemoveRow nm row (AbstractError "removeConcrete" row)
 => Proxy# nm
 -> Rcd row
 -> Rcd (DeleteRow nm row (AbstractError "removeConcrete" row))
remove = removeRow (proxy# @(AbstractError "removeConcrete" row))
