{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-redundant-constraints #-}

{-# OPTIONS_HADDOCK not-home #-}

-- | An internal module; do not rely on this interface.
--
-- See "BriskRows" instead.
module BriskRows.Internal (
    -- * Rows
    -- ** Kinds
    COL ((:=)),
    ROW (Emp),
    -- ** Constructors
    (:&),
    -- ** Queries
    Find,
    FindResult (Found, NoSuchColumn),
    Select,
    -- ** Constraints
    Absent,
    AllCols (anyDicts#),
    KnownLT (knownLT#),
    KnownLen (knownLen#),
    Lacks,
    -- * Names
    CmpName,
    Lexico,
    ShowName (docName),
    docName#,
    -- * Auxiliary
    Extend_Col,
    Err,
    AllColsHelp,
    NoErr,
    TypeErr,
    UnfoldExtOp,
    extAllCols,
    extKnownLT,
    -- * blarg
    AbstractROW,
    AbstractCOL,
    Extend_Row#,
    Restrict,
    Cons,
    NotAbsent,
    NotFound,
    Incomparable,
    ) where

import           Data.Kind (Constraint, Type)
import           Data.List.NonEmpty (NonEmpty ((:|)))
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Sequence as Seq
import qualified Data.Type.Ord
import           GHC.Exts (Any, Proxy#, proxy#)
import           GHC.Prim (Int#, (+#))
import           GHC.Tuple (Solo (Solo))
import           GHC.Types (Int (I#))
import           GHC.TypeLits (ErrorMessage (Text, (:<>:), (:$$:), ShowType), TypeError)
import           GHC.TypeLits (Natural, Symbol)
import qualified GHC.TypeLits as TypeLits
import           Unsafe.Coerce (unsafeCoerce)

import qualified BriskRows.Internal.PP as PP
import qualified BriskRows.Sem as Sem

-----

-- | A distinguished data kind for the 'GHC.TypeError.Assert'-like argument
--
-- TODO link to Fail-safe Arguments post on Tweag blog
data Err

type family NoErr :: Err where {}

-- This indirection is enough to disarm the errors while GHC compiles this module
type family TypeErr (err :: ErrorMessage) :: Err where TypeErr err = TypeError err

-----
----- specific error messages for code in this module
-----

type Incomparable (nm :: k) (x :: k) =
    Text "These names are incomparable! " :$$: (Text "        " :<>: ShowType nm) :$$: (Text "    and " :<>: ShowType x)

type NotFound (nm :: k) = Text "This column is not in the row! " :<>: ShowType nm

type NotAbsent (nm :: k) = Text "This column is not absent in the row! " :<>: ShowType nm

type AbstractROW (rho :: ROW k v) = Text "Equality constraints with row type variables are disallowed! " :<>: ShowType rho

type AbstractCOL (col :: COL k v) = Text "This column is not concrete! " :<>: ShowType col

-----

infix 7 :=

-- | A column in a row type
--
-- See 'ROW'.
data COL k v = k := v

-- | The order of column names
--
-- Consider this order to be deterministic but arbitrary. It determines merely
-- the order of columns within a row value. In general, you should write code
-- (eg codecs) assuming this order may change over time.
--
-- If you define your own name kinds, you'll need to instantiate this family.
-- Follow the pattern in the 'Either' instance for sums and the tuple instances
-- for products. See 'Lexico'. __Do not__ declarive reflexive instances; let
-- the plugin handle those.
--
-- The 'BriskRows.Plugin.plugin' adds reflexivity to this family. Relying on
-- the plugin is preferable to adding a top-level refl case to 'CmpName'
-- because such a case would eg prevent the recursive 'Just' case from
-- simplifying @Just (l :: ()) ``CmpName`` Just (r :: ())@. A plugin is
-- necessary and sufficient specifically because these are confluent paths to
-- 'EQ'.
type family CmpName (l :: k) (r :: k) :: Ordering

-- | The kind of a row type
data ROW (k :: Type) (v :: Type) =
  -- | The empty row
  Emp
{-
    -- | INVARIANT Non-descending, according to 'CmpName'
    --
    -- Of multiple columns with the same name, the outermost is the most
    -- recently added. See 'Lacks'.
    Row# [COL k v]
-}

type family Cons
    (  nm :: k       )
    (   a :: v       )
    ( rho :: ROW k v )
          :: ROW k v
  where
    {}
--    Cons nm a (Row# cols) = Row# (nm := a ': cols)

class ShowName (nm :: k) where
    docName :: proxy nm -> PP.Doc

docName# :: forall {nm}. ShowName nm => Proxy# nm -> PP.Doc
docName# _nm = docName (Proxy @nm)

-----

infixl `Lexico`

-- | Lexicographic ordering
--
-- Use this when defining new instances of 'CmpName' for product types.
type family Lexico (l :: Ordering) (r :: Ordering) :: Ordering
  where
    Lexico LT _ = LT
    Lexico EQ r = r
    Lexico GT _ = GT

-----

type instance CmpName @Char l r = Data.Type.Ord.Compare l r
instance TypeLits.KnownChar c => ShowName (c :: Char) where docName c = PP.docShowS $ shows $ TypeLits.charVal c

type instance CmpName @Natural l r = Data.Type.Ord.Compare l r
instance TypeLits.KnownNat n => ShowName (n :: Natural) where docName n = PP.docShowS $ shows $ TypeLits.natVal n

type instance CmpName @Symbol l r = Data.Type.Ord.Compare l r
instance TypeLits.KnownSymbol s => ShowName (s :: Symbol) where docName s = PP.docShowS $ shows $ TypeLits.symbolVal s

type instance CmpName @Bool l r = CmpBool l r
type family CmpBool (l :: Bool) (r :: Bool) :: Ordering
  where
    CmpBool False _     = LT
    CmpBool _     False = GT
instance ShowName True  where docName _prx = PP.docShowS $ shows True
instance ShowName False where docName _prx = PP.docShowS $ shows False

type instance CmpName @Ordering l r = CmpOrdering l r
type family CmpOrdering (l :: Ordering) (r :: Ordering) :: Ordering
  where
    CmpOrdering LT _  = LT
    CmpOrdering _  LT = GT
    CmpOrdering EQ _  = LT
    CmpOrdering _  EQ = GT
    CmpOrdering _  _  = GT
instance ShowName LT where docName _prx = PP.docShowS $ shows LT
instance ShowName EQ where docName _prx = PP.docShowS $ shows EQ
instance ShowName GT where docName _prx = PP.docShowS $ shows GT

type instance CmpName @(Maybe k) l r = CmpMaybe l r
type family CmpMaybe (l :: Maybe k) (r :: Maybe k) :: Ordering
  where
    CmpMaybe Nothing  _        = LT
    CmpMaybe _        Nothing  = GT
    CmpMaybe (Just l) (Just r) = CmpName l r
instance ShowName Nothing where docName _prx = PP.docString "Nothing"
instance ShowName a => ShowName (Just a) where docName _prx = PP.docString "Just" `PP.docApp` docName (Proxy @a)

type instance CmpName @(Either k0 k1) l r = CmpEither l r
type family CmpEither (l :: Either k0 k1) (r :: Either k0 k1) :: Ordering
  where
    CmpEither (Left  l) (Left  r) = CmpName l r
    CmpEither (Left  _) _         = LT
    CmpEither _         (Left  _) = GT
    CmpEither (Right l) (Right r) = CmpName l r
instance ShowName a => ShowName (Left  a) where docName _prx = PP.docString "Left"  `PP.docApp` docName (Proxy @a)
instance ShowName a => ShowName (Right a) where docName _prx = PP.docString "Right" `PP.docApp` docName (Proxy @a)

type instance CmpName @[k] l r = CmpList l r
type family CmpList (l :: [k]) (r :: [k]) :: Ordering
  where
    CmpList '[]       _         = LT
    CmpList _         '[]       = GT
    CmpList (l ': ls) (r ': rs) = CmpName l r `Lexico` CmpName ls rs
instance ShowNameList as => ShowName as where
    docName prx = case docNameList prx of
        []   -> PP.docString "'[]"
        x:xs -> PP.docList (if "'" == take 1 (show x) then "'[ " else "'[") ", " "]" (x:xs)
class                                     ShowNameList (as :: [k]) where docNameList :: proxy as -> [PP.Doc]
instance                                  ShowNameList '[]         where docNameList _prx = []
instance (ShowName a, ShowNameList as) => ShowNameList (a ': as)   where docNameList _prx = docName (Proxy @a) : docNameList (Proxy @as)

type instance CmpName @(NonEmpty k) (l :| ls) (r :| rs) = CmpName l r `Lexico` CmpName ls rs
instance (ShowName a, ShowName as) => ShowName (a :| as) where docName _prx = PP.docBop " :| " PP.RightAssoc 5 (docName (Proxy @a)) (docName (Proxy @as))

type instance CmpName @() l r = EQ
instance ShowName ('() :: ()) where docName _prx = PP.docString "'()"

type instance CmpName @(Proxy k) l r = EQ
instance ShowName 'Proxy where docName _prx = PP.docString "Proxy"

type instance CmpName @(Solo k) ('Solo l) ('Solo r) = CmpName l r
instance ShowName a => ShowName ('Solo a) where docName _prx = PP.docString "Solo" `PP.docApp` docName (Proxy @a)

type instance CmpName @(k0, k1) '(l0, l1) '(r0, r1) = CmpName l0 r0 `Lexico` CmpName l1 r1
instance (ShowName a, ShowName b) => ShowName '(a, b) where docName _prx = PP.docList "'(" ", " ")" [docName (Proxy @a), docName (Proxy @b)]

type instance CmpName @(k0, k1, k2) '(l0, l1, l2) '(r0, r1, r2) = CmpName l0 r0 `Lexico` CmpName l1 r1 `Lexico` CmpName l2 r2
instance (ShowName a, ShowName b, ShowName c) => ShowName '(a, b, c) where docName _prx = PP.docList "'(" ", " ")" [docName (Proxy @a), docName (Proxy @b), docName (Proxy @c)]

type instance CmpName @(k0, k1, k2, k3) '(l0, l1, l2, l3) '(r0, r1, r2, r3) = CmpName l0 r0 `Lexico` CmpName l1 r1 `Lexico` CmpName l2 r2 `Lexico` CmpName l3 r3
instance (ShowName a, ShowName b, ShowName c, ShowName d) => ShowName '(a, b, c, d) where docName _prx = PP.docList "'(" ", " ")" [docName (Proxy @a), docName (Proxy @b), docName (Proxy @c), docName (Proxy @d)]

type instance CmpName @(k0, k1, k2, k3, k4) '(l0, l1, l2, l3, l4) '(r0, r1, r2, r3, r4) = CmpName l0 r0 `Lexico` CmpName l1 r1 `Lexico` CmpName l2 r2 `Lexico` CmpName l3 r3 `Lexico` CmpName l4 r4
instance (ShowName a, ShowName b, ShowName c, ShowName d, ShowName e) => ShowName '(a, b, c, d, e) where docName _prx = PP.docList "'(" ", " ")" [docName (Proxy @a), docName (Proxy @b), docName (Proxy @c), docName (Proxy @d), docName (Proxy @e)]

type instance CmpName @(k0, k1, k2, k3, k4, k5) '(l0, l1, l2, l3, l4, l5) '(r0, r1, r2, r3, r4, r5) = CmpName l0 r0 `Lexico` CmpName l1 r1 `Lexico` CmpName l2 r2 `Lexico` CmpName l3 r3 `Lexico` CmpName l4 r4 `Lexico` CmpName l5 r5
instance (ShowName a, ShowName b, ShowName c, ShowName d, ShowName e, ShowName f) => ShowName '(a, b, c, d, e, f) where docName _prx = PP.docList "'(" ", " ")" [docName (Proxy @a), docName (Proxy @b), docName (Proxy @c), docName (Proxy @d), docName (Proxy @e), docName (Proxy @f)]

type instance CmpName @(k0, k1, k2, k3, k4, k5, k6) '(l0, l1, l2, l3, l4, l5, l6) '(r0, r1, r2, r3, r4, r5, r6) = CmpName l0 r0 `Lexico` CmpName l1 r1 `Lexico` CmpName l2 r2 `Lexico` CmpName l3 r3 `Lexico` CmpName l4 r4 `Lexico` CmpName l5 r5 `Lexico` CmpName l6 r6
instance (ShowName a, ShowName b, ShowName c, ShowName d, ShowName e, ShowName f, ShowName g) => ShowName '(a, b, c, d, e, f, g) where docName _prx = PP.docList "'(" ", " ")" [docName (Proxy @a), docName (Proxy @b), docName (Proxy @c), docName (Proxy @d), docName (Proxy @e), docName (Proxy @f), docName (Proxy @g)]

type instance CmpName @(k0, k1, k2, k3, k4, k5, k6, k7) '(l0, l1, l2, l3, l4, l5, l6, l7) '(r0, r1, r2, r3, r4, r5, r6, r7) = CmpName l0 r0 `Lexico` CmpName l1 r1 `Lexico` CmpName l2 r2 `Lexico` CmpName l3 r3 `Lexico` CmpName l4 r4 `Lexico` CmpName l5 r5 `Lexico` CmpName l6 r6 `Lexico` CmpName l7 r7
instance (ShowName a, ShowName b, ShowName c, ShowName d, ShowName e, ShowName f, ShowName g, ShowName h) => ShowName '(a, b, c, d, e, f, g, h) where docName _prx = PP.docList "'(" ", " ")" [docName (Proxy @a), docName (Proxy @b), docName (Proxy @c), docName (Proxy @d), docName (Proxy @e), docName (Proxy @f), docName (Proxy @g), docName (Proxy @h)]

type instance CmpName @(k0, k1, k2, k3, k4, k5, k6, k7, k8) '(l0, l1, l2, l3, l4, l5, l6, l7, l8) '(r0, r1, r2, r3, r4, r5, r6, r7, r8) = CmpName l0 r0 `Lexico` CmpName l1 r1 `Lexico` CmpName l2 r2 `Lexico` CmpName l3 r3 `Lexico` CmpName l4 r4 `Lexico` CmpName l5 r5 `Lexico` CmpName l6 r6 `Lexico` CmpName l7 r7 `Lexico` CmpName l8 r8

type instance CmpName @(k0, k1, k2, k3, k4, k5, k6, k7, k8, k9) '(l0, l1, l2, l3, l4, l5, l6, l7, l8, l9) '(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9) = CmpName l0 r0 `Lexico` CmpName l1 r1 `Lexico` CmpName l2 r2 `Lexico` CmpName l3 r3 `Lexico` CmpName l4 r4 `Lexico` CmpName l5 r5 `Lexico` CmpName l6 r6 `Lexico` CmpName l7 r7 `Lexico` CmpName l8 r8 `Lexico` CmpName l9 r9

type instance CmpName @(k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10) '(l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10) '(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10) = CmpName l0 r0 `Lexico` CmpName l1 r1 `Lexico` CmpName l2 r2 `Lexico` CmpName l3 r3 `Lexico` CmpName l4 r4 `Lexico` CmpName l5 r5 `Lexico` CmpName l6 r6 `Lexico` CmpName l7 r7 `Lexico` CmpName l8 r8 `Lexico` CmpName l9 r9 `Lexico` CmpName l10 r10

type instance CmpName @(k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11) '(l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11) '(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11) = CmpName l0 r0 `Lexico` CmpName l1 r1 `Lexico` CmpName l2 r2 `Lexico` CmpName l3 r3 `Lexico` CmpName l4 r4 `Lexico` CmpName l5 r5 `Lexico` CmpName l6 r6 `Lexico` CmpName l7 r7 `Lexico` CmpName l8 r8 `Lexico` CmpName l9 r9 `Lexico` CmpName l10 r10 `Lexico` CmpName l11 r11

type instance CmpName @(k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12) '(l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12) '(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12) = CmpName l0 r0 `Lexico` CmpName l1 r1 `Lexico` CmpName l2 r2 `Lexico` CmpName l3 r3 `Lexico` CmpName l4 r4 `Lexico` CmpName l5 r5 `Lexico` CmpName l6 r6 `Lexico` CmpName l7 r7 `Lexico` CmpName l8 r8 `Lexico` CmpName l9 r9 `Lexico` CmpName l10 r10 `Lexico` CmpName l11 r11 `Lexico` CmpName l12 r12

type instance CmpName @(k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13) '(l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13) '(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13) = CmpName l0 r0 `Lexico` CmpName l1 r1 `Lexico` CmpName l2 r2 `Lexico` CmpName l3 r3 `Lexico` CmpName l4 r4 `Lexico` CmpName l5 r5 `Lexico` CmpName l6 r6 `Lexico` CmpName l7 r7 `Lexico` CmpName l8 r8 `Lexico` CmpName l9 r9 `Lexico` CmpName l10 r10 `Lexico` CmpName l11 r11 `Lexico` CmpName l12 r12 `Lexico` CmpName l13 r13

type instance CmpName @(k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14) '(l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14) '(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14) = CmpName l0 r0 `Lexico` CmpName l1 r1 `Lexico` CmpName l2 r2 `Lexico` CmpName l3 r3 `Lexico` CmpName l4 r4 `Lexico` CmpName l5 r5 `Lexico` CmpName l6 r6 `Lexico` CmpName l7 r7 `Lexico` CmpName l8 r8 `Lexico` CmpName l9 r9 `Lexico` CmpName l10 r10 `Lexico` CmpName l11 r11 `Lexico` CmpName l12 r12 `Lexico` CmpName l13 r13 `Lexico` CmpName l14 r14

type instance CmpName @(k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15) '(l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15) '(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15) = CmpName l0 r0 `Lexico` CmpName l1 r1 `Lexico` CmpName l2 r2 `Lexico` CmpName l3 r3 `Lexico` CmpName l4 r4 `Lexico` CmpName l5 r5 `Lexico` CmpName l6 r6 `Lexico` CmpName l7 r7 `Lexico` CmpName l8 r8 `Lexico` CmpName l9 r9 `Lexico` CmpName l10 r10 `Lexico` CmpName l11 r11 `Lexico` CmpName l12 r12 `Lexico` CmpName l13 r13 `Lexico` CmpName l14 r14 `Lexico` CmpName l15 r15

-----

-- | Key data enabling methods on records, variants, etc
--
-- This class is /closed/; do not add more instances.
--
-- See 'Lacks'.
class KnownLT (nm :: k) (rho :: ROW k v)
  where
    -- | The number of lesser columns in the row, according to 'CmpName'
    knownLT# :: Proxy# nm -> Proxy# rho -> Int#

extKnownLT ::
  forall k v (nm :: k) (rho' :: ROW k v) (rho :: ROW k v).
     Int#
  -> (Proxy# nm -> Proxy# rho' -> Int#)
  -> (Proxy# nm -> Proxy# rho -> Int#)
extKnownLT i# f = \nm _rho -> f nm proxy# +# i#

instance KnownLT nm Emp
  where
    knownLT# = \_nm _rho -> 0#

{-
instance
    KnownLT_Ordering (TypeErr (Incomparable nm x)) (CmpName nm x) nm cols
 => KnownLT nm (Row# (x := b ': cols))
  where
    knownLT# = \nm _rho ->
        knownLT_Ordering
          (proxy# @(TypeErr (Incomparable nm x)))
          (proxy# @(CmpName nm x))
          nm
          (proxy# @cols)

class
    KnownLT_Ordering
      (  err :: Err       )
      (    o :: Ordering  )
      (   nm :: k         )
      ( cols :: [COL k v] )
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
    knownLT_Ordering = \_err _o nm _cols -> 1# +# knownLT# nm (proxy# @(Row# cols))
-}

-- | More data enabling methods on records, variants, etc
--
-- This class is /closed/; do not add more instances.
class KnownLen (rho :: ROW k v)
  where
    -- | The number of columns in the row
    knownLen# :: Proxy# rho -> Int#

instance KnownLen Emp
  where
    knownLen# = \_rho -> 0#
{-
instance
    KnownLen (Row# cols)
 => KnownLen (Row# (x := b ': cols))
  where
    knownLen# = \_rho -> 1# +# knownLen# (proxy# @(Row# cols))
-}
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
-- This class is /closed/; do not add more instances.
--
-- See 'Lacks'.
class Absent (nm :: k) (rho :: ROW k v)

instance Absent nm Emp

{-
instance
    Absent_Ordering (TypeErr (Incomparable nm x)) (CmpName nm x) nm cols
 => Absent nm (Row# (x := b ': cols))

class Absent_Ordering (err :: Err) (o :: Ordering) (nm :: k) (cols :: [COL k v])

instance Absent_Ordering err LT nm cols

instance TypeError (NotAbsent nm) => Absent_Ordering err EQ nm cols

instance Absent nm (Row# cols) => Absent_Ordering err GT nm cols
-}
-----

type family Extend_Col (err :: Err) (col :: COL k v) (rho :: ROW k v) :: ROW k v
  where
    {}
--    Extend_Col err (nm := a) rho = Extend_Row# nm a rho (TypeErr (AbstractROW rho))

-- We intentionally put the @err@ argument after the @rho@ argument, so that GHC renders the deeper error
type family Extend_Row#
    (  nm :: k       )
    (   a :: v       )
    ( rho :: ROW k v )
    ( err :: Err     )
          :: ROW k v
  where
    {}
{-    Extend_Row# nm a (Row# '[]             ) err = Row# '[nm := a]
    Extend_Row# nm a (Row# (x := b ': cols)) err = Extend_Ordering (TypeErr (Incomparable nm x)) (CmpName nm x) nm a x b cols

type family Extend_Ordering
    (  err :: Err       )
    (    o :: Ordering  )
    (   nm :: (k :: Type))
    (    a :: v         )
    (    x :: k         )
    (    b :: v         )
    ( cols :: [COL k v] )
           :: ROW k v
  where
    Extend_Ordering err LT nm a x b cols = Cons nm a (Cons x b (Row# cols))
    Extend_Ordering err EQ nm a x b cols = Cons nm a (Cons x b (Row# cols))
    Extend_Ordering err GT nm a x b cols = Cons x b (Extend_Row# nm a (Row# cols) NoErr)
-}
-----

-- | Restriction is essentially an implementation detail of the typechecker
-- plugin, not exposed to the user
type family Restrict (nm :: k) (rho :: ROW k v) :: ROW k v
  where
    {}
--    Restrict nm (Row# '[]             ) = TypeError (NotFound nm)
--    Restrict nm (Row# (x := b ': cols)) = Restrict_Ordering (TypeErr (Incomparable nm x)) (CmpName nm x) nm x b cols
{-
type family Restrict_Ordering
    (  err :: Err       )
    (    o :: Ordering  )
    (   nm :: k         )
    (    x :: k         )
    (    b :: v         )
    ( cols :: [COL k v] )
           :: ROW k v
  where
    Restrict_Ordering err LT nm x b cols = TypeError (NotFound nm)
    Restrict_Ordering err EQ nm x b cols = Row# cols
    Restrict_Ordering err GT nm x b cols = Cons x b (Restrict nm (Row# cols))
-}
-----

-- | The image of this name in the row
--
-- If multiple columns have the same name, it returns the outermost.
--
-- TODO does this encourage subtle bugs? Only use 'Find' instead?
type family Select (nm :: k) (rho :: ROW k v) :: v
  where
    {}
{-
    Select nm (Row# '[]             ) = TypeError (NotFound nm)
    Select nm (Row# (x := b ': cols)) = Select_Ordering (TypeErr (Incomparable nm x)) (CmpName nm x) nm x b cols

type family Select_Ordering
    (  err :: Err       )
    (    o :: Ordering  )
    (   nm :: k         )
    (    x :: k         )
    (    b :: v         )
    ( cols :: [COL k v] )
           :: v
  where
    Select_Ordering err LT nm x b cols = TypeError (NotFound nm)
    Select_Ordering err EQ nm x b cols = b
    Select_Ordering err GT nm x b cols = Select nm (Row# cols)
-}
-----

data FindResult k v = Found v | NoSuchColumn k

-- | The image of this name in the row, if any
--
-- If multiple columns have the same name, it returns the outermost.
type family Find (nm :: k) (rho :: ROW k v) :: FindResult k v
  where
    {}
{-
    Find nm (Row# '[]             ) = NoSuchColumn nm
    Find nm (Row# (x := b ': cols)) = Find_Ordering (TypeErr (Incomparable nm x)) (CmpName nm x) nm x b cols

type family Find_Ordering
    (  err :: Err       )
    (    o :: Ordering  )
    (   nm :: k         )
    (    x :: k         )
    (    b :: v         )
    ( cols :: [COL k v] )
           :: FindResult k v
  where
    Find_Ordering err LT nm x b cols = NoSuchColumn nm
    Find_Ordering err EQ nm x b cols = Found b
    Find_Ordering err GT nm x b cols = Find nm (Row# cols)
-}
-----

infixl 5 :&

-- | Extend the row by inserting the given column
type family (:&) (rho :: ROW k v) (col :: COL k v) :: ROW k v where {}
type UnfoldExtOp rho               col              = rho :& col -- Extend_Col (TypeErr (AbstractCOL col)) col rho

-----

class AllCols (c :: Sem.Fld k v Constraint) (rho :: ROW k v)
  where
    anyDicts# :: Proxy# c -> Proxy# rho -> Seq.Seq (Sem.Dict (Sem.Sem c Any Any))

class    (KnownLT nm rho, Sem.Sem c nm a) => AllColsHelp (c :: Sem.Fld k v Constraint) (nm :: k) (a :: v) (rho :: ROW k v)
instance (KnownLT nm rho, Sem.Sem c nm a) => AllColsHelp (c :: Sem.Fld k v Constraint) (nm :: k) (a :: v) (rho :: ROW k v)

instance AllCols c Emp where anyDicts# = \_c _emp -> Seq.empty

extAllCols ::
  forall k v (c :: Sem.Fld k v Constraint) (nm :: k) (a :: v) (rho :: ROW k v).
     AllColsHelp c nm a rho
  => Proxy# nm
  -> Proxy# a
  -> (Proxy# c -> Proxy# rho -> Seq.Seq (Sem.Dict (Sem.Sem c Any Any)))
  -> (Proxy# c -> Proxy# (rho :& nm := a)-> Seq.Seq (Sem.Dict (Sem.Sem c Any Any)))
extAllCols nm _a inner c _rho' =
    Seq.insertAt
      (I# (knownLT# nm (proxy# @rho)))
      (unsafeCoerce $ Sem.Dict @(Sem.Sem c nm a))
      (inner c proxy#)
