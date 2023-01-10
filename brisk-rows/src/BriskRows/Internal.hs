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
    -- ** Constraints
    Absent,
    AllCols (anyDicts#),
    KnownLT (knownLT#),
    KnownLen (knownLen#),
    Lacks,
    -- * Names
    CmpName,
    Lexico,
    NameApartness (NameGT, NameLT),
    NameOrdering (NameEQ, NameApart),
    ShowName (docName),
    docName#,
    -- * Auxiliary
    Err,
    NoErr,
    TypeErr,
    castAllCols,
    givenAllCols1,
    givenAllCols2,
    givenKnownLT,
    uncastAllCols,
    wantedKnownLT,
    wantedAllCols,
    ) where

import           Data.Kind (Constraint, Type)
import           Data.List.NonEmpty (NonEmpty ((:|)))
import           Data.Proxy (Proxy (Proxy))
import qualified Data.Sequence as Seq
import qualified Data.Type.Ord
import           GHC.Exts (Any, Proxy#, proxy#)
import           GHC.Prim (Int#, (+#), (-#))
import           GHC.Tuple (Solo (Solo))
import           GHC.Types (Int (I#))
import           GHC.TypeLits (ErrorMessage (Text), TypeError)
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
type family CmpName (l :: k) (r :: k) :: NameOrdering

-- | The kind of a row type
data ROW (k :: Type) (v :: Type) =
    -- | The empty row
    Emp

class ShowName (nm :: k) where
    docName :: proxy nm -> PP.Doc

docName# :: forall {nm}. ShowName nm => Proxy# nm -> PP.Doc
docName# _nm = docName (Proxy @nm)

-----

data NameApartness = NameLT | NameGT
data NameOrdering =  NameEQ | NameApart NameApartness

infixl `Lexico`

-- | Lexicographic ordering
--
-- Use this when defining new instances of 'CmpName' for product types.
type family Lexico (l :: NameOrdering) (r :: NameOrdering) :: NameOrdering
  where
    Lexico NameEQ NameEQ = NameEQ
    Lexico l r = NameApart (LexicoApartness l r)

type family LexicoApartness (l :: NameOrdering) (r :: NameOrdering) :: NameApartness
  where
    LexicoApartness (NameApart l) r = l
    LexicoApartness NameEQ (NameApart r) = r
    LexicoApartness l r = TypeError (Text "Impossible")

type family FromOrdering (o :: Ordering) :: NameOrdering
  where
    FromOrdering LT = NameApart NameLT
    FromOrdering EQ = NameEQ
    FromOrdering GT = NameApart NameGT

-----

type instance CmpName @Char l r = FromOrdering (Data.Type.Ord.Compare l r)
instance TypeLits.KnownChar c => ShowName (c :: Char) where docName c = PP.docShowS $ shows $ TypeLits.charVal c

type instance CmpName @Natural l r = FromOrdering (Data.Type.Ord.Compare l r)
instance TypeLits.KnownNat n => ShowName (n :: Natural) where docName n = PP.docShowS $ shows $ TypeLits.natVal n

type instance CmpName @Symbol l r = FromOrdering (Data.Type.Ord.Compare l r)
instance TypeLits.KnownSymbol s => ShowName (s :: Symbol) where docName s = PP.docShowS $ shows $ TypeLits.symbolVal s

type instance CmpName @Bool l r = FromOrdering (CmpBool l r)
type family CmpBool (l :: Bool) (r :: Bool) :: Ordering
  where
    CmpBool False False = EQ
    CmpBool False _     = LT
    CmpBool _     False = GT
    CmpBool True  True  = EQ
instance ShowName True  where docName _prx = PP.docShowS $ shows True
instance ShowName False where docName _prx = PP.docShowS $ shows False

type instance CmpName @Ordering l r = CmpOrdering l r
type family CmpOrdering (l :: Ordering) (r :: Ordering) :: NameOrdering
  where
    CmpOrdering LT LT = NameEQ
    CmpOrdering LT _  = NameApart NameLT
    CmpOrdering _  LT = NameApart NameGT
    CmpOrdering EQ EQ = NameEQ
    CmpOrdering EQ _  = NameApart NameLT
    CmpOrdering _  EQ = NameApart NameGT
    CmpOrdering GT GT = NameEQ
instance ShowName LT where docName _prx = PP.docShowS $ shows LT
instance ShowName EQ where docName _prx = PP.docShowS $ shows EQ
instance ShowName GT where docName _prx = PP.docShowS $ shows GT

type instance CmpName @(Maybe k) l r = CmpMaybe l r
type family CmpMaybe (l :: Maybe k) (r :: Maybe k) :: NameOrdering
  where
    CmpMaybe Nothing  Nothing  = NameEQ
    CmpMaybe Nothing  _        = NameApart NameLT
    CmpMaybe _        Nothing  = NameApart NameGT
    CmpMaybe (Just l) (Just r) = CmpName l r
instance ShowName Nothing where docName _prx = PP.docString "Nothing"
instance ShowName a => ShowName (Just a) where docName _prx = PP.docString "Just" `PP.docApp` docName (Proxy @a)

type instance CmpName @(Either k0 k1) l r = CmpEither l r
type family CmpEither (l :: Either k0 k1) (r :: Either k0 k1) :: NameOrdering
  where
    CmpEither (Left  l) (Left  r) = CmpName l r
    CmpEither (Left  _) _         = NameApart NameLT
    CmpEither _         (Left  _) = NameApart NameGT
    CmpEither (Right l) (Right r) = CmpName l r
instance ShowName a => ShowName (Left  a) where docName _prx = PP.docString "Left"  `PP.docApp` docName (Proxy @a)
instance ShowName a => ShowName (Right a) where docName _prx = PP.docString "Right" `PP.docApp` docName (Proxy @a)

type instance CmpName @[k] l r = CmpList l r
type family CmpList (l :: [k]) (r :: [k]) :: NameOrdering
  where
    CmpList '[]       '[]       = NameEQ
    CmpList '[]       _         = NameApart NameLT
    CmpList _         '[]       = NameApart NameGT
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

type instance CmpName @() l r = NameEQ
instance ShowName ('() :: ()) where docName _prx = PP.docString "'()"

type instance CmpName @(Proxy k) l r = NameEQ
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

givenKnownLT ::
  forall k v (nm :: k) (rho :: ROW k v) (rho' :: ROW k v).
     Int#
  -> (Proxy# nm -> Proxy# rho -> Int#)
  -> (Proxy# nm -> Proxy# rho' -> Int#)
givenKnownLT i# older = \nm _rho -> older nm proxy# -# i#

wantedKnownLT ::
  forall k v (nm :: k) (rho' :: ROW k v) (rho :: ROW k v).
     Int#
  -> (Proxy# nm -> Proxy# rho' -> Int#)
  -> (Proxy# nm -> Proxy# rho -> Int#)
wantedKnownLT i# newer = \nm _rho -> newer nm proxy# +# i#

instance KnownLT nm Emp
  where
    knownLT# = \_nm _rho -> 0#

-----

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

-----

infixl 5 :&

-- | Extend the row by inserting the given column
type family (:&) (rho :: ROW k v) (col :: COL k v) :: ROW k v where {}

-----

class AllCols (c :: Sem.Fld k v Constraint) (rho :: ROW k v)
  where
    anyDicts# :: Proxy# c -> Proxy# rho -> Seq.Seq (Sem.Dict (Sem.Sem c Any Any))

instance AllCols c Emp where anyDicts# = \_c _emp -> Seq.empty

uncastAllCols ::
  forall {k} {v} {c :: Sem.Fld k v Constraint} {rho :: ROW k v}.
     (Proxy# c               -> Seq.Seq (Sem.Dict (Sem.Sem c Any Any)))
  -> (Proxy# c -> Proxy# rho -> Seq.Seq (Sem.Dict (Sem.Sem c Any Any)))
uncastAllCols inner c _rho = inner c

castAllCols ::
  forall {k} {v} {c :: Sem.Fld k v Constraint} {rho :: ROW k v}.
     AllCols c rho
  => Proxy# rho
  -> (Proxy# c -> Seq.Seq (Sem.Dict (Sem.Sem c Any Any)))
castAllCols _rho c = anyDicts# c (proxy# @rho)

{-

w :: AllCols c (rho :& x := a :& y := b)
w = Seq.insertAt i w'1 w'2

w'1 :: c x a
w'2 :: AllCols c (rho :& y := b)

-}
wantedAllCols ::
  forall {k} {v} {c :: Sem.Fld k v Constraint} {nm :: k} {a :: v}.
     Sem.Sem c nm a
  => Proxy# nm
  -> Proxy# a
  -> Int#
  -> Int#
  -> (Proxy# c -> Seq.Seq (Sem.Dict (Sem.Sem c Any Any)))
  -> (Proxy# c -> Seq.Seq (Sem.Dict (Sem.Sem c Any Any)))
wantedAllCols _nm _a i# j# newer c =
    Seq.insertAt
        (I# (i# +# j#))
        (unsafeCoerce (Sem.Dict @(Sem.Sem c nm a)))
        (newer c)

{-

g :: AllCols c (rho :& x := a :& y := b)

g'1 :: c x a
g'1 = Seq.at i g

g'2 :: AllCols c (rho :& y := b)
g'2 = Seq.deleteAt i g

-}
givenAllCols1 ::
  forall {k} {v} {c :: Sem.Fld k v Constraint} {nm :: k} {a :: v}.
     Proxy# nm
  -> Proxy# a
  -> Int#
  -> Int#
  -> (Proxy# c -> Seq.Seq (Sem.Dict (Sem.Sem c Any Any)))
  -> Sem.Dict (Sem.Sem c nm a)
givenAllCols1 _nm _a i# j# older =
    unsafeCoerce
  $ Seq.index
        (older (proxy# @c))
        (I# (i# +# j#))

givenAllCols2 ::
  forall {k} {v} {c :: Sem.Fld k v Constraint}.
     Int#
  -> Int#
  -> (Proxy# c -> Seq.Seq (Sem.Dict (Sem.Sem c Any Any)))
  -> (Proxy# c -> Seq.Seq (Sem.Dict (Sem.Sem c Any Any)))
givenAllCols2 i# j# older c =
    Seq.deleteAt
        (I# (i# +# j#))
        (older c)
