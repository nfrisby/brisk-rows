{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -fplugin=BriskRows.Plugin #-}

{-# OPTIONS_HADDOCK -not-home #-}

module BriskRows.Internal.RVf (
    -- * Records
    Rcd (Rcd#),
    del#,
    emp,
    ins#,
    prj#,
    -- * Variants
    Vrt (Vrt#),
    abd,
    cas#,
    inj#,
    wkn#,
    -- * Both
    lacking#,
    ) where

import           Data.Kind (Type)
import qualified Data.Sequence as Sq
import           GHC.Exts (Any, Proxy#, proxy#)
import           GHC.Prim (Int#, (+#), (-#))
import           GHC.Types (Int (I#))
import           Unsafe.Coerce (unsafeCoerce)

import           BriskRows.Internal

-----

row# :: rOW (rho :: ROW k v) -> Proxy# rho
row# _ = proxy#

vrtRow# :: (t f (rho :: ROW k v) -> ans) -> Proxy# rho
vrtRow# _ = proxy#

knownLT :: KnownLT nm rho => Proxy# nm -> Proxy# rho -> Int
knownLT = \nm rho -> I# (knownLT# nm rho)

-----

-- | A record
newtype Rcd (f :: k -> v -> Type) (rho :: ROW k v) =
    -- | INVARIANT Same order as the row
    Rcd# (Sq.Seq Any)

emp :: Rcd f (Emp :: ROW k v)
emp = Rcd# Sq.empty

-- | Extend the record's row by inserting another field
ins# :: KnownLT nm rho => Proxy# nm -> f nm a -> Rcd f rho -> Rcd f (rho :& nm := a)
ins# = \nm a rcd ->
    let rho     = row# rcd
        Rcd# sq = rcd
    in
    Rcd# $ Sq.insertAt (knownLT nm rho) (unsafeCoerce a) sq

-- | Restrict the record's row by deleting a field
del# :: KnownLT nm rho => Proxy# nm -> Rcd f (rho :& nm := a) -> Rcd f rho
del# = \nm rcd ->
    let Rcd# sq = rcd
        rcd'    = Rcd# $ Sq.deleteAt (knownLT nm (row# rcd')) sq
    in
    rcd'

-- | Project a value out of the record
--
-- See 'Select'.
prj# :: KnownLT nm rho => Proxy# nm -> Rcd f rho -> f nm (Select nm rho)
prj# = \nm rcd ->
    let rho     = row# rcd
        Rcd# sq = rcd
    in
    unsafeCoerce $ Sq.index sq (knownLT nm rho)

-----

-- | A variant
data Vrt (f :: k -> v -> Type) (rho :: ROW k Type) =
    -- | INVARIANT The integer is the value's index in the row
    --
    -- For the most-recently added column of a given name, this tag is
    -- equivalent to 'knownLT#'. See 'Row#'.
    Vrt# !Any Int#

-- | An absurd value, since an empty variant is an empty type
abd :: Vrt f Emp -> ans
abd = error "Vrt.abd"

-- | Extend a variant continuation's row by adding another case
cas# :: KnownLT nm rho => Proxy# nm -> (f nm a -> ans) -> (Vrt f rho -> ans) -> (Vrt f (rho :& nm := a) -> ans)
cas# = \nm f g vrt ->
    let rho          = vrtRow# g
        !(Vrt# a i#) = vrt
    in
    case compare (I# i#) (knownLT nm rho) of
      LT -> g $ Vrt# a i#        
      EQ -> unsafeCoerce f a   -- the nm column is the first thing in rho :& nm that's not less than nm
      GT -> g $ Vrt# a (i# -# 1#)

-- | Restrict a variant continuation's row by weakening it no longer handle a specific case
wkn# :: KnownLT nm rho => Proxy# nm -> (Vrt f (rho :& nm := a) -> ans) -> (Vrt f rho -> ans)
wkn# = \nm f vrt ->
    let rho          = row# vrt
        !(Vrt# a i#) = vrt
    in
    case compare (I# i#) (knownLT nm rho) of
      LT -> f $ Vrt# a  i#
      EQ -> f $ Vrt# a (i# +# 1#)   -- the new nm column is the first thing in rho :& nm that's not less than nm
      GT -> f $ Vrt# a (i# +# 1#)

-- | Inject a value into the variant
--
-- See 'Select'.
inj# :: KnownLT nm rho => Proxy# nm -> f nm (Select nm rho) -> Vrt f rho
inj# = \nm a ->
    let vrt = Vrt# (unsafeCoerce a) (knownLT# nm (row# vrt))
    in
    vrt

-----

lacking# :: Absent nm rho => Proxy# nm -> t rho -> t rho
lacking# = \_nm -> id
