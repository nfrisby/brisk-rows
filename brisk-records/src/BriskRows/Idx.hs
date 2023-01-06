{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -fplugin=BriskRows.Plugin #-}

module BriskRows.Idx (
  EqualsKV (ReflKV),
  Ordering' (LT', EQ', GT'),
  Idx (Idx),
  compareIdx,
  idx#,
  idx1#,
  idxInt,
  nrw#,
  wdn#,
  ) where

import           Data.Kind (Type)
import           GHC.Exts (Int (I#), Proxy#, proxy#)
import           Unsafe.Coerce (unsafeCoerce)

import           BriskRows
import           BriskRows.Internal (knownLT#)

-----

row# :: rv (rho :: ROW k v) -> Proxy# rho
row# _ = proxy#

frow# :: f (rv (rho :: ROW k v)) -> Proxy# rho
frow# _ = proxy#

knownLT :: KnownLT nm rho => Proxy# nm -> Proxy# rho -> Int
knownLT = \nm rho -> I# (knownLT# nm rho)

-----

data EqualsKV :: k -> v -> k -> v -> Type where
  ReflKV :: EqualsKV nm a nm a

-- | An offset of @nm := a@ within the row
newtype Idx (nm :: k) (a :: v) (rho :: ROW k v) = Idx Int
  deriving (Eq, Ord, Show)

idxInt :: Idx nm a rho -> Int
idxInt (Idx i) = i

data Ordering' nmL aL nmR aR =
    LT' | EQ' {-# UNPACK #-} !(EqualsKV nmL aL nmR aR) | GT'

compareIdx :: Idx nmL aL rho -> Idx nmR aR rho -> Ordering' nmL aL nmR aR
compareIdx (Idx l) (Idx r) = case compare l r of
    LT -> LT'
    EQ -> EQ' $ unsafeCoerce ReflKV
    GT -> GT'

-- | The index of the outermost column with the given name
idx1# ::
     KnownLT nm rho
  => Proxy# nm
  -> Proxy# rho
  -> Idx nm a (rho :& nm := a)
idx1# = \nm rho -> Idx $ knownLT nm rho

-- | The index of the outermost column with the given name
idx# ::
     (KnownLT nm rho, Found a ~ Find nm rho)
  => Proxy# nm
  -> Proxy# rho
  -> Idx nm a rho
idx# = \nm rho -> Idx $ knownLT nm rho

-- | Widen the row
wdn# ::
     KnownLT nm rho
  => Proxy# nm
  -> Idx fixed_nm fixed_a rho
  -> Idx fixed_nm fixed_a (rho :& nm := a)
wdn# = \nm idx ->
    let Idx i = idx
    in
    if i < knownLT nm (row# idx)
    then Idx i
    else Idx (i + 1)   -- the new column is the /first/ thing in the extended row that's not less than nm

-- | Narrow the row
--
-- Returns 'EqualsKV' if the index points to the column being removed.
nrw# ::
     KnownLT nm rho
  => Proxy# nm
  -> Idx fixed_nm fixed_a (rho :& nm := a)
  -> Either (EqualsKV fixed_nm fixed_a nm a) (Idx fixed_nm fixed_a rho)
nrw# = \nm idx ->
    let Idx i = idx
        result = case idx `compareIdx` Idx (knownLT nm (frow# result)) of
            LT'      -> Right $ Idx i
            EQ' refl -> Left refl   -- the removed column is the /first/ thing in the extended row that's not less than nm
            GT'      -> Right $ Idx (i - 1)
    in
    result
