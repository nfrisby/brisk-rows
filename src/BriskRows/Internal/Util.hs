{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}

{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

module BriskRows.Internal.Util (
    needConstraint,
  ) where

-- | A way to disarm @-fwarn-redundant-constraints@ for a specific constraint
needConstraint :: c => ()
needConstraint = ()
