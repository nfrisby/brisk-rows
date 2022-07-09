{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_HADDOCK not-home #-}

-- | All of the definitions that require @-XAllowAmbiguousTypes@
module BriskRows.Internal.Ambiguous (module BriskRows.Internal.Ambiguous) where

import           GHC.Exts (proxy#)

import           BriskRows.Internal

extend, ext ::
 forall nm a row.
    Absent nm row
 => a
 -> Rcd row
 -> Rcd (Insert nm a row)
extend = extend# (proxy# @nm)
ext    = extend# (proxy# @nm)

project, prj ::
 forall nm row.
    Project nm row
 => Rcd row
 -> Lookup nm row
project = project# (proxy# @nm)
prj     = project# (proxy# @nm)

remove, rmv ::
 forall nm row.
    Present nm row
 => Rcd row
 -> Rcd (Delete nm row)
remove = remove# (proxy# @nm)
rmv    = remove# (proxy# @nm)

removed ::
 forall nm row.
    Present nm row
 => Rcd row
 -> (Lookup nm row, Rcd (Delete nm row))
removed = removed# (proxy# @nm)

unextend ::
 forall nm a row.
    Absent nm row
 => Rcd (Insert nm a row)
 -> (a, Rcd row)
unextend = unextend# (proxy# @nm)

unremove ::
 forall nm row.
    Present nm row
 => Rcd (Delete nm row)
 -> Lookup nm row
 -> Rcd row
unremove = unremove# (proxy# @nm)
