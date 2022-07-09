{-# LANGUAGE MagicHash #-}

module BriskRows (
    -- * Row types
    COL ((:::)),
    Delete,
    Insert,
    Lookup,
    Nil,
    ROW,
    -- * Records
    Absent,
    Present,    
    Project,
    Rcd,
    emp, empty,
    ext, extend, extend#, extendProxy,
    prj, project, project#, projectProxy,
    rmv, remove, remove#, removeProxy,
    unextend, unextend#, unextendProxy,
    -- * Folding over the record fields
    All,
    Vec (VCons, VNil),
    foldr#,
    -- * Convenient syntax
    Col (Col),
    Field (Field),
    (:&),
    (.*),
    (./),
  ) where

import           BriskRows.Internal
import           BriskRows.Internal.Ambiguous
