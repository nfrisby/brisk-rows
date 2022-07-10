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
    Agree,
    Present,    
    Project,
    Rcd,
    Union,
    emp, empty,
    ext, extend, extend#, extendProxy,
    prj, project, project#, projectProxy,
    rmv, remove, remove#, removeProxy,
    removed, removed#, removedProxy,
    unextend, unextend#, unextendProxy,
    unremove, unremove#, unremoveProxy,
    unmerge,
    -- * Folding over the record fields
    All,
    Vec (VCons, VNil),
    foldr#,
    -- * Convenient syntax
    Col (Col),
    Field (Field),
    (:&),
    (:#),
    (.*),
    (./),
  ) where

import           BriskRows.Internal
import           BriskRows.Internal.Ambiguous
