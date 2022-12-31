{-# LANGUAGE MagicHash #-}

-- | This module generalizes "BriskRows.RV" by parameterizing each record and
-- variant over a top-level structure common to all fields.
--
-- Use "BriskRows.Fields" to express that structure.
module BriskRows.RVf (
    module BriskRows,
    module BriskRows.Fields,
    -- * Records
    Rcd,
    -- ** Constructors
    AllCols,
    dicts#,
    emp,
    pur#,
    -- ** Deletion
    del, del#, delP, (./),
    -- ** Insertion
    ins, ins#, insP, (.*),
    -- ** Projection
    prj, prj#, prjP,
    -- * Variants
    Vrt,
    -- ** Constructors
    abd,
    -- ** Case insertion
    cas, cas#, casP, (.+),
    -- ** Injection
    inj, inj#, injP,
    -- ** Case weaking
    wkn, wkn#, wknP, (.-),
    -- * Both
    Name (Name),
    col,
    lacking, lacking#, lackingP,
    Splat,
    SplatF,
    splat,
    ) where

import           BriskRows
import           BriskRows.Fields
import           BriskRows.Internal.RVf
import           BriskRows.Internal.RVf.Ambiguous
import           BriskRows.Internal.RVf.Operators
import           BriskRows.Internal.RVf.Proxy
