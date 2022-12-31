{-# LANGUAGE MagicHash #-}

-- | This module is a variation of "BriskRows.RVf" that expresses the top-level
-- structure common to all fields in a different, more flexible way.
module BriskRows.RVtf (
    module BriskRows,
    -- * Records
    Rcd,
    del, del#, delP, (./),
    emp,
    ins, ins#, insP, (.*),
    prj, prj#, prjP,
    -- * Variants
    Vrt,
    abd,
    cas, cas#, casP, (.+),
    inj, inj#, injP,
    wkn, wkn#, wknP, (.-),
    -- * Both
    Name (Name),
    col,
    lacking, lacking#, lackingP,
    module BriskRows.Internal.Sem,
    ) where

import           BriskRows
import           BriskRows.Internal.RVtf
import           BriskRows.Internal.RVtf.Ambiguous
import           BriskRows.Internal.RVtf.Operators
import           BriskRows.Internal.RVtf.Proxy
import           BriskRows.Internal.Sem
