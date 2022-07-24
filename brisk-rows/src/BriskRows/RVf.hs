{-# LANGUAGE MagicHash #-}

module BriskRows.RVf (
    module BriskRows,
    module BriskRows.Fields,
    -- * Records
    Rcd,
    del, del#, delP,
    emp,
    ins, ins#, insP,
    prj, prj#, prjP,
    -- * Variants
    Vrt,
    abd,
    cas, cas#, casP,
    inj, inj#, injP,
    wkn, wkn#, wknP,
    -- * Both
    lacking, lacking#, lackingP,
    ) where

import           BriskRows
import           BriskRows.Fields
import           BriskRows.Internal.RVf
import           BriskRows.Internal.RVf.Ambiguous
import           BriskRows.Internal.RVf.Proxy
