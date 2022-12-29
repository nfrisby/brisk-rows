{-# LANGUAGE MagicHash #-}

module BriskRows.RVf (
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
    ) where

import           BriskRows
import           BriskRows.Internal.RVf
import           BriskRows.Internal.RVf.Ambiguous
import           BriskRows.Internal.RVf.Operators
import           BriskRows.Internal.RVf.Proxy
