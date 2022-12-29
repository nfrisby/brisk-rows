{-# LANGUAGE MagicHash #-}

module BriskRows.RV (
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
import           BriskRows.Internal.RV
import           BriskRows.Internal.RV.Ambiguous
import           BriskRows.Internal.RV.Operators
import           BriskRows.Internal.RV.Proxy
