{-# LANGUAGE MagicHash #-}

module BriskRows.RV (
    module BriskRows,
    -- * Records
    Rcd,
    del, del##, delPP,
    emp,
    ins, ins#, insP,
    prj, prj#, prjP,
    -- * Variants
    Vrt,
    abd,
    cas, cas#, casP,
    inj, inj#, injP,
    wkn, wkn##, wknPP,
    -- * Both
    lacking, lacking#, lackingP,
    ) where

import           BriskRows
import           BriskRows.Internal.RV
import           BriskRows.Internal.RV.Ambiguous
import           BriskRows.Internal.RV.Proxy
