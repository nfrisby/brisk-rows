module BriskRows (
    -- * Row types
    COL ((:=)),
    CmpName,
    ROW,
    Emp,
    Ext, (:&),
    -- * Row type constraints
    Absent,
    KnownLT,
    Lacks,
    -- * Util
    Lexico,
    ) where

import           BriskRows.Internal
