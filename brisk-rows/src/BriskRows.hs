module BriskRows (
    -- * Row types
    COL ((:=)),
    CmpName,
    ROW,
    Emp,
    Extend, (:&),
    -- * Row type constraints
    Absent,
    KnownLT,
    Lacks,
    -- * Util
    Lexico,
    ) where

import           BriskRows.Internal
