-- | The user interface for row types.
module BriskRows (
    -- * Rows
    -- ** Kinds
    COL ((:=)),
    ROW,
    -- ** Constructors
    Emp,
    Ext, (:&),
    -- ** Queries
    Select,
    -- ** Constraints
    Absent,
    KnownLT,
    KnownLen,
    Lacks,
    -- * Name Order
    CmpName,
    Lexico,
    ) where

import           BriskRows.Internal
