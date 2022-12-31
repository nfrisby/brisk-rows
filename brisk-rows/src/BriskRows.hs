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
    Find,
    FindResult (Found, NoSuchColumn),
    Select,
    -- ** Constraints
    Absent,
    KnownLT,
    KnownLen,
    Lacks,
    -- * Names
    CmpName,
    Lexico,
    ShowName (docName),
    ) where

import           BriskRows.Internal
