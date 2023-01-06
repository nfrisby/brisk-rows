-- | The user interface for row types.
module BriskRows (
    -- * Rows
    -- ** Kinds
    COL ((:=)),
    ROW (Emp),
    -- ** Constructors
    (:&),
    -- ** Queries
    Find,
    FindResult (Found, NoSuchColumn),
    Select,
    -- ** Constraints
    AllCols,
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
