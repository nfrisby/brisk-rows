-- | The user interface for row types.
module BriskRows (
    -- * Rows
    -- ** Kinds
    COL ((:=)),
    ROW (Emp),
    -- ** Constructors
    (:&),
    -- ** Constraints
    AllCols,
    Absent,
    KnownLT,
    KnownLen,
    Lacks,
    -- * Names
    CmpName,
    Lexico,
    NameApartness (NameGT, NameLT),
    NameOrdering (NameEQ, NameApart),
    ShowName (docName),
    ) where

import           BriskRows.Internal
