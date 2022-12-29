{-# LANGUAGE MagicHash #-}

-- | The user interface for simple records and variants
--
-- The interface to each is quite simple, just a few functions. However, this
-- module provides several aliases for each function, since there are several
-- possible syntactic preferences. For example:
--
-- * Use 'ins#' if you want to propagate your column names via the 'GHC.Exts.Proxy#' type.
--
-- * Use 'ins' if you want to propagate your column names via @-XTypeApplications@.
--
-- * Use 'insP' if you want to propagate your column names via (normal, lifted) type constructor applications, such as 'Data.Proxy.Proxy', 'Maybe', 'Name', etc.
--
-- * Use '.*' and 'BriskRows.:=' with the @'GHC.OverloadedLabels.IsLabel' 'Name'@ instance via @-XOverloadedLabels@ if you prefer operator syntax and are using 'GHC.TypeLits.Symbol' column names.
--
-- * Use '.*' and 'col' via @-XTypeApplications@ if you prefer operator syntax.
--
-- For a name of kind 'GHC.TypeLits.Symbol', these look like:
--
-- * @'ins#' foo True rcd@ assuming @foo :: Proxy# "foo"@
--
-- * @'ins' \@"foo" True rcd@, see @-XTypeApplications@
--
-- * @'insP' foo True rcd@ assuming @foo :: F "foo"@ for some @F@ such as 'Data.Proxy.Proxy', 'Maybe', 'Name', etc
--
-- * @'insP' #foo True rcd@; see "GHC.OverloadedLabels"
--
-- * @rcd '.*' 'col' \@"foo" True@, see @-XTypeApplications@
--
-- * @rcd '.*' #foo 'BriskRows.:=' True@; see "GHC.OverloadedLabels"
--
-- For a name of kind other than 'GHC.TypeLits.Symbol', these look like:
--
-- * @'ins#' foo True rcd@ assuming @foo :: Proxy# Foo@
--
-- * @'ins' \@Foo True rcd@, see @-XTypeApplications@
--
-- * @'insP' foo True rcd@ assuming @foo :: F Foo@ for some @F@ such as 'Data.Proxy.Proxy', 'Maybe', 'Name', etc
--
-- * @rcd '.*' 'col' \@Foo True@, see @-XTypeApplications@
module BriskRows.RV (
    module BriskRows,

    -- * Records
    Rcd,
    emp,
    -- ** 'Monoid'
    AllMonoid,
    pur,
    -- ** Via 'Proxy#'
    del#, ins#, prj#,
    -- ** Via @-XTypeApplications@
    del, ins, prj,
    -- ** Via @proxy@
    delP, insP, prjP,
    -- ** Via 'COL' operators
    (./), (.*),

    -- * Variants
    Vrt,
    abd,
    -- ** Via 'Proxy#'
    cas#, inj#, wkn#,
    -- ** Via @-XTypeApplications@
    cas, inj, wkn,
    -- ** Via @proxy@
    casP, injP, wknP,
    -- ** Via 'COL' operators
    (.-), (.+),

    -- * Both
    -- ** 'Semigroup'
    AllSemigroup,
    Splat,
    SplatF,
    splat,
    -- ** Via 'Proxy#'
    lacking#,
    -- ** Via @-XTypeApplications@
    lacking,
    -- ** Via @proxy@
    lackingP,
    -- ** Via 'COL' operators
    Name (Name),
    col,
    ) where

import           BriskRows
import           BriskRows.Internal.RV
import           BriskRows.Internal.RV.Ambiguous
import           BriskRows.Internal.RV.Operators
import           BriskRows.Internal.RV.Proxy
