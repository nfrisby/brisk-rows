{-# LANGUAGE LambdaCase #-}

-- | Derived from /Unparsing Expressions With Prefix and Postfix Operators/ by Norman Ramsey, 1998.
module BriskRows.Internal.PP (
  Prec (Prec),
  Assoc (LeftAssoc, NonAssoc, RightAssoc),
  Doc,
  docApp,
  docBop,
  docList,
  docParens,
  docShowS,
  docString,
  docTypeApp,
  ) where

-----

import qualified Data.List.NonEmpty as NE

-----

newtype Prec = Prec Int
  deriving (Eq, Ord)

-- page 12
data Assoc = LeftAssoc | RightAssoc | NonAssoc
  deriving (Eq)

-- page 12
data Op = Op !Prec !Assoc

data MinOp = NoOp | MinOp !Op

data Doc = Doc !MinOp !ShowS

instance Show Doc where show (Doc _ s) = s ""

-----

docShowS :: ShowS -> Doc
docShowS = Doc NoOp

docString :: String -> Doc
docString = docShowS . showString

docParens :: Doc -> Doc
docParens (Doc _ s) = docShowS $ showParen True s

docList :: String -> String -> String -> [Doc] -> Doc
docList open sep close docs =
    Doc NoOp $ showString open . mid . showString close
  where
    unDoc (Doc _ s) = s

    mid = case NE.nonEmpty docs of
        Nothing           -> id
        Just (x NE.:| ys) -> unDoc x . foldr (\y acc -> showString sep . unDoc y . acc) id ys

docBop :: String -> Assoc -> Int -> Doc -> Doc -> Doc
docBop sM f p (Doc mopL sL) (Doc mopR sR) =
    Doc
      (MinOp opM)
      (sL' . showString sM . sR')
  where
    opM = Op (Prec p) f
    sL' = showParen (parens mopL opM LeftAssoc ) sL
    sR' = showParen (parens mopR opM RightAssoc) sR

infixl `docApp`

-- | Application in Haskell is juxtaposition as a binary operator
docApp :: Doc -> Doc -> Doc
docApp = docBop " " LeftAssoc 10

-- | Type application in Haskell is @\@| as a binary operator
docTypeApp :: Doc -> Doc -> Doc
docTypeApp = docBop " @" LeftAssoc 10

parens :: MinOp -> Op -> Assoc -> Bool
parens = \case
    NoOp    -> \_o _side -> False
    MinOp i -> \o  side  -> not $ noparens i o side

-- page 14
noparens :: Op -> Op -> Assoc -> Bool
noparens (Op pI fI) (Op pO fO) side =
    (pI > pO) ||
    case (fI, side) of
        (LeftAssoc,  LeftAssoc ) -> pI == pO && fO == LeftAssoc
        (RightAssoc, RightAssoc) -> pI == pO && fO == RightAssoc
        (_,          NonAssoc  ) -> fI == fO
        _                        -> False
