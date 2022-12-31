{-# LANGUAGE LambdaCase #-}

module BriskRows.Internal.PP (
  Prec (Prec),
  Assoc (LeftAssoc, NonAssoc, RightAssoc),
  Doc,
  Fixity (LeftFix, Prefix, NonFix, RightFix),
  docApp,
  docBop,
  docList,
  docParens,
  docShowS,
  docString,
  ) where

-----

import qualified Data.List.NonEmpty as NE

-----

newtype Prec = Prec Int
  deriving (Eq, Ord)

-- page 12
data Assoc = LeftAssoc | RightAssoc | NonAssoc

-- page 12
data Fixity = Prefix | LeftFix | RightFix | NonFix
  deriving (Eq)

-- page 12
data Op = Op !Prec !Fixity

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

docBop :: String -> Fixity -> Int -> Doc -> Doc -> Doc
docBop sM f p (Doc mopL sL) (Doc mopR sR) =
    Doc
      (MinOp opM)
      (sL' . showString sM . sR')
  where
    opM = Op (Prec p) f
    sL' = showParen (parens mopL opM LeftAssoc ) sL
    sR' = showParen (parens mopR opM RightAssoc) sR

infixl `docApp`

docApp :: Doc -> Doc -> Doc
docApp = docBop " " LeftFix 10

parens :: MinOp -> Op -> Assoc -> Bool
parens = \case
    NoOp    -> \_o _side -> False
    MinOp i -> \o  side  -> not $ noparens i o side

-- page 14
noparens :: Op -> Op -> Assoc -> Bool
noparens (Op pI fI) (Op pO fO) side =
    (pI > pO) ||
    case (fI, side) of
        (Prefix,   RightAssoc) -> True
        (LeftFix,  LeftAssoc ) -> pI == pO && fO == LeftFix
        (RightFix, RightAssoc) -> pI == pO && fO == RightFix
        (_,        NonAssoc  ) -> fI == fO
        _                      -> False
