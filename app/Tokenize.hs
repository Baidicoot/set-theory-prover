module Tokenize (tokenize) where

import Data.Char
import qualified Data.Text as T
import qualified Data.Vector as V
import Data.Maybe

newtype Tok = Tok T.Text

isBracketChar :: Char -> Bool
isBracketChar = flip elem "{}[]()"

isSpaceChar :: Char -> Bool
isSpaceChar = isSpace

isSymbolChar :: Char -> Bool
isSymbolChar c = not (isIdentChar c) && not (isSpaceChar c)

isIdentChar :: Char -> Bool
isIdentChar = isAlphaNum

eatToken :: T.Text -> Maybe (Tok,T.Text)
eatToken cs
    | T.length cs == 0 = Nothing
    | isIdentChar (T.head cs) = Just (Tok $ T.takeWhile isIdentChar cs, T.dropWhile isIdentChar cs)
    | isBracketChar (T.head cs) = Just (Tok $ T.take 1 cs, T.tail cs)
    | isSymbolChar (T.head cs) = Just (Tok $ T.takeWhile isSymbolChar cs, T.dropWhile isSymbolChar cs)
    | isSpaceChar (T.head cs) = eatToken (T.dropWhile isSpace cs)

tokenize :: T.Text -> V.Vector Tok
tokenize = V.unfoldr eatToken