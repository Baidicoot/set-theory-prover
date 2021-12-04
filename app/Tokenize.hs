module Tokenize (tokenize) where

import Data.Char
import qualified Data.Text as T
import qualified Data.Vector as V
import Data.Maybe
import ParserTypes

isBracketChar :: Char -> Bool
isBracketChar = flip elem "{}[]()"

isEscapeChar :: Char -> Bool
isEscapeChar = flip elem "`"

isSpaceChar :: Char -> Bool
isSpaceChar = isSpace

isSymbolChar :: Char -> Bool
isSymbolChar c = not (isIdentChar c) && not (isSpaceChar c)

isIdentChar :: Char -> Bool
isIdentChar = isAlphaNum

eatToken :: T.Text -> Maybe (Tok,T.Text)
eatToken cs
    | T.length cs == 0 = Nothing
    | isEscapeChar (T.head cs) = Just (Tok Placeholder $ T.takeWhile isIdentChar (T.tail cs), T.dropWhile isIdentChar (T.tail cs))
    | isIdentChar (T.head cs) = Just (Tok Ident $ T.takeWhile isIdentChar cs, T.dropWhile isIdentChar cs)
    | isBracketChar (T.head cs) = Just (Tok Bracket $ T.take 1 cs, T.tail cs)
    | isSymbolChar (T.head cs) = Just (Tok Symbol $ T.takeWhile isSymbolChar cs, T.dropWhile isSymbolChar cs)
    | isSpaceChar (T.head cs) = eatToken (T.dropWhile isSpace cs)
eatToken _ = Nothing

tokenize :: T.Text -> V.Vector Tok
tokenize = V.unfoldr eatToken