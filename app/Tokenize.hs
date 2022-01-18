module Tokenize (tokenize) where

import Data.Char
import qualified Data.Text as T
import qualified Data.Set as S
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
isIdentChar c = isAlphaNum c || elem c "_"

eatToken :: Keywords -> T.Text -> Maybe (Tok,T.Text)
eatToken kw cs
    | T.length cs == 0 = Nothing
    | isEscapeChar (T.head cs) = case eatToken kw (T.tail cs) of
        Just (Tok k t,cs') -> Just (Tok (Escaped k) t,cs')
        Nothing -> Nothing
        --Just (Tok (Escaped Ident) $ T.takeWhile isIdentChar (T.tail cs), T.dropWhile isIdentChar (T.tail cs))
    | isIdentChar (T.head cs) =
        let t = T.takeWhile isIdentChar cs
            r = T.dropWhile isIdentChar cs
        in if t `S.member` kw then
            Just (Tok Keyword t, r)
        else
            Just (Tok Ident t, r)
    | isBracketChar (T.head cs) = Just (Tok Bracket $ T.take 1 cs, T.tail cs)
    | isSymbolChar (T.head cs) = Just (Tok Symbol $ T.takeWhile isSymbolChar cs, T.dropWhile isSymbolChar cs)
    | isSpaceChar (T.head cs) = eatToken kw (T.dropWhile isSpace cs)
eatToken _ _ = Nothing

tokenize :: Keywords -> T.Text -> V.Vector Tok
tokenize = V.unfoldr . eatToken