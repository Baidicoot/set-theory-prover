{-# LANGUAGE OverloadedLists #-}

module Tokenize (tokenize) where

import Data.Char
import qualified Data.Text as T
import qualified Data.Vector as V
import Data.Maybe

newtype Tok = Tok T.Text

isBracketChar :: Char -> Bool
isBracketChar = flip elem "{}[]()"

isSpaceChar :: Char -> Bool
isSymbolChar = isSpace

isSymbolChar :: Char -> Bool
isSymbolChar c = not (isIdentChar c) && not (isSpaceChar c)

isIdentChar :: Char -> Bool
isIdentChar = isAlphaNum

eatToken :: T.Text -> Maybe (Tok,T.Text)
eatToken [] = Nothing
eatToken cs@(c:_) | isIdentChar c = Just (Tok $ T.takeWhile isIdentChar cs, T.dropWhile isIdentChar cs)
eatToken cs@(c:_) | isBracketChar c = Just (Tok $ T.head cs, T.tail cs)
eatToken cs@(c:_) | isSymbolChar c = Just (Tok $ T.takeWhile isSymbolChar cs, T.dropWhile isSymbolChar cs)
eatToken cs@(c:_) | isSpaceChar c = eatToken (T.dropWhile isSpace cs)

tokenize :: Text -> V.Vector Tok
tokenize = V.unfoldr eatToken