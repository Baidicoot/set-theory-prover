{-# LANGUAGE LambdaCase #-}
module Notation (makeProdRule,placeholderNonterminals,addPlaceholders) where

import ParserTypes
import Control.Monad

import qualified Data.Map as M
import qualified Data.Set as S

acceptsSymbols :: [NotationBinding] -> [Symbol]
acceptsSymbols (ExactToken (Tok (Escaped k) t):tks) = Exact (Tok k t):acceptsSymbols tks
acceptsSymbols (ExactToken t:tks) = Exact t:acceptsSymbols tks
acceptsSymbols (BindNonterminal s _:tks) = Nonterminal s:acceptsSymbols tks
acceptsSymbols [] = []

bindSymbols :: [NotationBinding] -> [Maybe Name]
bindSymbols (BindNonterminal _ n:xs) = Just n:bindSymbols xs
bindSymbols (_:xs) = Nothing:bindSymbols xs
bindSymbols [] = []

placeholderNonterminals :: [NotationBinding] -> S.Set Name
placeholderNonterminals = foldr (\case
    BindNonterminal s n -> S.insert s
    _ -> id) S.empty

boundSymbols :: [NotationBinding] -> Either ParseError (S.Set Name)
boundSymbols (BindNonterminal _ n:xs) = do
    ss <- boundSymbols xs
    if n `S.member` ss then
        Left (MultiplyBound n)
    else
        Right (S.insert n ss)
boundSymbols (_:xs) = boundSymbols xs
boundSymbols _ = Right mempty

addPlaceholders :: S.Set Name -> Grammar -> Grammar
addPlaceholders ps = M.mapWithKey (\n gs ->
    if n `S.member` ps then
        (Placeholder,[Any (Escaped Ident)]):gs
    else gs)

usedSymbols :: SExpr -> S.Set Name
usedSymbols (SExpr _ xs) = mconcat (fmap usedSymbols xs)
usedSymbols (STok (Tok (Escaped Ident) n)) = S.singleton n
usedSymbols _ = mempty

makeProdRule :: Name -> [NotationBinding] -> SExpr -> Either ParseError ProdRule
makeProdRule n ns s = do
    bound <- boundSymbols ns
    if S.null (usedSymbols s `S.difference` bound) then
        Right (Subst (bindSymbols ns) s,acceptsSymbols ns)
    else
        Left (UnknownPlaceholder (usedSymbols s `S.difference` bound))