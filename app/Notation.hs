{-# LANGUAGE LambdaCase #-}
module Notation (makeProdRule,placeholderNonterminals) where

import ParserTypes
import Control.Monad

import qualified Data.Map as M
import qualified Data.Set as S

acceptsSymbols :: [NotationBinding] -> [Symbol]
acceptsSymbols (ExactToken t:tks) = Exact t:acceptsSymbols tks
acceptsSymbols (BindNonterminal s _:tks) = Nonterminal s:acceptsSymbols tks
acceptsSymbols [] = []

bindSymbols :: [NotationBinding] -> [SExpr] -> Maybe (M.Map Name SExpr)
bindSymbols (BindNonterminal s n:xs) (t:ss) = M.insert n t <$> bindSymbols xs ss
bindSymbols (_:xs) (_:ss) = bindSymbols xs ss
bindSymbols [] [] = pure M.empty
bindSymbols _ _ = Nothing

placeholderNonterminals :: [NotationBinding] -> S.Set Name
placeholderNonterminals = foldr (\case
    BindNonterminal s n -> S.insert s
    _ -> id) S.empty

substSExpr :: M.Map Name SExpr -> SExpr -> Maybe SExpr
substSExpr m (SExpr n xs) = SExpr n <$> mapM (substSExpr m) xs
substSExpr m (STok (Tok Placeholder n)) = M.lookup n m
substSExpr _ x = Just x

boundSymbols :: [NotationBinding] -> Either NotationError (S.Set Name)
boundSymbols (BindNonterminal _ n:xs) = do
    ss <- boundSymbols xs
    if n `S.member` ss then
        Left (MultiplyBound n)
    else
        Right (S.insert n ss)
boundSymbols (_:xs) = boundSymbols xs
boundSymbols _ = Right mempty

usedSymbols :: SExpr -> S.Set Name
usedSymbols (SExpr _ xs) = mconcat (fmap usedSymbols xs)
usedSymbols (STok (Tok Placeholder n)) = S.singleton n
usedSymbols _ = mempty

makeProdRule :: Name -> [NotationBinding] -> SExpr -> Either NotationError ProdRule
makeProdRule n ns s = do
    bound <- boundSymbols ns
    if S.null (usedSymbols s `S.difference` bound) then
        Right (bindSymbols ns >=> flip substSExpr s,acceptsSymbols ns)
    else
        Left (UnknownPlaceholder (usedSymbols s `S.difference` bound))