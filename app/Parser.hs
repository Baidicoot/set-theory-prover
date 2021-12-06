{-# LANGUAGE LambdaCase #-}
module Parser (parse, elimLeftRec) where

import ParserTypes
import Tokenize

import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Vector as V
import qualified Data.Text as T

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Data.Foldable (foldlM)

import Data.Bifunctor (bimap)
import Data.List (partition)

{- https://en.wikipedia.org/wiki/Left_recursion#Removing_all_left_recursion -}
{- https://www.csd.uwo.ca/~mmorenom/CS447/Lectures/Syntax.html/node8.html -}

fresh :: ParserGenerator Name
fresh = do
    ns <- get
    let (x:xs) = ns
    put xs
    pure x

{- tree rewrites to preserve structure after removal of LR -}

rewritePartial :: TreeRewrite -> TreeRewrite
rewritePartial f xs@(_:_) =
    let (xs',x) = (init xs,last xs)
    in case x of
        Partial g ys -> g . (++ys) . (:[]) =<< f xs'
        _ -> Nothing
rewritePartial _ _ = Nothing

constructPartial :: TreeRewrite -> TreeRewrite
constructPartial f = Just . Partial (rewritePartial f)

combineRewrites :: Int -> TreeRewrite -> TreeRewrite -> TreeRewrite
combineRewrites l f g xs = do
    x <- g (take l xs)
    f (x:drop l xs)

append :: a -> [a] -> [a]
append x = (++[x])

{- LR removal -}

rmDirectLR :: Name -> [ProdRule] -> ParserGenerator Grammar
rmDirectLR a prods =
    let (lrec,nonrec) = partition (\case
            (_,Nonterminal x:_) -> x == a
            _ -> False) prods
    in  if null lrec then
            pure (M.singleton a nonrec)
        else do
            a' <- fresh
            let lrec' =
                    map (bimap constructPartial (append (Nonterminal a') . tail)) lrec
            let nonrec' =
                    map (bimap rewritePartial (append (Nonterminal a'))) nonrec
            pure (M.fromList [(a,nonrec'),(a',append emptyRule lrec')])

reduceFirstNonterminal :: Grammar -> ProdRule -> ParserGenerator [ProdRule]
reduceFirstNonterminal g (f,Nonterminal x:xs) =
    case M.lookup x g of
        Just ps -> pure (map (\(g,ys) -> (combineRewrites (length ys) f g,ys++xs)) ps)
        Nothing -> pure [(f,Nonterminal x:xs)]
reduceFirstNonterminal _ x = pure [x]

rmIndirectLR :: Grammar -> ParserGenerator Grammar
rmIndirectLR = foldlM go M.empty . M.toList
    where
        go done (a,prods) = fmap (M.union done) $
            rmDirectLR a . concat =<< mapM (reduceFirstNonterminal done) prods

{- recursive descent parser -}

next :: Parser Tok
next = do
    v <- get
    if V.null v then
        throwError EndOfInput
    else
        put (V.tail v) >> pure (V.head v)

peek :: Parser Tok
peek = do
    v <- get
    if V.null v then
        throwError EndOfInput
    else
        pure (V.head v)

alternatives :: V.Vector Tok -> [Parser a] -> Parser a
alternatives _ [g] = g
alternatives v (f:gs) = do
    catchError f (\_ -> put v >> alternatives v gs)
alternatives _ [] = throwError EmptyAlternative

matchTerminal :: Symbol -> Tok -> Parser Tok
matchTerminal (Exact t) t' | t == t' = pure t
matchTerminal (Any k) t@(Tok k' _) | k == k' = pure t
matchTerminal (Nonterminal x) _ = throwError (NotTerminal x)
matchTerminal s t = throwError (NoMatch s t)

match :: Symbol -> Parser SExpr
match (Nonterminal x) = parseNonterminal x
match t = do
    t' <- next
    STok <$> matchTerminal t t'

parseRule :: ProdRule -> Parser SExpr
parseRule (f,xs) = do
    toks <- mapM match xs
    case f toks of
        Just s -> pure s
        Nothing -> throwError (NoSExpr toks)

parseNonterminal :: Name -> Parser SExpr
parseNonterminal n = do
    g <- ask
    case M.lookup n g of
        Just gs -> do
            v <- get
            alternatives v (map parseRule gs)
        Nothing -> throwError (NotNonterminal n)

{- everything wrapped up -}

runParserGenerator :: [Name] -> ParserGenerator a -> (Either ParseError a, [Name])
runParserGenerator s = flip runState s . runExceptT

runParser :: V.Vector Tok -> Grammar -> Parser a -> (Either ParseError a, V.Vector Tok)
runParser s r = flip runState s . flip runReaderT r . runExceptT

parse :: Grammar -> Name -> T.Text -> Either ParseError SExpr
parse g n t =
    let (a,b) = runParser (tokenize t) g (parseNonterminal n)
    in if not (V.null b) then
            throwError (LeftoverInput b)
        else a

elimLeftRec :: [Name] -> Grammar -> (Either ParseError Grammar, [Name])
elimLeftRec xs g = runParserGenerator xs (rmIndirectLR g)