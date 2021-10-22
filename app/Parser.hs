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

import Data.List (partition)

{- https://en.wikipedia.org/wiki/Left_recursion#Removing_all_left_recursion -}
{- https://www.csd.uwo.ca/~mmorenom/CS447/Lectures/Syntax.html/node8.html -}

{- left-recursion removal -}

fresh :: ParserGenerator Name
fresh = do
    ns <- get
    let (x:xs) = ns
    put xs
    pure x

{- need to 'bookkeep' -}

rewritePartial :: TreeRewrite -> TreeRewrite
rewritePartial f xs@(_:_) =
    let (xs',x) = (init xs,last xs)
    in case x of
        Partial g ys -> (g . (++ys) . (:[])) =<< f xs'
        _ -> Nothing
rewritePartial _ _ = Nothing

constructPartial :: TreeRewrite -> TreeRewrite
constructPartial f = Just . Partial (rewritePartial f)

rmDirectLR :: Name -> [ProdRule] -> ParserGenerator Grammar
rmDirectLR a prods =
    let (lrec,nonrec) = partition (\case
            Prod _ (Nonterminal x:_) -> x == a
            Prod _ _ -> False) prods
    in case lrec of
        [] -> pure [(a,nonrec)]
        _ -> do
            a' <- fresh
            let lrec' =
                    fmap (\(Prod f (_:xs)) ->
                        Prod (constructPartial f) (xs ++ [Nonterminal a'])) lrec
                    ++[emptyRule]
            let nonrec' =
                    fmap (\(Prod f xs) ->
                        Prod (rewritePartial f) (xs ++ [Nonterminal a'])) nonrec
            pure [(a,nonrec'),(a',lrec')]

combineRewrites :: Int -> TreeRewrite -> TreeRewrite -> TreeRewrite
combineRewrites l f g xs = do
    x <- g (take l xs)
    f (x:drop l xs)

reduceFirstNonterminal :: Grammar -> ProdRule -> ParserGenerator [ProdRule]
reduceFirstNonterminal g (Prod f (Nonterminal x:xs)) =
    case lookup x g of
        Just ps -> pure (map (\(Prod g ys) -> Prod (combineRewrites (length ys) f g) (ys ++ xs)) ps)
        Nothing -> pure [Prod f (Nonterminal x:xs)]
reduceFirstNonterminal _ x = pure [x]

rmIndirectLR :: Grammar -> Grammar -> ParserGenerator Grammar
rmIndirectLR done [] = pure done
rmIndirectLR done ((a,prods):gs) = do
    prods' <- concat <$> mapM (reduceFirstNonterminal done) prods
    done' <- rmDirectLR a prods'
    rmIndirectLR (done' ++ done) gs

{- recursive descent parser -}

next :: Parser Tok
next = do
    v <- get
    case V.null v of
        True -> throwError EndOfInput
        False -> put (V.tail v) >> pure (V.head v)

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
parseRule (Prod f xs) = do
    toks <- mapM match xs
    case f toks of
        Just s -> pure s
        Nothing -> throwError (NoSExpr toks)

parseNonterminal :: Name -> Parser SExpr
parseNonterminal n = do
    g <- ask
    case lookup n g of
        Just gs -> do
            v <- get
            alternatives v (map parseRule gs)
        Nothing -> throwError (NotNonterminal n)

{- everything -}

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
elimLeftRec xs g = runParserGenerator xs (rmIndirectLR [] g)