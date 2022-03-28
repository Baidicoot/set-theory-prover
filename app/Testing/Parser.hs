{-# LANGUAGE OverloadedStrings #-}
module Main where

import Test.Hspec

import ParserTypes
import Parser
import Tokenize
import ParserInit
import Elab
import Kernel.Types (names)

import qualified Data.Text as T
import qualified Data.Vector as V
import qualified Data.Set as S
import qualified Data.Map as M

tokenizeSpec :: Spec
tokenizeSpec = describe "tokenizer" $ do
    it "can distinguish brackets" $
        tokenize mempty "(1 + 1)"
        == V.fromList [Tok Bracket "(", Tok Ident "1", Tok Symbol "+", Tok Ident "1", Tok Bracket ")"]
    it "can distinguish keywords" $
        tokenize (S.singleton "kw") "abcd kw keyword"
        == V.fromList [Tok Ident "abcd", Tok Keyword "kw", Tok Ident "keyword"]
    it "can distinguish identifiers and symbols" $
        tokenize mempty "1..2abcd2/46"
        == V.fromList [Tok Ident "1", Tok Symbol "..", Tok Ident "2abcd2", Tok Symbol "/", Tok Ident "46"]

lrElimSpec :: Spec
lrElimSpec = describe "left-recursion elimination" $ do
    it "eliminates left-recursion" $
        fst (elimLeftRec names $ M.fromList
            [("E",
                [(Subst [Just "x"] (SExpr "fac" [SPlaceholder "x"]),
                    [Nonterminal "E", Exact (Tok Symbol "!")]),
                (Subst [Just "x"] (SPlaceholder "x"),
                    [Any Ident])])])
        == Right (M.fromList
            [("A0",
                [(ConstructPartial (Subst [Just "x"] (SExpr "fac" [SPlaceholder "x"])),
                    [Exact (Tok Symbol "!"), Nonterminal "A0"]),
                (Empty,
                    [])]),
            ("E",
                [(RewritePartial (Subst [Just "x"] (SPlaceholder "x")),
                    [Any Ident, Nonterminal "A0"])])])

parserSpec :: Spec
parserSpec = describe "parser" $ do
    it "can parse s-expressions" $
        parse mempty (makeLispGrammar "EXPR") "EXPR"
            "[add 1 2 [mult 2 3] [mult [sub 3 4] 5]]"
        == Right (SExpr "add" [STok $ Tok Ident "1", STok $ Tok Ident "2",
            SExpr "mult" [STok $ Tok Ident "2", STok $ Tok Ident "3"],
            SExpr "mult"
                [SExpr "sub" [STok $ Tok Ident "3", STok $ Tok Ident "4"],
                STok $ Tok Ident "5"]])

runParserStack :: [Name] -> S.Set Name -> Grammar -> Name -> T.Text -> Either ParseError SExpr
runParserStack ns kw g n t = do
    g' <- fst (elimLeftRec ns g)
    parse kw g' n t

parserStackSpec :: Spec
parserStackSpec = describe "parser stack" $ do
    it "can parse arithmetic expressions" $
        runParserStack names mempty (M.fromList
            [("expr",
                [(Subst [Nothing, Just "x", Nothing] (SPlaceholder "x"),
                    [Exact $ Tok Bracket "(", Nonterminal "expr", Exact $ Tok Bracket ")"]),
                (Subst [Just "x", Just "y", Just "z"] (SExpr "binop"
                    [SPlaceholder "y", SPlaceholder "x", SPlaceholder "z"]),
                    [Nonterminal "expr", Any Symbol, Nonterminal "expr"]),
                (Subst [Just "x"] (SPlaceholder "x"),
                    [Any Ident])])])
            "expr"
            "(1) + (2 * 3)"
        == Right (SExpr "binop" [STok $ Tok Symbol "+", STok $ Tok Ident "1",
            SExpr "binop" [STok $ Tok Symbol "*", STok $ Tok Ident "2", STok $ Tok Ident "3"]])

main :: IO ()
main = hspec $ do
    tokenizeSpec
    lrElimSpec
    parserSpec
    parserStackSpec