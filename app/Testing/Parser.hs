{-# LANGUAGE OverloadedStrings #-}
module Main where

import Test.Hspec

import ParserTypes
import Parser
import Tokenize
import ParserInit
import Elab
import Kernel.Types hiding(Name)
import Notation

import qualified Data.Text as T
import qualified Data.Vector as V
import qualified Data.Set as S
import qualified Data.Map as M

tokenizeSpec :: Spec
tokenizeSpec = describe "tokenizer" $ do
    it "can distinguish brackets" $
        tokenize mempty "(1 + 1)"
        == V.fromList
            [Tok Bracket "("
            , Tok Ident "1"
            , Tok Symbol "+"
            , Tok Ident "1"
            , Tok Bracket ")"]
    it "can distinguish keywords" $
        tokenize (S.singleton "kw")
            "abcd kw keyword"
        == V.fromList
            [Tok Ident "abcd"
            , Tok Keyword "kw"
            , Tok Ident "keyword"]
    it "can distinguish tokens" $
        tokenize mempty
            "1..2abcd2/46"
        == V.fromList
            [Tok Ident "1"
            , Tok Symbol ".."
            , Tok Ident "2abcd2"
            , Tok Symbol "/"
            , Tok Ident "46"]

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
                [(ConstructPartial
                    (Subst [Just "x"] (SExpr "fac" [SPlaceholder "x"])),
                    [Exact (Tok Symbol "!"), Nonterminal "A0"]),
                (Empty,
                    [])]),
            ("E",
                [(RewritePartial
                    (Subst [Just "x"] (SPlaceholder "x")),
                    [Any Ident, Nonterminal "A0"])])])

runParserStack :: [Name] -> S.Set Name -> Grammar -> Name -> T.Text -> Either ParseError SExpr
runParserStack ns kw g n t = do
    g' <- fst (elimLeftRec ns g)
    parse kw g' n t

parserStackSpec :: Spec
parserStackSpec = describe "parser stack" $ do
    it "can parse arithmetic expressions" $
        runParserStack names mempty (M.fromList
            [("expr",
                [(Subst [Nothing, Just "x", Nothing]
                    (SPlaceholder "x"),

                    [Exact $ Tok Bracket "("
                    , Nonterminal "expr"
                    , Exact $ Tok Bracket ")"]),

                (Subst [Just "x", Just "y", Just "z"]
                    (SExpr "binop"
                        [SPlaceholder "y"
                        , SPlaceholder "x"
                        , SPlaceholder "z"]),

                    [Nonterminal "expr"
                    , Any Symbol
                    , Nonterminal "expr"]),

                (Subst [Just "x"] (SPlaceholder "x"),
                    [Any Ident])])])

            "expr" "(1) + (2 * 3)"

        == Right (SExpr "binop"
            [STok $ Tok Symbol "+"
            , STok $ Tok Ident "1",
            SExpr "binop"
                [STok $ Tok Symbol "*"
                , STok $ Tok Ident "2"
                , STok $ Tok Ident "3"]])
    it "can parse s-expressions" $
        runParserStack names mempty (makeLispGrammar "EXPR")
            "EXPR" "[add 1 2 [mult 2 3] [mult [sub 3 4] 5]]"

        == Right (SExpr "add"
            [STok $ Tok Ident "1"
            , STok $ Tok Ident "2",
            SExpr "mult"
                [STok $ Tok Ident "2"
                , STok $ Tok Ident "3"],
            SExpr "mult"
                [SExpr "sub"
                    [STok $ Tok Ident "3"
                    , STok $ Tok Ident "4"],
                STok $ Tok Ident "5"]])
    it "can parse non-regular languages" $
        let g = M.fromList
                [("S",
                    [(Subst [Nothing,Just "x",Nothing,Nothing]
                        (SExpr "b" [SPlaceholder "x"]),

                        [Exact $ Tok Ident "b"
                        , Nonterminal "S"
                        , Exact $ Tok Ident "b"
                        , Exact $ Tok Ident "b"]),

                    (Subst [Just "x"]
                        (SExpr "as" [SPlaceholder "x"]),

                        [Nonterminal "A"])]),
                ("A",
                    [(Subst [Nothing, Just "x"]
                        (SExpr "a" [SPlaceholder "x"]),
                        
                        [Exact $ Tok Ident "a"
                        , Nonterminal "A"]),
                    
                    (Empty,
                        [])])]
        in
        (case runParserStack names mempty g
            "S"
            "b b a a a b b b b" of
            Right _ -> True
            Left _ -> False)
        && (case runParserStack names mempty g
            "S"
            "b b a a a b b b" of
            Right _ -> False
            Left _ -> True)
        && (case runParserStack names mempty g
            "S"
            "b b b" of
            Right _ -> True
            Left _ -> False)

notationSpec :: Spec
notationSpec = describe "notations" $ do
    it "can generate grammars from notations" $
        makeProdRule "expr"
            [BindNonterminal "expr" "x"
            ,ExactToken $ Tok Symbol "+"
            ,BindNonterminal "expr" "y"]
            
            (SExpr "add"
                [SPlaceholder "x"
                , SPlaceholder "y"])

        == Right (Subst [Just "x",Nothing,Just "y"]
            (SExpr "add"
                [SPlaceholder "x"
                , SPlaceholder "y"]),
            
            [Nonterminal "expr"
            , Exact $ Tok Symbol "+"
            , Nonterminal "expr"])

elabSpec :: Spec
elabSpec = describe "elaborator" $ do
    it "can elaborate proofs" $
        (parse mempty grINIT ntPROOF
            "[introThm x [forall y [prop] y] x]"
            >>=
                (fst . fst
                . runElaborator names mempty
                . elabProof))

        == Right (IntroThm "B0"
            (Forall "A0" Prop (Var "A0"))
            (Axiom "B0"))
    it "can elaborate propositions" $
        (parse mempty grINIT ntPROP
            "[forall x [prop] [imp x x]]"
            >>=
                (fst . fst
                . runElaborator names mempty
                . elabProp))

        == Right (Forall "D0" Prop
            (Imp (Var "D0") (Var "D0")))
    it "can elaborate sorts" $
        (parse mempty grINIT ntSORT
            "[func A [func [prop] B]]"
            >>=
                (fst . fst
                . runElaborator names mempty
                . elabMonotype))

        == Right (Arr
            (TyVar "A0")
            (Arr Prop (TyVar "B0")))

main :: IO ()
main = hspec $ do
    tokenizeSpec
    lrElimSpec
    parserStackSpec
    notationSpec
    elabSpec