{-# LANGUAGE OverloadedStrings #-}
module ParserInit where

import ParserTypes

import qualified Data.Map as M
import qualified Data.Text as T

ntPROOF, ntSORT, ntPROP, ntNOTATION, ntIDENT :: Name
ntPROOF = "PROOF"
ntSORT = "SORT"
ntPROP = "PROP"
ntNOTATION = "NOTATION"
ntIDENT = "IDENT"

makeLispGrammar :: Name -> Grammar
makeLispGrammar n = M.fromList
    [(T.append n "_LIST",
        [(ListCons (T.append n "_LIST"),
            [Nonterminal n, Nonterminal (T.append n "_LIST")])
        ,(ListNull (T.append n "_LIST"),
            [])])
    ,(n,
        [(RawSExpr,
            [Exact (Tok Bracket "["), Any Ident, Nonterminal (T.append n "_LIST"), Exact (Tok Bracket "]")])
        ,(Single
            ,[Any Ident])
        ,(Single
            ,[AnyEscaped])])
    ]

grPROOF, grSORT, grPROP, grNOTATION, grIDENT :: Grammar
grPROOF = makeLispGrammar ntPROOF
grSORT = makeLispGrammar ntSORT
grPROP = makeLispGrammar ntPROP
grNOTATION = makeLispGrammar ntNOTATION
grIDENT = M.fromList [(ntIDENT, [(Single,[Any Ident])])]

grINIT :: Grammar
grINIT = M.unions [grPROOF, grSORT, grPROP, grNOTATION, grIDENT]