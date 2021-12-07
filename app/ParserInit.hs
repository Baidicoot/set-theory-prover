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
        [(\[x,SExpr _ xs] -> Just (SExpr (T.append n "_LIST") (x:xs)),
            [Nonterminal n, Nonterminal (T.append n "_LIST")])
        ,(\[] -> Just (SExpr (T.append n "_LIST") []),
            [])])
    ,(n,
        [(\[_,STok (Tok _ k),SExpr _ xs,_] -> Just (SExpr k xs),
            [Exact (Tok Bracket "["), Any Ident, Nonterminal (T.append n "_LIST"), Exact (Tok Bracket "]")])
        ,(Just . head
            ,[Any Ident])
        ,(Just . head
            ,[AnyEscaped])])
    ]

grPROOF, grSORT, grPROP, grNOTATION, grIDENT :: Grammar
grPROOF = makeLispGrammar ntPROOF
grSORT = makeLispGrammar ntSORT
grPROP = makeLispGrammar ntPROP
grNOTATION = makeLispGrammar ntNOTATION
grIDENT = M.fromList [(ntIDENT, [(Just . head,[Any Ident])])]

grINIT :: Grammar
grINIT = M.unions [grPROOF, grSORT, grPROP, grNOTATION, grIDENT]