{-# LANGUAGE OverloadedStrings #-}
module ParserInit where

import ParserTypes

import qualified Data.Map as M
import qualified Data.Text as T

nt_PROOF, nt_SORT, nt_PROP, nt_NOTATION :: Name
nt_PROOF = "PROOF"
nt_SORT = "SORT"
nt_PROP = "PROP"
nt_NOTATION = "NOTATION"

makeLispGrammar :: Name -> Grammar
makeLispGrammar n = M.fromList
    [(T.append n "_LIST",
        [(\[x,SExpr _ xs] -> Just (SExpr (T.append n "_LIST") (x:xs)),
            [Nonterminal n, Nonterminal (T.append n "_LIST")])
        ,(\[] -> Just (SExpr (T.append n "_LIST") []),
            [])])
    ,(n,
        [(\[_,STok (Tok _ k),SExpr _ xs,_] -> Just (SExpr k xs),
            [Exact (Tok Bracket "("), Any Ident, Nonterminal (T.append n "_LIST"), Exact (Tok Bracket ")")])
        ,(Just . head
            ,[Any Ident])
        ,(Just . head
            ,[Any Symbol])])
    ]

gr_PROOF, gr_SORT, gr_PROP, gr_NOTATION :: Grammar
gr_PROOF = makeLispGrammar nt_PROOF
gr_SORT = makeLispGrammar nt_SORT
gr_PROP = makeLispGrammar nt_PROP
gr_NOTATION = makeLispGrammar nt_NOTATION

gr_INIT :: Grammar
gr_INIT = M.unions [gr_PROOF, gr_SORT, gr_PROP, gr_NOTATION]