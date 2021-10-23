{-# LANGUAGE OverloadedStrings #-}
module Tests where

import Parser
import ParserTypes
import qualified Data.Text as T
import qualified Data.Map as M

names :: [Name]
names = map (T.pack . ("X"++) . show) [0..] 

identAddition :: Grammar
identAddition = M.fromList [("X",
    [(mkExp,[Nonterminal "X",Exact (Tok Symbol "+"),Nonterminal "X"])
    ,(mkExp,[Any Ident])])]
    where
        mkExp = Just . SExpr "X"

additionNoLR = let (Right x,_) = elimLeftRec names identAddition in x

parseAdd = parse additionNoLR "X" "ab + ab + ab"