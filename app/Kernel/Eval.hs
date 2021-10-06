module Kernel.Eval where

import Kernel.Logic

import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Set as S

{-
Kernel.Eval - equality checking between normal forms
-}
data DeBrujin
    = DLam DeBrujin
    | DApp DeBrujin DeBrujin
    | DVar Int
    | DAll DeBrujin
    | DImp DeBrujin DeBrujin
    | DConst Name
    | DHole Name
    deriving(Eq)

data EvalError
    = UnificationFail DeBrujin DeBrujin
    | HigherOrderUnification DeBrujin DeBrujin

type UniSubst = M.Map Name DeBrujin
type Evaluator = Except EvalError 

unify :: DeBrujin -> DeBrujin -> Evaluator UniSubst
unify x y | x == y = pure M.empty
unify (DLam a) (DLam b) = unify a b
unify (DAll a) (DAll b) = unify a b
unify (DImp a b) (DImp c d) = do
    

whnf :: DeBrujin -> DeBrujin