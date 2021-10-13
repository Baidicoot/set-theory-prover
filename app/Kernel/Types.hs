module Kernel.Types where

import qualified Data.Text as T
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader

type Name = T.Text

type MetaVarTypes = M.Map Name Monotype
type TypeCtx = M.Map Name Polytype

names :: [Name]
names = [T.pack (v:show n) | v <- ['A'..'Z'], n <- [0..]]

data ProofError
    = InfiniteType Name Monotype
    | TypeUnificationFail Monotype Monotype
    | NotInContext Name
    | ObjectUnificationFail DeBrujin DeBrujin
    | HigherOrderUnification DeBrujin DeBrujin
    | NonFunctionEval DeBrujin
    | NoEvalRule DeBrujin
    | DoesNotMatch Proof Term
    | UnknownAxiom Name
    | UnknownConst Name

type Infer = ReaderT TypeCtx (ExceptT ProofError (State ([Name], MetaVarTypes)))

fresh :: Infer Name
fresh = do
    (ns, ms) <- get
    let (x:xs) = ns
    put (xs, ms)
    pure x

discoverMetaVar :: Name -> Infer Monotype
discoverMetaVar x = do
    t <- fmap TyVar fresh
    modify (\(ns,ms) -> (ns,M.insert x t ms))

data DeBrujin
    = DLam DeBrujin
    | DApp DeBrujin DeBrujin
    | DVar Int
    | DAll Monotype DeBrujin
    | DImp DeBrujin DeBrujin
    | DConst Name
    | DHole Name
    deriving(Eq)

data Term
    = Lam Name Term
    | Let Name Term Term
    | App Term Term
    | Var Name
    | Imp Term Term
    | Forall Name Monotype Term
    | Const Name
    | MetaVar Name
    deriving(Eq)

data Monotype
    = Arr Monotype Monotype
    | TyVar Name
    | ConstTy Name
    | Prop
    deriving(Eq)

data Polytype
    = Polytype (S.Set Name) Monotype
    deriving(Eq)

data Proof
    = ModPon Proof Proof
    | UniElim Proof Term
    | Axiom Name
    | Hole