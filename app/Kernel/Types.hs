module Kernel.Types where

import qualified Data.Text as T
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader
import Data.Bifunctor

type Name = T.Text

type MetaVarTypes = M.Map Name Monotype
type TypeCtx = M.Map Name Polytype
type ObjCtx = M.Map Name (DeBrujin,Polytype)
type ThmCtx = M.Map Name Term

names :: [Name]
names = [T.pack (v:show n) | v <- ['A'..'Z'], n <- [0..]]

data ProofError
    = InfiniteType Name Monotype
    | MonotypeUnificationFail Monotype Monotype
    | PolytypeUnificationFail Polytype Polytype
    | NotInContext Name
    | ObjectUnificationFail DeBrujin DeBrujin
    | HigherOrderUnification DeBrujin DeBrujin
    | NonFunctionEval DeBrujin
    | NoEvalRule DeBrujin
    | DoesNotMatch Proof Term
    | NotForall Proof Term
    | UnknownAxiom Name
    | UnknownConst Name
    | UnscopedDeBrujin Int

type Infer = ExceptT ProofError (State ([Name], MetaVarTypes))

fresh :: Infer Name
fresh = do
    (ns, ms) <- get
    let (x:xs) = ns
    put (xs, ms)
    pure x

discoverMetaVar :: Name -> Infer Monotype
discoverMetaVar x = do
    t <- fmap TyVar fresh
    modify (second (M.insert x t))
    pure t

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
    | IntrosThm Name Proof
    | UniElim Proof Term
    | IntrosObj Name Proof
    | Axiom Name
    | Hole