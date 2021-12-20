{-# LANGUAGE DeriveGeneric #-}
module Kernel.Types where

import qualified Data.Text as T
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader
import Data.Bifunctor

import GHC.Generics (Generic)
import Data.Binary (Binary)

type Name = T.Text

type MetaVarTypes = M.Map Name Monotype
type TypeCtx = M.Map Name Polytype
type ObjCtx = M.Map Name Polytype
type ThmCtx = M.Map Name Term
type DefCtx = M.Map Name Term

type Ctx = (ThmCtx,ObjCtx,DefCtx)

names :: [Name]
names = [T.pack (v:show n) | v <- ['A'..'Z'], n <- [0..]]

data ProofErrorType
    = InfiniteType Name Monotype
    | MonotypeUnificationFail Monotype Monotype
    | PolytypeUnificationFail Polytype Polytype
    | NotInContext Name
    | ObjectUnificationFail Term Term
    | HigherOrderUnification Term Term
    | NonFunctionEval Term
    | NoEvalRule Term
    | DoesNotMatch Proof Term
    | NotForall Proof Term
    | UnknownAxiom Name
    | UnscopedDeBrujin Int
    | CantInferHigherOrder Name Proof
    deriving(Show)

data ProofError = ProofError ProofErrorType [String] deriving(Show)

type Infer = ExceptT ProofError (State ([Name], MetaVarTypes))

throwErr :: ProofErrorType -> Infer a
throwErr = throwError . flip ProofError []

traceErr :: String -> Infer a -> Infer a
traceErr n f = f `catchError` (\(ProofError e t) -> throwError (ProofError e (n:t)))

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

runInfer :: ([Name], MetaVarTypes) -> Infer a -> (Either ProofError a, ([Name], MetaVarTypes))
runInfer s = flip runState s . runExceptT

fillHole :: Proof -> Proof -> Maybe Proof
fillHole Hole p = pure p
fillHole (ModPon a b) p = case fillHole a p of
    Just a' -> pure (ModPon a' b)
    Nothing -> ModPon a <$> fillHole b p
fillHole (IntroThm n t a) p = IntroThm n t <$> fillHole a p
fillHole (IntroObj n t a) p = IntroObj n t <$> fillHole a p
fillHole (UniElim a t) p = flip UniElim t <$> fillHole a p
fillHole _ _ = Nothing

data Term
    = Lam Name Term
    | Let Name Term Term
    | App Term Term
    | Imp Term Term
    | Forall Name Monotype Term
    | MetaVar Name
    | Var Name
    deriving(Eq,Show,Generic)

instance Binary Term

data Monotype
    = Arr Monotype Monotype
    | TyVar Name
    | ConstTy Name
    | Prop
    deriving(Eq,Show,Generic)

instance Binary Monotype

data Polytype
    = Polytype (S.Set Name) Monotype
    deriving(Eq,Show,Generic)

instance Binary Polytype

data Proof
    = ModPon Proof Proof
    | IntroThm Name Term Proof
    | UniElim Proof Term
    | IntroObj Name Monotype Proof
    | Axiom Name
    | Param Name
    | Hole
    deriving(Show,Generic)

instance Binary Proof