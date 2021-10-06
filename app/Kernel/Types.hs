module Kernel.Types where

import qualified Data.Text as T
import qualified Data.Set as S

type Name = T.Text

names :: [Name]
names = [T.pack (v:show n) | v <- ['A'..'Z'], n <- [0..]]

data Term
    = Lam Name Monotype Term
    | Let Name Term Term
    | App Term Term
    | Var Name
    | Imp Term Term
    | Forall Name Monotype Term
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