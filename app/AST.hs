module AST where

import qualified Data.Text as T

type Name = T.Text

data AST
    = Ann AST AST
    | Nat Int
    | Prop
    | Hole
    | Forall Name (Maybe AST) AST
    | Var Name
    | App AST AST
    | Lam Name (Maybe AST) AST