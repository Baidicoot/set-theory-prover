module AST where

import qualified Data.Text as T

data AST
    = Ann AST AST
    | Nat Int
    | Prop
    | Hole
    | Forall T.Text (Maybe AST) AST
    | Var T.Text
    | App AST AST
    | Lam T.Text (Maybe AST) AST