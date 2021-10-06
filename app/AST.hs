module AST where

import qualified Data.Text as T

type Name = T.Text

{-
SYNTAX:

<monotype> ::=
    | <var>
    | <monotype> → <monotype>
    | ℙ

<polytype> ::=
    | ∀ <var>* , <monotype>

<term> ::=
    | <var>
    | let <var> := <term> in <term>
    | let <var> : <polytype> := <term> in <term>
    | λ <var> , <term>
    | ∀ <var> , <term>
    | <term> ⟹ <term>

<proof> ::=
    | <var>
    | mod_pon <proof> <proof>
    | hole
-}

data Term
    = Forall Name (Maybe Type)

data AST
    = Ann AST AST
    | Nat Int
    | Prop
    | Hole
    | Forall Name (Maybe AST) AST
    | Var Name
    | App AST AST
    | Lam Name (Maybe AST) AST