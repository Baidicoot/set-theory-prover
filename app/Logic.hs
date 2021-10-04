module Logic where

import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Set as S

{-
Logic.hs - DATATYPES
====================
NEW CHANGES: MERGE PROP AND TERM

Term:
    for set theories, includes sets and higher-order functions on sets
    valid terms are those valid in HM type systems
Types:
    each term has a type:
        - (λx: A. M : B) : A → B
        - ((M: A → B) (N: A)) : B
        - (let x = (M: A) in (N: B)) : B, but (x : ∀X̅. A), where X̅ ∈ A
        - constants and variables are typed based of the typing context
    this is essentially the Hindley-Milner type system
Prop:
    the type of logical propositions:
        * A ⇒ B
                - implication
        * ∀x. A
                - quantification over terms
        * R(A,B,C,x,y,z)
                - relations/connectives over propositions and terms
Proof:
    the type of proofs of propositions
    a proof consists of a collection of axioms connected using elimination rules
-}

type Name = T.Text

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