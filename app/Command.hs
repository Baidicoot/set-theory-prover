module Command where
import Kernel

import Data.Identity

{- simple imperative metalanguage for manipulating proofs -}
{- further plans: stepwise execution -}

type Imp = Identity

data CommandVal
    = Proof Proof
    | Prop Term
    | Int Int

data CommandExpr
    = Lit CommandVal
    | Var Name
    | Op ([CommandExpr] -> Imp CommandVal) [CommandExpr]
    | Call Name [CommandExpr]

data CommandStmt
    = While CommandExpr [CommandStmt]
    | Switch CommandExpr [(CommandVal, [CommandStmt])]
    | Expr CommandExpr
    | Assign Name CommandExpr
    | Refine CommandExpr

data Command
    = Notation Grammar
    | NewTactic [Name] [CommandStmt]
    | BeginProof Name Term
    | Tactic CommandStmt
    | EndProof

evalExpr :: CommandExpr -> Imp CommandVal

evalStmt :: CommandStmt -> Imp CommandStmt

evalCommand :: Command -> Imp ()