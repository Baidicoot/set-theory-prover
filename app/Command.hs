module Command where
import Kernel

import Control.Monad.State
import Control.Monad.Except
import qualified Data.Map as M

{- simple imperative metalanguage for manipulating proofs -}
{- further plans: stepwise execution -}

data ImpError
    = UnknownVar Name

type ImpVarState = [M.Map Name CommandVal]
type Imp = ExceptT ImpError (State ImpVarState)

lookupVar :: Name -> Imp CommandVal
lookupVar n = do
    s <- get
    let lookupAll (m:ms) = case M.lookup n m of
            Just x -> pure x
            Nothing -> lookupAll ms
        lookupAll [] = throwError (UnknownVar n)
    lookupAll s

data Grammar

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