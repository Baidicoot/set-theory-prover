module Command where
import Kernel

import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Map as M

{- will just use lua for cool purposes -}
{- simple imperative metalanguage for manipulating proofs -}
{- further plans: stepwise execution -}

data ImpError
    = UnknownVar Name
    | NoFrame Name

type ImpVarState = [M.Map Name CommandVal]
type ImpFunctions = [M.Map Name CommandFunc]
type Imp = ExceptT ImpError (ReaderT ImpFunctions (State ImpVarState))

lookupVar :: Name -> Imp CommandVal
lookupVar n = do
    m <- get
    case m of
        (m:_) -> case M.lookup n m of
            Just v -> pure v
            Nothing -> throwError (UnknownVar n)
        [] -> throwError (NoFrame n)

lookupFunc :: Name -> Imp CommandFunc
lookupFunc n = do
    m <- ask
    case M.lookup n m of
        Just f ->

data Grammar

data CommandVal
    = Proof Proof
    | Prop Term
    | Int Int
    | Label Name

data CommandExpr
    = Lit CommandVal
    | Var Name
    | Op ([CommandExpr] -> Imp CommandVal) [CommandExpr]
    | Call CommandExpr [CommandExpr]

data CommandStmt
    = While CommandExpr [CommandStmt]
    | Switch CommandExpr [(CommandVal, [CommandStmt])]
    | Expr CommandExpr
    | Assign Name CommandExpr
    | Refine CommandExpr
    | Return CommandExpr

data CommandFunc = Func [Name] [CommandStmt]

data Command
    = Notation Grammar
    | NewTactic [Name] [CommandStmt]
    | BeginProof Name Term
    | Tactic CommandStmt
    | EndProof

evalExpr :: CommandExpr -> Imp CommandVal
evalExpr (Lit e) = pure e
evalExpr (Var n) = lookupVar n
evalExpr (Op fn xs) = mapM evalExpr xs >>= fn
evalExpr (Call n xs) = mapM 

evalStmt :: CommandStmt -> Imp CommandStmt

evalFunc :: CommandFunc -> [CommandVal] -> Imp CommandVal

evalCommand :: Command -> Imp ()