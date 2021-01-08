module Command where
import TT
import Control.Monad.Except
import Data.List

data Command
    = Axiom String Exp
    | Define String Exp
    | Check Exp
    | Eval Exp
    | Print [String]
    | PrintAll
    deriving(Show)

data CommandOutput
    = DefAxiom String Val
    | Defined String Val Val
    | Checked Val
    | Evaluated Val
    | PrintCtx Ctx

instance Show CommandOutput where
    show (DefAxiom s v) = "Defined Axiom \'" ++ s ++ "\' : " ++ show v ++ ".\n"
    show (Defined s t v) = "Defined \'" ++ s ++ "\' : " ++ show t ++ "\n    := " ++ show v ++ ".\n"
    show (Checked v) = "Has type " ++ show v ++ ".\n"
    show (Evaluated v) = "Results in " ++ show v ++ ".\n"
    show (PrintCtx c) = intercalate "\n\n" (fmap (\(n,(t,d)) -> case d of
        Just d -> "Definition '" ++ n ++ "' : " ++ show t ++ "\n    := " ++ show d ++ "."
        Nothing -> "Axiom '" ++ n ++ "' : " ++ show t ++ ".") c) ++ "\n"

type CommandState = Ctx

docmd :: Command -> CommandState -> Res (CommandOutput,CommandState)
docmd (Axiom n e) ctx = do
    infer ctx e
    x <- eval ctx e
    pure (DefAxiom n x,(n,(x,Nothing)):ctx)
docmd (Define n e) ctx = do
    t <- infer ctx e
    x <- eval ctx e
    pure (Defined n t x,(n,(t,Just x)):ctx)
docmd (Check e) ctx = do
    t <- infer ctx e
    pure (Checked t,ctx)
docmd (Eval e) ctx = do
    infer ctx e
    x <- eval ctx e
    pure (Evaluated x,ctx)
docmd (Print ns) ctx = do
    defs <- mapM (\n -> case lookup n ctx of
        Just d -> pure (n,d)
        Nothing -> throwError ("identifier \"" ++ show n ++ "\" not defined")) ns
    pure (PrintCtx defs,ctx)
docmd PrintAll ctx = pure (PrintCtx (reverse ctx),ctx)