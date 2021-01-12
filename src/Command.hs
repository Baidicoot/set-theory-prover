module Command where
import TT
import Graph
import Control.Monad.Except
import Control.Monad.Writer
import Data.List

data Command
    = Axiom String Exp
    | Define String Exp
    | Check Exp
    | Eval Exp
    | Print [String]
    | PrintAll
    | PrintUniverses
    | CheckConstraints [Constraint]

data CommandOutput
    = DefAxiom String Val
    | Defined String Val Val
    | Checked Val
    | Evaluated Val
    | PrintCtx Ctx
    | PrintGraph OrderingGraph
    | Success

type Cmd = ExceptT String (Writer [CommandOutput])

runCmd :: Cmd a -> (Either String a,[CommandOutput])
runCmd = runWriter . runExceptT

instance Show CommandOutput where
    show (DefAxiom s v) = "Defined Axiom \'" ++ s ++ "\' : " ++ show v ++ ".\n"
    show (Defined s t v) = "Defined \'" ++ s ++ "\' : " ++ show t ++ "\n    := " ++ show v ++ ".\n"
    show (Checked v) = "Has type " ++ show v ++ ".\n"
    show (Evaluated v) = "Results in " ++ show v ++ ".\n"
    show (PrintCtx c) = intercalate "\n\n" (fmap (\(n,(t,d)) -> case d of
        Just d -> "Definition '" ++ n ++ "' : " ++ show t ++ "\n    := " ++ show d ++ "."
        Nothing -> "Axiom '" ++ n ++ "' : " ++ show t ++ ".") c) ++ "\n"
    show (PrintGraph g) = showOrdering g
    show Success = "Ok.\n"

type CommandState = (Ctx,OrderingGraph,UniverseID)

inCtx :: Name -> Ctx -> Bool
inCtx n ctx = n `elem` fmap fst ctx

emptyState :: CommandState
emptyState = ([],[],0)

docmd :: Command -> CommandState -> Cmd CommandState
docmd (Axiom n _) (ctx,ord,u) | n `inCtx` ctx = throwError ("\"" ++ n ++ "\" is already defined.")
docmd (Define n _) (ctx,ord,u) | n `inCtx` ctx = throwError ("\"" ++ n ++ "\" is already defined.")
docmd (Axiom n e) (ctx,ord,u) = do
    ((_,ord),u) <- liftEither (runRes u (inferWithOrderCheck ctx ord e))
    (x,u) <- liftEither (runRes u (eval ctx e))
    tell [DefAxiom n x]
    pure ((n,(x,Nothing)):ctx,ord,u)
docmd (Define n e) (ctx,ord,u) = do
    ((t,ord),u) <- liftEither (runRes u (inferWithOrderCheck ctx ord e))
    (x,u) <- liftEither (runRes u (eval ctx e))
    tell [Defined n t x]
    pure ((n,(t,Just x)):ctx,ord,u)
docmd (Check e) (ctx,ord,u) = do
    ((t,_),_) <- liftEither (runRes u (inferWithOrderCheck ctx ord e))
    tell [Checked t]
    pure (ctx,ord,u)
docmd (Eval e) (ctx,ord,u) = do
    (_,u') <- liftEither (runRes u (inferWithOrderCheck ctx ord e))
    (x,_) <- liftEither (runRes u' (eval ctx e))
    tell [Evaluated x]
    pure (ctx,ord,u)
docmd (Print ns) (ctx,ord,u) = do
    defs <- mapM (\n -> case lookup n ctx of
        Just d -> pure (n,d)
        Nothing -> throwError ("Identifier \"" ++ show n ++ "\" is not defined.")) ns
    tell [PrintCtx defs]
    pure (ctx,ord,u)
docmd PrintAll (ctx,ord,u) = tell [PrintCtx ctx] >> pure (ctx,ord,u)
docmd PrintUniverses (ctx,ord,u) = tell [PrintGraph ord] >> pure (ctx,ord,u)
docmd (CheckConstraints cs) (ctx,ord,u) =
    liftEither (runRes u (appConstraints ord cs)) >> tell [Success] >> pure (ctx,ord,u)