module Command where
import TT
import Graph
import Control.Monad.Except
import Control.Monad.Writer

data Command
    = Axiom String Exp
    | Define String Exp
    | Redex [Var] [Exp] Exp Exp
    | Check Exp
    | Eval Exp
    | Print [String]
    | PrintAll
    | PrintUniverses
    | CheckConstraints [Constraint]
    | Match Exp Exp

data CommandOutput
    = DefAxiom String Val
    | Defined String Val Val
    | DefRedex [Var] Val Val
    | Checked Val
    | Evaluated Val
    | PrintCtx Ctx
    | PrintGraph OrderingGraph
    | Success

type Cmd = ExceptT String (Writer [CommandOutput])

trace :: String -> Cmd a -> Cmd a
trace s r = catchError r (\e -> throwError (e ++ "\n" ++ s))

runCmd :: Cmd a -> (Either String a,[CommandOutput])
runCmd = runWriter . runExceptT

instance Show CommandOutput where
    show (DefAxiom s v) = "Defined Axiom \'" ++ s ++ "\' : " ++ show v ++ ".\n"
    show (Defined s t v) = "Defined \'" ++ s ++ "\' : " ++ show t ++ "\n    := " ++ show v ++ ".\n"
    show (DefRedex vs u v) = "Defined Reduction [" ++ unwords (fmap show vs) ++ "] (" ++ showVal vs u ++ ")\n    := " ++ showVal vs v ++ ".\n"
    show (Checked v) = "Has type " ++ show v ++ ".\n"
    show (Evaluated v) = "Results in " ++ show v ++ ".\n"
    show (PrintCtx c) = show c
    show (PrintGraph g) = showOrdering g
    show Success = "Ok.\n"

type CommandState = (Ctx,OrderingGraph,UniverseID)

inCtx :: Name -> Ctx -> Bool
inCtx n ctx = n `elem` ctxNames ctx

emptyState :: CommandState
emptyState = ([],[],0)

marksFree :: [(Int,Val)] -> Exp -> Exp
marksFree ((i,v):vs) e = marksFree vs (markFree i v e)
marksFree _ e = e

docmd :: Command -> CommandState -> Cmd CommandState
docmd (Axiom n _) (ctx,ord,u) | n `inCtx` ctx = throwError ("\"" ++ n ++ "\" is already defined.")
docmd (Define n _) (ctx,ord,u) | n `inCtx` ctx = throwError ("\"" ++ n ++ "\" is already defined.")
docmd (Axiom n e) (ctx,ord,u) = do
    ((_,ord),u) <- liftEither (runRes u (inferWithOrderCheck ctx ord e))
    (x,u) <- liftEither (runRes u (eval ctx e))
    tell [DefAxiom n x]
    pure (CtxAxiom n x:ctx,ord,u)
docmd (Define n e) (ctx,ord,u) = do
    ((t,ord),u) <- liftEither (runRes u (inferWithOrderCheck ctx ord e))
    (x,u) <- liftEither (runRes u (eval ctx e))
    tell [Defined n t x]
    pure (CtxDelta n t x:ctx,ord,u)
docmd (Redex vrs vs i j) (ctx,ord,u) = do
    (vs,u,ord) <- chkAll u ord (reverse vs) []
    ((t,ord),u) <- liftEither (runResVars vrs u (inferWithOrderCheck ctx ord (marksFree (zip [0..] vs) i)))
    (i,u) <- liftEither (runResVars vrs u (eval ctx i))
    (ord,u) <- liftEither (runResVars vrs u (checkWithOrderCheck ctx ord (marksFree (zip [0..] vs) j) t))
    (j,u) <- liftEither (runResVars vrs u (eval ctx j))
    tell [DefRedex vrs i j]
    pure (CtxRedex vrs i j:ctx,ord,u)
    where
        chkAll :: UniverseID -> OrderingGraph -> [Exp] -> [Val] -> Cmd ([Val],UniverseID,OrderingGraph)
        chkAll u ord (e:es) vs = do
            (ord,u) <- liftEither (runRes (u+1) (checkWithOrderCheck ctx ord (marksFree (zip [0..] vs) e) (VSet u)))
            (v,u) <- liftEither (runRes u (eval ctx e))
            chkAll u ord es (fmap (modifFree (+1) 0) (v:vs))
        chkAll u ord [] vs = pure (vs,u,ord)
docmd (Check e) (ctx,ord,u) = do
    ((t,_),_) <- liftEither (runRes u (inferWithOrderCheck ctx ord e))
    tell [Checked t]
    pure (ctx,ord,u)
docmd (Eval e) (ctx,ord,u) = do
    (_,u') <- liftEither (runRes u (inferWithOrderCheck ctx ord e))
    (x,_) <- liftEither (runRes u' (eval ctx e))
    tell [Evaluated x]
    pure (ctx,ord,u)
docmd (Match a b) (ctx,ord,u) = do
    (_,u) <- liftEither (runRes u (inferWithOrderCheck ctx ord a))
    (a,u) <- liftEither (runRes u (eval ctx a))
    (_,u) <- liftEither (runRes u (inferWithOrderCheck ctx ord b))
    (b,u) <- liftEither (runRes u (eval ctx b))
    liftEither (runRes u (fit ctx a b))
    tell [Success]
    pure (ctx,ord,u)
docmd (Print ns) (ctx,ord,u) = do
    defs <- mapM (\n -> case getElem n ctx of
        Just d -> pure d
        Nothing -> throwError ("Identifier \"" ++ show n ++ "\" is not defined.")) ns
    tell [PrintCtx defs]
    pure (ctx,ord,u)
docmd PrintAll (ctx,ord,u) = tell [PrintCtx ctx] >> pure (ctx,ord,u)
docmd PrintUniverses (ctx,ord,u) = tell [PrintGraph ord] >> pure (ctx,ord,u)
docmd (CheckConstraints cs) (ctx,ord,u) =
    liftEither (runRes u (appConstraints ord cs)) >> tell [Success] >> pure (ctx,ord,u)