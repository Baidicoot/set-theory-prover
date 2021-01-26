module Command where
import TT
import Graph
import Control.Monad.Except
import Control.Monad.Writer

modifAbsExp :: (Int -> Int) -> Int -> Abstraction Exp -> Abstraction Exp
modifAbsExp f n (Abs d r) = Abs (fmap (modifFreeExp f n) d) (modifFreeExp f (n+1) r)

modifFreeExp :: (Int -> Int) -> Int -> Exp -> Exp
modifFreeExp f n (Var i m) | i >= n = Var (f i) m
modifFreeExp f n (App a b) = App (modifFreeExp f n a) (modifFreeExp f n b)
modifFreeExp f n (Ann a b) = Ann (modifFreeExp f n a) (modifFreeExp f n b)
modifFreeExp f n (Lam v abs) = Lam v (modifAbsExp f n abs)
modifFreeExp f n (Pi v abs) = Pi v (modifAbsExp f n abs)
modifFreeExp _ _ x = x

data Inductive = Ind String [Var] [Exp] Exp [(Name,Exp)]

instance Show Inductive where
    show (Ind n vs as t []) = "Inductive '" ++ n ++ "' [" ++ unwords (fmap show vs) ++ "] : "
        ++ showExp vs t
    show (Ind n vs as t xs) = "Inductive '" ++ n ++ "' [" ++ unwords (fmap show vs) ++ "] : "
        ++ showExp vs t ++ " :="
        ++ concatMap (\(n,xs) -> "\n| " ++ n ++ " : " ++ showExp vs xs) xs

splitArgs :: Exp -> ([(Var,Exp)], Exp)
splitArgs (Pi v (Abs (Just d) r)) = let (vs,e) = splitArgs r in ((v,d):vs,e)
splitArgs x = ([],x)

hasCons :: String -> Exp -> Maybe [Exp]
hasCons s (App a b) = fmap (++[b]) (hasCons s a)
hasCons s (Free t) | s == t = Just []
hasCons _ _ = Nothing

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
    | Ehnf Exp
    | Unfolding [Name]
    | EvalUnfold [Name] Exp
    | MkInductive Inductive

instance Show Command where
    show (Axiom s e) = "Defining Axiom '" ++ s ++ "' : " ++ showExp [] e
    show (Define s e) = "Defining '" ++ s ++ "' :=\n    " ++ showExp [] e
    show (Redex vs es r e) = "Defining Redex [" ++ unwords (fmap show vs) ++ "] " ++ showExp vs r ++ " :=\n    " ++ showExp vs e
    show (Check e) = "Checking " ++ showExp [] e
    show (MkInductive i) = "Defining " ++ show i

data CommandOutput
    = DefAxiom String Val
    | Defined String Val Val
    | DefinedInd Inductive
    | DefRedex [Var] Val Val
    | Checked Val
    | Evaluated Val
    | PrintCtx Ctx
    | PrintGraph OrderingGraph
    | Success
    | Debug String

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
    show (DefinedInd i) = "Defined " ++ show i ++ ".\n"
    show (Debug s) = "DEBUG: \"" ++ s ++ "\".\n"

type CommandState = (Ctx,OrderingGraph,UniverseID,EvalCtx)

inCtx :: Name -> Ctx -> Bool
inCtx n ctx = n `elem` ctxNames ctx

emptyState :: CommandState
emptyState = ([],[],0,[])

marksFree :: [(Int,Val)] -> Exp -> Exp
marksFree ((i,v):vs) e = marksFree vs (markFree i v e)
marksFree _ e = e

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f (Left e) = Left (f e)
mapLeft _ (Right x) = Right x

catchHoles = liftEither . mapLeft (unlines . fmap (\(n,vs,v) -> "Found hole '?" ++ n ++ "' of type \"" ++ showVal vs v ++ "\""))

docmd :: Command -> CommandState -> Cmd CommandState
docmd c g = docmd' c g `catchError` \s -> throwError (s ++ "\nwhile " ++ show c)

chkAll :: CommandState -> [Exp] -> [Val] -> Cmd ([Val],CommandState)
chkAll g@(ctx,ord,u,ev) (e:es) vs = do
    (r,u) <- liftEither (runRes ev (u+1) (checkWithOrderCheck ctx ord (marksFree (zip [0..] vs) e) (VSet u)))
    ord <- catchHoles r
    (v,u) <- liftEither (runRes ev u (eval ctx e))
    chkAll (ctx,ord,u,ev) es (fmap (modifFree (+1) 0) (v:vs))
chkAll g _ vs = pure (vs,g)

docmd' :: Command -> CommandState -> Cmd CommandState
docmd' (Axiom n _) (ctx,ord,u,e) | n `inCtx` ctx = throwError ("\"" ++ n ++ "\" is already defined.")
docmd' (Define n _) (ctx,ord,u,e) | n `inCtx` ctx = throwError ("\"" ++ n ++ "\" is already defined.")
docmd' (Axiom n e) (ctx,ord,u,ev) = do
    (r,u) <- liftEither (runRes ev u (inferWithOrderCheck ctx ord e))
    (_,ord) <- catchHoles r
    (x,u) <- liftEither (runRes ev u (eval ctx e))
    tell [DefAxiom n x]
    pure (CtxAxiom n x:ctx,ord,u,ev)
docmd' (Define n e) (ctx,ord,u,ev) = do
    (r,u) <- liftEither (runRes ev u (inferWithOrderCheck ctx ord e))
    (t,ord) <- catchHoles r
    (x,u) <- liftEither (runRes ev u (eval ctx e))
    tell [Defined n t x]
    pure (CtxDelta n t x:ctx,ord,u,ev)
docmd' (Check e) (ctx,ord,u,ev) = do
    (r,_) <- liftEither (runRes ev u (inferWithOrderCheck ctx ord e))
    (t,_) <- catchHoles r
    tell [Checked t]
    pure (ctx,ord,u,ev)
docmd' (Eval e) (ctx,ord,u,ev) = do
    (_,u') <- liftEither (runRes ev u (inferWithOrderCheck ctx ord e))
    (x,_) <- liftEither (runRes ev u' (eval ctx e))
    tell [Evaluated x]
    pure (ctx,ord,u,ev)
docmd' (Ehnf e) (ctx,ord,u,ev) = do
    (_,u') <- liftEither (runRes ev u (inferWithOrderCheck ctx ord e))
    (x,_) <- liftEither (runRes ev u' (eval ctx e >>= ehnf ctx))
    tell [Evaluated x]
    pure (ctx,ord,u,ev)
docmd' (EvalUnfold ns e) (ctx,ord,u,ev) = do
    (_,u') <- liftEither (runRes ev u (inferWithOrderCheck ctx ord e))
    (x,_) <- liftEither (runRes (ev ++ ns) u' (eval ctx e))
    tell [Evaluated x]
    pure (ctx,ord,u,ev)
docmd' (Unfolding ns) (ctx,ord,u,ev) = do
    mapM_ (\n -> case getElem n ctx of
        Just _ -> pure ()
        _ -> throwError ("Identifier \"" ++ n ++ "\" is not defined.")) ev    
    tell [Success]
    pure (ctx,ord,u,ev++ns)
docmd' (Match a b) (ctx,ord,u,ev) = do
    (_,u) <- liftEither (runRes ev u (inferWithOrderCheck ctx ord a))
    (a,u) <- liftEither (runRes ev u (eval ctx a))
    (_,u) <- liftEither (runRes ev u (inferWithOrderCheck ctx ord b))
    (b,u) <- liftEither (runRes ev u (eval ctx b))
    liftEither (runRes ev u (fit ctx a b))
    tell [Success]
    pure (ctx,ord,u,ev)
docmd' (Print ns) (ctx,ord,u,ev) = do
    defs <- mapM (\n -> case getElem n ctx of
        Just d -> pure d
        Nothing -> throwError ("Identifier \"" ++ n ++ "\" is not defined.")) ns
    tell [PrintCtx defs]
    pure (ctx,ord,u,ev)
docmd' PrintAll (ctx,ord,u,ev) = tell [PrintCtx ctx] >> pure (ctx,ord,u,ev)
docmd' PrintUniverses (ctx,ord,u,ev) = tell [PrintGraph ord] >> pure (ctx,ord,u,ev)
docmd' (CheckConstraints cs) (ctx,ord,u,ev) =
    liftEither (runRes ev u (appConstraints ord cs)) >> tell [Success] >> pure (ctx,ord,u,ev)
docmd' (Redex vrs vs i j) (ctx,ord,u,ev) = do
    (vs,(ctx,ord,u,ev)) <- chkAll (ctx,ord,u,ev) (reverse vs) []
    (r,u) <- liftEither (runResVars vrs ev u (inferWithOrderCheck ctx ord (marksFree (zip [0..] vs) i)))
    (t,ord) <- catchHoles r
    (i,u) <- liftEither (runResVars vrs ev u (eval ctx i))
    (r,u) <- liftEither (runResVars vrs ev u (checkWithOrderCheck ctx ord (marksFree (zip [0..] vs) j) t))
    ord <- catchHoles r
    (j,u) <- liftEither (runResVars vrs ev u (eval ctx j))
    tell [DefRedex vrs i j]
    pure (CtxRedex vrs i j:ctx,ord,u,ev)
docmd' (MkInductive i) (ctx,ord,u,ev) = do
    (ctx,ord,u,ev) <- makeType (ctx,ord,u,ev) i
    (ctx,ord,u,ev) <- makeCases (ctx,ord,u,ev) i
    (ctx,ord,u,ev) <- makeRecursor (ctx,ord,u,ev) i
    pure (ctx,ord,u,ev)

makeType :: CommandState -> Inductive -> Cmd CommandState
makeType g (Ind s _ vs t _) = (`docmd` g) . Axiom s $ foldr (\p c -> Pi Dummy (Abs (Just p) c)) t vs

makeCases :: CommandState -> Inductive -> Cmd CommandState
makeCases g (Ind _ _ vs _ cs) = foldM (flip docmd) g
    (fmap (\(s,t) -> Axiom s $ foldr (\p c -> Pi Dummy (Abs (Just p) c)) t vs) cs)

makeRecursor :: CommandState -> Inductive -> Cmd CommandState
makeRecursor g _ = pure g