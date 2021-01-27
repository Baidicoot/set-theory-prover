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
    | DefInd Inductive
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
    show (DefInd i) = "Defined " ++ show i ++ ".\n"
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
docmd' (MkInductive i) g = doInductive g i

forallParams :: [Val] -> Val -> Val
forallParams vs v = foldl (\t a -> VPi (Abs (Just a) t)) v vs

getParams :: Val -> ([Val],Val)
getParams (VPi (Abs (Just d) r)) = (\(a,b) -> (a++[d],b)) (getParams r)
getParams x = ([],x)

makeCase :: Name -> Int -> Int -> Name -> Val -> Cmd Val
makeCase s nconst nvary c t = do
    (subts,index) <- case getParams t of
        (subts,VApp (VFree t) index) | s == t -> pure (subts,index)
        _ -> throwError ("Constructor type of '" ++ c ++ "' must be '" ++ s ++ "'")
    let term = VApp (VFree c) . fmap (\i -> VApp (VVar i) []) . reverse $
            [0..length subts-1] ++ [length subts+1..nconst+length subts]
    let conc = VApp (VVar (length subts)) (drop nconst index ++ [term])
    let x = foldl (\t (i,a) -> case a of
            VApp (VFree s') index | s == s' ->
                let t' = modifFree (+1) 0 t
                in VPi . Abs (Just a) . VPi $ Abs (Just (VApp (VVar (length subts - i))
                    (drop nconst (fmap (modifFree (+1) 0) index) ++ [VApp (VVar 0) []]))) t'
            _ -> VPi (Abs (Just a) t)) conc (zip [0..] subts)
    pure x

doInductive :: CommandState -> Inductive -> Cmd CommandState
doInductive (ctx,ord,u,ev) i@(Ind s vrs vs t cs) = do
    (vs,(ctx,ord,u,ev)) <- chkAll (ctx,ord,u,ev) (reverse vs) []
    (r,u) <- liftEither (runResVars vrs ev (u+1) (checkWithOrderCheck ctx ord (marksFree (zip [0..] vs) t) (VSet u)))
    ord <- catchHoles r
    (t,u) <- liftEither (runResVars vrs ev (u+1) (eval ctx (marksFree (zip [0..] vs) t)))
    ctx <- pure (CtxAxiom s (forallParams vs t):ctx)

    (cs,(ctx,ord,u,ev)) <- foldM (\(cs,(ctx,ord,u,ev)) (n,t) -> do
        (r,u) <- liftEither (runResVars vrs ev (u+1) (checkWithOrderCheck ctx ord (marksFree (zip [0..] vs) t) (VSet u)))
        ord <- catchHoles r
        (t,u) <- liftEither (runResVars vrs ev (u+1) (eval ctx (marksFree (zip [0..] vs) t)))
        ctx <- pure (CtxAxiom n (forallParams vs t):ctx)
        pure ((n,t):cs,(ctx,ord,u,ev))) ([],(ctx,ord,u,ev)) cs
    
    let (varyingParams,_) = getParams t
    let nconst = length vs
    let nvary = length varyingParams
    let prop = forallParams varyingParams (VPi
            . Abs (Just $ VApp (VFree s) ((\i -> VApp (VVar i) []) <$> reverse [0..nconst+nvary-1])) $ VSet u)
    u <- pure (u+1)
    let conc = forallParams varyingParams $ VPi $ Abs (Just
            . VApp (VFree s)
            . fmap (\i -> VApp (VVar i) [])
            . reverse $ [0..nvary - 1] ++ [nvary + 1..nvary + nconst])
            . VApp (VVar (nvary+1))
            . fmap (\i -> VApp (VVar i) [])
            . reverse $ [0..nvary]
    ind <- forallParams vs . VPi . Abs (Just prop) <$> foldM (\p (n,t) -> do
        c <- makeCase s nconst nvary n t
        pure (VPi (Abs (Just c) (modifFree (+1) 0 p)))) conc cs
    ctx <- pure (CtxAxiom ("rec_" ++ s) ind:ctx)
    tell [DefInd i]
    tell [DefAxiom ("rec_" ++ s) ind]
    pure (ctx,ord,u,ev)