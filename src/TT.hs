module TT where

import Graph
import Data.List
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import Data.Char

type Name = String

data Constraint
    = UniverseID :>: UniverseID
    | UniverseID :>=: UniverseID

appConstraints :: OrderingGraph -> [Constraint] -> Res OrderingGraph
appConstraints g (i :>: j:cs) = do
    let g' = insertEdge j i True g
    unless (acyclic i g') (throwError ("could not add universe constraint Type." ++ show i ++ " > Type." ++ show j))
    appConstraints g' cs
appConstraints g (i :>=: j:cs) = do
    let g' = insertEdge j i False g
    unless (acyclic i g') (throwError ("could not add universe constraint Type." ++ show i ++ " ≥ Type." ++ show j))
    appConstraints g' cs
appConstraints g [] = pure g

data Exp
    = Ann Exp Exp
    | Set UniverseID
    | Hole
    | Pi (Abstraction Exp)
    -- variable is marked with a type if free
    | Var Int (Maybe Val) (Maybe Name)
    | Free Name
    | App Exp Exp
    | Lam (Abstraction Exp)
    deriving(Show)

data Abstraction e
    = Abs (Maybe e) e
    deriving(Eq,Show)

data ValVar
    = VVar Int
    | VFree Name
    deriving(Eq)

data Val
    = VApp ValVar [Val]
    | VSet UniverseID
    | VLam (Abstraction Val)
    | VPi (Abstraction Val)
    deriving(Eq)

varUsed :: Int -> Val -> Bool
varUsed n (VApp (VVar n') vs) = n == n' || any (varUsed n) vs
varUsed n (VApp _ vs) = any (varUsed n) vs
varUsed n (VLam abs) = varUsedAbs n abs
varUsed n (VPi abs) = varUsedAbs n abs
varUsed _ _ = False

varUsedAbs :: Int -> Abstraction Val -> Bool
varUsedAbs n (Abs (Just d) r) = varUsed n d || varUsed (n+1) r
varUsedAbs n (Abs Nothing r) = varUsed (n+1) r

boundVarUsed :: Abstraction Val -> Bool
boundVarUsed (Abs _ r) = varUsed 0 r

names :: [String]
names = [1..] >>= flip replicateM ['a'..'z']

showNamesAbs :: [String] -> [String] -> Abstraction Val -> (String,Maybe String,String)
showNamesAbs (u:unused) ns (Abs d r) = (u,fmap (showNames unused ns) d,showNames unused (u:ns) r)

parens :: String -> String
parens s | any isSpace s = "(" ++ s ++ ")"
parens s = s

showNames :: [String] -> [String] -> Val -> String
showNames us ns (VLam abs) =
    let (v,t,x) = showNamesAbs us ns abs
    in case t of
        Just t -> "fun (" ++ v ++ " : " ++ t ++ ") => " ++ x
        _ -> "lam " ++ v ++ " => " ++ x
showNames us ns (VPi abs) =
    let (v,Just t,x) = showNamesAbs us ns abs
    in  if boundVarUsed abs then
            "forall (" ++ v ++ " : " ++ t ++ "), " ++ x
        else parens t ++ " -> " ++ x
showNames us ns (VApp (VVar i) vs) = (if length ns <= i then show i else ns !! i) ++ concatMap ((' ':) . parens . showNames us ns) vs
showNames us ns (VApp (VFree i) vs) = i ++ concatMap ((' ':) . parens . showNames us ns) vs
showNames us ns (VSet i) = "Type." ++ show i

instance Show Val where
    show = showNames names []

showCtx :: Ctx -> String
showCtx ctx = "[" ++ intercalate ", " (fmap (\(n,(t,v))->show n ++ " : " ++ show t) ctx) ++ "]"

showEnv :: Env -> String
showEnv env = "[" ++ intercalate ", " (fmap (\x -> case x of
    Just v -> parens (show v)
    Nothing -> "_") env) ++ "]"

-- typing contexts (name, type, delta-expansion)
type Ctx = [(Name,(Val,Maybe Val))]
-- evaluation environments - should NOT include references to itself!
type Env = [Maybe Val]
type Res = StateT UniverseID (ExceptT String (Writer [Constraint]))

runRes :: UniverseID -> Res a -> Either String (a,UniverseID)
runRes u r = fst (runWriter (runExceptT (runStateT r u)))

freshUniverse :: Res UniverseID
freshUniverse = do
    u <- get
    put (u+1)
    pure u

constrain :: Constraint -> Res ()
constrain c = tell [c]

trace :: String -> Res a -> Res a
trace s m = m `catchError` (throwError . (++"\n"++s))

modifEnv :: (Int -> Int) -> Env -> Env
modifEnv f = fmap (fmap (modifFree f 0))

modifAbs :: (Int -> Int) -> Int -> Abstraction Val -> Abstraction Val
modifAbs f n (Abs d r) = Abs (fmap (modifFree f n) d) (modifFree f (n+1) r)

modifFree :: (Int -> Int) -> Int -> Val -> Val
modifFree f n (VApp (VVar i) vs) | i >= n = VApp (VVar (f i)) (fmap (modifFree f n) vs)
modifFree f n (VApp v vs) = VApp v (fmap (modifFree f n) vs)
modifFree f n (VLam abs) = VLam (modifAbs f n abs)
modifFree f n (VPi abs) = VPi (modifAbs f n abs)
modifFree _ _ (VSet i) = VSet i

substValAbs :: Ctx -> Int -> Val -> Abstraction Val -> Res (Abstraction Val)
substValAbs g n x (Abs d r) = do
    d' <- mapM (substVal g n x) d
    r' <- substVal g (n+1) (modifFree (+1) 0 x) r
    pure (Abs d' r')

-- beta-reduction
substVal :: Ctx -> Int -> Val -> Val -> Res Val
substVal g n x e@(VApp (VVar i) xs) | i == n = trace ("while substituting " ++ show x ++ " in " ++ show e) $ do
    xs' <- mapM (substVal g n x) xs
    foldM (evalApp g) x xs'
substVal g n x (VApp i xs) = VApp i <$> mapM (substVal g n x) xs
substVal g n x (VLam abs) = VLam <$> substValAbs g n x abs
substVal g n x (VPi abs) = VPi <$> substValAbs g n x abs
substVal g n x (VSet i) = pure (VSet i)

evalAbs :: Ctx -> Abstraction Exp -> Res (Abstraction Val)
evalAbs g (Abs d r) = do
    d' <- mapM (eval g) d
    r' <- eval g r
    pure (Abs d' r')

eval :: Ctx -> Exp -> Res Val
eval g (Var i _ _) = pure (VApp (VVar i) [])
eval g (Free n) = pure (VApp (VFree n) [])
eval g (Ann x t) = eval g x
eval g (Set i) = pure (VSet i)
eval g (Pi abs) = trace ("while evaluating Pi " ++ show abs) (VPi <$> evalAbs g abs)
eval g (App f x) = trace ("while evaluating App " ++ show f ++ " " ++ show x) $ do
    f' <- eval g f
    x' <- eval g x
    evalApp g f' x'
eval g (Lam abs) = trace ("while evaluating Lam" ++ show abs) (VLam <$> evalAbs g abs)

evalApp :: Ctx -> Val -> Val -> Res Val
evalApp g (VApp n vs) v = pure (VApp n (vs ++ [v]))
evalApp g f@(VLam (Abs _ x)) v = trace ("while applying " ++ show f ++ " to " ++ show v) $ fmap (modifFree (\x->x-1) 0) (substVal g 0 (modifFree (+1) 0 v) x)
evalApp g f@(VPi (Abs _ x)) v = trace ("while applying " ++ show f ++ " to " ++ show v) $ fmap (modifFree (\x->x-1) 0) (substVal g 0 (modifFree (+1) 0 v) x)
evalApp _ f x = throwError ("non-function application of " ++ show f ++ " to " ++ show x)

ehnf :: Ctx -> Val -> Res Val
ehnf g v@(VApp (VFree n) xs) = case lookup n g of
    Just (_,Just d) -> foldM (evalApp g) d xs >>= ehnf g
    _ -> pure v
ehnf _ v = pure v

fit :: Ctx -> Val -> Val -> Res ()
fit g v0@(VPi ab) v1@(VPi bb) = trace ("while matching " ++ show v0 ++ " and " ++ show v1) $ matchAbs g ab bb
fit g v0@(VLam ab) v1@(VLam bb) = trace ("while matching " ++ show v0 ++ " and " ++ show v1) $ matchAbs g ab bb
fit g (VSet i) (VSet j) = tell [j :>=: i]
fit g v0@(VApp a as) v1@(VApp b bs) | length as == length bs && a == b =
    trace ("while matching " ++ show v0 ++ " and " ++ show v1) $ mapM_ (uncurry (fit g)) (zip as bs)
fit g a@(VApp (VFree n) xs) b = trace ("while expanding definition of " ++ n) $ case lookup n g of
    Just (_,Just d) -> do
        a' <- foldM (evalApp g) d xs
        fit g a' b
    _ -> throwError ("could not fit types " ++ show a ++ " and " ++ show b)
fit g a b@(VApp (VFree n) xs) = trace ("while expanding definition of " ++ n) $ case lookup n g of
    Just (_,Just d) -> do
        b' <- foldM (evalApp g) d xs
        fit g a b'
    _ -> throwError ("could not fit types " ++ show a ++ " and " ++ show b)
fit g a b = throwError ("could not fit types " ++ show a ++ " and " ++ show b)

matchAbs :: Ctx -> Abstraction Val -> Abstraction Val -> Res ()
matchAbs g (Abs (Just a) b) (Abs (Just x) y) = fit g a x >> fit g b y
matchAbs g (Abs _ a) (Abs _ b) = fit g a b

markFree :: Int -> Val -> Exp -> Exp
markFree n x (Var i _ o) | n == i = Var i (Just x) o
markFree n x (Lam abs) = Lam (markFreeAbs n x abs)
markFree n x (Pi abs) = Pi (markFreeAbs n x abs)
markFree n x (App f a) = App (markFree n x f) (markFree n x a)
markFree n x (Ann e t) = Ann (markFree n x e) (markFree n x t)
markFree _ _ (Set i) = Set i
markFree _ _ (Free n) = Free n
markFree _ _ (Var i t o) = Var i t o
markFree _ _ Hole = Hole

markFreeAbs :: Int -> Val -> Abstraction Exp -> Abstraction Exp
markFreeAbs n x (Abs d r) = Abs (fmap (markFree n x) d) (markFree (n+1) (modifFree (+1) 0 x) r)

infer :: Ctx -> Exp -> Res Val
infer g (Set i) = do
    j <- freshUniverse
    tell [j :>: i]
    pure (VSet j)
infer g (Var i (Just t) n) = pure t
infer g (Free n) = case lookup n g of
    Just (t,_) -> pure t
    Nothing -> throwError ("undefined identifier " ++ show n)
infer g (Ann x t) = do
    i <- freshUniverse
    check g t (VSet i)
    t' <- eval g t
    check g x t'
    pure t'
infer g (Lam (Abs (Just t) x)) = do
    i <- freshUniverse
    check g t (VSet i)
    dt <- eval g t
    rt <- infer g (markFree 0 (modifFree (+1) 0 dt) x)
    pure (VPi (Abs (Just dt) rt))
infer g (Pi (Abs (Just d) r)) = do
    i <- freshUniverse
    j <- freshUniverse
    k <- freshUniverse
    check g d (VSet i)
    dt <- eval g d
    check g (markFree 0 (modifFree (+1) 0 dt) r) (VSet j)
    tell [k :>=: i, k :>=: j]
    pure (VSet k)
infer g (App f x) = do
    s <- infer g f >>= ehnf g
    case s of
        VPi (Abs (Just d) _) -> do
            check g x d
            x' <- eval g x
            evalApp g s x'
        _ -> throwError ("non-function application of \"" ++ show s ++ "\" to \"" ++ show x ++ "\"")
infer _ x = throwError ("could not infer type of \"" ++ show x ++ "\"")

check :: Ctx -> Exp -> Val -> Res ()
check g (Lam (Abs t x)) (VPi (Abs (Just d) r)) = do
    case t of
        Just t -> do
            i <- freshUniverse
            check g t (VSet i)
            t <- eval g t
            fit g t d
        _ -> pure ()
    check g (markFree 0 (modifFree (+1) 0 d) x) r
check g Hole t = throwError ("found hole of type: " ++ show t ++ "\nin environment: " ++ showCtx g)
check g x t = do
    xt <- infer g x
    fit g xt t

inferWithOrderCheck :: Ctx -> OrderingGraph -> Exp -> Res (Val,OrderingGraph)
inferWithOrderCheck g gr e = do
    (v,c) <- listen (infer g e)
    gr <- appConstraints gr c
    pure (v,gr)

showPar :: Show x => x -> String
showPar x | ' ' `elem` show x = "(" ++ show x ++ ")"
showPar x = show x