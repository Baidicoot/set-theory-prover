{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
module Frontend
    ( initialState
    , refineExt
    , assertExt
    , newSortExt
    , newConstExt
    , beginProofExt
    , endProofExt
    , notationExt
    , printGrammarExt
    , doneExt
    , dieExt
    , runExt
    , runActionExt
    , TracedError
    , ProverState)
    where

-- TODO: Check `Prop`s when asserting.

import qualified Data.Map as M
import qualified Data.Set as S
import Data.IORef
import Foreign.Ptr

import qualified Data.Text as T

import Kernel hiding(Name)
import ParserTypes
import ParserInit
import Parser
import Elab
import Notation

import Control.Monad.State
import Control.Monad.Except
import Control.Monad.IO.Class
import Control.Exception
import Data.List (partition)

import qualified Foreign.Lua as L

newtype ConstObjs = ConstObjs (M.Map Name Monotype) deriving(Show)
newtype DefObjs = DefObjs (M.Map Name (Monotype,DeBrujin)) deriving(Show)
newtype ConstSorts = Sorts (S.Set Name) deriving(Show)
newtype Axioms = Axioms (M.Map Name Term) deriving(Show)
type Env = (ConstSorts, ConstObjs, DefObjs, Axioms)

-- names, reference grammar, global environment, current proof and local names for each goal (if applicable)
type ProverState = (Grammar, Env, Maybe (Term, Proof, [ElabCtx]))

type Prover = ExceptT TracedError (StateT ([Name],Maybe Grammar) L.Lua)

getNames :: Prover [Name]
getNames = gets fst

putNames :: [Name] -> Prover ()
putNames ns = modify (\(_,g) -> (ns,g))

compileGrammar :: ProverState -> Prover Grammar
compileGrammar (grammar, _, _) = do
    x <- gets snd
    case x of
        Just g -> pure g
        Nothing -> do
            ns <- getNames
            case elimLeftRec ns grammar of
                (Right g,ns) -> do
                    put (ns,Just g)
                    pure g
                (Left err,ns) -> throwExt (Parser (show err))

uncompileGrammar :: Prover ()
uncompileGrammar = modify (\(ns,_)->(ns,Nothing))

data TracedError
    = TracedError NormalError [(String,String)] deriving(Show)
instance Exception TracedError

data NormalError
    = NotInProofMode
    | InProofMode
    | NoOpenGoals
    | OpenGoals
    | Terminated
    | Parser String
    | Checker String
    deriving(Show)

throwExt :: NormalError -> Prover a
throwExt = throwError . flip TracedError []

traceAs :: String -> String -> Prover a -> Prover a
traceAs x i f = catchError f (\(TracedError e xs) -> throwError (TracedError e ((x,i):xs)))

runExt :: Show i => String -> (ProverState -> i -> Prover ProverState) -> IORef (ProverState,([Name],Maybe Grammar)) -> i -> L.Lua L.NumResults
runExt n f state i = do
    (s,ns) <- liftIO (readIORef state)
    (s',ns') <- runProver (traceAs n (show i) $ f s i) ns
    case s' of
        Right s' -> liftIO (writeIORef state (s',ns')) >> pure 0
        Left err -> L.raiseError (show err)

runActionExt :: String -> (ProverState -> Prover ProverState) -> IORef (ProverState,([Name],Maybe Grammar)) -> L.Lua L.NumResults
runActionExt n f state = do
    (s,ns) <- liftIO (readIORef state)
    (s',ns') <- runProver (traceAs n "" $ f s) ns
    case s' of
        Right s' -> liftIO (writeIORef state (s',ns')) >> pure 0
        Left err -> L.raiseError (show err)

runProver :: Prover i -> ([Name],Maybe Grammar) -> L.Lua (Either TracedError i, ([Name],Maybe Grammar))
runProver f = runStateT (runExceptT f)

envToElabCtx :: Env -> ElabCtx
envToElabCtx (Sorts s, ConstObjs o, DefObjs d, Axioms a) =
    let sorts = M.fromList (fmap (\s -> (s,(s,Global,Sort))) (S.toList s))
        consts = M.fromList (fmap (\c -> (c,(c,Global,Obj))) (M.keys o))
        defs = M.fromList (fmap (\d -> (d,(d,Global,Obj))) (M.keys d))
        axioms = M.fromList (fmap (\a -> (a,(a,Global,Prf))) (M.keys a))
    in sorts `M.union` consts `M.union` defs `M.union` axioms

initialState :: ProverState
initialState = (grINIT, (Sorts mempty, ConstObjs mempty, DefObjs mempty, Axioms mempty), Nothing)

insertAxiom :: Name -> Term -> ProverState -> ProverState
insertAxiom n m (grammar, (s,o,d,Axioms a), goal) =
    (grammar, (s,o,d,Axioms (M.insert n m a)), goal)

insertSort :: Name -> ProverState -> ProverState
insertSort n (grammar, (Sorts s,o,d,a), goal) =
    (grammar, (Sorts (S.insert n s),o,d,a), goal)

insertConst :: Name -> Monotype -> ProverState -> ProverState
insertConst n t (grammar, (s,ConstObjs o,d,a), goal) =
    (grammar, (s,ConstObjs (M.insert n t o),d,a), goal)

envToCtx :: Env -> Ctx
envToCtx (_, ConstObjs objs, DefObjs defobjs, Axioms ax) =
    let objctx = fmap (Polytype mempty) (objs `M.union` fmap fst defobjs)
        defctx = fmap snd defobjs
        thmctx = ax
    in (thmctx,objctx,defctx)

checkProof :: ProverState -> Term -> Proof -> Prover [Term]
checkProof (_, env, _) prop prf = do
    names <- getNames
    case runProofCheck names (envToCtx env) prop prf of
        (Right (_, holes), names') -> putNames names' >> pure holes
        (Left err, _) -> throwExt (Checker (show err))

checkProp :: ProverState -> Monotype -> Term -> Prover Term
checkProp (_, env, _) sort prop = do
    names <- getNames
    case runPropCheck names (envToCtx env) sort prop of
        (Right t, names') -> putNames names' >> pure t
        (Left err, _) -> throwExt (Checker (show err))

refine :: ProverState -> (Proof, [ElabCtx]) -> Prover ProverState
refine (_, _, Nothing) _ = throwExt NotInProofMode
refine (grammar, env, Just (prop, prf, ctxs)) (p, ctxs') = case fillHole prf p of
    Just prf' ->
        let state' = (grammar, env, Just (prop, prf', ctxs'))
        in checkProof state' prop prf' >> pure state'
    Nothing -> throwExt NoOpenGoals

addNotation :: ProverState -> Name -> [NotationBinding] -> SExpr -> Prover ProverState
addNotation (grammar, env, p) n ns s =
    case makeProdRule n ns s of
        Left err -> throwExt (Parser (show err))
        Right prod -> uncompileGrammar >> pure (M.adjust (prod:) n grammar, env, p)

beginProof :: ProverState -> Term -> Prover ProverState
beginProof (grammar, env, Nothing) t = pure (grammar, env, Just (t, Hole, [mempty]))
beginProof _ _ = throwExt InProofMode

endProof :: ProverState -> T.Text -> Prover ProverState
endProof (_, _, Nothing) t = throwExt NotInProofMode
endProof (_, _, Just (_, _, _:_)) _ = throwExt OpenGoals
endProof s@(_, _, Just (prop, _, [])) t =
    pure (insertAxiom t prop s)

goalCtx :: ProverState -> Prover ElabCtx
goalCtx (_, env, Just (_, _, ctx:_)) = pure (ctx `M.union` envToElabCtx env)
goalCtx (_, _, Just _) = throwExt NoOpenGoals
goalCtx _ = throwExt NotInProofMode

envCtx :: ProverState -> ElabCtx
envCtx (_, env, _) = envToElabCtx env

parseProof :: ProverState -> Grammar -> ElabCtx -> T.Text -> Prover (Proof, [ElabCtx], ProverState)
parseProof s@(grammar, env, p) g ctx t =
    case parse g ntPROOF t of
        Left err -> throwExt (Parser (show err))
        Right s -> do
            names <- getNames
            case runElaborator names ctx (elabProof s) of
                ((Right o, ctx'), names') -> putNames names' >> pure (o, ctx', (grammar, env, p))
                ((Left err, _), _) -> throwExt (Parser (show err))

parseMonotype :: ProverState -> Grammar -> ElabCtx -> T.Text -> Prover (Monotype, ProverState)
parseMonotype (grammar, env, p) g ctx t =
    case parse g ntSORT t of
        Left err -> throwExt (Parser (show err))
        Right s -> do
            names <- getNames
            case runElaborator names ctx (elabMonotype s) of
                ((Right o, _), names') -> putNames names' >> pure (o, (grammar, env, p))
                ((Left err, _), _) -> throwExt (Parser (show err))

parseProp :: ProverState -> Grammar -> ElabCtx -> T.Text -> Prover (Term, ProverState)
parseProp (grammar, env, p) g ctx t =
    case parse g ntPROP t of
        Left err -> throwExt (Parser (show err))
        Right s -> do
            names <- getNames
            case runElaborator names ctx (elabProp s) of
                ((Right o, _), names') -> putNames names' >> pure (o, (grammar, env, p))
                ((Left err, _), _) -> throwExt (Parser (show err))

parseSort :: ProverState -> Grammar -> ElabCtx -> T.Text -> Prover (Monotype, ProverState)
parseSort (grammar, env, p) g ctx t =
    case parse g ntSORT t of
        Left err -> throwExt (Parser (show err))
        Right s -> do
            names <- getNames
            case runElaborator names ctx (elabSort s) of
                ((Right o, _), names') -> putNames names' >> pure (o, (grammar, env, p))
                ((Left err, _), _) -> throwExt (Parser (show err))

parseNotationBinding :: ProverState -> Grammar -> T.Text -> Prover (Name, [NotationBinding])
parseNotationBinding (grammar, env, p) g t =
    case parse g ntNOTATION t of
        Left err -> throwExt (Parser (show err))
        Right s -> do
            case runElaborator [] mempty (elabNotation s) of
                ((Right o, _), _) -> pure o
                ((Left err, _), _) -> throwExt (Parser (show err))

parseNotationProduct :: ProverState -> S.Set Name -> Name -> T.Text -> Prover SExpr
parseNotationProduct (grammar, env, p) ps n t = do
    ns <- getNames
    g <- case elimLeftRec ns (addPlaceholders ps grammar) of
            (Right g,ns) -> do
                putNames ns
                pure g
            (Left err,ns) -> throwExt (Parser (show err))
    case parse g n t of
        Left err -> throwExt (Parser (show err))
        Right s -> pure s

refineExt :: ProverState -> T.Text -> Prover ProverState
refineExt s t = do
    (p, ctxs', s') <- do
        ctx <- goalCtx s
        g <- compileGrammar s
        parseProof s g ctx t
    refine s (p, ctxs')

newConstExt :: ProverState -> (T.Text, T.Text) -> Prover ProverState
newConstExt s (n, t) = do
    (m, s') <- do
        g <- compileGrammar s
        parseSort s g (envCtx s) t
    pure (insertConst n m s')

assertExt :: ProverState -> (T.Text, T.Text) -> Prover ProverState
assertExt s (n, t) = do
    (m, s') <- do
        g <- compileGrammar s
        parseProp s g (envCtx s) t
    m' <- checkProp s' Prop m
    pure (insertAxiom n m' s')

newSortExt :: ProverState -> T.Text -> Prover ProverState
newSortExt s n = pure (insertSort n s)

notationExt :: ProverState -> (T.Text, T.Text) -> Prover ProverState
notationExt s (b, e) = do
    (t,b') <- do
        g <- compileGrammar s
        parseNotationBinding s g b
    e' <- parseNotationProduct s (placeholderNonterminals b') t e
    addNotation s t b' e'

beginProofExt :: ProverState -> T.Text -> Prover ProverState
beginProofExt s t = do
    (p, s') <- do
        g <- compileGrammar s
        parseProp s g (envCtx s) t
    beginProof s' p

endProofExt :: ProverState -> T.Text -> Prover ProverState
endProofExt = endProof

printGrammarExt :: ProverState -> Prover ProverState
printGrammarExt s@(g, _, _) = liftIO (print (fmap (fmap snd) g)) >> pure s

doneExt :: ProverState -> Prover ProverState
doneExt (_, _, Nothing) = throwExt NotInProofMode
doneExt (_, _, Just (_, _, _:_)) = throwExt OpenGoals
doneExt s@(_, _, Just (prop, _, [])) =
    pure s

dieExt :: ProverState -> Prover ProverState
dieExt _ = throwExt Terminated