{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
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
    , loadStateExt
    , includeStateExt
    , dumpStateExt
    , defineExt
    , runExt
    , runActionExt
    , runOutputExt
    , newKeywordExt
    , showEnv
    , ProverState)
    where

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
import Errors
import PrettyPrint

import Control.Monad.State
import Control.Monad.Trace
import Control.Monad.Except
import Control.Monad.IO.Class
import Control.Exception
import Data.List (partition,intercalate)

import qualified Foreign.Lua as L

import Data.Binary (Binary,encode,decodeOrFail)

import qualified Data.ByteString.Lazy as B

newtype ConstObjs = ConstObjs (M.Map Name Polytype) deriving(Show,Binary,Semigroup)
newtype DefObjs = DefObjs (M.Map Name (Polytype,Term)) deriving(Show,Binary,Semigroup)
newtype ConstSorts = Sorts (S.Set Name) deriving(Show,Binary,Semigroup)
newtype Axioms = Axioms (M.Map Name Term) deriving(Show,Binary,Semigroup)
type Env = (ConstSorts, ConstObjs, DefObjs, Axioms)

showEnv :: Env -> String
showEnv = (\(x,y,_) -> showDefs y 0 ++ "\n\n" ++ showDefs x 0) . envToCtx

-- names, reference grammar, global environment, current proof and local names for each goal (if applicable)
type ProverState = (Keywords, Grammar, Env, Maybe (Term, Proof, [ElabCtx]))

serializeProverState :: (Keywords, Grammar,Env) -> Prover B.ByteString
serializeProverState (kw,g,e) = pure (encode (kw,g,e))

deserializeProverState :: B.ByteString -> Prover (Keywords, Grammar,Env)
deserializeProverState b = case decodeOrFail b of
    Left (_,_,e) -> throwError (Serializer e)
    Right (b,_,(kw,g,e)) | B.null b -> pure (kw,g,e)
    Right _ -> throwError (Serializer "did not consume entire input")

type Prover = TraceT NormalError NormalTrace (StateT ([Name],Maybe Grammar) L.Lua)

getNames :: Prover [Name]
getNames = gets fst

putNames :: [Name] -> Prover ()
putNames ns = modify (\(_,g) -> (ns,g))

compileGrammar :: ProverState -> Prover Grammar
compileGrammar (_,grammar, _, _) = do
    x <- gets snd
    case x of
        Just g -> pure g
        Nothing -> do
            ns <- getNames
            case elimLeftRec ns grammar of
                (Right g,ns) -> do
                    put (ns,Just g)
                    pure g
                (Left err,ns) -> throwError (Parser err)

uncompileGrammar :: Prover ()
uncompileGrammar = modify (\(ns,_)->(ns,Nothing))

errorToString :: NormalError -> [NormalTrace] -> String
errorToString err tr = showWith err (0::ShowCtx) ++ concat (("\n\nwhile "++) . (`showWith` (0::ShowCtx)) <$> reverse tr)

runExt :: Show i => String -> (ProverState -> i -> Prover ProverState) -> IORef (ProverState,([Name],Maybe Grammar)) -> i -> L.Lua L.NumResults
runExt n f state i = do
    (s,ns) <- liftIO (readIORef state)
    (s',ns') <- runProver (traceError (CallingFunc n) $ f s i) ns
    case s' of
        Right s' -> liftIO (writeIORef state (s',ns')) >> pure 0
        Left (err,tr) -> L.raiseError (errorToString err tr)

runActionExt :: String -> (ProverState -> Prover ProverState) -> IORef (ProverState,([Name],Maybe Grammar)) -> L.Lua L.NumResults
runActionExt n f state = do
    (s,ns) <- liftIO (readIORef state)
    (s',ns') <- runProver (traceError (CallingFunc n) $ f s) ns
    case s' of
        Right s' -> liftIO (writeIORef state (s',ns')) >> pure 0
        Left (err,tr) -> L.raiseError (errorToString err tr)

runOutputExt :: L.Pushable o => String -> (ProverState -> Prover (ProverState, o)) -> IORef (ProverState,([Name],Maybe Grammar)) -> L.Lua L.NumResults
runOutputExt n f state = do
    (s,ns) <- liftIO (readIORef state)
    (o,ns') <- runProver (traceError (CallingFunc n) $ f s) ns
    case o of
        Right (s',o) -> liftIO (writeIORef state (s',ns')) >> L.push o >> pure 1
        Left (err,tr) -> L.raiseError (errorToString err tr)

runProver :: Prover i -> ([Name],Maybe Grammar) -> L.Lua (Either (NormalError,[NormalTrace]) i, ([Name],Maybe Grammar))
runProver f = runStateT (runTraceT f)

envToElabCtx :: Env -> ElabCtx
envToElabCtx (Sorts s, ConstObjs o, DefObjs d, Axioms a) =
    let sorts = M.fromList (fmap (\s -> (s,(s,Global,Sort))) (S.toList s))
        consts = M.fromList (fmap (\c -> (c,(c,Global,Obj))) (M.keys o))
        defs = M.fromList (fmap (\d -> (d,(d,Global,Obj))) (M.keys d))
        axioms = M.fromList (fmap (\a -> (a,(a,Global,Prf))) (M.keys a))
    in sorts `M.union` consts `M.union` defs `M.union` axioms

initialState :: ProverState
initialState = (S.empty, grINIT, (Sorts mempty, ConstObjs mempty, DefObjs mempty, Axioms mempty), Nothing)

insertAxiom :: Name -> Term -> ProverState -> ProverState
insertAxiom n m (kw, grammar, (s,o,d,Axioms a), goal) =
    (kw, grammar, (s,o,d,Axioms (M.insert n m a)), goal)

insertSort :: Name -> ProverState -> ProverState
insertSort n (kw, grammar, (Sorts s,o,d,a), goal) =
    (kw, grammar, (Sorts (S.insert n s),o,d,a), goal)

insertConst :: Name -> Polytype -> ProverState -> ProverState
insertConst n t (kw, grammar, (s,ConstObjs o,d,a), goal) =
    (kw, grammar, (s,ConstObjs (M.insert n t o),d,a), goal)

insertDef :: Name -> Polytype -> Term -> ProverState -> ProverState
insertDef n m t (kw, grammar, (s,o,DefObjs d,a), goal) =
    (kw, grammar, (s,o,DefObjs (M.insert n (m,t) d),a), goal)

insertKeyword :: Name -> ProverState -> ProverState
insertKeyword k (kw, grammar, env, goal) = (S.insert k kw, grammar, env, goal)

envToCtx :: Env -> Ctx
envToCtx (_, ConstObjs objs, DefObjs defobjs, Axioms ax) =
    let objctx = objs `M.union` fmap fst defobjs
        defctx = fmap snd defobjs
        thmctx = ax
    in (thmctx,objctx,defctx)

checkProof :: ProverState -> Term -> Proof -> Prover [Term]
checkProof (_, _, env, _) prop prf = do
    names <- getNames
    let (err,names') = runProofCheck names (envToCtx env) prop prf
    putNames names'
    fmap snd . withTraceT CheckerT . withErrorT Checker $ liftTrace err

checkProp :: ProverState -> Monotype -> Term -> Prover Term
checkProp (_, _, env, _) sort prop = do
    names <- getNames
    let (err,names') = runPropCheck names (envToCtx env) sort prop
    putNames names'
    withTraceT CheckerT . withErrorT Checker $ liftTrace err

inferProp :: ProverState -> Term -> Prover (Term,Monotype)
inferProp (_, _, env, _) prop = do
    names <- getNames
    let (err,names') = runPropInfer names (envToCtx env) prop
    putNames names'
    withTraceT CheckerT . withErrorT Checker $ liftTrace err

evalProp :: ProverState -> Term -> Prover Term
evalProp (_, _, env, _) prop = do
    names <- getNames
    let (err,names') = evalTerm names (envToCtx env) prop
    putNames names'
    withTraceT CheckerT . withErrorT Checker $ liftTrace err

refine :: ProverState -> (Proof, [ElabCtx]) -> Prover ProverState
refine (_, _, _, Nothing) _ = throwError NotInProofMode
refine (kw, grammar, env, Just (prop, prf, ctxs)) (p, ctxs') = case fillHole prf p of
    Just prf' ->
        let state' = (kw, grammar, env, Just (prop, prf', ctxs'))
        in do
            holes <- checkProof state' prop prf'
            pure state'
    Nothing -> throwError NoOpenGoals

addNotation :: ProverState -> Name -> [NotationBinding] -> SExpr -> Prover ProverState
addNotation (kw, grammar, env, p) n ns s =
    case makeProdRule n ns s of
        Left err -> throwError (Parser err)
        Right prod -> uncompileGrammar >> pure (kw, M.adjust (prod:) n grammar, env, p)

beginProof :: ProverState -> Term -> Prover ProverState
beginProof (kw, grammar, env, Nothing) t = pure (kw, grammar, env, Just (t, Hole, [mempty]))
beginProof _ _ = throwError InProofMode

endProof :: ProverState -> T.Text -> Prover ProverState
endProof (_, _, _, Nothing) t = throwError NotInProofMode
endProof (_, _, _, Just (_, _, _:_)) _ = throwError OpenGoals
endProof s@(kw, gr, env, Just (prop, _, [])) t =
    pure (insertAxiom t prop (kw, gr, env, Nothing))

goalCtx :: ProverState -> Prover ElabCtx
goalCtx (_, _, env, Just (_, _, ctx:_)) = pure (ctx `M.union` envToElabCtx env)
goalCtx (_, _, _, Just _) = throwError NoOpenGoals
goalCtx _ = throwError NotInProofMode

envCtx :: ProverState -> ElabCtx
envCtx (_, _, env, _) = envToElabCtx env

parseProof :: ProverState -> Grammar -> ElabCtx -> T.Text -> Prover (Proof, [ElabCtx], ProverState)
parseProof s@(kw, grammar, env, p) g ctx t = do
    case parse kw g ntPROOF t of
        Left err -> throwError (Parser err)
        Right s -> do
            names <- getNames
            case runElaborator names ctx (elabProof s) of
                ((Right o, ctx'), names') -> putNames names' >> pure (o, ctx', (kw, grammar, env, p))
                ((Left err, _), _) -> throwError (Parser err)

parseMonotype :: ProverState -> Grammar -> ElabCtx -> T.Text -> Prover (Monotype, ProverState)
parseMonotype (kw, grammar, env, p) g ctx t =
    case parse kw g ntSORT t of
        Left err -> throwError (Parser err)
        Right s -> do
            names <- getNames
            case runElaborator names ctx (elabMonotype s) of
                ((Right o, _), names') -> putNames names' >> pure (o, (kw, grammar, env, p))
                ((Left err, _), _) -> throwError (Parser err)

parseProp :: ProverState -> Grammar -> ElabCtx -> T.Text -> Prover (Term, ProverState)
parseProp (kw, grammar, env, p) g ctx t =
    case parse kw g ntPROP t of
        Left err -> throwError (Parser err)
        Right s -> do
            names <- getNames
            case runElaborator names ctx (elabProp s) of
                ((Right o, _), names') -> putNames names' >> pure (o, (kw, grammar, env, p))
                ((Left err, _), _) -> throwError (Parser err)

parseSort :: ProverState -> Grammar -> ElabCtx -> T.Text -> Prover (Monotype, ProverState)
parseSort (kw, grammar, env, p) g ctx t =
    case parse kw g ntSORT t of
        Left err -> throwError (Parser err)
        Right s -> do
            names <- getNames
            case runElaborator names ctx (elabSort s) of
                ((Right o, _), names') -> putNames names' >> pure (o, (kw, grammar, env, p))
                ((Left err, _), _) -> throwError (Parser err)

parsePolytype :: ProverState -> Grammar -> ElabCtx -> T.Text -> Prover (Polytype, ProverState)
parsePolytype (kw, grammar, env, p) g ctx t =
    case parse kw g ntSORT t of
        Left err -> throwError (Parser err)
        Right s -> do
            names <- getNames
            case runElaborator names ctx (elabPolytype s) of
                ((Right o, _), names') -> putNames names' >> pure (o, (kw, grammar, env, p))
                ((Left err, _), _) -> throwError (Parser err)

parseNotationBinding :: ProverState -> Grammar -> T.Text -> Prover (Name, [NotationBinding])
parseNotationBinding (kw, grammar, env, p) g t =
    case parse kw g ntNOTATION t of
        Left err -> throwError (Parser err)
        Right s -> do
            case runElaborator [] mempty (elabNotation s) of
                ((Right o, _), _) -> pure o
                ((Left err, _), _) -> throwError (Parser err)

parseNotationProduct :: ProverState -> S.Set Name -> Name -> T.Text -> Prover SExpr
parseNotationProduct (kw, grammar, env, p) ps n t = do
    ns <- getNames
    g <- case elimLeftRec ns (addPlaceholders ps grammar) of
            (Right g,ns) -> do
                putNames ns
                pure g
            (Left err,ns) -> throwError (Parser err)
    case parse kw g n t of
        Left err -> throwError (Parser err)
        Right s -> pure s

refineExt :: ProverState -> T.Text -> Prover ProverState
refineExt s t = do
    (p, ctxs', s') <- do
        ctx <- goalCtx s
        g <- compileGrammar s
        parseProof s g ctx t
    refine s' (p, ctxs')

newKeywordExt :: ProverState -> T.Text -> Prover ProverState
newKeywordExt s t = pure (insertKeyword t s)

-- maybe add a flag to check if polytype constants should be allowed
newConstExt :: ProverState -> (T.Text, T.Text) -> Prover ProverState
newConstExt s (n, t) = do
    (m, s') <- do
        g <- compileGrammar s
        parseSort s g (envCtx s) t
    pure (insertConst n (Polytype mempty m) s')

defineExt :: ProverState -> (T.Text, T.Text) -> Prover ProverState
defineExt s (n, d) = do
    (df, s') <- do
        g <- compileGrammar s
        parseProp s g (envCtx s) d
    (df',m) <- inferProp s' df
    db <- evalProp s' df
    pure (insertDef n (runGeneralize m) db s')

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
printGrammarExt s@(_, g, _, _) = liftIO (print (fmap (fmap snd) g)) >> pure s

doneExt :: ProverState -> Prover ProverState
doneExt (_, _, _, Nothing) = throwError NotInProofMode
doneExt (_, _, _, Just (_, _, _:_)) = throwError OpenGoals
doneExt s@(_, _, _, Just (prop, _, [])) =
    pure s

dieExt :: ProverState -> Prover ProverState
dieExt _ = throwError Terminated

updatedState :: Keywords -> Grammar -> Env -> Prover ProverState
updatedState kw g e = do
    uncompileGrammar
    pure (kw, g,e,Nothing)

includeStateExt :: ProverState -> B.ByteString -> Prover ProverState
includeStateExt (kw,g,e,Nothing) b = do
    (kw', g',e') <- deserializeProverState b
    updatedState (kw `S.union` kw') (g `M.union` g') (e <> e')
includeStateExt _ _ = throwError InProofMode

loadStateExt :: ProverState -> B.ByteString -> Prover ProverState
loadStateExt (_,_,_,Nothing) b = do
    (kw,g,e) <- deserializeProverState b
    updatedState kw g e
loadStateExt _ _ = throwError InProofMode

dumpStateExt :: ProverState -> Prover (ProverState,B.ByteString)
dumpStateExt (kw,g,e,Nothing) = do
    b <- serializeProverState (kw,g,e)
    pure ((kw,g,e,Nothing),b)
dumpStateExt _ = throwError InProofMode