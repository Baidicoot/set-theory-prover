{-# LANGUAGE FunctionalDependencies #-}
module Frontend (initialState, refineExt, assertExt, newSortExt, newConstExt, beginProofExt, endProofExt) where

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

import Control.Monad.State
import Control.Monad.IO.Class

import qualified Foreign.Lua as L

newtype ConstObjs = ConstObjs (M.Map Name Monotype) deriving(Show)
newtype DefObjs = DefObjs (M.Map Name (Monotype,DeBrujin)) deriving(Show)
newtype ConstSorts = Sorts (S.Set Name) deriving(Show)
newtype Axioms = Axioms (M.Map Name Term) deriving(Show)
type Env = (ConstSorts, ConstObjs, DefObjs, Axioms)

-- names, grammar, global environment, current proof and local names for each goal (if applicable)
type ProverState = (Grammar, Env, Maybe (Term, Proof, [ElabCtx]))

type Prover = StateT [Name] L.Lua

runExt :: (ProverState -> i -> Prover ProverState) -> IORef (ProverState,[Names]) -> i -> L.Lua ()
runExt f state i = do
    (s,ns) <- liftIO (readIORef state)
    let (x,ns') = runProver (f s i) ns
    s' <- x
    liftIO (writeIORef state (s',ns'))
    pure s'

runProver :: Prover i -> [Names] -> (L.Lua i, [Names])
runProver = runStateT

envToElabCtx :: Env -> ElabCtx
envToElabCtx (Sorts s, ConstObjs o, DefObjs d, Axioms a) =
    let sorts = M.fromList (fmap (\s -> (s,(s,Global,Sort))) (S.toList s))
        consts = M.fromList (fmap (\c -> (c,(c,Global,Obj))) (M.keys o))
        defs = M.fromList (fmap (\d -> (d,(d,Global,Obj))) (M.keys d))
        axioms = M.fromList (fmap (\a -> (a,(a,Global,Prf))) (M.keys a))
    in sorts `M.union` consts `M.union` defs `M.union` axioms

initialState :: ProverState
initialState = (gr_INIT, (Sorts mempty, ConstObjs mempty, DefObjs mempty, Axioms mempty), Nothing)

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

fillHole :: Proof -> Proof -> Maybe Proof
fillHole Hole p = pure p
fillHole (ModPon a b) p = case fillHole a p of
    Just a' -> pure (ModPon a' b)
    Nothing -> ModPon a <$> fillHole b p
fillHole (IntrosThm n t a) p = IntrosThm n t <$> fillHole a p
fillHole (IntrosObj n t a) p = IntrosObj n t <$> fillHole a p
fillHole (UniElim a t) p = flip UniElim t <$> fillHole a p
fillHole _ _ = Nothing

checkProof :: Term -> Proof -> Prover [Term]
checkProof prop prf = do
    names <- get
    case runProofCheck names (envToCtx env) prop prf of
        (Right (_, holes), names') -> put names' >> pure holes
        (Left err, _) -> error (show err)

checkProp :: Monotype -> Term -> Prover Term
checkProp sort prop = do
    names <- get
    case runPropCheck names (envToCtx env) sort prop of
        (Right t, names') -> put names' >> pure t
        (Left err, _) -> error (show err)

refine :: ProverState -> (Proof, [ElabCtx]) -> Prover ProverState
refine (_, _, Nothing) _ = error "NOT IN PROOF MODE"
refine (grammar, env, Just (prop, prf, ctxs)) (p, ctxs') = case fillHole prf p of
    Just prf' ->
        let state' = (grammar, env, Just (prop, prf', ctxs'))
        in snd <$> checkProof state' prop prf'
    Nothing -> error "NO HOLES TO REFINE"

beginProof :: ProverState -> Term -> Prover ProverState
beginProof (grammar, env, Nothing) t = pure (grammar, env, Just (t, Hole, [mempty]))
beginProof _ _ = error "ALREADY IN PROOF MODE"

endProof :: ProverState -> T.Text -> Prover ProverState
endProof (_, _, Nothing) t = error "NOT IN PROOF MODE"
endProof (_, _, Just (_, _, _:_)) _ = error "PROOF NOT FINISHED"
endProof s@(_, _, Just (prop, _, [])) t =
    pure (insertAxiom t prop s)

goalCtx :: ProverState -> Prover ElabCtx
goalCtx (_, env, Just (_, _, ctx:_)) = pure (ctx `M.union` envToElabCtx env)
goalCtx (_, _, Just _) = error "NO OPEN GOALS"
goalCtx _ = error "NOT IN PROOF MODE"

envCtx :: ProverState -> ElabCtx
envCtx (_, env, _) = envToElabCtx env

parseProof :: ProverState -> ElabCtx -> T.Text -> Prover (Proof, [ElabCtx], ProverState)
parseProof (names, grammar, env, p) ctx t =
    case parse grammar nt_PROOF t of
        Left err -> error (show err)
        Right s -> do
            names <- get
            case runElaborator names ctx (elabProof s) of
                ((Right o, ctx'), names') -> put names' >> pure (o, ctx', (grammar, env, p))
                ((Left err, _), _) -> error (show err)

parseMonotype :: ProverState -> ElabCtx -> T.Text -> Prover (Monotype, ProverState)
parseMonotype (grammar, env, p) ctx t =
    case parse grammar nt_SORT t of
        Left err -> error (show err)
        Right s -> do
            names <- get
            case runElaborator names ctx (elabMonotype s) of
                ((Right o, _), names') -> put names' >> pure (o, (grammar, env, p))
                ((Left err, _), _) -> error (show err)

parseProp :: ProverState -> ElabCtx -> T.Text -> Prover (Term, ProverState)
parseProp (grammar, env, p) ctx t =
    case parse grammar nt_PROP t of
        Left err -> error (show err)
        Right s -> do
            names <- get
            case runElaborator names ctx (elabProp s) of
                ((Right o, _), names') -> put names' >> pure (o, (grammar, env, p))
                ((Left err, _), _) -> error (show err)

parseSort :: ProverState -> ElabCtx -> T.Text -> Prover (Monotype, ProverState)
parseSort (names, grammar, env, p) ctx t =
    case parse grammar nt_SORT t of
        Left err -> error (show err)
        Right s -> do
            names <- get
            case runElaborator names ctx (elabSort s) of
                ((Right o, _), names') -> put names' >> pure (o, (grammar, env, p))
                ((Left err, _), _) -> error (show err)

{-
parseProd :: ProverState -> T.Text -> T.Text -> Prover ProdRule
-}

refineExt :: ProverState -> T.Text -> Prover ProverState
refineExt s t = do
    (p, ctxs', s') <- goalCtx s >>= \x -> parseProof s x t
    refine s (p, ctxs')

newConstExt :: ProverState -> (T.Text, T.Text) -> Prover ProverState
newConstExt s (n, t) = do
    (m, s') <- parseSort s (envCtx s) t
    pure (insertConst n m s')

assertExt :: ProverState -> (T.Text, T.Text) -> Prover ProverState
assertExt s (n, t) = do
    (m, s') <- parseProp s (envCtx s) t
    (m', s'') <- checkProp s' Prop m
    pure (insertAxiom n m' s'')

newSortExt :: ProverState -> T.Text -> Prover ProverState
newSortExt s n = pure (insertSort n s)

{-
notationExt :: IORef ProverState -> T.Text -> T.Text -> Prover ()
-}

beginProofExt :: ProverState -> T.Text -> Prover ProverState
beginProofExt s t = do
    (p, s') <- parseProp s (envCtx s) t
    beginProof s' p

endProofExt :: ProverState -> T.Text -> Prover ProverState
endProofExt s n = endProof s n

{- references to IORef through CLOSURES! -}

{-
-- i.e.
main = do
    x <- newIORef mempty
    Lua.registerHaskellFunction "reduce" (reduce x)
-}