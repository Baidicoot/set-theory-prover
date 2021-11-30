module Frontend (initialState, refineExt, assertExt, newSortExt, beginProofExt, endProofExt) where

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

import qualified Foreign.Lua as L

newtype ConstObjs = ConstObjs (M.Map Name Monotype) deriving(Show)
newtype DefObjs = DefObjs (M.Map Name (Monotype,DeBrujin)) deriving(Show)
newtype ConstSorts = Sorts (S.Set Name) deriving(Show)
newtype Axioms = Axioms (M.Map Name Term) deriving(Show)
type Env = (ConstSorts, ConstObjs, DefObjs, Axioms)

-- names, grammar, global environment, current proof and local names for each goal (if applicable)
type State = ([Name], Grammar, Env, Maybe (Term, Proof, [ElabCtx]))

envToElabCtx :: Env -> ElabCtx
envToElabCtx (Sorts s, ConstObjs o, DefObjs d, Axioms a) =
    let sorts = M.fromList (fmap (\s -> (s,(s,Global,Sort))) (S.toList s))
        consts = M.fromList (fmap (\c -> (c,(c,Global,Obj))) (M.keys o))
        defs = M.fromList (fmap (\d -> (d,(d,Global,Obj))) (M.keys d))
        axioms = M.fromList (fmap (\a -> (a,(a,Global,Prf))) (M.keys a))
    in sorts `M.union` consts `M.union` defs `M.union` axioms

initialNames :: [Name]
initialNames = fmap (T.pack . ("v"++) . show) [1..]

initialState :: State
initialState = (initialNames, gr_INIT, (Sorts mempty, ConstObjs mempty, DefObjs mempty, Axioms mempty), Nothing)

insertAxiom :: Name -> Term -> State -> State
insertAxiom n m (names, grammar, (s,o,d,Axioms a), goal) =
    (names, grammar, (s,o,d,Axioms (M.insert n m a)), goal)

insertSort :: Name -> State -> State
insertSort n (names, grammar, (Sorts s,o,d,a), goal) =
    (names, grammar, (Sorts (S.insert n s),o,d,a), goal)

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

checkProof :: State -> L.Lua [Term]
checkProof (_, _, _, Nothing) = error "NOT IN PROOF MODE"
checkProof (ns, _, env, Just (prop, prf, _)) =
    let (res, ns') = runProofCheck ns (envToCtx env) prop prf
    in case res of
        Right (_, hs) -> pure hs
        Left err -> error (show err)

refine :: State -> (Proof, [ElabCtx]) -> L.Lua State
refine (_, _, _, Nothing) _ = error "NOT IN PROOF MODE"
refine (names, grammar, env, Just (prop, prf, ctxs)) (p, ctxs') = case fillHole prf p of
    Just prf' -> let state' = (names, grammar, env, Just (prop, prf', ctxs')) in checkProof state' >> pure state'
    Nothing -> error "NO HOLES TO REFINE"

beginProof :: State -> Term -> L.Lua State
beginProof (names, grammar, env, Nothing) t = pure (names, grammar, env, Just (t, Hole, [mempty]))
beginProof _ _ = error "ALREADY IN PROOF MODE"

endProof :: State -> T.Text -> L.Lua State
endProof (_, _, _, Nothing) t = error "NOT IN PROOF MODE"
endProof (_, _, _, Just (_, _, _:_)) _ = error "PROOF NOT FINISHED"
endProof s@(_, _, _, Just (prop, _, [])) t =
    pure (insertAxiom t prop s)

parseProof :: State -> T.Text -> L.Lua (Proof, [ElabCtx], State)
parseProof (_, _, _, Nothing) _ = error "NOT IN PROOF MODE"
parseProof (_, _, _, Just (_, _, [])) _ = error "NO OPEN GOALS"
parseProof (names, grammar, env, Just (prop, prf, ctx:ctxs)) t = case parse grammar nt_PROOF t of
    Left err -> error (show err)
    Right s -> case runElaborator names (ctx `M.union` envToElabCtx env) (elabProof s) of
        ((Right o, ctx'), names') -> pure (o, ctx', (names', grammar, env, Just (prop, prf, ctx:ctxs)))
        ((Left err, _), _) -> error (show err)

parseMonotype :: State -> T.Text -> L.Lua (Monotype, State)
parseMonotype (names, grammar, env, p) t =
    let ctx = case p of
            Just (_, _, ctx:_) -> ctx
            Just (_, _, []) -> error "NO OPEN GOALS"
            _ -> mempty
    in case parse grammar nt_SORT t of
    Left err -> error (show err)
    Right s -> case runElaborator names (ctx `M.union` envToElabCtx env) (elabMonotype s) of
        ((Right o, _), names') -> pure (o, (names', grammar, env, p))
        ((Left err, _), _) -> error (show err)

parseProp :: State -> T.Text -> L.Lua (Term, State)
parseProp (names, grammar, env, p) t =
    let ctx = case p of
            Just (_, _, ctx:_) -> ctx
            Just (_, _, []) -> error "NO OPEN GOALS"
            _ -> mempty
    in case parse grammar nt_PROP t of
    Left err -> error (show err)
    Right s -> case runElaborator names (ctx `M.union` envToElabCtx env) (elabProp s) of
        ((Right o, _), names') -> pure (o, (names', grammar, env, p))
        ((Left err, _), _) -> error (show err)

{-
parseProd :: State -> T.Text -> T.Text -> L.Lua ProdRule
-}

refineExt :: IORef State -> T.Text -> L.Lua ()
refineExt is t = do
    s <- L.liftIO (readIORef is)
    (p, ctxs', s') <- parseProof s t
    s'' <- refine s (p, ctxs')
    L.liftIO (writeIORef is s'')

assertExt :: IORef State -> T.Text -> T.Text -> L.Lua ()
assertExt is n t = do
    s <- L.liftIO (readIORef is)
    (m, s') <- parseProp s t
    L.liftIO (print m)
    L.liftIO (writeIORef is (insertAxiom n m s'))

newSortExt :: IORef State -> T.Text -> L.Lua ()
newSortExt is n = L.liftIO (modifyIORef is (insertSort n))

{-
notationExt :: IORef State -> T.Text -> T.Text -> L.Lua ()
-}

beginProofExt :: IORef State -> T.Text -> L.Lua ()
beginProofExt is t = do
    s <- L.liftIO (readIORef is)
    (p, s') <- parseProp s t
    s'' <- beginProof s' p
    L.liftIO (writeIORef is s'')

endProofExt :: IORef State -> T.Text -> L.Lua ()
endProofExt is n = do
    s <- L.liftIO (readIORef is)
    s' <- endProof s n
    L.liftIO (writeIORef is s')

{- references to IORef through CLOSURES! -}

{-
-- i.e.
main = do
    x <- newIORef mempty
    Lua.registerHaskellFunction "reduce" (reduce x)
-}