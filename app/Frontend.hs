module Frontend where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.IORef
import Foreign.Ptr

import Kernel

import qualified Foreign.Lua as Lua

newtype ConstObjs = ConstObjs (M.Map Name Monotype)
newtype DefinedObjs = DefObjs (M.Map Name (Monotype,DeBrujin))
newtype ConstSorts = Sorts (S.Set Name)
newtype Axioms = Axioms (M.Map Name DeBrujin)
type Env = (ConstSorts, ConstObjs, DefObjs, Axioms)

-- names, grammar, global environment, current proof and local names for each goal (if applicable)
type State = ([Name], Grammar, Env, Maybe (Proof, [ElabCtx]))

fillHole :: Proof -> Proof -> Maybe Proof
fillHole Hole p = pure p
fillHole (ModPon a b) p = case fillHole a p of
    Just a' -> pure (ModPon a' b)
    Nothing -> ModPon a <$> fillHole b p
fillHole (IntrosThm n t a) p = IntrosThm n t <$> fillHole a p
fillHole (IntrosObj n t a) p = IntrosObj n t <$> fillHole a p
fillHole (UniElim a t) = flip UniElim t <$> fillHole a p
fillHole _ = Nothing

refine :: State -> Proof -> Lua State

beginProof :: State -> Text -> Prop -> Lua State

endProof :: State -> Lua State

parseProof :: State -> Text -> Lua (Proof, [Name], [ElabCtx])
parseProof (_, _, _, Nothing) _ = error "NOT IN PROOF MODE"
parseProof (_, _, _, Just (_, [])) _ = error "NO OPEN GOALS"
parseProof (names, grammar, env, Just (prf, (ctx:ctxs))) t = case parse grammar nt_PROOF t of
    Left err -> error (show err)
    Right s -> case runElaborator names ctx (elabProof s) of
        ((Right o, names'), ctx') -> pure (o, names', ctx')
        ((Left err, _), _) -> error (show err)

parseSort :: State -> Text -> Lua Monotype

parseProp :: State -> Text -> Lua Term

parseProd :: State -> Text -> Text -> Lua ProdRule

refineExt :: IORef State -> Text -> Lua ()

assertExt :: IORef State -> Text -> Text -> Lua ()

newSortExt :: IORef State -> Text -> Lua ()

notationExt :: IORef State -> Text -> Text -> Lua ()

beginProofExt :: IORef State -> Text -> Text -> Lua ()

endProofExt :: IORef State -> Lua ()

{- references to IORef through CLOSURES! -}

{-
-- i.e.
main = do
    x <- newIORef mempty
    Lua.registerHaskellFunction "reduce" (reduce x)
-}