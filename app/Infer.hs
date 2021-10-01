module Infer where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad
import Control.Monad.State
import Control.Monad.Except

import Logic

{-
Infer.hs - INFERENCE FOR THE OBJECT LANGUAGE
============================================
Basically just Hindley-Milner.
Adapted from http://dev.stephendiehl.com/fun/006_hindley_milner.html
-}

type Subst = Map.Map Name Monotype
type TypingCtx = M.Map Name Polytype

names :: [Name]
names = [T.pack (v:show n) | v <- ['A'..'Z'], n <- [0..]]

data TypeError

type Infer = ExceptT TypeError (State [Name])

fresh :: Infer Name
fresh = do
    (x:xs) <- get
    put xs
    pure x

class Substitutable a where
    subst :: Subst -> a -> a
    free :: a -> S.Set Name

instance Substitutable Monotype where
    subst s (Arr a b) = App (subst s a) (subst s b)
    subst s (TyVar n) = case M.lookup n s of
        Nothing -> TyVar n
        Just t -> t
    subst _ t = t
    
    free (Arr a b) = free a `S.union` free b
    free (TyVar n) = S.singleton n
    free _ = S.empty

instance Substitutable Polytype where
    subst s (Polytype v t) = Polytype v (subst (M.filter (not . flip elem v) s) t)
    free (Polytype v t) = free t `S.difference` v

instance Substitutable TypingCtx where
    subst s ctx = M.fmap (subst s) ctx
    free ctx = S.unions (fmap free $ M.toList ctx)

instantiate :: Polytype -> Infer Monotype
instantiate (Polytype v t) = do
    s <- M.fromList <$> mapM (\n -> ((,) n) <$> fresh) (S.toList v)
    pure (subst s t)

generalize :: TypingCtx -> Monotype -> Polytype
generalize ctx t = Polytype (M.keysSet `S.difference`)