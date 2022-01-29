module Kernel.Eval (unifyTerm,whnfTerm) where

import Kernel.Subst
import Kernel.Types

import Kernel.TypeCheck

import Control.Monad
import Control.Monad.Except
import Control.Monad.Trace

import qualified Data.Set as S
import qualified Data.Map as M
import Data.Maybe (fromMaybe)

occurs :: Name -> Term -> Bool
occurs n x = S.member n (locations substMetaVarsTerm x)

bind2 :: Monad m => (a -> b -> m c) -> m a -> m b -> m c
bind2 f x y = liftM2 (,) x y >>= uncurry f

composeTermSubst :: TermSubst -> TermSubst -> Infer TermSubst
composeTermSubst f g = (<>g) <$> traverse (substRenaming substMetaVarsTerm f) g

unifyTerm :: DefCtx -> Term -> Term -> Infer (TermSubst, TypeSubst)
unifyTerm ctx x y | x == y = pure mempty
unifyTerm ctx (MetaVar a) y | not (occurs a y) = pure (M.singleton a y,mempty)
unifyTerm ctx x (MetaVar b) | not (occurs b x) = pure (M.singleton b x,mempty)
unifyTerm ctx (App x y) (App z w) = do
    (t,m) <- unifyTerm ctx x z
    (t',m') <- bind2 (unifyTerm ctx) (substRenaming substMetaVarsTerm t y) (substRenaming substMetaVarsTerm t z)
    u <- composeTermSubst t' t
    pure (u,m'<+m)
unifyTerm ctx (Imp x y) (Imp z w) = do
    (t,m) <- unifyTerm ctx x z
    (t',m') <- bind2 (unifyTerm ctx) (substRenaming substMetaVarsTerm t y) (substRenaming substMetaVarsTerm t z)
    u <- composeTermSubst t' t
    pure (u,m'<+m)
unifyTerm ctx (Forall n0 m0 t0) (Forall n1 m1 t1) = do
    m <- unifyTyp m0 m1
    t1' <- replace n1 n0 <$> rename t1
    (t,m') <- unifyTerm ctx (subst m t0) (subst m t1')
    pure (t,m'<+m)
unifyTerm ctx a b = do
    a' <- reduceWhnfTerm ctx a
    b' <- reduceWhnfTerm ctx b
    case (a',b') of
        (Nothing,Nothing) -> throwError (ObjectUnificationFail a b)
        (Just a,Nothing) -> unifyTerm ctx a b
        (Nothing,Just b) -> unifyTerm ctx a b
        (Just a, Just b) -> unifyTerm ctx a b

reduceWhnfTerm :: DefCtx -> Term -> Infer (Maybe Term)
reduceWhnfTerm ctx (App f x) = do
    f' <- whnfTerm ctx f
    case f' of
      Lam v d -> fmap Just . whnfTerm ctx =<< substRenaming substVarsTerm (M.singleton v x) d
      _ -> pure Nothing
reduceWhnfTerm ctx (Var n) = pure (M.lookup n ctx)
reduceWhnfTerm _ _ = pure Nothing

whnfTerm :: DefCtx -> Term -> Infer Term
whnfTerm ctx (App f x) = do
    f' <- whnfTerm ctx f
    case f' of
        Lam v d -> whnfTerm ctx =<< substRenaming substVarsTerm (M.singleton v x) d
        x -> pure x
whnfTerm ctx (Var n) = pure (fromMaybe (Var n) (M.lookup n ctx))
whnfTerm _ x = pure x