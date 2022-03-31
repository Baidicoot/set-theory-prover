{-# LANGUAGE OverloadedStrings #-}
module Main where

import Test.Hspec

import Kernel
import Kernel.Eval
import Kernel.ProofCheck
import Kernel.Subst
import Kernel.TypeCheck
import Kernel.Types

import qualified Data.Text as T
import qualified Data.Map as M

runNoCtx :: Infer a -> Either (ProofError, [ProofTrace]) a
runNoCtx = fst . runInfer mempty

runNames :: Infer a -> Either (ProofError, [ProofTrace]) a
runNames = fst . runInfer (names, mempty)

reduceSpec :: Spec
reduceSpec = describe "whnf reduction" $ do
    it "evaluates lambdas" $
        runNoCtx (whnfTerm mempty (App
            (Lam "x" (Var "x"))
            (Var "y")))
        == Right
            (Var "y")
    it "evaluates lets" $
        runNoCtx (whnfTerm mempty (Let
            "x" (Var "y")
            (Var "x")))
        == Right
            (Var "y")
    it "does not reduce vars" $
        runNoCtx (whnfTerm mempty (Var "x"))
        == Right (Var "x")

unifyTypSpec :: Spec
unifyTypSpec = describe "sort unifier" $ do
    it "binds on the left" $
        runNoCtx (unifyTyp
            (TyVar "M")
            (ConstTy "x"))
        == Right
            (M.singleton "M" (ConstTy "x"))
    it "binds on the left" $
        runNoCtx (unifyTyp
            (ConstTy "x")
            (TyVar "M"))
        == Right
            (M.singleton "M" (ConstTy "x"))

unifyTermSpec :: Spec
unifyTermSpec = describe "term unifier" $ do
    it "binds on the left" $
        runNoCtx (unifyTerm mempty
            (MetaVar "M")
            (Var "x"))
        == Right
            (M.singleton "M" (Var "x")
            , mempty)
    it "binds on the right" $
        runNoCtx (unifyTerm mempty
            (Var "x")
            (MetaVar "M"))
        == Right
            (M.singleton "M" (Var "x")
            , mempty)
    it "does not bind to itself" $
        runNoCtx (unifyTerm mempty
            (MetaVar "M")
            (MetaVar "M"))
        == Right mempty
    it "binds after reduction" $
        runNoCtx (unifyTerm mempty
            (App
                (Lam "x" (Var "x"))
                (MetaVar "M"))
            (Var "x"))
        == Right
            (M.singleton "M" (Var "x")
            , mempty)

sortInferSpec :: Spec
sortInferSpec = describe "sort inference" $ do
    it "infers lambdas correctly" $
        fmap snd (runNames (inferObj mempty
            (Lam "x" (Var "x"))))
        == Right
            (Arr (TyVar "A0") (TyVar "A0"))
    it "infers let-expressions correctly" $
        fmap snd (runNames (inferObj mempty
            (Let "x" (Lam "y" $ Var "y") (Var "x"))))
        == Right
            (Arr (TyVar "B0") (TyVar "B0"))
    it "does not admit omega" $
        case runNames (inferObj mempty
            (Lam "x" $ App (Var "x") (Var "x"))) of
            Left (InfiniteType _ _, _) -> True
            Right _ -> False
    it "infers propositions correctly" $
        fmap snd (runNames (inferObj mempty
            (Forall "x" Prop (Imp (Var "x") (Var "x")))))
        == Right Prop

fst3 :: (a,b,c) -> a
fst3 (a,_,_) = a

snd3 :: (a,b,c) -> b
snd3 (_,b,_) = b

proofInferSpec :: Spec
proofInferSpec = describe "proof checking" $ do
    it "infers introThm correctly" $
        fmap fst3 (runNames (inferThm
            (mempty,M.singleton "X" (Polytype mempty Prop),mempty)
            (IntroThm "H" (Var "X") (Axiom "H"))))
        == Right (Imp (Var "X") (Var "X"))

main :: IO ()
main = hspec $ do
    unifyTermSpec
    unifyTypSpec
    reduceSpec
    sortInferSpec
    proofInferSpec