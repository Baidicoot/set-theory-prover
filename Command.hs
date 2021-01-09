module Command where
import TT
import Control.Monad.Except
import Control.Monad.State
import Data.List

data Command
    = Axiom String Exp
    | Define String Exp
    | Check Exp
    | Eval Exp
    | Print [String]
    | PrintAll
    | PrintUniverses
    deriving(Show)

data CommandOutput
    = DefAxiom String Val
    | Defined String Val Val
    | Checked Val
    | Evaluated Val
    | PrintCtx Ctx
    | PrintGraph OrderingGraph

roots :: OrderingGraph -> [Universe]
roots g =
    let candidates = fmap fst g
        reached = concatMap snd g
    in [n | n <- candidates, n `notElem` reached]

data ShowGraph
    = Fork Universe [ShowGraph]

showPipeIndent :: [Int] -> String
showPipeIndent [] = ""
showPipeIndent (n:ns) = internal ns ++ replicate n ' ' ++ "|"
    where
        internal (n:ns) = internal ns ++ replicate n ' ' ++ "|   "
        internal [] = ""

flagLast :: [a] -> [(Bool,a)]
flagLast [a] = [(True,a)]
flagLast [] = []
flagLast (a:as) = (False,a):flagLast as

showShowGraph :: Bool -> [Int] -> ShowGraph -> String
showShowGraph False i (Fork u gs) =
    let is = show u
        i' = length is - 1:i
    in is ++ intercalate ('\n':showPipeIndent i') (fmap (\(b,g) -> " < "++showShowGraph b i' g) (flagLast gs))
showShowGraph True (p:i) (Fork u gs) =
    let is = show u
        i' = p+4+length is-1:i
    in is ++ intercalate ('\n':showPipeIndent i') (fmap (\(b,g) -> " < "++showShowGraph b i' g) (flagLast gs))

instance Show ShowGraph where
    show = showShowGraph False []

graphNodes :: ShowGraph -> [Universe]
graphNodes (Fork u ns) = u:concatMap graphNodes ns

showGraph :: Universe -> [Universe] -> OrderingGraph -> ShowGraph
showGraph n f g = case lookup n g of
    Just ns -> Fork n (foldr (\n gs -> showGraph n (f++concatMap graphNodes gs) g:gs) [] (filter (`notElem` f) ns))
    Nothing -> Fork n []

showOrdering :: OrderingGraph -> String
showOrdering g =
    let gs = foldr (\n gs -> showGraph n (concatMap graphNodes gs) g:gs) [] (roots g)
    in intercalate "\n\n" (fmap show gs)

instance Show CommandOutput where
    show (DefAxiom s v) = "Defined Axiom \'" ++ s ++ "\' : " ++ show v ++ ".\n"
    show (Defined s t v) = "Defined \'" ++ s ++ "\' : " ++ show t ++ "\n    := " ++ show v ++ ".\n"
    show (Checked v) = "Has type " ++ show v ++ ".\n"
    show (Evaluated v) = "Results in " ++ show v ++ ".\n"
    show (PrintCtx c) = intercalate "\n\n" (fmap (\(n,(t,d)) -> case d of
        Just d -> "Definition '" ++ n ++ "' : " ++ show t ++ "\n    := " ++ show d ++ "."
        Nothing -> "Axiom '" ++ n ++ "' : " ++ show t ++ ".") c) ++ "\n"
    show (PrintGraph g) = showOrdering g

type CommandState = (Ctx,OrderingGraph,Universe)

emptyState :: CommandState
emptyState = ([],[],0)

docmd :: Command -> CommandState -> Res (CommandOutput,CommandState)
docmd (Axiom n e) (ctx,ord,u) = do
    put u
    (_,ord) <- inferWithOrderCheck ctx ord e
    x <- eval ctx e
    u <- get
    pure (DefAxiom n x,((n,(x,Nothing)):ctx,ord,u))
docmd (Define n e) (ctx,ord,u) = do
    put u
    (t,ord) <- inferWithOrderCheck ctx ord e
    x <- eval ctx e
    u <- get
    pure (Defined n t x,((n,(t,Just x)):ctx,ord,u))
docmd (Check e) (ctx,ord,u) = do
    put u
    (t,_) <- inferWithOrderCheck ctx ord e
    pure (Checked t,(ctx,ord,u))
docmd (Eval e) (ctx,ord,u) = do
    put u
    inferWithOrderCheck ctx ord e
    x <- eval ctx e
    pure (Evaluated x,(ctx,ord,u))
docmd (Print ns) (ctx,ord,u) = do
    defs <- mapM (\n -> case lookup n ctx of
        Just d -> pure (n,d)
        Nothing -> throwError ("identifier \"" ++ show n ++ "\" not defined")) ns
    pure (PrintCtx defs,(ctx,ord,u))
docmd PrintAll (ctx,ord,u) = pure (PrintCtx (reverse ctx),(ctx,ord,u))
docmd PrintUniverses (ctx,ord,u) = pure (PrintGraph ord,(ctx,ord,u))