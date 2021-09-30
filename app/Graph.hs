module Graph (insertEdge,acyclic,showOrdering,UniverseID,OrderingGraph) where

import Data.List

type UniverseID = Int

type OrderingGraph = [(UniverseID,[(UniverseID,Bool)])]

insertEdge :: UniverseID -> UniverseID -> Bool -> OrderingGraph -> OrderingGraph
insertEdge from to strict ((u,us):gs) | from == u && (to,strict) `elem` us = (u,us):gs
insertEdge from to strict ((u,us):gs) | from == u = (u,(to,strict):us):gs
insertEdge from to strict (n:gs) = n:insertEdge from to strict gs
insertEdge from to strict [] = [(from,[(to,strict)])]

type Cycle = [(UniverseID,Bool)]

takeUntil :: UniverseID -> Bool -> [(UniverseID,Bool)] -> [Cycle]
takeUntil u s ((x,_):_) | u == x = [[(u,s)]]
takeUntil u s (x:xs) = fmap (x:) (takeUntil u s xs)
takeUntil _ _ [] = []

getCycles :: [(UniverseID,Bool)] -> OrderingGraph -> (UniverseID,Bool) -> [Cycle]
getCycles vs _ (u,s) | u `elem` fmap fst vs = takeUntil u s vs
getCycles vs g (u,s) = case lookup u g of
    Just us -> concatMap (getCycles ((u,s):vs) g) us
    Nothing -> []

cycleStrict :: Cycle -> Bool
cycleStrict = or . fmap snd

illegal :: [Cycle] -> Bool
illegal = any cycleStrict

acyclic :: UniverseID -> OrderingGraph -> Bool
acyclic u g = (not . illegal) (getCycles [] g (u,False))

data ShowGraph
    = Fork UniverseID [(ShowGraph,Bool)]
    deriving(Show)

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
    in is ++ intercalate ('\n':showPipeIndent i') (fmap (\(b,(g,s)) -> (if s then " < " else " ≤ ")++showShowGraph b i' g) (flagLast gs))
showShowGraph True (p:i) (Fork u gs) =
    let is = show u
        i' = p+4+length is-1:i
    in is ++ intercalate ('\n':showPipeIndent i') (fmap (\(b,(g,s)) -> (if s then " < " else " ≤ ")++showShowGraph b i' g) (flagLast gs))

graphNodes :: ShowGraph -> [UniverseID]
graphNodes (Fork u ns) = u:concatMap (graphNodes . fst) ns

showGraph :: UniverseID -> [UniverseID] -> OrderingGraph -> ShowGraph
showGraph n f g | n `elem` f = Fork n []
showGraph n f g = case lookup n g of
    Just ns -> Fork n (foldr (\(n',s) gs -> (showGraph n' (n:f++concatMap (graphNodes . fst) gs) g,s):gs) [] ns)
    Nothing -> Fork n []

showOrdering :: OrderingGraph -> String
showOrdering g =
    let gs = filter (\(Fork _ l) -> not (null l))
            (foldl (\gs n -> showGraph n (concatMap graphNodes gs) g:gs) [] (fmap fst g))
    in intercalate "\n\n" (fmap (showShowGraph False []) (reverse gs))