module Parser where
import TT
import Graph
import Command
import Data.Char
import Control.Monad.Except

data ParExp
    = Parens [ParExp]
    | Tok String
    deriving(Eq)

data AST
    = ASTAnn AST AST
    | ASTSet
    | ASTHole
    | ASTForall Var (Maybe AST) AST
    | ASTVar String
    | ASTApp AST AST
    | ASTLam Var (Maybe AST) AST

instance Show ParExp where
    show (Parens xs) = "(" ++ show xs ++ ")"
    show (Tok s) = s
    showList xs s = unwords (fmap show xs) ++ s

isTokChar :: Char -> Bool
isTokChar ',' = False
isTokChar '(' = False
isTokChar ')' = False
isTokChar ':' = False
isTokChar '.' = False
isTokChar c = not (isSpace c)

eatComments :: Int -> String -> String
eatComments 0 s = s
eatComments n ('(':'*':xs) = eatComments (n+1) xs
eatComments n ('*':')':xs) = eatComments (n-1) xs
eatComments n (_:xs) = eatComments n xs
eatComments _ [] = []

tokenize :: String -> ([ParExp],String)
tokenize [] = ([],[])
tokenize ('(':'*':xs) = tokenize (eatComments 1 xs)
tokenize ('(':xs) =
    let (ps,xs') = tokenize xs
        (ts,xs'') = tokenize xs'
    in (Parens ps:ts,xs'')
tokenize (')':xs) = ([],xs)
tokenize (',':xs) =
    let (ps,xs') = tokenize xs
    in (Tok ",":ps,xs')
tokenize ('.':xs) =
    let (ps,xs') = tokenize xs
    in (Tok ".":ps,xs')
tokenize (':':'=':xs) =
    let (ps,xs') = tokenize xs
    in (Tok ":=":ps,xs')
tokenize (':':xs) =
    let (ps,xs') = tokenize xs
    in (Tok ":":ps,xs')
tokenize ('=':'>':xs) =
    let (ps,xs') = tokenize xs
    in (Tok "=>":ps,xs')
tokenize ('-':'>':xs) =
    let (ps,xs') = tokenize xs
    in (Tok "->":ps,xs')
tokenize (c:xs)
    | isSpace c = tokenize xs
tokenize (c:_)
    | not (isTokChar c) = error ("found " ++ show c)
tokenize xs =
    let t = takeWhile isTokChar xs
        (ps,xs') = tokenize (dropWhile isTokChar xs)
    in (Tok t:ps,xs')

ext :: ParExp -> [ParExp]
ext (Tok s) = [Tok s]
ext (Parens xs) = xs

parseIdents :: [ParExp] -> Cmd [Name]
parseIdents (Tok n:ns) = fmap (n:) (parseIdents ns)
parseIdents [] = pure []
parseIdents xs = throwError ("Could not parse identifiers \"" ++ unwords (fmap show xs) ++ "\"")

parseName :: ParExp -> Cmd Var
parseName (Tok "_") = pure Dummy
parseName (Tok n) = pure (User n)
parseName xs = throwError ("Could not parse name \"" ++ show xs ++ "\"")

parseNames :: [ParExp] -> Cmd [Var]
parseNames = mapM parseName

parseArgs :: [ParExp] -> Cmd [(Var,Maybe AST)]
parseArgs (Parens ds:xs) = do
    let t = drop 1 (dropWhile (/=Tok ":") ds)
    let ns = takeWhile (/=Tok ":") ds
    ns <- parseNames ns
    t <- parseParExp t
    as <- parseArgs xs
    pure (fmap (\x -> (x,Just t)) ns ++ as)
parseArgs (Tok "_":xs) = do
    as <- parseArgs xs
    pure ((Dummy,Nothing):as)
parseArgs (Tok n:xs) = do
    as <- parseArgs xs
    pure ((User n,Nothing):as)
parseArgs [] = pure []

parseParExp :: [ParExp] -> Cmd AST
parseParExp (Tok "forall":xs) = do
    let e = drop 1 (dropWhile (/=Tok ",") xs)
    let ns = takeWhile (/=Tok ",") xs
    ns <- parseArgs ns
    e <- parseParExp e
    pure (foldr (uncurry ASTForall) e ns)
parseParExp (Tok "fun":xs) = do
    let e = drop 1 (dropWhile (/=Tok "=>") xs)
    let ns = takeWhile (/=Tok "=>") xs
    ns <- parseArgs ns
    e <- parseParExp e
    pure (foldr (uncurry ASTLam) e ns)
parseParExp (e:Tok ":":t) = do
    e <- parseParExp (ext e)
    t <- parseParExp t
    pure (ASTAnn e t)
parseParExp (d:Tok "->":r) = do
    d <- parseParExp (ext d)
    r <- parseParExp r
    pure (ASTForall Dummy (Just d) r)
parseParExp [Tok "Type"] = pure ASTSet
parseParExp [Tok "_"] = pure ASTHole
parseParExp [Tok s] = pure (ASTVar s)
parseParExp (e:es) = do
    args <- mapM (parseParExp . ext) es
    e <- parseParExp (ext e)
    pure (foldl ASTApp e args)
parseParExp x = throwError ("Could not parse expression \"" ++ unwords (fmap show x) ++ "\"")

parseConstraints :: [ParExp] -> Cmd [Constraint]
parseConstraints xs = fmap concat (mapM parseConstraint (wordsWhen (==Tok ",") xs))

parseNat :: String -> Cmd Int
parseNat s | all isDigit s = pure (read s)
parseNat s = throwError ("'" ++ s ++ "' is not a natural")

parseConstraint :: [ParExp] -> Cmd [Constraint]
parseConstraint [Tok i,Tok ">",Tok j] = do
    i <- parseNat i
    j <- parseNat j
    pure [i :>: j]
parseConstraint [Tok i,Tok "<",Tok j] = do
    i <- parseNat i
    j <- parseNat j
    pure [j :>: i]
parseConstraint [Tok i,Tok ">=",Tok j] = do
    i <- parseNat i
    j <- parseNat j
    pure [i :>=: j]
parseConstraint [Tok i,Tok "<=",Tok j] = do
    i <- parseNat i
    j <- parseNat j
    pure [j :>=: i]
parseConstraint [Tok i,Tok "≥",Tok j] = do
    i <- parseNat i
    j <- parseNat j
    pure [i :>=: j]
parseConstraint [Tok i,Tok "≤",Tok j] = do
    i <- parseNat i
    j <- parseNat j
    pure [j :>=: i]
parseConstraint [Tok i,Tok "=",Tok j] = do
    i <- parseNat i
    j <- parseNat j
    pure [i :>=: j, j :>=: i]

indexOf :: (Eq a, Show a) => [a] -> a -> Maybe Int
indexOf (a:_) b | a == b = Just 0
indexOf (_:as) a = fmap (+1) (indexOf as a)
indexOf _ a = Nothing

elab :: UniverseID -> [Name] -> [Var] -> AST -> Cmd (Exp,UniverseID,[Name])
elab u ps ns (ASTVar v) = case indexOf ns (User v) of
    Just i -> pure (Var i Nothing,u,ps)
    Nothing -> pure (Free v,u,ps)
elab u ps ns (ASTAnn a b) = do
    (a,u,ps) <- elab u ps ns a
    (b,u,ps) <- elab u ps ns b
    pure (Ann a b,u,ps)
elab u ps ns ASTSet = pure (Set u,u+1,ps)
elab u (p:ps) ns ASTHole = pure (Hole p,u,ps)
elab u ps ns (ASTForall n a b) = do
    (a,u,ps) <- case a of
        Just a -> do
            (t,u,ps) <- elab u ps ns a
            pure (Just t,u,ps)
        Nothing -> pure (Nothing,u,ps)
    (b,u,ps) <- elab u ps (n:ns) b
    pure (Pi n (Abs a b),u,ps)
elab u ps ns (ASTLam n t x) = do
    (t,u,ps) <- case t of
        Just t -> do
            (t,u,ps) <- elab u ps ns t
            pure (Just t,u,ps)
        Nothing -> pure (Nothing,u,ps)
    (x,u,ps) <- elab u ps (n:ns) x
    pure (Lam n (Abs t x),u,ps)
elab u ps ns (ASTApp f x) = do
    (f,u,ps) <- elab u ps ns f
    (x,u,ps) <- elab u ps ns x
    pure (App f x,u,ps)

holes :: [String]
holes = [1..] >>= flip replicateM ['A'..'Z']

parse :: UniverseID -> String -> Cmd (Exp,UniverseID)
parse u = fmap (\(a,b,_)->(a,b)) . elab u holes [] <=< parseParExp . fst . tokenize

parseParRedex :: [Var] -> [ParExp] -> Cmd Exp
parseParRedex ns [Tok n] = case indexOf ns (User n) of
    Just i -> pure (Var i Nothing)
    Nothing -> pure (Free n)
parseParRedex ns (Tok n:es) = foldl App (Free n) <$> mapM (parseParRedex ns . ext) es
parseParRedex _ xs = throwError ("Could not parse reducible expression \"" ++ unwords (fmap show xs) ++ "\"")

elabRedexArgs :: UniverseID -> [Name] -> [Var] -> [(Var,Maybe AST)] -> Cmd ([(Name,Exp)], UniverseID, [Name])
elabRedexArgs u ps ns ((User n,Just t):xs) = do
    (t,u,ps) <- elab u ps ns t
    fmap (\(xs,u,ps) -> (xs ++ [(n,t)],u,ps)) (elabRedexArgs u ps (User n:ns) xs)
elabRedexArgs u ps _ [] = pure ([],u,ps)
elabRedexArgs _ _ _ xs = throwError ("Could not parse redex arguments \""
    ++ unwords (fmap (show . fst) xs) ++ "\"")

parseRedex :: UniverseID -> [Name] -> [ParExp] -> [ParExp] -> [ParExp] -> Cmd (([(Name,Exp)], Exp, Exp), UniverseID, [Name])
parseRedex u ps as rs es = do
    (args,u,ps) <- parseArgs as >>= elabRedexArgs u ps []
    r <- parseParRedex (fmap (User . fst) args) rs
    (e,u,ps) <- parseParExp es >>= elab u ps (fmap (User . fst) args)
    pure ((args, r, e),u,ps)

parseCommand :: UniverseID -> [ParExp] -> Cmd (Command,UniverseID)
parseCommand u xs = case xs of
        (Tok "Axiom":Tok n:Tok ":":ts) -> do
            (x,u,_) <- parseParExp ts >>= elab u holes []
            pure (Axiom n x,u)
        (Tok "Definition":Tok n:Tok ":=":ts) -> do
            (x,u,_) <- parseParExp ts >>= elab u holes []
            pure (Define n x,u)
        (Tok "Check":Tok "Constraint":xs) -> fmap (\a -> (CheckConstraints a,u)) (parseConstraints xs)
        (Tok "Check":ts) -> fmap (\(a,b) -> (Check a,b)) (parseParExp ts >>= fmap (\(a,b,_) -> (a,b)) . elab u holes [])
        (Tok "Unfolding":ns) -> do
            ns <- parseIdents ns
            pure (Unfolding ns,u)
        (Tok "Compute":bs:Tok "with":as) -> do
            (a,u,h) <- parseParExp as >>= elab u holes []
            (b,u,_) <- parseParExp (ext bs) >>= elab u h []
            pure (Match a b,u)
        (Tok "Compute":Tok "ehnf":ts) ->
            fmap (\(a,b) -> (Ehnf a,b)) (parseParExp ts >>= fmap (\(a,b,_) -> (a,b)) .  elab u holes [])
        (Tok "Compute":Tok "unfold":Parens ns:ts) -> do
            ns <- parseIdents ns
            (t,u,_) <- parseParExp ts >>= elab u holes []
            pure (EvalUnfold ns t,u)
        (Tok "Compute":ts) -> fmap (\(a,b) -> (Eval a,b)) (parseParExp ts >>= fmap (\(a,b,_) -> (a,b)) .  elab u holes [])
        [Tok "Print",Tok "All"] -> pure (PrintAll,u)
        [Tok "Print",Tok "Universes"] -> pure (PrintUniverses,u)
        (Tok "Print":xs) -> fmap (\a -> (Print a,u)) (parseIdents xs)
        (Tok "Reduction":Parens is:Tok ":=":os) -> do
            ((_,is,os),u,_) <- parseRedex u holes [] is os
            pure (Redex [] [] is os,u)
        (Tok "Reduction":Parens args:Parens is:Tok ":=":os) -> do
            ((args,is,os),u,_) <- parseRedex u holes args is os
            pure (Redex (fmap (User . fst) args) (fmap snd args) is os,u)
        xs -> throwError ("Unrecognised command \"" ++ unwords (fmap show xs) ++ "\".")

trim :: String -> String
trim = f . f
    where f = reverse . dropWhile isSpace

wordsWhen :: (a -> Bool) -> [a] -> [[a]]
wordsWhen p s =
    case dropWhile p s of
            [] -> []
            s' -> w : wordsWhen p s''
                where (w, s'') = break p s'

parseCommands :: UniverseID -> [[ParExp]] -> Cmd ([Command],UniverseID)
parseCommands u (x:xs) = do
    (cmd,u) <- parseCommand u x
    (cmds,u) <- parseCommands u xs
    pure (cmd:cmds,u)
parseCommands u [] = pure ([],u)

interpret :: String -> CommandState -> Cmd CommandState
interpret s (ctx,ord,u,ns) = do
    let (toks,r) = tokenize s
    unless (r == "") (throwError
        ("Parsed \""
        ++ (let s = show toks in if length s > 75 then "..." ++ drop (length s - 75) s else s)
        ++ "\" but did not consume entire sequence."))
    (cmds,u) <- parseCommands u (wordsWhen (==Tok ".") toks)
    i (ctx,ord,u,ns) cmds
        where
            i st (c:cmds) = do
                st' <- docmd c st
                i st' cmds
            i st [] = pure st