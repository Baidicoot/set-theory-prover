{-# LANGUAGE LambdaCase #-}
module Parser where
import TT
import Graph
import Command
import Data.Char
import Control.Monad.Except
import Control.Monad.Writer

data ParExp
    = Parens [ParExp]
    | Tok String
    deriving(Eq)

data AST
    = ASTAnn AST AST
    | ASTNat Int
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
parseParExp [Tok n] | all isDigit n = pure (ASTNat (read n))
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
indexOf _ _ = Nothing

elab :: UniverseID -> [Name] -> [Name] -> [Var] -> AST -> Cmd (Exp,UniverseID,[Name])
elab u ps _ _ (ASTNat n) = pure (nTimes n (App (Free "S")) (Free "Z"),u,ps)
elab u ps hs ns (ASTVar v) = case indexOf ns (User v) of
    Just i -> pure (Var i Nothing,u,ps)
    Nothing -> pure (if v `elem` hs then Meta v else Free v,u,ps)
elab u ps hs ns (ASTAnn a b) = do
    (a,u,ps) <- elab u ps hs ns a
    (b,u,ps) <- elab u ps hs ns b
    pure (Ann a b,u,ps)
elab u ps hs ns ASTSet = pure (Set u,u+1,ps)
elab u (p:ps) hs ns ASTHole = pure (Hole p,u,ps)
elab u ps hs ns (ASTForall n a b) = do
    (a,u,ps) <- case a of
        Just a -> do
            (t,u,ps) <- elab u ps hs ns a
            pure (Just t,u,ps)
        Nothing -> pure (Nothing,u,ps)
    (b,u,ps) <- elab u ps hs (n:ns) b
    pure (Pi n (Abs a b),u,ps)
elab u ps hs ns (ASTLam n t x) = do
    (t,u,ps) <- case t of
        Just t -> do
            (t,u,ps) <- elab u ps hs ns t
            pure (Just t,u,ps)
        Nothing -> pure (Nothing,u,ps)
    (x,u,ps) <- elab u ps hs (n:ns) x
    pure (Lam n (Abs t x),u,ps)
elab u ps hs ns (ASTApp f x) = do
    (f,u,ps) <- elab u ps hs ns f
    (x,u,ps) <- elab u ps hs ns x
    pure (App f x,u,ps)

parse :: UniverseID -> String -> Cmd (Exp,UniverseID)
parse u = fmap (\(a,b,_)->(a,b)) . elab u holes [] [] <=< parseParExp . fst . tokenize

parseParRedex :: [Name] -> [Name] -> [Var] -> [ParExp] -> Cmd (Exp,[Name])
parseParRedex _ (h:hs) _ [Tok "_"] = pure (Hole h,hs)
parseParRedex ns hs vs [Tok n] = case indexOf vs (User n) of
    Just i -> pure (Var i Nothing,hs)
    Nothing -> pure (if n `elem` ns then Meta n else Free n,hs)
parseParRedex ns hs vs (Tok n:es) = (\(es,hs) -> (foldl App (Free n) es,hs)) <$> foldM (\(es,hs) p -> do
    (e,hs) <- parseParRedex ns hs vs (ext p)
    pure (es++[e],hs)) ([],hs) es
parseParRedex _ _ _ xs = throwError ("Could not parse reducible expression \"" ++ unwords (fmap show xs) ++ "\"")

elabRedexArgs :: UniverseID -> [Name] -> [Name] -> [(Name,AST)] -> Cmd ([(Name,Exp)], UniverseID, [Name])
elabRedexArgs u ps ns ((n,t):xs) = do
    (t,u,ps) <- elab u (filter (/= n) ps) ns [] t
    fmap (\(xs,u,ps) -> (xs ++ [(n,t)],u,ps)) (elabRedexArgs u ps (n:ns) xs)
elabRedexArgs u ps _ [] = pure ([],u,ps)

refineArgs :: [(Var,Maybe AST)] -> Cmd [(Name,AST)]
refineArgs ((User n,Just t):xs) = do
    xs' <- refineArgs xs
    pure ((n,t):xs')
refineArgs [] = pure []
refineArgs ((User n,_):_) = throwError ("Redex/Inductive parameter \"" ++ n ++ "\" must have a type.")
refineArgs ((_,_):_) = throwError "A redex/inductive parameter must be named."

parseRedex :: UniverseID -> [Name] -> [ParExp] -> [ParExp] -> [ParExp] -> Cmd (([(Name,Exp)], Exp, Exp), UniverseID, [Name])
parseRedex u ps as rs es = do
    args <- parseArgs as >>= refineArgs
    (args,u,ps) <- elabRedexArgs u ps [] args
    (r,ps) <- parseParRedex (fmap fst args) ps [] rs
    (e,u,ps) <- parseParExp es >>= elab u ps (fmap fst args) []
    pure ((args, r, e),u,ps)

elabIndArgs :: UniverseID -> [Name] -> [Name] -> [(Name,AST)] -> Cmd ([(Name,Exp)], UniverseID, [Name])
elabIndArgs u ps ns ((n,t):xs) = do
    (t,u,ps) <- elab u ps [] (fmap User ns) t
    fmap (\(xs,u,ps) -> (xs ++ [(n,t)],u,ps)) (elabIndArgs u ps (n:ns) xs)
elabIndArgs u ps _ [] = pure ([],u,ps)

elabInductive :: UniverseID -> [Name] -> String -> [(Name,AST)] -> AST -> [(String,AST)] -> Cmd (Inductive, UniverseID)
elabInductive u h s params ty cases = do
    (args,u,h) <- elabIndArgs u h [] params
    (indTy,u,h) <- elab u h [] (fmap (User . fst) args) ty
    (cases,u,_) <- foldM (\(cs,u,h) (n,t) -> do
        (t,u,h) <- elab u h [] (fmap (User . fst) args) t
        pure ((n,t):cs,u,h)) ([],u,h) cases
    pure (Ind s (fmap (User . fst) args) (fmap snd args) indTy cases,u)

parseRed :: UniverseID -> [ParExp] -> Cmd ([RedScheme],UniverseID)
parseRed u (Tok "ehnf":xs) = fmap (\(s,u) -> (Ehnf:s,u)) (parseRed u xs)
parseRed u (Tok "esnf":xs) = fmap (\(s,u) -> (Esnf:s,u)) (parseRed u xs)
parseRed u (Parens (Tok "unfolding":ns):xs) = do
    ns <- parseIdents ns
    fmap (\(s,u) -> (DeltaWith ns:s,u)) (parseRed u xs)
parseRed u (Parens (Tok "match":es):xs) = do
    (e,u,_) <- parseParExp es >>= elab u holes [] []
    fmap (\(s,u) -> (Match e:s,u)) (parseRed u xs)
parseRed u [] = pure ([],u)
parseRed _ xs = throwError ("Could not parse reduction stratedy \"" ++ show xs ++ "\"")

parseCommand :: UniverseID -> [ParExp] -> Cmd (Command,UniverseID)
parseCommand u xs = case xs of
        (Tok "Axiom":Tok n:Tok ":":ts) -> do
            (x,u,_) <- parseParExp ts >>= elab u holes [] []
            pure (Axiom n x,u)
        (Tok "Definition":Tok n:Tok ":=":ts) -> do
            (x,u,_) <- parseParExp ts >>= elab u holes [] []
            pure (Define n x,u)
        (Tok "Check":Tok "Constraint":xs) -> fmap (\a -> (CheckConstraints a,u)) (parseConstraints xs)
        (Tok "Check":ts) -> fmap (\(a,b) -> (Check a,b)) (parseParExp ts >>= fmap (\(a,b,_) -> (a,b)) . elab u holes [] [])
        (Tok "Transparent":ns) -> do
            ns <- parseIdents ns
            pure (Transparent ns,u)
        (Tok "Opaque":ns) -> do
            ns <- parseIdents ns
            pure (Opaque ns,u)
        (Tok "Eval":xs) -> do
            let rs = takeWhile (/= Tok "in") xs
            let ts = drop 1 (dropWhile (/= Tok "in") xs)
            (r,u) <- parseRed u rs
            (t,u,_) <- parseParExp ts >>= elab u holes [] []
            pure (Eval r t,u)
        (Tok "Compute":ts) -> fmap (\(a,b) -> (Eval [] a,b)) (parseParExp ts >>= fmap (\(a,b,_) -> (a,b)) .  elab u holes [] [])
        [Tok "Print",Tok "All"] -> pure (PrintAll,u)
        [Tok "Print",Tok "Universes"] -> pure (PrintUniverses,u)
        (Tok "Print":xs) -> fmap (\a -> (Print a,u)) (parseIdents xs)
        (Tok "Reduction":xs) -> do
            let lhs = takeWhile (/= Tok ":=") xs
            let os = drop 1 (dropWhile (/= Tok ":=") xs)
            (args,is) <- case lhs of
                    (_:_) -> pure (init lhs,ext (last lhs))
                    _ -> throwError "Expected reducible expression, got nothing."
            ((args,is,os),u,_) <- parseRedex u holes args is os
            pure (Redex args is os,u)
        (Tok "Inductive":Tok s:xs) -> do
            let params = takeWhile (/= Tok ":") xs
            let xs' = drop 1 (dropWhile (/= Tok ":") xs)
            let indty = takeWhile (/= Tok ":=") xs'
            let indcs = if Tok ":=" `elem` xs' then
                        filter (/= []) $ wordsWhen (==Tok "|") $ drop 1 (dropWhile (/= Tok ":=") xs')
                    else
                        []
            params <- parseArgs params >>= refineArgs
            indty <- parseParExp indty
            indcs <- mapM (\case
                (Tok c:Tok ":":ts) -> do
                    t <- parseParExp ts
                    pure (c,t)) indcs
            (i,u) <- elabInductive u holes s params indty indcs
            pure (MkInductive i,u)
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

interpret :: String -> CommandState -> Cmd (Maybe String, CommandState)
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
                case st' of
                    Right st' -> i st' cmds
                    Left e -> pure (Just e,st)
            i st [] = pure (Nothing,st)