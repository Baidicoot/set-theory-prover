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

data Var
    = Dummy
    | User String
    deriving(Eq,Show)

data AST
    = ASTAnn AST AST
    | ASTSet
    | ASTHole
    | ASTForall Var (Maybe AST) AST
    | ASTVar String
    | ASTApp AST AST
    | ASTLam Var (Maybe AST) AST

instance Show ParExp where
    show (Parens xs) = "(" ++ unwords (fmap show xs) ++ ")"
    show (Tok s) = s

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
parseIdents xs = throwError ("could not parse identifiers '\"" ++ unwords (fmap show xs) ++ "'\"")

parseName :: ParExp -> Cmd Var
parseName (Tok "_") = pure Dummy
parseName (Tok n) = pure (User n)

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
parseParExp x = throwError ("could not parse \"" ++ unwords (fmap show x) ++ "\"")

indexOf :: (Eq a, Show a) => [a] -> a -> Maybe Int
indexOf (a:_) b | a == b = Just 0
indexOf (_:as) a = fmap (+1) (indexOf as a)
indexOf _ a = Nothing

elab :: UniverseID -> [Var] -> AST -> Cmd (Exp,UniverseID)
elab u ns (ASTVar v) = case indexOf ns (User v) of
    Just i -> pure (Var i Nothing (Just v),u)
    Nothing -> pure (Free v,u)
elab u ns (ASTAnn a b) = do
    (a,u) <- elab u ns a
    (b,u) <- elab u ns b
    pure (Ann a b,u)
elab u ns ASTSet = pure (Set u,u+1)
elab u ns ASTHole = pure (Hole,u)
elab u ns (ASTForall n a b) = do
    (a,u) <- case a of
        Just a -> do
            (t,u) <- elab u ns a
            pure (Just t,u)
        Nothing -> pure (Nothing,u)
    (b,u) <- elab u (n:ns) b
    pure (Pi (Abs a b),u)
elab u ns (ASTLam n t x) = do
    (t,u) <- case t of
        Just t -> do
            (t,u) <- elab u ns t
            pure (Just t,u)
        Nothing -> pure (Nothing,u)
    (x,u) <- elab u (n:ns) x
    pure (Lam (Abs t x),u)
elab u ns (ASTApp f x) = do
    (f,u) <- elab u ns f
    (x,u) <- elab u ns x
    pure (App f x,u)

parse :: UniverseID -> String -> Cmd (Exp,UniverseID)
parse u = elab u [] <=< parseParExp . fst . tokenize

parseCommand :: UniverseID -> [ParExp] -> Cmd (Command,UniverseID)
parseCommand u xs = case xs of
        (Tok "Axiom":Tok n:Tok ":":ts) -> do
            (x,u) <- parseParExp ts >>= elab u []
            pure (Axiom n x,u)
        (Tok "Definition":Tok n:Tok ":=":ts) -> do
            (x,u) <- parseParExp ts >>= elab u []
            pure (Define n x,u)
        (Tok "Check":ts) -> fmap (\(a,b) -> (Check a,b)) (parseParExp ts >>= elab u [])
        (Tok "Compute":ts) -> fmap (\(a,b) -> (Eval a,b)) (parseParExp ts >>= elab u [])
        [Tok "Print",Tok "All"] -> pure (PrintAll,u)
        [Tok "Print",Tok "Universes"] -> pure (PrintUniverses,u)
        (Tok "Print":xs) -> fmap (\a -> (Print a,u)) (parseIdents xs)
        xs -> throwError ("unrecognised sequence: '" ++ unwords (fmap show xs) ++ "'")

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
interpret s (ctx,ord,u) = do
    let toks = fst (tokenize s)
    (cmds,u) <- parseCommands u (wordsWhen (==Tok ".") toks)
    i (ctx,ord,u) cmds
        where
            i st (c:cmds) = do
                st' <- docmd c st
                i st' cmds
            i st [] = pure st