module Parser where
import TT
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
    | ASTForall Var AST AST
    | ASTVar String
    | ASTApp AST AST
    | ASTLam Var AST
    | ASTLamTy Var AST AST

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

parseIdents :: [ParExp] -> Res [Name]
parseIdents (Tok n:ns) = fmap (n:) (parseIdents ns)
parseIdents [] = pure []
parseIdents xs = throwError ("could not parse identifiers '\"" ++ unwords (fmap show xs) ++ "'\"")

parseNames :: [ParExp] -> Res [Var]
parseNames (Tok "_":ns) = fmap (Dummy:) (parseNames ns)
parseNames (Tok n:ns) = fmap (User n:) (parseNames ns)
parseNames [] = pure []
parseNames xs = throwError ("could not parse arguments '\"" ++ unwords (fmap show xs) ++ "'\"")

parseArgs :: [ParExp] -> Res [(Var,AST)]
parseArgs (Parens ds:xs) = do
    let t = drop 1 (dropWhile (/=Tok ":") ds)
    let ns = takeWhile (/=Tok ":") ds
    ns <- parseNames ns
    t <- parseParExp t
    as <- parseArgs xs
    pure (fmap (\x -> (x,t)) ns ++ as)
parseArgs [] = pure []

parseParExp :: [ParExp] -> Res AST
parseParExp (Tok "forall":xs)= trace ("while parsing forall " ++ unwords (fmap show xs)) $ do
    let e = drop 1 (dropWhile (/=Tok ",") xs)
    let ns = takeWhile (/=Tok ",") xs
    ns <- parseArgs ns
    e <- parseParExp e
    pure (foldr (uncurry ASTForall) e ns)
parseParExp (Tok "lam":xs) = trace ("while parsing lam " ++ unwords (fmap show xs)) $ do
    let e = drop 1 (dropWhile (/=Tok "=>") xs)
    let ns = takeWhile (/=Tok "=>") xs
    ns <- parseNames ns
    e <- parseParExp e
    pure (foldr ASTLam e ns)
parseParExp (Tok "fun":xs) = trace ("while parsing fun " ++ unwords (fmap show xs)) $ do
    let e = drop 1 (dropWhile (/=Tok "=>") xs)
    let ns = takeWhile (/=Tok "=>") xs
    ns <- parseArgs ns
    e <- parseParExp e
    pure (foldr (uncurry ASTLamTy) e ns)
parseParExp (e:Tok ":":t) = trace ("while parsing " ++ show e ++ " : " ++ unwords (fmap show t)) $ do
    e <- parseParExp (ext e)
    t <- parseParExp t
    pure (ASTAnn e t)
parseParExp (d:Tok "->":r) = trace ("while parsing " ++ show d ++ " -> " ++ unwords (fmap show r)) $ do
    d <- parseParExp (ext d)
    r <- parseParExp r
    pure (ASTForall Dummy d r)
parseParExp [Tok "Set"] = pure ASTSet
parseParExp [Tok "_"] = pure ASTHole
parseParExp [Tok s] = pure (ASTVar s)
parseParExp (e:es) = trace ("while parsing" ++ unwords (fmap show (e:es))) $ do
    args <- mapM (parseParExp . ext) es
    e <- parseParExp (ext e)
    pure (foldl ASTApp e args)
parseParExp x = throwError ("could not parse \"" ++ unwords (fmap show x) ++ "\"")

indexOf :: (Eq a, Show a) => [a] -> a -> Maybe Int
indexOf (a:_) b | a == b = Just 0
indexOf (_:as) a = fmap (+1) (indexOf as a)
indexOf _ a = Nothing

elab :: [Var] -> AST -> Res Exp
elab ns (ASTVar v) = case indexOf ns (User v) of
    Just i -> pure (Var i Nothing (Just v))
    Nothing -> pure (Free v)
elab ns (ASTAnn a b) = do
    a <- elab ns a
    b <- elab ns b
    pure (Ann a b)
elab ns ASTSet = Set <$> freshUniverse
elab ns ASTHole = pure Hole
elab ns (ASTForall n a b) = do
    a <- elab ns a
    b <- elab (n:ns) b
    pure (Pi (Abs (Just a) b))
elab ns (ASTLam n x) = do
    x <- elab (n:ns) x
    pure (Lam (Abs Nothing x))
elab ns (ASTLamTy n t x) = do
    t <- elab ns t
    x <- elab (n:ns) x
    pure (Lam (Abs (Just t) x))
elab ns (ASTApp f x) = do
    f <- elab ns f
    x <- elab ns x
    pure (App f x)

parse :: String -> Res Exp
parse = elab [] <=< parseParExp . fst . tokenize

parseCommand :: [ParExp] -> Res Command
parseCommand xs = case xs of
        (Tok "Axiom":Tok n:Tok ":":ts) -> do
            x <- parseParExp ts >>= elab []
            pure (Axiom n x)
        (Tok "Definition":Tok n:Tok ":=":ts) -> do
            x <- parseParExp ts >>= elab []
            pure (Define n x)
        (Tok "Check":ts) -> fmap Check (parseParExp ts >>= elab [])
        (Tok "Eval":ts) -> fmap Eval (parseParExp ts >>= elab [])
        [Tok "Print",Tok "All"] -> pure PrintAll
        [Tok "Print",Tok "Universes"] -> pure PrintUniverses
        (Tok "Print":xs) -> fmap Print (parseIdents xs)
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

parseCommands :: [ParExp] -> Res [Command]
parseCommands xs = mapM parseCommand (wordsWhen (==Tok ".") xs)

interpret :: String -> CommandState -> Res ([CommandOutput],CommandState)
interpret s st = do
    let toks = fst (tokenize s)
    cmds <- parseCommands toks
    i st [] cmds
        where
            i st out (c:cmds) = do
                (o,st') <- docmd c st
                i st' (out++[o]) cmds
            i st out [] = pure (out,st)