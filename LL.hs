import Control.Applicative((<*))
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language
import Text.Read 

data Form = Atom String | Zero | One | Tr | Unary Unop Form | Binary Binop Form Form
    deriving (Show,Eq)
data Unop = Excl
    deriving (Show,Eq)
data Binop = Prod | Impl | Sum | Amp
    deriving (Show,Eq)

def :: LanguageDef st
def = emptyDef{ identStart = letter,
                identLetter = alphaNum,
                opStart = oneOf "!*-+&",
                opLetter = oneOf "!*-o+&",
                reservedOpNames = ["!", "*", "-o", "+", "&"],
                reservedNames = ["0", "1", "Tr"]
}

TokenParser{ Text.Parsec.Token.parens = m_parens
           , identifier = m_identifier
           , reservedOp = m_reservedOp
           , reserved = m_reserved
           , semiSep1 = m_semiSep1
           , whiteSpace = m_whiteSpace } = makeTokenParser def

formparser :: Parser Form
formparser = buildExpressionParser table term <?> "expression"
table = [ [Prefix (m_reservedOp "!" >> return (Unary Excl))]
        , [Infix (m_reservedOp "&" >> return (Binary Amp)) AssocLeft, Infix (m_reservedOp "*" >> return (Binary Prod)) AssocLeft]
        , [Infix (m_reservedOp "+" >> return (Binary Sum)) AssocLeft]
        , [Infix (m_reservedOp "-o" >> return (Binary Impl)) AssocRight]
        ]
term = m_parens formparser
       <|> fmap Atom m_identifier
       <|> (m_reserved "0" >> return (Zero))
       <|> (m_reserved "1" >> return (One))
       <|> (m_reserved "Tr" >> return (Tr))

play :: String -> IO ()
play inp = case parse formparser "" inp of
             { Left err -> print err
             ; Right ans -> print ans
             }

readForm :: String -> Maybe Form
readForm s = case parse formparser "" s of
                Left err -> Nothing
                Right ans -> Just ans

binopStr :: Binop -> String
binopStr Prod = "*"
binopStr Sum  = "+"
binopStr Impl = "-o"
binopStr Amp  = "&"

printForm :: Form -> String
printForm (Atom str) = str
printForm Zero = "0"
printForm One = "1"
printForm Tr = "Tr"
printForm (Unary Excl p) = "!" ++ (printForm p)
printForm (Binary o p q) = "(" ++ (printForm p) ++ " " ++ (binopStr o) ++ " " ++ (printForm q) ++ ")"

data Names = Name Int deriving (Eq, Show)

printName :: Names -> String
printName (Name n) = "H" ++ (show n)

type Judgement = (Names, Form)

printJudge :: Judgement -> String
printJudge (name, p) = (printName name) ++ " : " ++ (printForm p)

maxInt :: [Judgement] -> Int
maxInt [] = -1
maxInt ((Name n, p):js) = max n (maxInt js)

freshName :: [Judgement] -> Names
freshName js = Name (1 + maxInt js)

--returns the list of first projections of a list of pairs.
fstList :: [(a,b)] -> [a]
fstList [] = []
fstList (p:ps) = (fst p):(fstList ps)

--on input xs a, removes a from xs and returns the remaining list if a belongs to xs, and returns Nothing otherwise.
maybeRemove :: Eq a => a -> [(a,b)] -> Maybe ( (a,b) , [(a,b)] )
maybeRemove a [] = Nothing
maybeRemove a (p:ps) = if (fst p == a) then Just (p,ps)
                          else case (maybeRemove a ps) of 
                            Just (q,qs) -> Just (q,(p:qs))
                            Nothing -> Nothing

maybePart :: Eq a => [a] -> [(a,b)] -> Maybe ([(a,b)] , [(a,b)])
maybePart [] ps = Just ([] , ps)
maybePart (a:as) ps = case (maybePart as ps) of
                        Just (qs,rs) -> case (maybeRemove a rs) of
                                            Just (p,ts) -> Just (p:qs,ts)
                                            Nothing -> Nothing
                        Nothing -> Nothing


--returns the list of first projections of a list of pairs.
sndList :: [(a,b)] -> [b]
sndList [] = []
sndList (p:ps) = (snd p):(sndList ps)

-- the various tactics, corresponding to proof rules in the sequent calculus
type Sequent = ([Judgement] , Form)

-- identity tactic
idtac :: Sequent -> Bool
idtac (js,p) = (sndList js == [p])

-- one tactic
onetac :: Sequent -> Bool
onetac (js,p) = (js == []) && (p == One)

-- true tactic
trtac :: Sequent -> Bool
trtac (js,p) = (p == Tr)

sndIn :: Eq b => [(a,b)] -> b -> Bool
sndIn [] b = False
sndIn (p:ps) b = (snd p == b) || (sndIn ps b)

-- zero tactic
zerotac :: Sequent -> Bool
zerotac (js,p) = sndIn js Zero

--intro tactic
introtac :: Sequent -> Maybe Sequent
introtac (js,p) = case p of
                    (Binary Impl q r) -> Just (((freshName js , q) : js) , r)
                    _ -> Nothing

--remove tactic
removetac :: Sequent -> Maybe Sequent
removetac ([] , p) = Nothing
removetac ((j:js),p) = if (snd j == One) then Just (js,p)
                        else case (removetac (js,p)) of
                        Just (ks,_) -> Just (j:ks,p)
                        Nothing -> Nothing

--left tactic
lefttac :: Sequent -> Maybe Sequent
lefttac (js,p) = case p of
                    Binary Sum q r -> Just (js,q)
                    _ -> Nothing

--right tactic
righttac :: Sequent -> Maybe Sequent
righttac (js,p) = case p of
                    Binary Sum q r -> Just (js,r)
                    _ -> Nothing

allexcl :: [Judgement] -> Bool
allexcl [] = True
allexcl (j:js) = case (snd j) of
                    Unary Excl p -> allexcl js
                    _ -> False

promotetac :: Sequent -> Maybe Sequent
promotetac (js,p) = if (allexcl js) then 
                        case p of
                            Unary Excl q -> Just (js,q)
                            _ -> Nothing
                    else Nothing

ampsplittac :: Sequent -> Maybe (Sequent , Sequent)
ampsplittac (js,p) = case p of
                        Binary Amp q r -> Just ((js,q),(js,r))
                        _ -> Nothing

prodsplittac :: Sequent -> [Names] -> Maybe (Sequent,Sequent)
prodsplittac (js,p) ns = case p of 
                            Binary Prod q r -> case (maybePart ns js) of
                                                    Just (sigma,delta) -> Just ( (sigma,q) , (delta,r))
                                                    Nothing -> Nothing
                            _ -> Nothing

cuttac :: Sequent -> Form -> [Names] -> Maybe (Sequent,Sequent)
cuttac (js,p) q ns = case (maybePart ns js) of
                        Just (sigma,delta) -> Just ((sigma,q) ,  ((((freshName delta),q):delta),p))
                        Nothing -> Nothing

getpair :: Eq a => [(a,b)] -> a -> Maybe ((a,b) , [(a,b)])
getpair [] _ = Nothing
getpair (p:ps) a = if (fst p == a) then
                        Just (p,ps)
                    else case (getpair ps a) of
                        Just (q,qs) -> Just (q,p:qs)
                        Nothing -> Nothing

ampdestrltac :: Sequent -> Names -> Maybe Sequent
ampdestrltac (js,p) n = case (getpair js n) of
                            Just (j,ks) -> case (snd j) of
                                                Binary Amp q r -> Just (((n,q):ks),p)
                                                _ -> Nothing
                            Nothing -> Nothing

ampdestrrtac :: Sequent -> Names -> Maybe Sequent
ampdestrrtac (js,p) n = case (getpair js n) of
                            Just (j,ks) -> case (snd j) of
                                                Binary Amp q r -> Just (((n,r):ks),p)
                                                _ -> Nothing
                            Nothing -> Nothing

proddestrtac :: Sequent -> Names -> Maybe Sequent
proddestrtac (js,p) n = case (getpair js n) of
                            Just (j,ks) -> case (snd j) of
                                                Binary Prod q r -> Just ((((freshName js),r):(n,q):ks),p)
                                                _ -> Nothing
                            Nothing -> Nothing

sumdestrtac :: Sequent -> Names -> Maybe (Sequent,Sequent)
sumdestrtac (js,p) n = case (getpair js n) of
                            Just (j,ks) -> case (snd j) of
                                                Binary Sum q r -> Just (((n,q):ks,p) , ((n,r):ks,p) )
                                                _ -> Nothing
                            Nothing -> Nothing

applytac :: Sequent -> Names -> [Names] -> Maybe (Sequent,Sequent)
applytac (js,p) n ms = case (getpair js n) of
                            Just (j,ls) -> case (snd j) of
                                                Binary Impl q r -> case (maybePart ms ls) of
                                                    Just (gamma,delta) -> Just ((gamma,q),((n,r):delta,p))
                                                    Nothing -> Nothing
                                                _ -> Nothing
                            Nothing -> Nothing

derelicttac :: Sequent -> Names -> Maybe Sequent
derelicttac (js,p) n = case (getpair js n) of
                            Just (j,ks) -> case (snd j) of
                                                Unary Excl q -> Just ((n,q):ks,p)
                                                _ -> Nothing
                            Nothing -> Nothing

contracttac :: Sequent -> Names -> Maybe Sequent
contracttac (js,p) n = case (getpair js n) of
                            Just (j,_) -> case (snd j) of
                                                Unary Excl q -> Just (((freshName js),(Unary Excl q)):js,p)
                                                _ -> Nothing
                            Nothing -> Nothing

weakentac :: Sequent -> Names -> Maybe Sequent
weakentac (js,p) n = case (getpair js n) of 
                            Just (j,ks) -> case (snd j) of
                                                Unary Excl _ -> Just (ks,p)
                                                _ -> Nothing
                            Nothing -> Nothing

readName :: String -> Maybe Names
readName ('H' : rest) =  case (readMaybe rest) of 
                            Just n -> Just (Name n)
                            Nothing -> Nothing
readName _ = Nothing

readNames :: [String] -> Maybe [Names]
readNames [] = Just []
readNames (w:ws) = case (readNames ws) of
                        Just ns -> case (readName w) of
                                    Just n -> Just (n:ns)
                                    Nothing -> Nothing
                        Nothing -> Nothing

readListNames :: String -> Maybe [Names]
readListNames s = readNames (words s)

--splits a list based on the first occurence of a given element
splitList :: Eq a => a -> [a] -> Maybe ([a],[a])
splitList a [] = Nothing
splitList a (x:xs) = if (x == a) then Just ([] , xs) else
                        case (splitList a xs) of
                            Just (ys,zs) -> Just (x:ys,zs)
                            Nothing -> Nothing

maybeBrackets :: String -> Maybe (String,String)
maybeBrackets ('[' : rest) = splitList ']' rest
maybeBrackets _ = Nothing

bracketNames :: String -> Maybe ([Names],String)
bracketNames s = case (maybeBrackets s) of
                    Just (t,u) -> case (readListNames t) of
                                    Just ns -> Just (ns,u)
                                    Nothing -> Nothing
                    Nothing -> Nothing

stripSpace :: String -> Maybe String
stripSpace (' ' : rest) = Just rest
stripSpace _ = Nothing

bracketNamestrip :: String -> Maybe ([Names],String)
bracketNamestrip s = case (bracketNames s) of
                        Just (ns,s) -> case stripSpace s of 
                                        Just t -> Just (ns,t)
                                        Nothing -> Nothing
                        Nothing -> Nothing

hline :: String
hline = "___________________________________________"

printSnds :: (b -> String) -> [(a,b)] -> IO()
printSnds _ [] =  do putStrLn ""
printSnds pr (p:ps) =  do 
                        putStrLn (pr (snd p))
                        putStrLn hline
                        printSnds pr ps
                        putStrLn ""

printList :: (a -> String) -> [a] -> IO()
printList _ [] = do putStrLn ""
printList pr (a:as) = do
                        putStrLn (pr a)
                        printList pr as

printSeqs :: [Sequent] -> IO()
printSeqs [] = do putStrLn ""
printSeqs ((js,p):xs) = do 
                            printList printJudge js
                            putStrLn hline
                            putStrLn (printForm p)
                            putStrLn hline
                            printSnds printForm xs

printErr :: [Sequent] -> IO()
printErr seqs = do 
                    putStrLn "Error!"
                    thmmode seqs

gettactic :: Sequent -> [Sequent] -> String -> IO()
gettactic s rest "id" = if (idtac s) then (thmmode rest) else
                        printErr (s:rest)

gettactic s rest "intro" = case (introtac s) of
                            Just t -> thmmode (t:rest)
                            Nothing -> printErr (s:rest)

gettactic s rest "one" = if (onetac s) then (thmmode rest) else
                            printErr (s:rest)

gettactic s rest "truth" = if (trtac s) then (thmmode rest) else
                                printErr (s:rest)

gettactic s rest "zero" = if (zerotac s) then (thmmode rest) else
                                    printErr (s:rest)

gettactic s rest "left" = case (lefttac s) of
                            Just t -> thmmode (t:rest)
                            Nothing -> printErr (s:rest)

gettactic s rest "right" = case (righttac s) of
                            Just t -> thmmode (t:rest)
                            Nothing -> printErr (s:rest)

gettactic s rest "promote" = case (promotetac s) of
                                Just t -> thmmode (t:rest)
                                Nothing -> printErr (s:rest)

gettactic s rest "split" = case (ampsplittac s) of
                                Just (t,u) -> thmmode (t:u:rest)
                                Nothing -> printErr (s:rest)

gettactic s rest ('s' : 'p' : 'l' : 'i' : 't' : ' ' : str) = case (bracketNames str) of
                                                                Just (ns,r) -> case (prodsplittac s ns) of
                                                                                Just (t,u) -> thmmode (t:u:rest)
                                                                                Nothing -> printErr (s:rest)
                                                                Nothing -> printErr (s:rest)

gettactic s rest ('d' : 'e' : 's' : 't' : 'r' : 'u' : 'c' : 't' : ' ' : str) = case (readName str) of
                                                                                Just n -> case (proddestrtac s n) of
                                                                                            Just t -> thmmode (t:rest)
                                                                                            Nothing -> case (sumdestrtac s n) of
                                                                                                        Just (t,u) -> thmmode (t:u:rest)
                                                                                                        Nothing -> printErr (s:rest)
                                                                                Nothing -> printErr (s:rest)

gettactic s rest ('d' : 'e' : 's' : 't' : 'r' : 'u' : 'c' : 't' : '_' : 'l' : ' ' : str) = case (readName str) of
                                                                                            Just n -> case (ampdestrltac s n) of
                                                                                                        Just t -> thmmode (t:rest)
                                                                                                        Nothing -> printErr (s:rest)
                                                                                            Nothing -> printErr (s:rest)

gettactic s rest ('d' : 'e' : 's' : 't' : 'r' : 'u' : 'c' : 't' : '_' : 'r' : ' ' : str) = case (readName str) of
                                                                                            Just n -> case (ampdestrrtac s n) of
                                                                                                        Just t -> thmmode (t:rest)
                                                                                                        Nothing -> printErr (s:rest)
                                                                                            Nothing -> printErr (s:rest)

gettactic s rest "remove" = case (removetac s) of
                                Just t -> thmmode (t:rest)
                                Nothing -> printErr (s:rest)

gettactic s rest ('d' : 'e' : 'r' : 'e' : 'l' : 'i' : 'c' : 't' : ' ' : str) = case (readName str) of
                                                                                Just n -> case (derelicttac s n) of
                                                                                            Just t -> thmmode (t:rest)
                                                                                            Nothing -> printErr (s:rest)
                                                                                Nothing -> printErr (s:rest)

gettactic s rest ('c' : 'o' : 'n' : 't' : 'r' : 'a' : 'c' : 't' : ' ' : str) = case (readName str) of
                                                                                Just n -> case (contracttac s n) of
                                                                                            Just t -> thmmode (t:rest)
                                                                                            Nothing -> printErr (s:rest)
                                                                                Nothing -> printErr (s:rest)

gettactic s rest ('w' : 'e' : 'a' : 'k' : 'e' : 'n' : ' ' : str) = case (readName str) of
                                                                    Just n -> case (weakentac s n) of
                                                                                Just t -> thmmode (t:rest)
                                                                                Nothing -> printErr (s:rest)
                                                                    Nothing -> printErr (s:rest)

gettactic s rest ('a' : 'p' : 'p' : 'l' : 'y' : ' ' : str) = case (bracketNamestrip str) of
                                                                Just (ns,r) -> case (readName r) of
                                                                                Just n -> case (applytac s n ns) of
                                                                                            Just (t,u) -> thmmode (t:u:rest)
                                                                                            Nothing -> printErr (s:rest)
                                                                                Nothing -> printErr (s:rest)
                                                                Nothing -> printErr (s:rest)

gettactic s rest ('c' : 'u' : 't' : ' ' : str) = case (bracketNamestrip str) of
                                                    Just (ns,r) -> case (readForm r) of
                                                                    Just p -> case (cuttac s p ns) of
                                                                                Just (t,u) -> thmmode (t:u:rest)
                                                                                Nothing -> printErr (s:rest)
                                                                    Nothing -> printErr (s:rest)
                                                    Nothing -> printErr (s:rest)

gettactic s rest "exit" = commands

gettactic s rest _ = printErr (s:rest)


main :: IO ()
main = do 
    putStrLn "Welcome :)"
    putStrLn ""
    commands

thmmode :: [Sequent] -> IO()
thmmode [] = do 
                putStrLn "Proved!"
                putStrLn ""
                commands
thmmode (s:rest) = do
                    printSeqs (s:rest)
                    x <- getLine
                    gettactic s rest x

commands :: IO ()
commands = do
            x <- getLine
            case x of
                'T' : 'h' : 'e' : 'o' : 'r' : 'e' : 'm' : ' ' : rest -> case (readForm rest) of
                                                                    Just p -> thmmode [([],p)]
                                                                    Nothing -> do 
                                                                                putStrLn "Error!"
                                                                                commands
                "exit" -> do 
                            putStrLn ""
                            return()
                _ -> do
                    putStrLn "Error!"
                    commands
