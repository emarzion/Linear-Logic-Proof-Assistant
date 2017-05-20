import Lang
import PPrinter
import Parser
import Tactics

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

printErr :: String -> [Sequent] -> IO()
printErr e seqs = do 
                    putStrLn e
                    thmmode seqs

main :: IO ()
main = do 
    putStrLn "Welcome :)"
    putStrLn ""
    commands

commands :: IO ()
commands = do
            x <- getLine
            case readCommand x of
                Nothing -> do 
                            putStrLn "Syntax Error."
                            commands
                Just Ex -> return ()
                Just (Goal p) -> thmmode [([],p)]

thmmode :: [Sequent] -> IO()
thmmode [] = do 
                putStrLn "Proved!"
                putStrLn ""
                commands
thmmode (s:rest) = do
                    printSeqs (s:rest)
                    x <- getLine
                    case readTact x of
                        Nothing -> printErr "Syntax Error." (s:rest)
                        Just t  -> case t of
                                    Id              -> case idtac s of
                                                        Left e -> printErr e (s:rest)
                                                        Right _ -> thmmode rest
                                    OneT            -> case onetac s of
                                                        Left e -> printErr e (s:rest)
                                                        Right _ -> thmmode rest
                                    TrT             -> case trtac s of
                                                        Left e -> printErr e (s:rest)
                                                        Right _ -> thmmode rest
                                    ZeroT           -> case zerotac s of
                                                        Left e -> printErr e (s:rest)
                                                        Right _ -> thmmode rest
                                    Intro           -> case introtac s of
                                                        Left e -> printErr e (s:rest)
                                                        Right s' -> thmmode (s':rest)
                                    Remove n        -> case removetac s n of
                                                        Left e -> printErr e (s:rest)
                                                        Right s' -> thmmode (s':rest)
                                    LeftT           -> case lefttac s of
                                                        Left e -> printErr e (s:rest)
                                                        Right s' -> thmmode (s':rest)
                                    RightT          -> case righttac s of
                                                        Left e -> printErr e (s:rest)
                                                        Right s' -> thmmode (s':rest)
                                    Promote         -> case promotetac s of
                                                        Left e -> printErr e (s:rest)
                                                        Right s' -> thmmode (s':rest)
                                    AmpSplit        -> case ampsplittac s of
                                                        Left e -> printErr e (s:rest)
                                                        Right (s1,s2) -> thmmode (s1:s2:rest)
                                    ProdSplit ns    -> case prodsplittac s ns of
                                                        Left e -> printErr e (s:rest)
                                                        Right (s1,s2) -> thmmode (s1:s2:rest)
                                    Cut p ns        -> case cuttac s p ns of
                                                        Left e -> printErr e (s:rest)
                                                        Right (s1,s2) -> thmmode (s1:s2:rest)
                                    AmpL n          -> case ampdestrltac s n of
                                                        Left e -> printErr e (s:rest)
                                                        Right s' -> thmmode (s':rest)
                                    AmpR n          -> case ampdestrrtac s n of
                                                        Left e -> printErr e (s:rest)
                                                        Right s' -> thmmode (s':rest)
                                    Destr n         -> case destrtac s n of
                                                        Left e -> printErr e (s:rest)
                                                        Right (Left s') -> thmmode (s':rest)
                                                        Right (Right (s1,s2)) -> thmmode (s1:s2:rest)
                                    Apply n ns      -> case applytac s n ns of
                                                        Left e -> printErr e (s:rest)
                                                        Right (s1,s2) -> thmmode (s1:s2:rest)
                                    Derelict n      -> case derelicttac s n of
                                                        Left e -> printErr e (s:rest)
                                                        Right s' -> thmmode (s':rest)
                                    Contract n      -> case contracttac s n of
                                                        Left e -> printErr e (s:rest)
                                                        Right s' -> thmmode (s':rest)