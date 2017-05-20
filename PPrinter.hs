module PPrinter where

import Lang

--Pretty Printing Formulas

printBinop :: Binop -> String
printBinop Impl = " -o "
printBinop Sum  = " + "
printBinop Amp  = " & "
printBinop Prod = " * "

printForm :: Form -> String
printForm (Atom str) = str
printForm Zero = "0"
printForm One = "1"
printForm Tr = "Tr"
printForm (Unary Excl p) = "!" ++ (addParensU printForm p)
printForm (Binary c s1 s2) = (addParensB1 c printForm s1) ++ printBinop c ++ (addParensB2 c printForm s2)

addParensU :: (Form -> String) -> Form -> String
addParensU p s = case s of
                  Binary _ _ _ -> "(" ++ p s ++ ")"
                  _            -> p s

addParensB1 :: Binop -> (Form -> String) -> Form -> String
addParensB1 c p s = case s of
                     Binary c1 s1 s2 -> if c1 >= c then "(" ++ p s ++ ")" else p s
                     _               -> p s

addParensB2 :: Binop -> (Form -> String) -> Form -> String
addParensB2 c p s = case s of
                     Binary c1 s1 s2 -> if c1 > c then "(" ++ p s ++ ")" else p s
                     _               -> p s