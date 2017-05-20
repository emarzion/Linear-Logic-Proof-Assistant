module Parser where

import Control.Applicative((<*))
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import Text.Read 

import Lang
import Tactics

def :: LanguageDef st
def = emptyDef{ identStart = letter,
                identLetter = alphaNum,
                opStart = oneOf "!*-+&[]",
                opLetter = oneOf "!*-o+&[]",
                reservedOpNames = ["!", "*", "-o", "+", "&", "->", "[", "]"],
                reservedNames = ["0", "1", "Tr", "id" , "one" , "true" , "zero" , "intro" , "remove" , "left" , "right" , "promote" , "split" ,
                                 "cut" , "destruct" , "apply" , "derelict" , "duplicate" , "Theorem" , "exit"]
}

lexer = Token.makeTokenParser def

res   = Token.reserved   lexer
nat    = Token.natural    lexer
ws    = Token.whiteSpace lexer


TokenParser{ Text.Parsec.Token.parens = m_parens
           , identifier = m_identifier
           , reservedOp = m_reservedOp
           , reserved = m_reserved
           , semiSep1 = m_semiSep1
           , whiteSpace = m_whiteSpace } = makeTokenParser def

formparser :: Parser Form
formparser = buildExpressionParser table term <?> "expression"
table = [ [Prefix (m_reservedOp "!" >> return (Unary Excl))]
        , [Infix (m_reservedOp "*" >> return (Binary Prod)) AssocRight]
        , [Infix (m_reservedOp "&" >> return (Binary Amp)) AssocRight]
        , [Infix (m_reservedOp "+" >> return (Binary Sum)) AssocRight]
        , [Infix (m_reservedOp "-o" >> return (Binary Impl)) AssocRight , Infix (m_reservedOp "->" >> return (regImpl)) AssocRight]
        ]
term = m_parens formparser
       <|> fmap Atom m_identifier
       <|> (m_reserved "0" >> return (Zero))
       <|> (m_reserved "1" >> return (One))
       <|> (m_reserved "Tr" >> return (Tr))

data Command = Goal Form | Ex


goalParse :: Parser Command
goalParse = do
                res "Theorem"
                p <- formparser
                return (Goal p)

exitParse :: Parser Command
exitParse = do
                res "exit"
                return Ex

commandParse :: Parser Command
commandParse =  goalParse
            <|> exitParse

readCommand :: String -> Maybe Command
readCommand s = case parse commandParse "" s of
                 Left err -> Nothing
                 Right ans -> Just ans

readForm :: String -> Maybe Form
readForm s = case parse formparser "" s of
                Left err -> Nothing
                Right ans -> Just ans

nameparse :: Parser Names
nameparse = do
              _ <- char 'H'
              n <- nat
              return (Name (fromInteger n))

namesparse :: Parser [Names]
namesparse = do
                _ <- char '['
                ns <- many nameparse
                _ <- char ']'
                return ns

idParse :: Parser Tactic
idParse = do
            res "id"
            return Id

oneParse :: Parser Tactic
oneParse = do
            res "one"
            return OneT

trParse :: Parser Tactic
trParse = do
            res "true"
            return TrT

zeroParse :: Parser Tactic
zeroParse = do
             res "zero"
             return ZeroT

introParse :: Parser Tactic
introParse = do
                res "intro"
                return Intro

removeParse :: Parser Tactic
removeParse = do
                res "remove"
                n <- nameparse
                return (Remove n)

leftParse :: Parser Tactic
leftParse = do
                res "left"
                return LeftT

rightParse :: Parser Tactic
rightParse = do
                res "right"
                return RightT

promoteParse :: Parser Tactic
promoteParse = do
                res "promote"
                return Promote

ampsplitParse :: Parser Tactic
ampsplitParse = do
                 res "split"
                 return AmpSplit

prodsplitParse :: Parser Tactic
prodsplitParse = do
                    res "split"
                    ns <- namesparse
                    return (ProdSplit ns)

cutParse :: Parser Tactic
cutParse = do
            res "cut"
            p <- formparser
            ns <- namesparse
            return (Cut p ns)

amplParse :: Parser Tactic
amplParse = do
             res "left"
             n <- nameparse
             return (AmpL n)

amprParse :: Parser Tactic
amprParse = do
             res "right"
             n <- nameparse
             return (AmpR n)

destrParse :: Parser Tactic
destrParse = do
              res "destruct"
              n <- nameparse
              return (Destr n)

applyParse :: Parser Tactic
applyParse = do
                res "apply"
                n <- nameparse
                ns <- namesparse
                return (Apply n ns)

derelictParse :: Parser Tactic
derelictParse = do
                    res "derelict"
                    n <- nameparse
                    return (Derelict n)

duplicateParse :: Parser Tactic
duplicateParse = do
                    res "duplicate"
                    n <- nameparse 
                    return (Contract n)

tactParse :: Parser Tactic
tactParse =  idParse
         <|> oneParse
         <|> trParse
         <|> zeroParse
         <|> introParse
         <|> removeParse
         <|> try amplParse
         <|> try amprParse
         <|> promoteParse
         <|> try prodsplitParse
         <|> ampsplitParse
         <|> cutParse
         <|> leftParse
         <|> rightParse
         <|> destrParse
         <|> applyParse
         <|> derelictParse
         <|> duplicateParse

readTact :: String -> Maybe Tactic
readTact s = case parse tactParse "" s of
                Left err -> Nothing
                Right ans -> Just ans
