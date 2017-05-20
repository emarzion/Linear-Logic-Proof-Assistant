module Tactics where

import PPrinter
import Lang

import Data.Foldable

data Names = Name Int deriving (Eq, Show)

printName :: Names -> String
printName (Name n) = "H" ++ (show n)

type Judgement = (Names, Form)

printJudge :: Judgement -> String
printJudge (name, p) = (printName name) ++ " : " ++ (printForm p)

maxInt :: [Judgement] -> Int
maxInt = foldr (\(Name i,_) -> max i) (-1)

freshName :: [Judgement] -> Names
freshName js = Name (1 + maxInt js)

fstList :: [(a,b)] -> [a]
fstList = map fst

maybeRemove :: Eq a => a -> [(a,b)] -> Maybe ( (a,b) , [(a,b)] )
maybeRemove a [] = Nothing
maybeRemove a (p:ps) = if (fst p == a) then Just (p,ps)
                          else case (maybeRemove a ps) of 
                            Just (q,qs) -> Just (q,(p:qs))
                            Nothing -> Nothing

maybePart :: Eq a => [a] -> [(a,b)] -> Maybe ( [(a,b)] , [(a,b)] )
maybePart xs ps = foldrM (\a (u,v) -> do
                                (p,qs) <- maybeRemove a v
                                return (p:u,qs)
                                ) ( [] , ps ) xs

-- the various tactics, corresponding to proof rules in the sequent calculus

type Sequent = ([Judgement] , Form)

idtac :: Sequent -> Either String ()
idtac ([],_) = Left $ "Error: Context is empty."
idtac ((_,q):js,p)
    | q == p && null js = Right ()
    | otherwise         = Left "Error: Additional assumptions found in context."

onetac :: Sequent -> Either String ()
onetac ([],One) = Right ()
onetac ([],_)   = Left "Error: Goal is not 1."
onetac _        = Left "Error: Context is not empty."

trtac :: Sequent -> Either String ()
trtac (_,Tr) = Right ()
trtac _      = Left "Error: Goal is not Tr"

sndIn :: Eq b => [(a,b)] -> b -> Bool
sndIn [] b = False
sndIn (p:ps) b = (snd p == b) || (sndIn ps b)

zerotac :: Sequent -> Either String ()
zerotac (js,_) = if sndIn js Zero then Right () else Left "Error: 0 not found in context."

introtac :: Sequent -> Either String Sequent
introtac (js,Binary Impl p q) = Right (((freshName js , p) : js) , q)
introtac _                    = Left "Error: Goal is not an -o."

removetac :: Sequent -> Names -> Either String Sequent
removetac (js,p) n = case maybeRemove n js of 
                            Just (j,ks) -> case (snd j) of
                                                Unary Excl _ -> Right (ks,p)
                                                One          -> Right (ks,p)
                                                _ -> Left $ "Error: " ++ (printName $ fst j) ++ " is not a ! or 1."
                            Nothing -> Left $ "Error: " ++ (printName n) ++ " not found in context."

lefttac :: Sequent -> Either String Sequent
lefttac (js,Binary Sum p q) = Right (js,p)
lefttac _                   = Left "Error: Goal is not a +."

righttac :: Sequent -> Either String Sequent
righttac (js,Binary Sum p q) = Right (js,q)
righttac _                   = Left "Error: Goal is not a +."

allexcl :: [Judgement] -> Bool
allexcl = all $ \(_,p) -> case p of
                            Unary Excl _ -> True
                            _            -> False

promotetac :: Sequent -> Either String Sequent
promotetac (js,Unary Excl p)
    | allexcl js = Right (js,p)
    | otherwise  = Left "Error: Not all assumptions are !."
promotetac _     = Left "Error: Goal is not a !."

ampsplittac :: Sequent -> Either String (Sequent , Sequent)
ampsplittac (js,Binary Amp p q) = Right ((js,p),(js,q))
ampsplittac _                   = Left "Error: Goal is not an &."

prodsplittac :: Sequent -> [Names] -> Either String (Sequent,Sequent)
prodsplittac (js,Binary Prod p q) ns = case maybePart ns js of
                                        Just (sigma,delta) -> Right ((sigma,p) , (delta,q))
                                        Nothing            -> Left "Error: Could not find all names in context."
prodsplittac _ _                     = Left "Error: Goal is not an *"

cuttac :: Sequent -> Form -> [Names] -> Either String (Sequent,Sequent)
cuttac (js,p) q ns = case (maybePart ns js) of
                        Just (sigma,delta) -> Right ((sigma,q) ,  ((((freshName delta),q):delta),p))
                        Nothing -> Left "Error: Could not find all names in context."

ampdestrltac :: Sequent -> Names -> Either String Sequent
ampdestrltac (js,p) n = case maybeRemove n js of
                            Just (j,ks) -> case (snd j) of
                                                Binary Amp q r -> Right (((n,q):ks),p)
                                                _              -> Left $ "Error: " ++ (printName $ fst j) ++ " is not a &."
                            Nothing -> Left $ "Error: " ++ (printName n) ++ " not found in context."

ampdestrrtac :: Sequent -> Names -> Either String Sequent
ampdestrrtac (js,p) n = case maybeRemove n js of
                            Just (j,ks) -> case (snd j) of
                                                Binary Amp q r -> Right (((n,r):ks),p)
                                                _              -> Left $ "Error: " ++ (printName $ fst j) ++ " is not a &."
                            Nothing -> Left $ "Error: " ++ (printName n) ++ " not found in context."

destrtac :: Sequent -> Names -> Either String (Either Sequent (Sequent,Sequent))
destrtac (js,p) n = case maybeRemove n js of
                        Just (j,ks) -> case snd j of
                                            Binary Prod q r -> Right (Left ((((freshName js),r):(n,q):ks),p))
                                            Binary Sum  q r -> Right (Right (((n,q):ks,p) , ((n,r):ks,p)))
                                            _               -> Left $ "Error: " ++ (printName $ fst j) ++ " is not a * or +."
                        Nothing -> Left $ "Error: " ++ (printName n) ++ " not found in context."

applytac :: Sequent -> Names -> [Names] -> Either String (Sequent,Sequent)
applytac (js,p) n ms = case maybeRemove n js of
                            Just (j,ls) -> case (snd j) of
                                                Binary Impl q r -> case (maybePart ms ls) of
                                                    Just (gamma,delta) -> Right ((gamma,q),((n,r):delta,p))
                                                    Nothing -> Left "Error: Could not find all names in context."
                                                _ -> Left $ "Error: " ++ (printName $ fst j) ++ " is not a -o."
                            Nothing -> Left $ "Error: " ++ (printName n) ++ " not found in context."

derelicttac :: Sequent -> Names -> Either String Sequent
derelicttac (js,p) n = case maybeRemove n js of
                            Just (j,ks) -> case (snd j) of
                                                Unary Excl q -> Right ((n,q):ks,p)
                                                _ -> Left $ "Error: " ++ (printName $ fst j) ++ " is not a !."
                            Nothing -> Left $ "Error: " ++ (printName n) ++ " not found in context."

contracttac :: Sequent -> Names -> Either String Sequent
contracttac (js,p) n = case maybeRemove n js of
                            Just (j,_) -> case (snd j) of
                                                Unary Excl q -> Right (((freshName js),(Unary Excl q)):js,p)
                                                _ -> Left $ "Error: " ++ (printName $ fst j) ++ " is not a !."
                            Nothing -> Left $ "Error: " ++ (printName n) ++ " not found in context."

data Tactic = 
      Id
    | OneT
    | TrT
    | ZeroT
    | Intro
    | Remove Names
    | LeftT
    | RightT
    | Promote
    | AmpSplit
    | ProdSplit [Names]
    | Cut Form [Names]
    | AmpL Names
    | AmpR Names
    | Destr Names
    | Apply Names [Names]
    | Derelict Names
    | Contract Names deriving Show