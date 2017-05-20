module Lang where

data Form = Atom String | Zero | One | Tr | Unary Unop Form | Binary Binop Form Form
    deriving (Show,Eq)
data Unop = Excl
    deriving (Show,Eq)
data Binop = Prod | Amp | Sum | Impl
    deriving (Show,Eq,Ord)

regImpl :: Form -> Form -> Form
regImpl p q = Binary Impl (Unary Excl p) q