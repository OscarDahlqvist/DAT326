{-# LANGUAGE GADTs #-}
import Data.List
import Test.QuickCheck

-- Part 1

data TERM v where 
    Empty         :: TERM v
    Singleton     :: TERM v -> TERM v
    Union         :: TERM v -> TERM v -> TERM v
    Intersection  :: TERM v -> TERM v -> TERM v
    Value         :: v -> TERM v
    deriving Show
 
data PRED v where
    Elem      :: v -> TERM v -> PRED v
    Subset    :: TERM v -> TERM v -> PRED v
    And       :: PRED v -> PRED v -> PRED v
    Or        :: PRED v -> PRED v -> PRED v
    Implies   :: PRED v -> PRED v -> PRED v
    Not       :: PRED v -> PRED v


-- Part 2

newtype Set = S [Set]
    deriving (Show)
instance Eq Set where
    (==) s1 s2 = all (==[]) [l1\\l2, l2\\l1]
        where l1 = setAsList s1; l2 = setAsList s2

setAsList :: Set -> [Set]
setAsList (S lst) = lst

type Env var dom = [(var,dom)]

getDom :: (Eq v) => (Env v x) -> v -> x
getDom e v = head [dom | (var,dom)<-e, var==v]

-- eval
eval :: (Eq v) => (Env v Set) -> TERM v -> Set
eval env (Empty)                = S []
eval env (Singleton t)          = S [eval env t]
eval env (Union t1 t2)          = S $ nub $ list1 ++ list2
    where 
        list1 = setAsList $ eval env t1
        list2 = setAsList $ eval env t2
eval env (Intersection t1 t2)   = S $ filter (\x -> x `elem` list2) list1
    where 
        list1 = setAsList $ eval env t1
        list2 = setAsList $ eval env t2
eval env (Value name)           = getDom env name

-- check
(-->) :: Bool -> Bool -> Bool
False --> _ = True
True  --> x = x

check :: (Eq v) => (Env v Set) -> PRED v -> Bool
check env (Elem v t)        = set `elem` (setAsList $ eval env t)
    where set = getDom env v
check env (Subset t1 t2)    = and $ map (\x -> x `elem` s2) s1  -- Subset is presumed to be of form "t1 is subset of t2"
    where
        s1 = setAsList $ eval env t1
        s2 = setAsList $ eval env t2
check env (And p1 p2)       = check env p1 && check env p2
check env (Or p1 p2)        = check env p1 || check env p2
check env (Implies p1 p2)   = check env p1 --> check env p2
check env (Not p)           = not $ check env p


-- Part 3

vonNeumann :: Integer -> TERM Integer
vonNeumann 0 = Empty
vonNeumann n = Union child (Singleton child)
    where child = vonNeumann (n-1)

claim1 :: Integer -> Integer -> Bool
claim1 n1 n2 = (n1 <= n2) --> (check [] ((vonNeumann n1) `Subset` (vonNeumann n2)))

claim2 n = (eval [] $ vonNeumann n) == set
    where set = S $ map (\x -> eval [] $ vonNeumann x) [0..(n-1)]
