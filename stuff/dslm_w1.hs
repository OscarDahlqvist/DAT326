--1.3, 1,4, 1.5, 1.6, 1.7, 1.8, 1.9
{-# LANGUAGE GADTs #-}

data Exp where
  Con   :: Integer -> Exp
  Plus  :: Exp -> Exp -> Exp
  Minus :: Exp -> Exp -> Exp
  Times :: Exp -> Exp -> Exp
  Var   :: String -> Exp
 deriving (Eq, Show)

a1 = Con 2 `Plus` Con 2
a2 = a1 `Plus` (Con 7 `Times` Con 9)
a3 = (Con 8 `Times` (Con 2 `Plus` Con 11)) `Minus` ((Con 3 `Plus` Con 7) `Times` (a1 `Plus` a2))

{-
eval :: Exp -> Integer
eval (Plus e f) = eval e + eval f
eval (Minus e f) = eval e - eval f
eval (Times e f) = eval e * eval f
eval (Con int) = int
-}

{-1.1
c1 = (x − 15) * (y + 12) * z
 where x = 5; y = 8; z = 13 -}
 
c1 = (Var "x" `Minus` Con 15) `Times` (Var "y" `Plus` Con 12) `Times` (Var "z")
 
eval :: (String -> Integer) -> Exp -> Integer
eval tbl (Plus e f) = eval tbl e + eval tbl f
eval tbl (Minus e f) = eval tbl e - eval tbl f
eval tbl (Times e f) = eval tbl e * eval tbl f
eval tbl (Con int) = int
eval tbl (Var x) = tbl x

varVal :: String -> Integer
varVal "x" = 5
varVal "y" = 8
varVal "z" = 13

--1.3
{-
cardinality = number of items in set
Either a b: Cardinality = A+B 
     (a,b): Cardinality = A*B new set is the cartesian product of the two sets and #a×b = #a*#b = A*B
    a -> b: Cardinality = B^A
     if A = 1: the function can return B different results
     the result of each input is independent from the other so Cardinality = (number of results)^(how many inputs) = B^A
     
     
-}

--1.4
{-
1. f :: Bool -> Maybe Bool

   f(True) = Just True   f(False) = Just True
   f(True) = Just True   f(False) = Just False
   f(True) = Just True   f(False) = Nothing
   f(True) = Just False  f(False) = Just True
   f(True) = Just False  f(False) = Just False
   f(True) = Just False  f(False) = Nothing
   f(True) = Nothing     f(False) = Just True
   f(True) = Nothing     f(False) = Just False
   f(True) = Nothing     f(False) = Nothing
    
    Number of items = (#Maybe Bool)^(#Bool) 
                    = (1 + #Bool)^(#Bool)
                         = 9
    
2. f :: Maybe Bool -> Bool

    f(Just True) = True   f(Just False) = True   f(Nothing) = True
    f(Just True) = True   f(Just False) = True   f(Nothing) = False
    f(Just True) = True   f(Just False) = False  f(Nothing) = True
    f(Just True) = True   f(Just False) = False  f(Nothing) = False
    f(Just True) = False  f(Just False) = True   f(Nothing) = True
    f(Just True) = False  f(Just False) = True   f(Nothing) = False
    f(Just True) = False  f(Just False) = False  f(Nothing) = True
    f(Just True) = False  f(Just False) = False  f(Nothing) = False
    
    Number of items = (#Bool)^(#Maybe Bool) 
                    = (#Bool)^(1 + #Bool)
                         = 8

3.
    Nothing
    Just (True,  Nothing)
    Just (True,  (True, Nothing)
    Just (True,  (True, Just True)
    Just (True,  (True, Just False) 
    Just (True,  (False, Nothing)
    Just (True,  (False, Just True)
    Just (True,  (False, Just False)
    Just (False, Nothing)
    Just (False, (True, Nothing)
    Just (False, (True, Just True)
    Just (False, (True, Just False) 
    Just (False, (False, Nothing)
    Just (False, (False, Just True)
    Just (False, (False, Just False)
    
    Number of items = #(Maybe (Bool, Maybe (Bool Maybe Bool)))
                    = 1 + #(Bool, Maybe (Bool, Maybe Bool))
                    = 1 + #Bool * #(Maybe (Bool, Maybe Bool))
                    = 1 + #Bool * (1 + #(Bool, Maybe Bool))
                    = 1 + #Bool * (1 + #Bool * #Maybe Bool)
                    = 1 + #Bool * (1 + #Bool * (1 + #Bool))
                    = 1 + 2 * (1 + 2 * (1 + 2))
                    = 1 + 2 * (1 + 2 * 3)
                    = 1 + 2 * (1 + 6)
                    = 1 + 2 * 7
                    = 1 + 14
                         = 15
                         
    Suitable notation
    True ∈ Bool
-}

--5
isoR :: (Bool -> t) -> (t,t)
isoR f = (f True, f False)

isoL :: (t,t) -> (Bool -> t)
isoL (fOfTrue, fOfFalse) = f
 where 
  f True = fOfTrue
  f False = fOfFalse

{-
the set (f(True),f(False)) is the output for for each possible input to the function, which is a complete description

    #(Bool -> t) = #t ^ #Bool = #t^2
    #(t,t) = #t * #t          = #t^2
-}

--6
f2p :: (a -> (b,c)) -> (a->b, a->c)
f2p f = (fL, fR)
 where
  fL = fst.f   --can also be written "\x -> fst (f x)" 
  fR = snd.f

p2f :: (a->b, a->c) -> (a -> (b,c)) 
p2f (fL, fR) = \x -> (fL x, fR x)

--7
s2p :: (Either b c -> a) -> (b -> a, c -> a)
s2p f = (fL, fR)
 where
  fL = f.Left
  fR = f.Right

p2s :: (b -> a, c -> a) -> (Either b c -> a)
p2s (fL, fR) = \x -> either fL fR x

--example 
--funcPair = (length, fromEnum)

--1.8
-- • What does function composition do to a sequence? More concretely: for
-- a sequence a what is a◦(1+)? What is (1+)◦a?
-- adding "◦f" in front applies f to any argument and then its result is input to the next part
-- f◦g = \x -> f(g(x))

-- a◦(1+) = λx -> a(1+x)
-- (1+)◦a = λx -> 1+(a(x))

--1.9
{-
(1+)      = λx → 1 + x
(*2)      = λx → x * 2
(1+)◦(*2) = λx → 1+(x*2)
(*2)◦(1+) = λx → (1+x)*2
(+1)◦(^2) = λx → xˆ2 + 1
(^2)◦(+1) = λx → (x + 1)ˆ2
(a+)◦(b+) = λx → a+(b+x)


-}










