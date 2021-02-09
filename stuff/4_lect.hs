--Pick one of 2.12 and 2.25.
{-# LANGUAGE GADTs #-}
data Prop = Con Bool
 | Not Prop
 | And Prop Prop
 | Or Prop Prop
 | Implies Prop Prop
 | Name String
 deriving(Show)
 
{-
H2 :: (a->b) -> (a->a->a) -> (b->b->b) -> Prop
H2 h f1 f2 = ∀x,y∈A h(f1 x y) == f2 (h x) (h y)

ex
∃f H₂(odd,+,f)?
does there exist a function where odd(x+y) == (odd x) `f` (odd y)
H₂ :: (a->b) -> (a->a->a) -> (b->b->b)
=> g :: Bool -> Bool -> Bool

yes f = xor 
	(if x&y is odd => is even)
-}

data Tup a b where
  Pair :: a -> b -> Tup
  Nest :: a -> Tup -> Tup
 deriving (Show)

