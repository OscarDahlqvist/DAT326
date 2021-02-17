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
H2 h f1 f2 = ∀x,y∈A h(f1 x y) <==> f2 (h x) (h y)

H1 :: (a->b) -> (a->a) -> (b->b) -> Prop
H1 h f1 f2 = ∀x∈A h(f1 x) <==> f2 (h x)

H0 :: (a->b) -> a -> b -> Prop
H0 h E e = h E <==> e

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



{-
type REAL = Double
type S = REAL -> REAL
newtype Bi a = Bi (a, a)

data F where
  A :: F -> F -> F
  M :: F -> F -> F
  X :: F
  C :: REAL -> F
 deriving Show
 
-- ================= --
-- type Syntax = F
-- type Semantic = S

eval :: F -> S
eval (A f g) = oadd (eval f) (eval g)
eval (M f g) = omul (eval f) (eval g)
eval X       = id
eval (C c)   = const c

oadd, omul :: S -> S -> S
oadd f g = \x -> f x + g x
omul f g = \x -> f x * g x

--cant be defined sice der :: F a -> Bi (F a)
--eval' = eval.der

--eval'' = eval.der.der
--alt: eval''= eval'.der


der :: F -> Bi F
der (A f g)   = addder (der f) (der g)
der (M f g)   = mulder (der f) (der g)
der X         = xder
der (C c)     = cder c

derSnd = extractDer.der
 where extractDer (Bi (f,f')) = f'

xder :: Bi F
xder = Bi (X, C 1)

cder :: REAL -> Bi F
cder c = Bi (C c, C 0)

addder, mulder :: Bi F -> Bi F -> Bi F
addder (Bi (f, f')) (Bi (g, g')) = Bi (A f g, A f' g')
mulder (Bi (f, f')) (Bi (g, g')) = Bi (M f g, A (M f' g) (M f g'))

{-
class Additive a where
 zero   :: a
 add    :: a -> a -> a

class Multiplicative a where
 one    :: a
 mul    :: a -> a -> a
 
class Additive a => AddGroup a where
 negate    :: a -> a
 
class (AddGroup a, Multiplicative a) => Ring a
-}

class Ring a where
 zero   :: a
 add    :: a -> a -> a
 one    :: a
 mul    :: a -> a -> a
 negate    :: a -> a

instance Ring FunExp where 
 zero   = Const 0
 add    = (`Add`)
 one    = Const 1
 mul    = (`Mul`)
 negate    = Negate




{-
refefefef
-}
-}

