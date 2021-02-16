{-# LANGUAGE GADTs #-}
import Data.List
import Test.QuickCheck

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

--1a
{-# LANGUAGE GADTs #-}

import Prelude hiding (recip,negate)

type REAL = Double

eval :: FunExp -> FunSem
eval expr x = error "todo"

eval' :: FunExp -> FunSem
eval'= eval.derive

eval'' :: FunExp -> FunSem
eval'' = eval'.derive
--eval'' = eval.derive.derive

derive :: FunExp -> FunExp
derive = error "todo"

data FunExp where
 Con    :: REAL -> FunExp
 FunX   :: FunExp
 Add    :: FunExp -> FunExp -> FunExp
 Mul    :: FunExp -> FunExp -> FunExp
 Negate :: FunExp -> FunExp
 Recip  :: FunExp -> FunExp
 Root   :: FunExp -> FunExp
 Pi     :: FunExp
 Sin    :: FunExp -> FunExp
 Cos    :: FunExp -> FunExp
 Exp    :: FunExp -> FunExp

type FunSem = (REAL -> REAL)

{-
By def. the homomorphism conserves the operation, in this case eval''. Thus if eval'' is a homomorphism,
    then eval'' (f oplus g) == (eval'' f) oplus (eval'' g) for every operation oplus on the function 
    expressions f and g. To prove that eval'' is not a homomorphism it suffices to observe that the second
    derivative of the product of two functions is not the product of the two individual second derivatives.
    This simply follows from the product rule. Note that this does not take into account the two domains,
    but it is not neccissary due to the fact that the derivitaive is not liniar in multiplication.

H0 :: (a->b) -> a -> b -> Prop
H0 eval'' funExp funSem =
  (eval'' funExp) <==> funSem
  
H2 :: (a->b) -> (a->a->a) -> (b->b->b) -> Prop
H0 <==> H2
  
if this is true, then the homomorphism be true for all constructors in FunExp

H2 :: (a->b) -> (a->a->a) -> (b->b->b) -> Prop

H2 eval'' (`Mul`) omul
H2 :: (FunExp->(R->R)) -> (FunExp->FunExp->FunExp) -> ((R->R)->(R->R)->(R->R)) -> Prop
H2 :: (FunExp->FunSem) -> (FunExp->FunExp->FunExp) -> (FunSem->FunSem->FunSem) -> Prop

H2 h f1 f2 
 = ∀x,y∈FunExp eval''(x `Mul` y) <==> omul (eval'' x) (eval'' y)

x = FunX 
y = FunX `Add` (Con 1)

eval''(x `Mul` y) <==> omul (eval'' x) (eval'' y)

eval'' $ (FunX) `Mul` (FunX `Add` (Con 1)) <==> omul (\r -> 0) (\r -> 0)
\r -> 2*r <==> \r -> 0
which is false, hence statement H2 is false.
-}

type Tri a    = (a,a,a)
type TriFun a = Tri (a -> a)    -- (a->a, a->a, a->a)
type FunTri a = a -> Tri a      -- a -> (a,a,a)

class Additive a where
 zero   :: a
 add    :: a -> a -> a

class Multiplicative a where
 one    :: a
 mul    :: a -> a -> a
 
class Additive a => AddGroup a where
 negate :: a -> a
 
class Multiplicative a => MulGroup a where
 recip  :: a -> a
 
class (MulGroup a, AddGroup a) => Algebraic a where
 root   :: a -> a
 
class Algebraic a => Transcendental a where
 π      :: a
 sin    :: a -> a
 cos    :: a -> a
 exp    :: a -> a
 
--dd :: Transcendental a => FunExp -> (Tri FunExp)

instance Transcendental FunExp where
 zero   = Con 0
 add    = Add
 one    = Con 1
 mul    = Mul
 negate = Negate
 recip  = Recip
 root   = Root
 π      = Pi
 sin    = Sin
 cos    = Cos
 exp    = Exp

d :: FunExp -> FunExp
d (Con _)       = Con 0
d (FunX)        = Con 1
d (Add a b)     = Add (d a) (d b)
d (Mul a b)     = Add (a `Mul` d b) (d a `Mul` b)
d (Negate a)    = Negate (d a)
d (Recip a)     = (Negate $ Recip (a `Mul` a)) `Mul` (d a)      --1/f(x) = -¹/f(x)² * f'(x)
d (Root a)      = (Recip $ (Root a `Mul` Con 2)) `Mul` (d a)    --f(x)¹ᐟ² = ⁻¹/(2f(x)) * f'(x)
d (Pi)          = Con 0
d (Sin a)       = (Cos a) `Mul` (d a)
d (Cos a)       = (Negate $ Sin a) `Mul` (d a)
d (Exp a)       = (Exp a) `Mul` (d a)

dd = d.d

evalDD :: Transcendental a => FunExp -> (a -> Tri a)
evalDD expr = \a -> (expr a, (d expr) a, (dd expr) a)

{- Con    :: REAL -> FunExp
 FunX   :: FunExp
 Add    :: FunExp -> FunExp -> FunExp
 Mul    :: FunExp -> FunExp -> FunExp
 Negate :: FunExp -> FunExp
 Recip  :: FunExp -> FunExp
 Root   :: FunExp -> FunExp
 Pi     :: FunExp
 Sin    :: FunExp -> FunExp
 Cos    :: FunExp -> FunExp
 Exp    :: FunExp -> FunExp
 -}

 