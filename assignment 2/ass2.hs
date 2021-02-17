{-# LANGUAGE GADTs, FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
import Data.List
import Test.QuickCheck

--1a

import qualified Prelude (sin,cos,exp)
import Prelude hiding (recip,negate,exp,sin,cos)

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

instance Additive FunExp where
 zero   = Con 0
 add    = Add
instance Multiplicative FunExp where
 one    = Con 1
 mul    = Mul
instance AddGroup FunExp where
 negate = Negate
instance MulGroup FunExp where
 recip  = Recip
instance Algebraic FunExp where
 root   = Root
instance Transcendental FunExp where
 π      = Pi
 sin    = Sin
 cos    = Cos
 exp    = Exp
 
instance Additive REAL where
 zero   = 0
 add    = (+)
instance Multiplicative REAL where
 one    = 1
 mul    = (*)
instance AddGroup REAL where
 negate = (zero-)
instance MulGroup REAL where
 recip  = (one/)
instance Algebraic REAL where
 root   = sqrt
instance Transcendental REAL where
 π      = pi
 sin    = Prelude.sin
 cos    = Prelude.cos
 exp    = Prelude.exp

d :: FunExp -> FunExp
d (Con _)       = zero
d (FunX)        = one
d (Add a b)     = add (d a) (d b)
d (Mul a b)     = add (a `mul` d b) (d a `mul` b)
d (Negate a)    = negate (d a)
d (Recip a)     = (negate $ recip (a `mul` a)) `mul` (d a)      --1/f(x) = -¹/f(x)² * f'(x)
d (Root a)      = (recip $ (root a `mul` (one `add` one))) `mul` (d a)    --f(x)¹ᐟ² = ⁻¹/(2f(x)) * f'(x)
d (Pi)          = zero
d (Sin a)       = (cos a) `mul` (d a)
d (Cos a)       = (negate $ sin a) `mul` (d a)
d (Exp a)       = (exp a) `mul` (d a)

dd :: FunExp -> FunExp
dd = d.d

--evalDD :: Transcendental a => FunExp -> (a -> Tri a)
evalDD expr = \a -> (f a, f' a, f'' a)
 where 
  f   = eval (expr)
  f'  = eval (d expr)
  f'' = eval (dd expr)

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

 