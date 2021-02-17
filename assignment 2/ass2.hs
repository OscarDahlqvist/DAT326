{-# LANGUAGE GADTs, FlexibleContexts, FlexibleInstances, TypeSynonymInstances, StandaloneDeriving #-}
import Data.List
import Test.QuickCheck

-- ============== 1a ============== --

import qualified Prelude (sin,cos,exp,pi)
import Prelude hiding (recip,negate,sin,cos,exp,pi)

type REAL = Double

eval :: Transcendental a => FunExp a -> (a -> a)
eval (Zero)     = \x -> zero
eval (One)      = \x -> one
eval (Con c)    = \x -> c
eval (FunX)     = \x -> x 
eval (Add a b)  = \x -> eval a x `add` eval b x
eval (Mul a b)  = \x -> eval a x `mul` eval b x
eval (Negate a) = \x -> negate (eval a x)
eval (Recip a)  = \x -> recip (eval a x)
eval (Root a)   = \x -> root (eval a x)
eval (Pi)       = \x -> pi
eval (Sin a)    = \x -> sin (eval a x)
eval (Cos a)    = \x -> cos (eval a x)
eval (Exp a)    = \x -> exp (eval a x)


--eval' :: Transcendental a => FunExp -> FunSem
--eval'= eval.derive
--
--eval' :: Transcendental a => FunExp -> FunSem
--eval'' = eval'.derive
--eval'' = eval.derive.derive

derive :: FunExp a -> FunExp a
derive = error "todo"

data FunExp a where
 Zero   :: FunExp a --bad
 One    :: FunExp a --bad
 Con    :: (Transcendental a) => a -> FunExp a
 FunX   :: FunExp a
 Add    :: FunExp a -> FunExp a -> FunExp a
 Mul    :: FunExp a -> FunExp a -> FunExp a
 Negate :: FunExp a -> FunExp a
 Recip  :: FunExp a -> FunExp a
 Root   :: FunExp a -> FunExp a
 Pi     :: FunExp a
 Sin    :: FunExp a -> FunExp a
 Cos    :: FunExp a -> FunExp a
 Exp    :: FunExp a -> FunExp a
 
deriving instance Show (FunExp REAL)
 
--type FunSem = (REAL -> REAL)

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

-- ============== 1b ============== --

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
 pi     :: a
 sin    :: a -> a
 cos    :: a -> a
 exp    :: a -> a
 
--dd :: Transcendental a => FunExp -> (Tri FunExp)

instance Additive a => Additive (FunExp a) where
 zero   = Zero
 add    = Add
instance Multiplicative a => Multiplicative (FunExp a) where
 one    = One
 mul    = Mul
instance AddGroup a => AddGroup (FunExp a) where
 negate = Negate
instance MulGroup a => MulGroup (FunExp a) where
 recip  = Recip
instance Algebraic a => Algebraic (FunExp a) where
 root   = Root
instance Transcendental a => Transcendental (FunExp a) where
 pi     = Pi
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
 pi     = Prelude.pi
 sin    = Prelude.sin
 cos    = Prelude.cos
 exp    = Prelude.exp

d :: Transcendental a => FunExp a -> FunExp a
d (Con _)       = zero
d (FunX)        = one
d (Add a b)     = add (d a) (d b)
d (Mul a b)     = add (a `mul` d b) (d a `mul` b)
d (Negate a)    = negate (d a)
d (Recip a)     = (negate $ recip (a `mul` a)) `mul` (d a)                --1/f(x) = -¹/f(x)² * f'(x)
d (Root a)      = (recip $ (root a `mul` (one `add` one))) `mul` (d a)    --f(x)¹ᐟ² = ⁻¹/(2f(x)) * f'(x)
d (Pi)          = zero
d (Sin a)       = (cos a) `mul` (d a)
d (Cos a)       = (negate $ sin a) `mul` (d a)
d (Exp a)       = (exp a) `mul` (d a)
d _             = zero

dd :: Transcendental a => FunExp a -> FunExp a
dd = d.d

evalDD :: Transcendental a => FunExp a -> FunTri a
evalDD expr a = (f a, f' a, f'' a)
 where 
  f   = eval (expr)
  f'  = eval (d expr)
  f'' = eval (dd expr)

-- ============== 1c ============== --

--step one, surrender

-- ============== 2a ============== --

newton :: (REAL -> REAL) -> REAL -> REAL -> REAL
newton f ep x = if abs (f x) < ep
                    then x

