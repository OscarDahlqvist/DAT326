{-# LANGUAGE GADTs, FlexibleContexts, FlexibleInstances, TypeSynonymInstances, StandaloneDeriving #-}
import Data.List
import Debug.Trace


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
--
--derive :: FunExp a -> FunExp a
--derive = error "todo"

data FunExp a where
    Zero   :: FunExp a
    One    :: FunExp a
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
-- ============== 1a ============== --

{-
By def. the homomorphism conserves the operation. Thus if eval'' is a homomorphism,
    then eval'' (f op1 g) == (eval'' f) op2 (eval'' g) for every operation op1 on the function 
    expressions f and g. That is there exists a operation op2 in the semantic domain directly corresponding to the operation op1 in the syntactic domain. 
    
To prove that eval'' is not a homomorphism it suffices to observe that the second
    derivative of the product of two functions cannot be constructed using only the value of the second derivative itself.
    This simply follows from the product rule.


H2 :: (a->b) -> (a->a->a) -> (b->b->b) -> Prop
in this case
H2 :: (FunExp->(R->R)) -> (FunExp->FunExp->FunExp) -> ((R->R)->(R->R)->(R->R)) -> Prop

H2 eval'' Mul omul
 should hold if eval'' is a homomophism

H2 eval'' Mul omul
 = ∀x,y∈FunExp $ eval''(x `Mul` y) <==> omul (eval'' x) (eval'' y)

example x,y where this is not true:
    x = FunX 
    y = FunX

    eval''(x `Mul` y) <==> omul (eval'' x) (eval'' y)d
    
    eval $ derive $ derive (x `Mul` y) <==> omul (eval'' x) (eval'' y)

    eval $ derive $ derive $ FunX `Mul` FunX                           <==> omul (λr -> 0) (λr -> 0)
    eval $ derive          $ Add (FunX `Mul` Con 1) (FunX `Mul` Con 1) <==> λr -> 0*0
    eval $ derive          $ Add (FunX) (FunX)                         <==> λr -> 0
    eval                   $ Add (Con 1) (Con 1)                       <==> λr -> 0
    eval                   $ Con 2                                     <==> λr -> 0
    λr -> 2                                                            <==> λr -> 0
    
    λr -> 2 <==> λr -> 0
    which is false, hence statement H2 is false.
-}

-- ============== 1b ============== --

type Tri a    = (a,a,a)
type TriFun a = Tri (a -> a)    -- (a->a, a->a, a->a)
type FunTri a = a -> Tri a      -- a -> (a,a,a)         --why is not used for newton?

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

{-
  To prove that evalDD is a homomophism in the case of multiplication we need to prove the existance of
  a funtion:

  muld :: Transcendental a => (a->a,a->a,a->a) -> (a->a,a->a,a->a) -> (a->a,a->a,a->a),
  
  such that

  H2 = evalDD (mul f g) == muld (evalDD f) (evalDD g).

  Using the notation f' = d f, f'' = dd f (mutatis mutandis for g), add = +, mul = *, (...)*(...)= (...)*(...)
  we prove this by directly expanding the definition of our evalDD funtion:

  evalDD (mul f g)  = (eval f*g, eval (f*g)', eval (f*g)'') = [one iter of product rule] =
  = (eval f*g, eval (f*g' + f'*g), eval (f*g' + f'*g)') = [derivative is linear and second iter of prod rule] =
  = (..., eval ((f*g')(f'*g)' + (f*g')'(f'*g)) = (..., eval ((f*g')(f'*g' + f''*g)
                                                 + (f*g'' + f'*g')(f'*g)) =
  = (..., eval (f*f'*g'*g' + f*f''*g'*g +f*f'*g''*g + f'*f'*g'*g)).

  This shows that we can construct a function muld such that H2 is satisfied. Such a function
  would be defined as:

  muld f g = (f*g, f*g' + f'*g, f*f'*g'*g' + f*f''*g'*g +f*f'*g''*g + f'*f'*g'*g)
    where f   = fst f
          f'  = snd f
          f'' = trd f
          g   = fst g
          g'  = snd g
          g'' = trd g
  QED
-}

-- ============== 2a ============== --

--reference unimplementable function
newton :: (REAL -> REAL) -> REAL -> REAL -> REAL
newton f ep x = 
    if (abs fx) < ep
        then x
    else if abs fx' /=  0
        then newton f ep next
        else newton f ep (x+ep)
    where 
        fx  = f x
        fx' = error "undefined"
        next = x - (fx/fx')
        
--uneccesary function used for testing   
newtonF :: FunExp REAL -> REAL -> REAL -> REAL
newtonF f ep x = 
    if (abs fx) < ep
        then x
    else if abs fx' /=  0
        then newtonF f ep next
        else newtonF f ep (x+ep)
    where 
        fx  = eval f x
        fx' = eval (d f) x
        next = x - (fx/fx')

newtonTri :: (Tri REAL -> Tri REAL) -> REAL -> REAL -> REAL
newtonTri f ep x = 
    if (abs fx) < ep
        then x
    else if abs fx' /=  0
        then newtonTri f ep next
        else newtonTri f ep (x+ep)
    where 
        (fx,fx',fx'') = f (x,x,x)
        next = x - (fx/fx')
        
toTriSem :: FunExp REAL -> (Tri REAL -> Tri REAL)
toTriSem expr = help
    where help (a,b,c) = (eval expr a, eval (d expr) b, eval (dd expr) c)

--newtonTri (toTriSem (Cos FunX)) 0.01 1
--newtonF (Cos FunX) 0.001 1

-- ============== 2b ============== --

test0 :: Tri REAL -> Tri REAL
test0 (a,b,c) = (a^2,   2*b,2)
test1 (a,b,c) = (a^2-1, 2*b,2)
test2 (a,b,c) = (Prelude.sin a, Prelude.cos b, 0-(Prelude.sin c))


test3ex :: Tri REAL -> Tri REAL
test3ex = test3 1 1

test3 :: REAL -> REAL -> Tri REAL -> Tri REAL
test3 n x (y1,y2,y3) = (y1**n - x, n*y2**(n-1) - x, n*(n-1)*y3**(n-2) - x)

--test0 x = x^2                   -- one (double) zero, in 0
--test1 x = x^2 − 1               -- two zeros, in −1 and 1
--test2 = Prelude.sin             -- many, many zeros (n ∗ π)
--test3 n x y = y^n − constTri x  -- test3 n x specifies the nth root of x

s0 = map (newtonTri test0 0.001) [-2.0, -1.5 .. 2.0]
s1 = map (newtonTri test1 0.001) [-2.0, -1.5 .. 2.0]
s2 = map (newtonTri test2 0.001) [-2.0, -1.5 .. 2.0]
s3 n x = map (newtonTri (test3 n x) 0.001) [-2.0, -1.5 .. 2.0]
        
-- ============== 3 ============== --        

data Result where 
    Maxima :: REAL -> Result
    Minima :: REAL -> Result
    Dunno  :: REAL -> Result
    deriving Show
    
optim :: (Tri REAL -> Tri REAL) -> REAL -> REAL -> Result
optim f ep x
 | fx'' < 0  = Maxima ntr
 | fx'' > 0  = Minima ntr
 | otherwise = Dunno ntr
    where 
        ntr = newtonTri helper ep x
        (fx,fx',fx'') = f (ntr, ntr, ntr)
        helper (a,b,c) = (fb', fc'', error "undefined")
            where (fa,fb',fc'') = f (a,b,c)








{-
(>>>) :: a -> String -> a
(>>>) a str = (trace str a)
debugged :: Show a => a -> a
debugged a = (trace (">>>"++show(a)) a)
-}