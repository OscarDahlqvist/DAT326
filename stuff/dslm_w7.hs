{-# LANGUAGE GADTs, FlexibleContexts, FlexibleInstances, TypeSynonymInstances, StandaloneDeriving, ConstraintKinds, MultiParamTypeClasses#-}

import Debug.Trace
import qualified Prelude 
import Prelude (Show,show)
import Data.Maybe

type Real = Prelude.Double

class AddGroup a where
    zero    :: a
    (+)     :: a -> a -> a
    negate  :: a -> a
    
class AddGroup a => Field a where 
    one     :: a
    (*)     :: a -> a -> a
    recip   :: a -> a
    
instance AddGroup Real where
    zero = fromInteger 0
    (+) = (Prelude.+)
    negate = (Prelude.-) zero
instance Field Real where
    one = fromInteger 1
    (*) = (Prelude.*)
    recip = (Prelude./) one
    
(-) a b = a + (negate b)
(/) a b = a * (recip b)

infixl 6 - 
infixl 6 + 
infixl 7 * 
infixl 7 /
    
instance AddGroup Int where
    zero = 0
    (+) = (Prelude.+)
    negate = (Prelude.-) zero
    
instance AddGroup b => AddGroup (a -> b) where
    zero     = \_ -> zero
    (+) a b  = \x -> (a x) + (b x)
    negate a = \x -> negate $ a x

instance Field b => Field (a -> b) where
    one      = \_ -> one
    (*) a b  = \x -> (a x) * (b x)
    recip a  = \x -> recip $ a x
    
class (Field s, AddGroup v) => VectorSpace v s where
    scale :: s -> v -> v

type Poly a = [a]
type Vector s i = i -> s            --Vectors made of s indexed by i
type Matrix s i j = j -> Vector s i --Matrix indexed by j gives a vector of s indexed by i

instance Field s => VectorSpace (Vector s Int) s where
    scale s v = \i -> s*(v i)


sum :: AddGroup a => [a] -> a
sum = foldl (+) zero 

evalWithMX :: (VectorSpace (Vector s Int) s) => Matrix s Int Int -> Vector s Int -> Vector s Int
evalWithMX m v = sum (map (\i -> scale (v i) (m i)) [1..10]) 
-- the code never finishes if iterating through [1..], but it technically works? No idea how to use haskelllaziness to solve this. 

--poly derivative
oneUp :: Field a => Poly a
oneUp = one:map (+one) oneUp

zeros :: Field a => Poly a
zeros = zero:zeros

derPoly :: Field a => Poly a -> Poly a
derPoly a = zipWith (*) (drop 1 a) oneUp

integPoly :: Field a => Poly a -> Poly a
integPoly a = zero : zipWith (/) a oneUp
--

-- converters  --
tovec :: Field s => [s] -> Vector s Int 
tovec arr = \s -> (arr++zeros)!!(s-1)

unvec :: Int -> Vector s Int -> [s]
unvec 0 vec = []
unvec n vec = (unvec (n-1) vec)++[vec n]
--

--der :: (VectorSpace Int s) => (Int -> s) -> (Int -> s)
der3 :: (VectorSpace (Vector s Int) s) => Vector s Int -> Vector s Int
der3 v = (tovec.derPoly.(unvec 3)) v

integ3 :: (VectorSpace (Vector s Int) s) => Vector s Int -> Vector s Int
integ3 v = (tovec.integPoly.(unvec 3)) v

base :: Field s => Int -> [s]
base 1 = one:zeros
base n = zero:(base (n-1))

der3M :: (VectorSpace (Vector s Int) s) => Matrix s Int Int
der3M = tovec [(tovec.derPoly) (base 1), (tovec.derPoly) (base 2), (tovec.derPoly) (base 3)]
        
derM :: (VectorSpace (Vector s Int) s) => Matrix s Int Int
derM = tovec (map (\i -> (tovec.derPoly) (base i)) [1..])
    where
        base :: Field s => Int -> [s]
        base 1 = one:zeros
        base n = zero:(base (n-1))
-- [1..]
        
integM :: (VectorSpace (Vector s Int) s) => Matrix s Int Int
integM = tovec (map (\i -> (tovec.integPoly) (base i)) [1..])

-- ===== PROOF FOR Deriv * Integ = Id ==== --
{-
more specifically derM * integM, written here as DM and IM

DM = [D(e₁), D(e₂), D(e₃)...]
IM = [I(e₁), I(e₂), I(e₃)...]

A,B are matrixes
evalWithMX = evm

A * B = flip $ evm A.flip B
A * B = v -> flip $ evm A (evm (flip B) v)


DM * IM = flip $ (evm DM (flip IM))
DM * IM = flip (evm DM (flip IM))
DM * IM = p -> flip $ (evm DM ((flip IM) p))

DM*IM p q = flip (evm DM (flip IM)) p q
DM*IM p q = (\j -> evm DM ((flip IM) j)) q p
DM*IM p q = evm DM ((flip IM) q)) p

          = (ᵢΣ scale ((flip IM) q) i) (DM i) ) p
          = (ᵢΣ scale ((flip IM) q i) (DM i) ) p
          = (ᵢΣ scale (IM i q) (DM i) ) p
		  
scale s v = \j -> s*(v j)	  
DM*IM p q = (ᵢΣ scale (IM i q) (DM i) ) p
DM*IM p q = (ᵢΣ \j -> (IM i q)*(DM i j)) p
DM*IM p q = ᵢΣ (IM i q)*(DM i p)			-- works since ᵢΣ is linear

IM i q = I(Eᵢ) q
DM i p = D(Eᵢ) p

I(Eᵢ) q = 1/i if p = i
          0   otherwise
D(Eᵢ) p = i   if q = i
          0   otherwise
		  
(IM i q)*(DM i p) = (1/i)*i if (p = i) AND (q = i)
		                  0 otherwise
						  
(IM i q)*(DM i p) = 1 if (p = q = i)
		            0 otherwise
					
DM*IM p q = ᵢΣ (IM i q)*(DM i p)	
DM*IM p q = ᵢΣ if (p=q=i) then 1 else 0
since we iterate through each i, p=q=i will be fulfilled for exatly one of the i:s
=>
DM*IM p q = ᵢΣ if (p=q=i) then 1 else 0
DM*IM p q = if (p=q) then 1 else 0

QED

-}
-- == NOTHING OF IMPORTANCE FURTHER DOWN HERE == --































--test
d2 = ((scale (2::Real) (tovec px))::Vector Real Int)
d3 = ((scale (3::Real) (tovec px2))::Vector Real Int)

{-
F : R³ -> R³
F w = der w
F = [der (e₁), der (e₂), der (e₃])
-}

{- m = derivation matrix

\v -> evalWithMX m v = der
evalWithMX m = der
evalWithMX m v = der v
ᵢΣ scale (vᵢ) (mᵢ) = der v

scale (v₁) (m₁) = der v - (scale (v₂) (m₂) + scale (v₃) (m₃) +....)
scale (1/v₁) $ scale (v₁) (m₁) = scale (1/v₁) $ der v - (scale (v₂) (m₂) + scale (v₃) (m₃) +....)

mₙ = scale (1/vₙ) $ der v - (evalWithMX m v - scale (vₙ) (mₙ))

for 3x3 matrix:
m₁ = scale (1/v₁) $ der v - (scale (v₂) (m₂) + scale (v₃) (m₃))
m₂ = scale (1/v₂) $ der v - (scale (v₁) (m₁) + scale (v₃) (m₃))
m₃ = scale (1/v₃) $ der v - (scale (v₁) (m₁) + scale (v₂) (m₂))

m₁ = 1/v₁* $ der v - [m₂,m₃]*[v₂;v₃]
m₂ = 1/v₂* $ der v - [m₁,m₃]*[v₁;v₃]
m₃ = 1/v₃* $ der v - [m₁,m₂]*[v₁;v₂]

m v = [1/v₁* $ der v - [m₂,m₃]*[v₂;v₃], 1/v₂* $ der v - [m₁,m₃]*[v₁;v₃], 1/v₃* $ der v - [m₁,m₂]*[v₁;v₂]]
m v = [der v - [m₂,m₃]*[v₂;v₃], der v - [m₁,m₃]*[v₁;v₃], der v - [m₁,m₂]*[v₁;v₂]] [1/v₁; 1/v₂; 1/v₃]
m v = [der v,der v,der v] - [[m₂,m₃]*[v₂;v₃], [m₁,m₃]*[v₁;v₃], [m₁,m₂]*[v₁;v₂]] [1/v₁; 1/v₂; 1/v₃]

m v = DV - [[m₂,m₃]*[v₂;v₃], [m₁,m₃]*[v₁;v₃], [m₁,m₂]*[v₁;v₂]] IV

m v = DV - [[m₁,m₂,m₃]*[v₁,v₂;v₃]*[0;1;1], [m₁,m₂,m₃]*[v₁,v₂;v₃]*[1;0;1], [m₁,m₂,m₃]*[v₁,v₂;v₃]*[1;1;0]] IV
m v = DV - [m*v*[0;1;1], m*v*[1;0;1], m*v*[1;1;0]] IV
m v = DV - [m*v, m*v, m*v] [[0;1;1]; [1;0;1]; [1;1;0]] IV

m v = [der v,der v,der v] - [m, m, m] [v;v;v] [[0;1;1]; [1;0;1]; [1;1;0]] [1/v₁; 1/v₂; 1/v₃]
m v = [der v,der v,der v] - [m, m, m] [v;v;v] [[0;1;1]; [1;0;1]; [1;1;0]] [1/v₁; 1/v₂; 1/v₃]



derMatrix3 :: Field s => Matrix s Int Int
derMatrix3 :: Field s => Int -> (Int -> s)
derMatrix3 :: Field s => Int -> Int -> s
derMatrix3 = getRow get
-}



px,px2,px3 :: Field s => [s]
px  = [zero,one]
px2 = [zero,zero,one]
px3 = [zero,zero,zero,one]


-- ======================== --
transpose :: Matrix s i j ->  Matrix s j i
transpose m = \i j -> m j i     -- <=> flip m

getRow :: Matrix s i j -> j -> Vector s i
getRow m j = m j

getCol :: Matrix s i j -> i -> Vector s j
getCol m i = (transpose m) i    -- <=> flip m

{-
V = G -> s      ≈> v∈V v = [a;b;c] => v 1 = a
                ≈> V ≈ [s]



====================================
V :: G₁ -> S
U :: G₂ -> S
h :: V -> U

isLinTransform(h,V,U) =       
      H₀(h, zero::V, zero::U) &
      H₂(h, (+)::V, (+)::U) &
 ∀s∈S H₁(h, scale::V s, scale::U s) 
 
 enough proving H₁(...) for H₁(h, scale::V (-one), scale::U (-one)) 
 
 
h v = h (ᵥΣ scaleᵥ vᵢ eᵢ)
    = ᵤΣ h scaleᵥ vᵢ eᵢ
    = ᵤΣ scaleᵤ vᵢ (h eᵢ)
    
h v = h $ sum $ map (\i -> scale vᵢ eᵢ ) [1,2,3..iₘₐₓ]
    = sum $ map (\i -> h $ scale vᵢ eᵢ ) [1,2,3..iₘₐₓ]
    = sum $ map (\i -> scale vᵢ (h eᵢ) ) [1,2,3..iₘₐₓ]
====================================

der :: P 2 -> P 3
PN = {polynomials of degree <= n} = 
evalp :: P n -> R -> R
evalp a = sum $ map (\i -> scale aᵢ pᵢ)
    pᵢ x = xᶦ
    

evalWithMX m v = ᵢΣ scale (vᵢ) (mᵢ)

H2 (evalWithMX, mulMX, (.))
 <=> ∀a,b∈Matrix    evalWithMX (a mulMX b) = (evalWithMX a).(evalWithMX b)
 by specification
 
what is mulMX?

evalWithMX (a `mulMX` b) = (evalWithMX a).(evalWithMX b)
evalWithMX (mulMX a b) = (evalWithMX a).(evalWithMX b)

getCol m i = evalWithMX m (e i)             get i:th vector
getCol m   = evalWithMX m . e
flip m     = evalWithMX m . e
flip $ flip m = flip $ evalWithMX m . e
m             = flip $ evalWithMX m . e

(mulMX a b)   = flip $ evalWithMX (mulMX a b) . e
mulMX         = \a b -> flip $ evalWithMX (mulMX a b) . e
mulMX         = \a b -> flip $ ((evalWithMX a).(evalWithMX b)) . e      --according to H2 spec
mulMX         = \a b -> flip $ (evalWithMX a).(evalWithMX b).e
mulMX         = \a b -> flip $ (evalWithMX a).(evalWithMX b.e)          -- getCol m   = evalWithMX m . e
mulMX         = \a b -> flip $ (evalWithMX a).(flip b)
mulMX         = \a b -> flip $ evalWithMX a.flip b

mulMX a b     = flip $ evalWithMX a.flip b

mulMX :: M s a b -> M s b c -> M s a c
-}

{-
type V = Vector R R
Der :: V -> V
isLinTransform(Der)
isLinTransform(Der,V,V)
isLinTransform(Der,V,V) =       
      H₀(Der, zero::V, zero::V) &
      H₂(Der, (+)::V, (+)::V) &
 ∀r∈R H₁(Der, scale::V r, scale::V r) 
 
isLinTransform(Der,V,V) = 
      H₀(Der, 0, 0) &
      H₂(Der, +, +) &
 ∀r∈R H₁(Der, *r, *r)
 
 isLinTransform(Der,V,V) =                       is true
           Der 0 = 0 &                              √
    ∀a,b∈V Der (a+b) = (Der a)+(Der b) &            √
 ∀r∈R ∀a∈V Der (a*r) = (Der a) *r                   √

----
D = sematic derivative

gs t = exp (-s*t)
gs = \t -> exp (-s*t)

D gs = \t -> (-s)*exp(-s*t) = scale (-s) gs
----

D :: V -> V
D(f*g) = Df*g + f*Dg

I :: V -> V
I f x = ₀∫ˣf = ₀∫ˣf(t)dt

I(D f)    x = f x - f 0
I(D(f*g)) x = f*g x - f*g 0 = I(Df*g x + f*Dg x)        -- * is elevated mul here
I(D(f*g)) x = f*g x - f*g 0 = I(Df*g x) + I(f*Dg x)     -- since linear
I(D(f*g)) x = f*g x - f*g 0 = I(Df*g) x + I(f*Dg) x

let g = gs
 D gs = scale (-s) gs
assume (f*gs) x -> 0 as x -> ∞

f*gs x - f*gs 0 = I(Df*g) x + I(f*Dg) x
f*gs x - f(0)*gs(0) = I(Df*gs) ∞ + I(f*Dg) ∞
     0 - f(0)*1     = I(Df*gs) ∞ + I(f*(scale (-s) gs) ∞
     0 - f(0)*1     = I(Df*gs) ∞ + (-s)*I(f*gs) ∞           --since linear

define L as:
L :: (R -> R) -> C -> C
L f s = I (f*gs) ∞

       - f(0)*1     = I(Df*gs) ∞ + (-s)*L(f*gs) ∞           
       - f(0)       = L Df s + (-s)*L f s 
       - f(0) -(-s)*L f s = L Df s 
       - f(0) + s*L f s = L Df s 
       =>
       L Df s  = s*L f s - f(0)
       
========== LAPLACE ==========
L f s  = I(f*gs) ∞
       = ₀∫ᶦⁿᶠ f(t)*e⁻ˢᣟᵗ dt
       
L Df s = (-f 0) + s*(L f s)
!! ONLY IF x -> ∞ => f(x)*gs(x) -> 0 !!


L :: V -> W 
isLinTransform(L,V,W) √ (trust me dude)
=============================
-}


type String = Prelude.String
type Int = Prelude.Int
(++) = (Prelude.++)
(!!) = (Prelude.!!)
($) = (Prelude.$)
(.) = (Prelude..)
fromInteger = (Prelude.fromInteger)
otherwise = Prelude.otherwise
map = (Prelude.map)
foldl = (Prelude.foldl)
drop = (Prelude.drop)
zipWith = (Prelude.zipWith)
error = (Prelude.error)
flip = (Prelude.flip)

(>>>) :: a -> (Prelude.String) -> a
(>>>) a str = trace str a
debugged :: Show a => a -> a
debugged a = (trace (">>>"++(show a)) a)