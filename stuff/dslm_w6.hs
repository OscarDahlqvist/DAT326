{-# LANGUAGE GADTs, FlexibleContexts, FlexibleInstances, TypeSynonymInstances, StandaloneDeriving, ConstraintKinds #-}

import Debug.Trace
import Test.QuickCheck

-- ============ Exercise 6.11.  ============ --

-- f can be expressed as e³ᵗ = Σₙ₌₀ aₙtⁿ

data Poly a = Poly [a] deriving (Show,Eq)
type PowerSeries a = Poly a
type REAL = Double

derivXp n = \t -> (3^n)*exp(3*t)

expx3 :: PowerSeries REAL
expx3 = Poly $ helper 0
    where 
        coeff n = ((derivXp 0) 0) / (fac n)
        helper n = coeff n:(helper (n+1))

fac 0 = 1
fac n = n*(fac (n-1))

class Ring a where 
    zero   :: a
    add    :: a -> a -> a
    one    :: a
    mul    :: a -> a -> a
    negate :: a -> a
    recip  :: a -> a
    
instance Ring REAL where
    zero    = fromInteger 0
    add     = (+)
    one     = fromInteger 1
    mul     = (*)
    negate  = (zero-)
    recip   = (one/)

--f''(t) = e³ᵗ+2f(t)-f'(t)

deriv :: Ring a => Poly a -> Poly a
deriv (Poly xs) = Poly (derivL xs)

derivL :: Ring a => [a] -> [a]
derivL [] = []
derivL (_:xs) = zipWith mul oneUp xs

oneUp :: Ring a => [a]
oneUp = one : map (add one) oneUp

-----------

takep n (Poly lst) = take n lst













sp []     = ""
sp (x:xs) = (show x)++(helper xs 1)
    where 
        helper [] _       = ""
        helper (x:xs) 1   = "+"++(shownon1 x)++"x"++(helper xs 2)
        helper (x:xs) pow = "+"++(shownon1 x)++"x^"++(show pow)++(helper xs (pow+1))
        
shownon1 1 = ""
shownon1 x = show x

--poly [1,2,3] = 1+2x+3x²

mulp :: [Integer] -> [Integer] -> [Integer]
                                --[] = 0
mulp [] _       = []
mulp _ []       = []
                                --const*(q₀+q₁x+q₂x²..)
mulp [c] q     = map (*c) q
mulp p [c]     = map (*c) p
                                --(p₀+p₁x+p₂x²..)*(q₀+q₁x+q₂x³..) = p₀*qs + p₁x*qs + ...
                                --                                = p₀*qs + x*(p₁*qs) + ...
                                
mulp (p:ps) qs  = addp (map (*p) qs) ([0] ++ mulp ps qs)
                                -- [0]++ in the start <=> multiply by x

addp :: [Integer] -> [Integer] -> [Integer]
addp p []          = p
addp [] q          = q
addp (p:ps) (q:qs) = (p+q):(addp ps qs)
























tru1 ps qs     = mulp ps qs == mulp qs ps
tru2 ps qs     = addp ps qs == addp qs ps

--(whole p*whole q) == p₀*qs + (p₁x+p₂x²+..)*qs
tru3 [] _      = True
tru3 (p:ps) qs = addp (map (*p) qs) (mulp (0:ps) qs) == mulp (p:ps) qs 


--mulp ps (q:qs)  = 

{-
mulp [] p = error "-- TODO"
mulp p [] = error "-- TODO"
mulp [a] p = error "-- TODO"
mulp p [b] = error "-- TODO"
mulp (0:as) p = error "-- TODO"
mulp p (0:bs) = error "-- TODO"
mulp (a:as) q@(b:bs) = error "-- TODO"
-}

(>>>) :: a -> String -> a
(>>>) a str = (trace str a)
debugged :: Show a => a -> a
debugged a = (trace (">>>"++show(a)) a)