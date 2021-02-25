import Debug.Trace
import Test.QuickCheck

-- ============ Exercise 5.1. Polynomial multiplication ============ --
e1,e2,e3 :: [Integer]
e1 = [1]
e2 = [2,1]
e3 = [1,2,1]
x = [0,1]

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