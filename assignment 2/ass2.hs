{-# LANGUAGE GADTs #-}
import Data.List
import Test.QuickCheck

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

--cant be defined sice der :: F a -> Bi (F a)
--eval' = eval.der

--eval'' = eval.der.der
--alt: eval''= eval'.der

oadd, omul :: S -> S -> S
oadd f g = \x -> f x + g x
omul f g = \x -> f x * g x

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

data FunExp = Const REAL 
 | FunX
 | FunExp :+: FunExp
 | FunExp :*: FunExp
 | Negate FunExp

{-
class Additive a where
 zero   :: a
 add    :: a -> a -> a

class Multiplicative a where
 one    :: a
 mul    :: a -> a -> a
 
class Additive a => AddGroup a where
 neg    :: a -> a
 
class (AddGroup a, Multiplicative a) => Ring a
-}

class Ring a where
 zero   :: a
 add    :: a -> a -> a
 one    :: a
 mul    :: a -> a -> a
 neg    :: a -> a

instance Ring FunExp where 
 zero   = Const 0
 add    = (:+:)
 one    = Const 1
 mul    = (:*:)
 neg    = Negate

type Tri a    = (a,a,a)
type TriFun a = Tri (a -> a)    -- (a->a, a->a, a->a)
type FunTri a = a -> Tri a      -- a -> (a,a,a)


{-

-}