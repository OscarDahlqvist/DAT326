--Pick one of 2.12 and 2.25.
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}

-- 4.21

--i
class Ring a where 
 (¤+) :: a -> a -> a    --addition
 (¤*) :: a -> a -> a    --multiplication
 (¤!) :: a -> a         --negation
 zero :: a
 one  :: a

--ii
data Expr where 
 Add  :: Expr -> Expr -> Expr
 Mul  :: Expr -> Expr -> Expr
 Neg  :: Expr -> Expr
 Zero :: Expr
 One  :: Expr
 Var  :: String -> Expr
 deriving Show

instance Ring Expr where
 (¤+) x y       = Add x y
 (¤*) x y       = Mul x y
 (¤!) x         = Neg x
 one            = One
 zero           = Zero
 
type AF n = (String -> n)

--iii
instance Ring Bool where
 (¤+) x y   = x||y
 (¤*) x y   = x&&y
 (¤!) x     = not x
 zero       = False
 one        = True

instance Ring Integer where
 (¤+) x y   = x+y
 (¤*) x y   = x*y
 (¤!) x     = -x
 zero       = 0
 one        = 1

{-
instance Ring (AF Bool -> Bool) where
 (¤+) f g   = \x -> f x || g x
 (¤*) f g   = \x -> f x && g x
 (¤!) f     = \x -> not $ f x
 zero       = \x -> False
 one        = \x -> True
-- var str    = \x -> x str       --get the bool value from the AF of Bools
 
instance Ring (AF Integer -> Integer) where
 (¤+) f g   = \x -> f x + g x
 (¤*) f g   = \x -> f x * g x
 (¤!) f     = \x -> -(f x)
 zero       = \x -> 0
 one        = \x -> 1
-- var str    = \x -> x str       --get the int value from the AF of Ints
-}
--iv

eval :: Expr -> AF a -> ((a->a->a), (a->a->a), (a->a), a, a) -> a
eval expr af funcs@(iadd,imul,ineg,izero,ione) = case expr of 
 (Add x y) -> iadd (eval x af funcs) (eval y af funcs)
 (Mul x y) -> imul (eval x af funcs) (eval y af funcs)
 (Neg x)   -> ineg (eval x af funcs)
 (Zero)    -> izero
 (One)     -> ione
 (Var str) -> af str
  where fold x = eval x af funcs

eval' expr af funcs = fold expr
 where 
  (iadd,imul,ineg,izero,ione) = funcs
  fold (Add x y) = iadd (fold x) (fold y)
  fold (Mul x y) = imul (fold x) (fold y)
  fold (Neg x)   = ineg (fold x)
  fold (Zero)    = izero
  fold (One)     = ione
  fold (Var str) = af str
 
eval'' :: Ring a => Expr -> AF a -> a
eval'' expr af = eval' expr af ((¤+),(¤*),(¤!),zero,one)

--v
evalBool :: Expr -> AF Bool -> Bool
evalBool = eval''

evalInt :: Expr -> AF Integer -> Integer
evalInt = eval''

x1,x2,x3 :: Ring a => a
x1 = (one ¤+ zero)
x2 = x1 ¤+ (¤!)x1
x3 = x1 ¤* one









af x = error $ "\""++x++"\" is undefined"

bAf :: AF Bool
bAf "t" = True
bAf "f" = False
bAf x = error $ "\""++x++"\" is undefined"

iAf :: AF Integer
iAf "one" = 1
iAf "zero" = 0
iAf x = error $ "\""++x++"\" is undefined"

b1,b3,b4,b5 :: Ring a => a
b1 = (one ¤+ zero)
b3 = b1 ¤+ zero
b4 = b3 ¤* ((¤!)b3)
b5 = b3 ¤+ (¤!)b3

i1,i3,i4,i5 :: Ring a => a
i1 = (one ¤+ zero)
i3 = i1 ¤+ one
i4 = i3 ¤* (¤!)i3
i5 = i3 ¤+ (¤!)i3