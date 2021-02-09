{-# LANGUAGE GADTs #-}
data Prop where 
  Con 	  :: Bool -> Prop
  Not 	  :: Prop -> Prop
  And 	  :: Prop -> Prop -> Prop
  Or      :: Prop -> Prop -> Prop
  Implies :: Prop -> Prop -> Prop
  Name    :: String -> Prop
 deriving (Show)
 
type Syn = Prop
type Sem = Tab -> Bool
type Tab = String -> Bool
type Sem' = Bool

eval :: Syn -> Sem
eval (Con b)			= conSem b
eval (Not e)			= notSem (eval e)
eval (And e1 e2)		= andSem (eval e1) (eval e2)
eval (Or e1 e2)			= orSem  (eval e1) (eval e2)
eval (Implies e1 e2)	= impSem (eval e1) (eval e2)
-- eval (String s)

conSem' :: Sem' -> Sem'
conSem' = id
notSem' = not
andSem' :: Sem' -> Sem' -> Sem'
andSem' = (&&)
orSem'  = (||)
impSem' = (==>)

(==>) :: Bool -> Bool -> Bool
False ==> _ = True
True  ==> x = x


--          2arg func    arg       arg
lift2arg :: (b->b->b) -> (a->b) -> (a->b) -> (a->b)
lift2arg op f g = \x -> op (f x) (g x)

conSem :: (Tab -> Bool) -> (Tab -> Sem)
conSem = error "undefined"
notSem = error "undefined"

conSem :: (Tab -> Bool) -> (Tab -> Bool) -> (Tab -> Sem)
andSem = lift2arg andSem'
orSem  = lift2arg orSem'
impSem = lift2arg impSem' 
 
  
  
  
  
  

data Mängd where
  Empty :: Mängd
  M     :: Mängd -> Mängd
  Union :: Mängd -> Mängd -> Mängd
  Snitt  :: Mängd -> Mängd -> Mängd
 deriving (Eq, Show)
 
elemOf :: Mängd -> Mängd -> Bool
elemOf search (Empty)     = search == Empty
elemOf search m@(M x) =
 search == m || 
 search `elemOf` x
elemOf search m@(Union x y) = 
 search == m || 
 search `elemOf` x || 
 search `elemOf` y
elemOf search m@(Snitt x y) = 
 search == m || 
 (search `elemOf` x &&  search `elemOf` y)

-- |A|+|B| = |A∪B|+|A∩B|
card :: Mängd -> Integer
card (Empty)     = 0
card (M a)       = 1
card (Union a b) = card a + card b - card (Snitt a b)
card (Snitt a b) = card a + card b - card (Union a b) 



