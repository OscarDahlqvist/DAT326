--Pick one of 2.12 and 2.25.
{-# LANGUAGE GADTs #-}

-- 2.12
data Prop = Con Bool
 | Not Prop
 | And Prop Prop
 | Or Prop Prop
 | Implies Prop Prop
 | Name String
 deriving(Show)

mdual :: Prop -> Prop
mdual (Not(And a b)) = Not a `Or` Not b
mdual (Not(Or a b))  = Not a `And` Not b
mdual (And a b)      = Not $ Not a `Or` Not b
mdual (Or a b)       = Not $ Not a `And` Not b
mdual x = x


{-==== SECTION 2.6.3 Continuity and limits ====-}

--2.22





-- ∃L∈R. ∀e>0. P a L €
-- ∃L∈R. ∀e∈R>0. P a L €
-- ∃L∈R(∀e>0(P a L €))

-- B :: ℝ → ℝ>0 → 𝒫(ℝ)
-- B c r = {x| |x−c| < r}
-- B(c,r) = {x| |x−c| < r} = SET(c-r,c+r)

-- I :: (ℕ → X) → ℕ → 𝒫(X)
-- I a N = {a n | n ≥ N}

-- P a L e = ∃N∈ℕ. ∀n≥N. |aₙ − L| < e
-- P a L e = ∃N∈ℕ. ∀n≥N. aₙ ∈ B L e
-- P a L e = ∃N∈ℕ. I a N ⊆ B L e

-- 2.24
--1
sq :: Integer -> Double
sq n = fromIntegral (n`mod`2)
{-

--2
P a L e = ∃N∈ℕ. ∀n≥N. |aₙ − L| < e
P a L e = ∃N∈ℕ. ∀n∈ℕ. n>N → |aₙ − L| < e

¬(∃L∈ℝ. ∀e∈ℝ>0. (P a L e))
¬(∃L∈ℝ. ∀e∈ℝ>0. ∃N∈ℕ. ∀n∈ℕ. n>N → |aₙ − L| < e)
∀L∈ℝ. ¬(∀e∈ℝ>0. ∃N∈ℕ. ∀n∈ℕ. n>N → |aₙ − L| < e)
∀L∈ℝ. ∃e∈ℝ>0. ¬(∃N∈ℕ. ∀n∈ℕ. n>N → |aₙ − L| < e)
∀L∈ℝ. ∃e∈ℝ>0. ∀N∈ℕ. ¬(∀n∈ℕ. n>N → |aₙ − L| < e)
∀L∈ℝ. ∃e∈ℝ>0. ∀N∈ℕ. ∃n∈ℕ. ¬(n>N → |aₙ − L| < e)
∀L∈ℝ. ∃e∈ℝ>0. ∀N∈ℕ. ∃n∈ℕ. (n>N ∧ ¬(|aₙ − L| < e))
∀L∈ℝ. ∃e∈ℝ>0. ∀N∈ℕ. ∃n∈ℕ. (n>N ∧ (|aₙ − L| ≥ e))

--3
for all real numbers L (
	there exists a real number > 0 e (
		which for all integers N (
			there exists an n for which (
				(n bigger than N) and (|aₙ − L| ≥ e)
			)
		)
	)
)

--4
for L = 0 (
	there exists a real number > 0 e (
		which for all integers N (
			there exists an n for which (
				(n bigger than N) and (aₙ ≥ e) 
			)
		)
	)
)

for L != 0 (
	there exists a real number > 0 e (
		which for all integers N (
			there exists an n for which (
				(n bigger than N) and (|aₙ − L| ≥ e)
			)
		)
	)
)

===2.25.1==============================
id x = x
---2.25.2------------------------------
:proof for 2.23.2
¬(∃L∈ℝ. ∀e∈ℝ>0. (P a L e))
¬(∃L∈ℝ. ∀e∈ℝ>0. ∃N∈ℕ. ∀n∈ℕ. n>N → |aₙ − L| < e)
∀L∈ℝ. ¬(∀e∈ℝ>0. ∃N∈ℕ. ∀n∈ℕ. n>N → |aₙ − L| < e)
∀L∈ℝ. ∃e∈ℝ>0. ¬(∃N∈ℕ. ∀n∈ℕ. n>N → |aₙ − L| < e)
∀L∈ℝ. ∃e∈ℝ>0. ∀N∈ℕ. ¬(∀n∈ℕ. n>N → |aₙ − L| < e)
∀L∈ℝ. ∃e∈ℝ>0. ∀N∈ℕ. ∃n∈ℕ. ¬(n>N → |aₙ − L| < e)
∀L∈ℝ. ∃e∈ℝ>0. ∀N∈ℕ. ∃n∈ℕ. (n>N ∧ ¬(|aₙ − L| < e))
∀L∈ℝ. ∃e∈ℝ>0. ∀N∈ℕ. ∃n∈ℕ. (n>N ∧ (|aₙ − L| ≥ e))

in 2.24 a is a function ℕ → ℝ where aₙ is the nth element of (0,1,0,1, ...)
a(n) = a n = aₙ (just different notation)

for 2.25 it makes more sense replacing the aₓ notation with a(x)

2.24:   ∀L∈ℝ. ∃e∈ℝ>0. ∀N∈ℕ. ∃n∈ℕ. (n>N ∧ (|aₙ − L| ≥ e))
    <=> ∀L∈ℝ. ∃e∈ℝ>0. ∀N∈ℕ. ∃n∈ℕ. (n>N ∧ (|a(n) − L| ≥ e))
	
2.25:   ∀L∈ℝ. ∃e∈ℝ>0. ∀N∈ℕ. ∃n∈ℕ. (n>N ∧ (|id(n) − L| ≥ e))
    <=> ∀L∈ℝ. ∃e∈ℝ>0. ∀N∈ℕ. ∃n∈ℕ. (n>N ∧ (|n − L| ≥ e))
	
NOTE: :t id = ℕ→ℕ, which is not the same type as "a"
But this does not matter since ℕ⊆ℝ and all operations inside (n>N ∧ (|aₙ − L| ≥ e))
do not need non integers (ℝ\ℕ)
	
---2.25.3------------------------------
for all real numbers L (
	there exists a real number > 0 e (
		which for all integers N (
			there exists an n for which (
				(n bigger than N) and (|n − L| ≥ e)
			)
		)
	)
)

---2.25.4------------------------------
∀L∈ℝ. ∃e∈ℝ>0. ∀N∈ℕ. ∃n∈ℕ. (n>N ∧ (|n − L| ≥ e))

for L=0
	∃e∈ℝ>0. ∀N∈ℕ. ∃n∈ℕ. (n>N ∧ (|n − 0| ≥ e))
	∃e∈ℝ>0. ∀N∈ℕ. ∃n∈ℕ. (n>N ∧ (|n| ≥ e))			
	∃e∈ℝ>0. ∀N∈ℕ. ∃n∈ℕ. (n>N ∧ (n ≥ e))				(seeing as ℕ only contains positive)

	pick e = n to always make the second part of the AND is true
	∀N∈ℕ. ∃n∈ℕ. (n>N ∧ (n ≥ n))	
	∀N∈ℕ. ∃n∈ℕ. (n>N ∧ T)	
	∀N∈ℕ. ∃n∈ℕ. (n>N)
	for all N∈ℕ
	 there in an n∈ℕ for which
	  n>N is True
	This can not be solved
	=> the statement "the sequence is not convergent" is false
	=> the sequence is convergent

for L!=0
∀L∈(ℝ\{0}). ∃e∈ℝ>0. ∀N∈ℕ. ∃n∈ℕ. (n>N ∧ (|n − L| ≥ e))




R(x) = x is rational

S = ∃p. ∃q. ¬R(p) & ¬R(q) & R(pˆq) 
  = ∃p. ∃q. f(p,q)

either R(pˆq) is rational OR R(pˆq) is irrational
R(p^q) AND ¬R(p^q) = FALSE
R(p^q) OR  ¬R(p^q) = TRUE


z = p^q
for p = q = r = √2 -> EITHER
 z is rational
  DONE
 OR
 z is irrational
  for p = z -> EITHER
  (z^r = (√2^√2)^√2 = 2)
   z^r is rational
    DONE
   OR
   z^r is irrational
   
R(p) = TRUE & R(q) = TRUE
	¬R(p*q) = TRUE √
	¬R(p*q) = FALSE
		=> R(p*q) & R(q) = TRUE
			¬R((p*q)*q) = TRUE √
			¬R((p*q)*q) = FALSE
		AND
		=> R(p) & R(p*q) = TRUE
			¬R(p*(p*q)) = TRUE √
			¬R(p*(p*q)) = FALSE
			
S = ∃p∃q. f(a) & f(b) & ¬f(a*b)
S = ¬¬(∃p∃q. f(a) & f(b) & ¬f(a*b))
S = ¬(∀p∀q. ¬(f(a) & f(b) & ¬f(a*b)))


S(a,b)
f(a) & f(b) & ¬f(a?b)
	if ¬f(a?b) = FALSE 
		S = f(a?b) & f(b) & ¬f((a?b)?b) OR 
			f(a) & f(a?b) & ¬f(a?(a?b))


? :: X -> X -> X
a,b∈X
			
S(a,b) = f(a) & f(b) & ¬f(a?b)
<=> 
S(a,b) = S(a,b) OR S(a?b, b) OR S(a, a?b)

A,B ∈ ℝ\ℚ
ORR
	A^B is Rational
	OR
		(A^B)^B Is Rational
		A^(A^B) Is Rational
		

-}
{-
data Prop = Con Bool
 | Not Prop
 | And Prop Prop
 | Or Prop Prop
 | Implies Prop Prop
 | Name String
 deriving(Show)
-}

data Proof where 
 TruthIntro		::											   Proof
 FalseElim 		:: Proof 									-> Proof
 AndIntro  		:: Proof -> Proof 							-> Proof
 AndElimL 		:: Prop  -> Proof 							-> Proof
 AndElimR 		:: Prop  -> Proof 							-> Proof
 OrIntroL 		:: Proof 									-> Proof
 OrIntroR 		:: Proof 									-> Proof
 OrElim 		:: Prop -> Prop -> Proof -> Proof -> Proof 	-> Proof
 NotIntro 		:: Prop -> Proof -> Proof 					-> Proof
 NotElim 		:: Proof 									-> Proof
 Assume 		:: Prop 									-> Proof
 ImplyIntro 	:: (Proof -> Proof) 						-> Proof
 ImplyElim 		:: Prop -> Proof -> Proof 					-> Proof

checkProof :: Proof -> Prop -> Bool
checkProof TruthIntro (Con True) = True
checkProof (AndIntro a b) (And b y) = checkProof a x && checkProof b y



