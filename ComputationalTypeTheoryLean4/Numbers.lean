import ComputationalTypeTheoryLean4.Booleans
/-!
-/

open B (T F)

/- 自然数 -/
inductive ℕ : Type where
  | Z : ℕ
  | S : ℕ → ℕ

open ℕ (Z S)

#check S Z

def plus : ℕ → ℕ → ℕ
  | Z, y => y
  | S x, y => S (plus x y)
infixl:65 "+" => plus

#check Z + Z

/- 0以下は切り捨てて0になる減算 -/
def cutOffMinus : ℕ → ℕ → ℕ
  | Z, _ => Z
  | S m, n => S (cutOffMinus m n)
infixl:65 "∸" => cutOffMinus

def times : ℕ → ℕ → ℕ
  | Z, _ => Z
  | S m, n => n + (times m n)
infixl:65 "*" => times

def exponentiation : ℕ → ℕ → ℕ
  | _, Z => S Z
  | x, S n => times x (exponentiation x n)
infixl:70 "^" => exponentiation

def minimum : ℕ → ℕ → ℕ
  | Z, _ => Z
  | _, Z => Z
  | S x, S y => S (minimum x y)

def equal : ℕ → ℕ → B
  | Z, Z => T
  | Z, S _ => F
  | S _, Z => F
  | S x, S y => equal x y

def less : ℕ → ℕ → B
  | Z, Z => F
  | Z, S _ => T
  | S _, Z => F
  | S x, S y => less x y
