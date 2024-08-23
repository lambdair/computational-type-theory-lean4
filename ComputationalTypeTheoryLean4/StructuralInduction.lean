import ComputationalTypeTheoryLean4.Numbers

/-!
構造帰納法(strucral induction)
-/
open ℕ (Z S)

example (n : ℕ) : n + Z = n := by
  induction n
  case Z =>  simp [plus]
  case S n ih =>
    dsimp [plus]
    rw [ih]

example (x y : ℕ) : x + S y = S (x + y) := by
  induction x
  /- Z + S y = S (Z + y) -/
  case Z => rfl
  case S x ih =>
    dsimp [plus]
    rw [ih]
