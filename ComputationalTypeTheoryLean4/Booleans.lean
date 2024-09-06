import ComputationalTypeTheoryLean4.CustomTactics

/-!
 inductive typeは重要みたいな話
-/

/--
 Bool型

-/
inductive B : Type where
  /-- True -/
  | T : B
  /-- False -/
  | F : B
  deriving DecidableEq

open B (T F)

/- 無限の宇宙 -/

#check B
#check Type
#check Type 1

/- inductive function は各コンストラクタに対してすべて定義される必要がある -/

def negation : B → B :=
  λ b ↦ match b with
    | T => F
    | F => T
notation:100 "!" b => negation b

#check ! T

#check negation

example : !!!T = F := by
  /-
  rw はEqualityが必要だからderivingじゃなくてちゃんと与える必要がある
  rw []
  -/
  simp
  done

def conjunction (b1 : B) (b2 : B) : B :=
  match b1, b2 with
    | T, b2 => b2
    | F, _ => F
infix: 60 "&" => conjunction

def disjunction (b1 : B) (b2 : B) : B :=
  match b1, b2 with
    | T, _ => T
    | F, b2 => b2
infix: 55 "||" => disjunction

theorem distributivity_law : x & (y || z) = (x & y) || (x & z) := by
  sorry

theorem commutativity_law : x & y = y & x := by
  sorry
