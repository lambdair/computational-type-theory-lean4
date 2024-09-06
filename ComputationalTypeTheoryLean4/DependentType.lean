import ComputationalTypeTheoryLean4.CustomTactics
-- s, t, u, v ∷= c | x | 𝕋 | ∀x:s.t | st
inductive Term : Type where
  | 𝕋 : Term
  | var : String → Term
  | const : String → Term
  | fa : String → Term → Term → Term
  | application : Term → Term → Term
open Term

notation:100 "𝑥" => Term.var
notation:100 "𝑐" => Term.const
infixr:50 " ⇝ " => Term.tArrow
infixl:60 " ∘ " =>  Term.application
notation:40 " ⍱ " y:40 " ⫶ " s:40 " , " t:40  =>  Term.fa y s t

#check ⍱ "x" ⫶ 𝕋 , 𝕋

def subst (x : String) (s : Term) : Term → Term
  | 𝕋 => 𝕋
  | var y => if x = y then s else var y
  | const c => const c
  | fa y s' t => if x = y then s else ⍱ y ⫶ subst x s s' , subst x s t
  | application s t => application (subst x s s) (subst x s t)

/--
 `⟦x := s⟧ v` は `v` の中の `x` を `s` に置き換えたもの
 ⊢ s t : ⟦x := s⟧ v
-/
inductive WellTyped : Option (String × Term) → Term → Term → Prop where
  | wt_universe : WellTyped none 𝕋 𝕋
  | wt_dep_fun : ∀ {x s t},
      WellTyped none s 𝕋 →
      WellTyped (some (x, s)) t 𝕋 →
      WellTyped none (⍱ x ⫶ s , t) 𝕋
  | wt_app : ∀ {s t u v},
      WellTyped none s (⍱ x ⫶ u , v) →
      WellTyped none t u →
      WellTyped none (s ∘ t) v
open WellTyped

notation:100 env " ⊢ " t " : " u => WellTyped env t u
