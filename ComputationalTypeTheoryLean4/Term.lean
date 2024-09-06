import ComputationalTypeTheoryLean4.CustomTactics

-- s, t, u, v ∷= c | 𝕋 | s → t | st
inductive Term : Type where
  | 𝕋 : Term
  | c : String → Term
  | tArrow : Term → Term → Term
  | application : Term → Term → Term
open Term

infixr:50 " ⇝ " => Term.tArrow
infixl:60 " ∘ " =>  Term.application

inductive WellTyped : Term → Term → Prop where
  | wt_universe : WellTyped 𝕋 𝕋
  | wt_arrow : ∀ {s t}, WellTyped s 𝕋 → WellTyped t 𝕋 → WellTyped (s ⇝ t) 𝕋
  | wt_app : ∀ {s t u v}, WellTyped s (u ⇝ v) → WellTyped t u → WellTyped (s ∘ t) v
open WellTyped

notation:100 " ⊢ " t " : " u => WellTyped t u
#check ⊢ 𝕋 : 𝕋
-- #check ⊢ WellTyped (c "s") 𝕋 : 𝕋
-- #check ⊢ WellTyped (s ⇝ t) 𝕋 : 𝕋
-- #check ⊢ WellTyped (s ∘ t) v :  𝕋

example : ∀ {N Z S},
  (⊢ N : 𝕋) →
  (⊢ Z : N) →
  (⊢ S : (N ⇝ N)) →
  ⊢ N ⇝ N : 𝕋
  := by
    intro N Z S HT_N _HT_Z _HT_S
    apply wt_arrow HT_N HT_N
    done
