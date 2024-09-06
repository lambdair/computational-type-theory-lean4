import Lean.Elab.Tactic
import Lean.Meta
import Lean

elab "show_goal" : tactic => do
  let goals ← Lean.Elab.Tactic.getGoals
  match goals with
  | [] => Lean.logInfo "No goals"
  | goal :: _ =>
    let ctx ← Lean.MVarId.getDecl goal
    let lctx := ctx.lctx

    -- 仮定を文字列のリストとして収集
    let hypotheses ← lctx.foldrM (init := []) fun ldecl acc => do
      if !ldecl.isAuxDecl then
        let type ← Lean.Meta.inferType ldecl.type
        pure $ (s!"{ldecl.userName} : {type}") :: acc
      else
        pure acc

    -- 仮定を表示
    if hypotheses.isEmpty then
      Lean.logInfo "No hypotheses"
    else
      Lean.logInfo "Current hypotheses:"
      for h in hypotheses do
        Lean.logInfo h

    -- ゴールを表示
    let goalType ← Lean.MVarId.getType goal
    Lean.logInfo m!"Current goal: {goalType}"

example (a b : Nat): a + b = b + a := by
  show_goal
  apply Nat.add_comm
  show_goal

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro hpq
  show_goal
  obtain ⟨hp, hq⟩ := hpq
  show_goal
  exact ⟨hq, hp⟩
