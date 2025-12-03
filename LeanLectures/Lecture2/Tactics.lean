import Lean

/-
This sounds lame but often tactics can be as simple as a macro short hand
-/

macro "hopium" : tactic =>
  `(tactic| try first | grind | rfl | omega)

example : x > y + 1 → y < x := by
  hopium


/-
Remember macros can take arguments
-/

macro fst:tactic " and_then " snd:tactic : tactic => `(tactic|(
  $fst; all_goals $(⟨snd⟩) -- `all_goals` takes a sequence of tactics, so we need to coerce this piece of syntax
))

theorem test_and_then: 1 = 1 ∧ 2 = 2 := by
  apply And.intro and_then rfl


#print test_and_then



/-
More complex interactions can be done as an elaborator
-/

open Lean Meta Elab Tactic

elab "reverse" : tactic => do
  let goals ← getUnsolvedGoals
  setGoals goals.reverse

example : p → q → r → p ∧ q ∧ r := by
  intros
  constructor
  reverse
  · constructor
    reverse
    all_goals assumption
  · all_goals assumption

#check absurd
elab "contra" : tactic =>
  withMainContext do
    let decls ← getMainDecl
    let fvs := decls.lctx.getFVars
    for fv in fvs do
      let t ← inferType fv
      let tt ← inferType t
      if tt.isProp then
        for fv' in fvs do
          let t' ← Meta.inferType fv'
          let tt' ← Meta.inferType t'
          if tt'.isProp then
            if t' == .app (.const ``Not []) t then
              let mv ← getMainGoal
              let u ← Meta.getLevel (← getMainTarget)
              mv.assign (mkApp4 (.const ``absurd [u]) t (← mv.getType) fv fv')
              return
    throwError "Could not find a prop and its negation"

example : p → ¬p → r := by
  intros
  rename p => h

  contra

-- example : p → q → r := by
--   intros
--   contra


#check LocalContext
#check LocalDecl

#check Nat.add 10 <| Nat.add 10 10

elab "rename " typeStx:term " => " h:ident : tactic =>
    withMainContext do
      /- Remark: we also use `withoutRecover` to make sure `elabTerm` does not succeed
         using `sorryAx`, and we get `"failed to find ..."` which will not be logged because
         it contains synthetic sorry's -/
      let fvarId ← withoutModifyingState <| withNewMCtxDepth <| withoutRecover do
        let type ← elabTerm typeStx none (mayPostpone := true)
        let lctx ← getLCtx
        let fvarId? ← lctx.findDeclRevM? fun localDecl => do
          if !localDecl.isImplementationDetail
              && (← isDefEq type localDecl.type) then
            return localDecl.fvarId
          else
            return none
        match fvarId? with
        | none => throwError "Failed to find a hypothesis with type{indentExpr type}"
        | some fvarId => return fvarId
      replaceMainGoal [← (← getMainGoal).rename fvarId h.getId]

example : p → p := by
  intros
  rename p => h
  exact h

-- example : q → p := by
--   intros
--   rename p => h
--   exact h
