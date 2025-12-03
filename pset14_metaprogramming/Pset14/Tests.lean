import Pset14.Pset14

--# --------Tests---------------

example : True := by
  have := trivial
  match_goal with
  | h : True ⊢ True => exact h

example : 1 + 2 = 3 := by
  match_goal with
  | _ ⊢ _ + _ = _ => omega

example : p → q → p ∧ q := by
  intros
  match_goal with
  | hp : p, hq : q ⊢ _ ∧ _ => exact ⟨hp, hq⟩

example : p → p → p := by
  intros
  match_goal with
  | h1 : p, h2 : p ⊢ _ => exact h1

example : p1 ∧ p2 → p2 ∧ p3 → p1 ∧ p2 ∧ p3 := by
  intros
  match_goal with
  | h1 : _ ∧ _, h2 : _ ∧ _ ⊢ _ =>
    cases h1; cases h2
    repeat first | apply And.intro | assumption

/-- A limited version of the propositional tactics used in Rocq -/
macro "propositional" : tactic => `(tactic|(
  repeat match_goal with
  /- Conjunctions -/
  | h : _ ∧ _ ⊢ _ => cases h
  | _ ⊢ _ ∧ _ => apply And.intro
  /- Disjunctions -/
  | _ ⊢ _ ∨ _ => apply Or.inl; assumption
  | _ ⊢ _ ∨ _ => apply Or.inr; assumption
  | h : _ ∨ _ ⊢ _ => cases h
  /- Negations -/
  | _ ⊢ ¬_ => intro _
  /- Catch all -/
  | _ ⊢ _ => first | contradiction | assumption
))

example : p1 → p2 → p1 ∧ p2 := by
  intros
  propositional

example : p1 → p1 ∨ p2 := by
  intros
  propositional

example : p2 → p1 ∨ p2 := by
  intros
  propositional

example : p → ¬p → q := by
  intros
  propositional

example : ¬p → ¬(p ∧ q) := by
  intros
  propositional

example : ¬q → ¬(p ∧ q) := by
  intros
  propositional

example : ¬p → ¬q → ¬(p ∨ q) := by
  intros
  propositional
