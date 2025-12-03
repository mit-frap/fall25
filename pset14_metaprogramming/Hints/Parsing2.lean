import Lean

/-
Here is the intermediate data structure used to store the parsed output in the solution
-/

open Lean

/--
A single match arm inside a match goal.
-/
structure MatchArm where
  /-- The names and types of the hypotheses to be matched.
      If renaming is not needed (i.e., the user put an underscore for the name),
      it will be a none. -/
  hyps : Array (Option Name × Expr)
  /-- The proof goal to be matched.
      If the user put underscore then this is none. -/
  goal : Option Expr
  /-- The tactic to be applied if the match succeeded. -/
  tac  : Syntax
