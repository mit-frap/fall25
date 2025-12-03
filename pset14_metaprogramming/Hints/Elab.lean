import Lean
import Std.Data.HashSet.Basic
open Lean Meta Elab Tactic

/-
Here's the signature of some helper function used in our solution
-/

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


/-- Find a single hypothesis with type `type` in the local context `lctx`.
    Only succeed if it doesn't appear in the `used` set. -/
def findHyp (lctx : LocalContext) (used : Std.HashSet FVarId) (type : Expr) : TacticM (Option FVarId) := do
  sorry

/-- Find the set of hypotheses in `hyps` under the local context `lctx` and rename them accordingly.
    NOTE: This function may modify the meta-variable state! -/
def findHyps (lctx : LocalContext) (hyps : Array (Option Name × Expr)) : TacticM Bool := do
  let mut used : Std.HashSet FVarId := {} -- track hypotheses that are already used
  sorry

/-- Check if a pattern matches the current proof state.
    NOTE: This function may modify the meta-variable state! -/
def checkPattern (goal : MVarId) (arm : MatchArm) : TacticM Bool := do
  sorry
