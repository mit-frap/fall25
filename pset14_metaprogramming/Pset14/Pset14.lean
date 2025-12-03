import Lean
import Std.Data.HashSet.Basic
open Lean Meta Elab Tactic

/-- A single match arm starting from the `|` character. -/
declare_syntax_cat match_arm

elab "match_goal" " with " arms:match_arm+ : tactic => do
  withMainContext do
    /- Fill in your solution here -/
    throwError "nothing matched"
