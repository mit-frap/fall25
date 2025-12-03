import Lean
import Std.Data.HashSet.Basic
open Lean Meta Elab Tactic

/- Here's a bunch of functions that you might find useful -/

-- You'll probably want to set the `mayPostpone` argument to `true`,
-- this allows the assignment of mvars to be postponed
#check elabTerm

#check isDefEq

#check withoutModifyingState
#check saveState
#check restoreState

#check replaceMainGoal
#check getMainGoal
#check getLCtx

#check evalTactic

#check Std.HashSet.contains
