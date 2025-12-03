# Assignment: Implementing match_goal Tactic
## Overview
In this assignment, you will implement a limited version of Rocq's `match goal` tactic from Ltac. This tactic allows you to pattern-match on the current proof state and conditionally execute tactics based on what hypotheses and goal are present.

## Important note about hints
We expect everyone to read through the hints listed at the bottom of this README before starting the assignment.
Additional spoiler-like hints can be found in the `Hints` folder.

## Installing Lean
Follow the instructions here:
[https://lean-lang.org/](https://lean-lang.org/)

## Syntax Specification
The `match_goal` tactic has the following syntax:

```
match_goal with
| <pattern₁> => <tactics₁>
| <pattern₂> => <tactics₂>
...
| <patternₙ> => <tacticsₙ>
```

Each pattern has the form: `<hypotheses> ⊢ <goal>`

### Hypothesis Patterns
- `_` - matches any set of hypotheses (wildcard)
- `_ : <type>` - matches any hypothesis with the given type
- `<name> : <type>` - matches a hypothesis with the given type and renames it to <name>
- Multiple hypothesis patterns can be comma-separated: `h₁ : T₁, h₂ : T₂, ...`

### Goal Patterns
- `_` - matches any goal (wildcard)
- `<term>` - matches a goal that unifies with the given term

## Behavior Requirements

### Pattern Matching:
The tactic should try each arm (rule with a pattern and a tactic) in order, checking if the current proof state matches the pattern.

When matching hypotheses, check that there exist distinct hypotheses in the context with the specified types.
Use unification `isDefEq` to check type equality.
Each hypothesis can only be matched once per pattern.
When a name is provided (e.g., `h : t`), rename the matched hypothesis to that name.

If a specific goal pattern is provided, check that the current goal unifies with it.
If `_` is used, any goal matches.

### Execution:

Execute the tactic sequence of the first matching arm.
If the tactic fails, try the next matching arm.
If no arms match, throw an error "nothing matched".

### Backtracking:
If a pattern matches but its tactic fails, restore the proof state and try the next pattern.
Unification effects should be isolated between pattern-matching attempts.

### Example Usage
```
example : p → q → p ∧ q := by
  intros
  match_goal with
  | hp : p, hq : q ⊢ _ ∧ _ => exact ⟨hp, hq⟩
```
This invocation matches when there are hypotheses of types `p` and `q`, renaming them to `hp` and `hq` respectively, and the goal has the form `_ ∧ _`.

## Grading:
All test cases used in grading are in the `Pset14/Tests.lean` file.
There are no hidden tests.
If you run `lake build` in the `pset14_metaprogramming` directory and get no warnings or errors, you will get 100% credit.
```bash
$ lake build
Build completed successfully (4 jobs).
```

## Files to Submit
Write your solution in `Pset14/Pset14.lean` and submit that file only.


## Implementation Hints
<!-- - Define syntax categories for the different components (`hyp`, `hyps`, `goal_state`, `match_arm`). -->
### Parsing
You need to use these builtin parsers in your solution:

### `ident`:

This parses a Lean identifier. For example, if you defined a syntax category of hypothesis called `hyp`, you can write:
```lean4
syntax ident " : " term : hyp
```
to parse something like `h : p ∧ q`.
Note that `ident` does not parse underscores, so you'll need a separate rule for that explicitly like this:
```lean4
syntax "_" " : " term : hyp
```

### `tacticSeq`

`tactic` will only parse a single tactic, `tacticSeq` can parse a sequence of tactics.

### Separation of Concerns

Creating a data structure for storing intermediate results will help you separate the parsing code from everything else and simplify the implementation.

<!-- - Implement pattern matching that handles both hypothesis matching and goal matching. -->

### Type unification
These functions are helpful for managing the unification state:

[`Lean.withoutModifyingState`](https://leanprover-community.github.io/mathlib4_docs/Lean/Util/MonadBacktrack.html#Lean.withoutModifyingState)

[`Lean.MonadBacktrack.saveState`](https://leanprover-community.github.io/mathlib4_docs/Lean/Util/MonadBacktrack.html#Lean.MonadBacktrack.saveState)

[`Lean.MonadBacktrack.restoreState`](https://leanprover-community.github.io/mathlib4_docs/Lean/Util/MonadBacktrack.html#Lean.MonadBacktrack.restoreState)

Use `withoutModifyingState` when checking patterns to avoid unintended side effects.

### Goal Renaming
Remember to handle local naming of matched hypotheses. A useful code pattern is `replaceMainGoal [← (← getMainGoal).rename fvarId name]` where `fvarId` is the hypothesis to be renamed, and `name` is the new name provided by the user. If the use provided an underscore for that hypothesis, don't rename it.

### Executing Tactics
This function is useful for evaluating tactics: [`Lean.Elab.Tactic.evalTactic`](https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Basic.html#Lean.Elab.Tactic.evalTactic).

Note that this can throw an exception if the tactic fails.
You can handle that like this:

```lean4
try
  evalTactic tac
  ...
catch ex =>
  ...
```

Also remember that evaluating tactics can modify the current state.

### Length

Our entire solution is on the order of ~120 lines (including white spaces and comments).
If your solution is getting much longer, reconsider your approach.
