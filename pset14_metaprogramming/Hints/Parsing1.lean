
/-
Here are the syntax categories used in our solution
-/

/-- An individual hypothesis to be matched. -/
declare_syntax_cat hyp

/-- The list of hypotheses to be matched.
    This can just be a single underscore. -/
declare_syntax_cat hyps

/-- Everything on the left-hand side of a match arm,
    i.e. `h : p, _ : q ⊢ goal`. -/
declare_syntax_cat goal_state

/-- A single match arm starting from the `|` character. -/
declare_syntax_cat match_arm
