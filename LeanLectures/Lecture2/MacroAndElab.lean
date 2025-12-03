
/-
Macros are simply syntax to syntan trasformations
-/

import Lean

open Lean

namespace MacroExamples
/-
Macros are syntax-to-syntax transformations
-/

/- `scoped` keyword makes sure this syntax only works in the current namespace -/
scoped syntax:10 (name := lxor) term:10 " LXOR " term:11 : term

@[macro lxor] def lxorImpl : Macro
  | `($l:term LXOR $r:term) => `(!$l && $r) -- we can use the quotation mechanism to create `Syntax` in macros
  | _ => Macro.throwUnsupported

#eval true LXOR true -- false
#eval true LXOR false -- false
#eval false LXOR true -- true
#eval false LXOR false -- false

/- `macro_rules` is a shorthand for writing the above -/
scoped syntax:10 term:10 " RXOR " term:11 : term

scoped macro_rules
  | `($l:term RXOR $r:term) => `($l && !$r)

/- The `macro` command makes it even shorter -/

/-- My funny operator -/
scoped macro:10 l:term:10 " ⊕ " r:term:11 : term => `((!$l && $r) || ($l && !$r))

#eval true ⊕ true -- false
#eval true ⊕ false -- true
#eval false ⊕ true -- true
#eval false ⊕ false -- false

end MacroExamples

-- open MacroExamples
/- If we didn't scope the above example, it would clash with the standard notation for sum types -/
#check Nat ⊕ Nat
/- btw, here's the notation for product types -/
#check Nat × Bool


/-
Syntax combinators

There are many builtin syntax combinators to make life easier for you

This one is particularly useful for the assignment
-/

-- run the function given at the end for each element of the list
syntax "foreach " "[" term,+ "]" term : term

macro_rules
  | `(foreach [ $[ $x:term ],* ] $func:term) =>
    `(let f := $func; [ $[f $x],* ])

#eval foreach [1,2,3,4] (Nat.add 2) -- [3, 4, 5, 6]



/-
Macros are very powerful and sufficient for a wide range of simple meta-programming tasks

But sometimes we need to interact with the environment is more complicated ways,
which requires us to do elaboration
-/

open Lean Elab Command Term Meta

syntax (name := hello) "#hello!" : command -- declare the syntax

@[command_elab hello]
def mycommand1Impl : CommandElab := fun _ => do -- declare and register the elaborator
  logInfo "Welcome Rocq users!"

#hello!

/-
The same short-hand for `macro` also exists for `elab`
-/

elab "#hello2" : command =>
  logInfo "Hello World"

#hello2
