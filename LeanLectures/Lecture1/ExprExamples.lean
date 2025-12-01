import Lean

open Lean

/--
The constant `0`

Use backtick to quote a name into `Lean.Name` used in expressions
-/
def z' := Expr.const `Nat.zero []
#eval z'

/-
Double backticks will fully resolve the name and check it's validity in the current context

Try making a typo here
-/
def z := Expr.const ``Nat.zero []
#eval z

/-
Function applications
`Nat.succ Nat.zero`
-/
def one := Expr.app (.const ``Nat.succ []) z
#eval one

def natExpr: Nat → Expr
| 0     => z
| n + 1 => .app (.const ``Nat.succ []) (natExpr n)
#eval natExpr 0
#eval natExpr 1

/-
There are many utility short-hands for defining expressions
For example, `mkAppN`
-/
def sumExpr : Nat → Nat → Expr
| n, m => mkAppN (.const ``Nat.add []) #[natExpr n, natExpr m]
#eval sumExpr 0 1

/-
lambda abstractions

`BinderInfo.default` makes it an standard explicit argument
-/
def constZero : Expr :=
  .lam `x (.const ``Nat []) (.const ``Nat.zero []) BinderInfo.default
#eval constZero

/-
With universe levels
-/

def nat : Expr := .const ``Nat []

def addOne : Expr :=
  .lam `x nat
    (mkAppN (.const ``Nat.add []) #[.bvar 0, mkNatLit 1])
    BinderInfo.default

def mapAddOneNil : Expr :=
  mkAppN (.const ``List.map [levelZero, levelZero])
    #[nat, nat, addOne, .app (.const ``List.nil [levelZero]) nat]

/- Trick to turn expr into a Lean term -/
elab "mapAddOneNilE" : term => return mapAddOneNil
#check mapAddOneNilE
#eval mapAddOneNilE




/- 1 + 2 -/
def three : Expr :=
  .app (.app (.const ``Nat.add []) (natExpr 1)) (natExpr 2)

elab "threeE" : term => return three
#eval threeE




/- fun (a b c : Nat) => b * ((fun d => a + d) c) -/
def multPlus : Expr :=
  .lam `a nat (
    .lam `b nat (
      .lam `c nat (
        mkAppN (.const ``Nat.mul []) #[
          .bvar 1,
          .app (.lam `d nat (mkAppN (.const ``Nat.add []) #[.bvar 3, .bvar 0]) .default) (.bvar 0)
        ]
      ) .default
    ) .default
  ) .default

elab "multPlusE" : term => return multPlus
#check multPlusE
