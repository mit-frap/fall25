import Lean
open Lean

inductive Arith
  | const (n : Nat)
  | plus (e1 e2 : Arith)
  | times (e1 e2 : Arith)
  | pow (e1 e2 : Arith)
  | neg (e : Arith)
deriving Nonempty

/-- Syntax category for arithmetic expressions -/
declare_syntax_cat arith

syntax num : arith
syntax "(" arith ")" : arith
syntax:30 arith:31 " ^ " arith:30 : arith
syntax:20 arith:20 " * " arith:21 : arith
syntax:10 arith:10 " + " arith:11 : arith
syntax:40 "-" arith:39 : arith

/-
`TSyntax` allows us to use lean's type checker to make sure we are passing around
then right kind of syntax to the right parser function.
They are not strictly enforced and syntax types can be easily coerced into each other.
-/

/-
Syntax quotations allows us to easily build and pattern match on `Syntax` objects.
-/

partial def parseArith : TSyntax `arith → Arith
  | `(arith| $n:num) =>
    -- parseArith ⟨n.raw⟩
    .const n.getNat
  | `(arith| ( $e:arith )) => parseArith e
  | `(arith| $e1:arith + $e2:arith) =>
    let e1 := parseArith e1
    let e2 := parseArith e2
    .plus e1 e2
  | `(arith| $e1:arith * $e2:arith) =>
    let e1 := parseArith e1
    let e2 := parseArith e2
    .times e1 e2
  | `(arith| $e1:arith ^ $e2:arith) =>
    let e1 := parseArith e1
    let e2 := parseArith e2
    .pow e1 e2
  | `(arith| -$e:arith) =>
    let e := parseArith e
    .neg e
  | _ => .const 0

def Arith.printTree (e : Arith) : Std.Format :=
  match e with
  | .const n => s!"{n}"
  | .plus x y =>
    let x := cont ++ nest x.printTree
    let y := last ++ nest y.printTree
    join [s!"(+)", x, y]
  | .pow x y =>
    let x := cont ++ nest x.printTree
    let y := last ++ nest y.printTree
    join [s!"(^)", x, y]
  | .times x y =>
    let x := cont ++ nest x.printTree
    let y := last ++ nest y.printTree
    join [s!"(*)", x, y]
  | .neg x =>
    let x := last ++ nest x.printTree
    join [s!"(-)", x]
where
  nest x := Std.Format.nest 5 x
  join (l : List Std.Format) := Std.Format.joinSep l "\n"
  cont := " |---"
  last := " '---"

def test : Elab.TermElabM Arith := do
  let stx ← `(arith| 1 + 2 + 3)
  pure (parseArith stx)
#eval do let e ← test; IO.println e.printTree
