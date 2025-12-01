
/-
Block comments
-/

-- Line comments

/--
Doc strings
-/
inductive Arith where
| const (n : Nat)
| plus (e1 e2 : Arith)
| times (e1 e2 : Arith)

def e1 := Arith.const 42
def e2 : Arith := .plus (.const 1) (.times (.const 2) (.const 3))

def Arith.size (e : Arith) : Nat :=
  match e with
  | .const _ => 1
  | .plus e1 e2 => 1 + Arith.size e1 + size e2
  | .times e1 e2 => 1 + e1.size + e2.size

#check e1.size
#eval e1.size

/-
Namespaces
-/

namespace Arith

def depth : Arith → Nat
  | .const _ => 1
  | .plus e1 e2 | .times e1 e2 => 1 + Nat.max e1.depth e2.depth

#check e1.depth
#eval e2.depth

theorem depth_le_size : ∀ e : Arith, e.depth ≤ e.size := by
  intro e
  induction e <;> grind [Arith.depth, Arith.size]

end Arith

structure Point where
  x : Nat
  y : Nat := 0 -- default values

def p1 := {x := 1, y := 2 :  Point}
def p2 : Point := {x := 0}
def p3 : Point := ⟨0, 0⟩
def p4 := Point.mk 0 0

#check p1.x + p2.y
#eval p1.x + p2.y

/- Dependent types -/

inductive Ty
  | nat
  | bool
  | fn : Ty → Ty → Ty

inductive Exp (rep : Ty → Type) : Ty → Type
  | var {α : Ty} (v : rep α) : Exp rep α
  | abs (body : rep α → Exp rep β) : Exp rep (.fn α β)
  | app (f : Exp rep (.fn α β)) (x : Exp rep α) : Exp rep β
  | nat (n : Nat) : Exp rep .nat
  | bool (b : Bool) : Exp rep .bool
  | plus (e1 e2 : Exp rep .nat) : Exp rep .nat
  | ite (cond : Exp rep .bool) (thn els : Exp rep α) : Exp rep α

abbrev Ty.denote : Ty → Type
  | .nat => Nat
  | .bool => Bool
  | .fn α β => α.denote → β.denote

def Exp.denote {α : Ty} : Exp Ty.denote α → α.denote
  | .var v => v
  | .abs body => fun x => (body x).denote
  | .app f x => f.denote x.denote
  | .nat v | .bool v => v
  | .plus e1 e2 => e1.denote + e2.denote
  | .ite cond thn els =>
    if cond.denote then
      thn.denote
    else
      els.denote

/-
Dependent structures
-/

structure Vec (α : Type) (n : Nat) : Type where
  data : List α
  isLt : data.length = n

def v1 : Vec Nat 1 := ⟨[0], by grind⟩

/-
Some prop stuff
-/

theorem and_comm' {p q : Prop} : p ∧ q → q ∧ p := by
  intro h
  exact ⟨h.right, h.left⟩

theorem or_comm' {p q : Prop} : p ∨ q → q ∨ p := by
  intro h
  apply h.elim
  · intro h; right; exact h
  · intro h; left; exact h

example : True ↔ True := by
  grind

example : ¬False := by
  grind

example : ∃ x, x + 1 = 2 := by
  exists 1

/-
Universe polymorphism
-/

inductive List' (α : Type u)
  | nil
  | cons (hd : α) (tl : List' α)

/-
Q: what is the type of `α` and `β` here?
-/
def List'.map (f : α → β) : List α → List β
  | .nil => .nil
  | .cons hd tl => .cons (f hd) (tl.map f)

/-
Type classes
-/

class Plus (α : Type) where
  plus : α → α → α

instance : Plus Nat where
  plus x y := Nat.add x y

#check Plus.plus 1 2
#check @Plus.plus Nat instPlusNat 1 2
#eval Plus.plus 1 2

class SemiGroup (α : Type) extends Plus α where
  id : α
  id_left : ∀ (a : α), Plus.plus id a = a
  id_right : ∀ (a : α), Plus.plus a id = a
  assoc : ∀ (a b c : α), Plus.plus a (Plus.plus b c) = Plus.plus (Plus.plus a b) c

instance : SemiGroup Nat where
  id := 0
  id_left := by intros; simp [Plus.plus]
  id_right := by intros; simp [Plus.plus]
  assoc := by intros; simp [Plus.plus]; omega


/-
Monadic programming
-/

def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | hd :: tl => do
    let hd ← f hd
    let tl ← mapM f tl
    return hd :: tl

def forLoop : Nat := Id.run do
  let mut x := 0
  for i in List.range 4 do
    x := x + i
  return x

#eval forLoop

def whileLoop : Nat := Id.run do
  let mut x := 0
  let mut y := 3
  while y > 0 do
    x := x + y
    y := y - 1
  return x

#eval whileLoop

/-
Partials and unsafes
-/

partial def nonTerm : Nat → Nat
  | 0 => nonTerm 1
  | n + 1 => nonTerm n

/- This is not provable since nonTerm is opaque to the kernel -/
-- theorem nonTerm_zero : nonTerm 0 = nonTerm 1 := by
--   sorry

unsafe def nonTermFalse : Nat → False
  | 0 => nonTermFalse 1
  | n + 1 => nonTermFalse n

/- The kernel doesn't accept this since it uses unsafe features -/
-- theorem false : False :=
--   nonTermFalse 0
