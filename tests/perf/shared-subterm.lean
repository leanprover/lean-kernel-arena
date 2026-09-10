/-
A term whose normal form has 2^n nodes and whose representation has n. Does
the checker consume it without expanding it?

From Courant and Leroy, "A Lazy, Concurrent Convertibility Checker",
POPL 2026, section 10.
-/
import Lean

open Lean Elab Command

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option debug.skipKernelTC true

inductive N where
  | O : N
  | S : N → N

inductive Tr where
  | leaf : Tr
  | node : Tr → Tr → Tr

-- The definitions below apply the recursor directly. Structural recursion
-- would compile through `brecOn`, whose course-of-values table dominates every
-- cost these tests are about: measured on `discarded-argument`, the `brecOn`
-- form costs 3074M instructions against 17M, and reorders the checkers under
-- test.
noncomputable def N.add (a b : N) : N :=
  N.rec (motive := fun _ => N) b (fun _ ih => N.S ih) a

noncomputable def perfect (k : N) (t : Tr) : Tr :=
  N.rec (motive := fun _ => Tr → Tr) (fun t => t) (fun _ ih => fun t => ih (Tr.node t t)) k t

noncomputable def ldepth (t : Tr) : N :=
  Tr.rec (motive := fun _ => N) N.O (fun _ _ ih _ => N.S ih) t

noncomputable def ldepth2 (t : Tr) : N :=
  Tr.rec (motive := fun _ => N) N.O (fun _ _ ih _ => N.add ih (N.S N.O)) t

run_elab do
  let n := 1000
  let ty := mkConst ``N
  let num : Nat → Expr := fun k => Id.run do
    let mut e := mkConst ``N.O
    for _ in [:k] do
      e := mkApp (mkConst ``N.S) e
    return e
  let tree := mkApp2 (mkConst ``perfect) (num n) (mkConst ``Tr.leaf)
  let lhs := mkApp (mkConst ``ldepth) tree
  let rhs := mkApp (mkConst ``ldepth2) tree
  Lean.addDecl (.thmDecl {
    name := `kernel_shared_subterm
    levelParams := []
    type := mkApp3 (mkConst ``Eq [1]) ty lhs rhs
    value := mkApp2 (mkConst ``Eq.refl [1]) ty lhs
  })
