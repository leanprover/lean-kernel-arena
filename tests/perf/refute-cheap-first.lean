/-
A pair whose two components each refute convertibility on their own, one
cheaply and one expensively. In which order does the checker visit them? Here
the cheap component comes first; `refute-cheap-last.lean` swaps them.

From Courant and Leroy, "A Lazy, Concurrent Convertibility Checker",
POPL 2026, section 10, where the two orders cost Rocq 4 × 10⁻⁶s and 0.61s.
-/
import Lean

open Lean Elab Command

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option debug.skipKernelTC true

inductive N where
  | O : N
  | S : N → N

-- The definitions below apply the recursor directly. Structural recursion
-- would compile through `brecOn`, whose course-of-values table dominates every
-- cost these tests are about: measured on `discarded-argument`, the `brecOn`
-- form costs 3074M instructions against 17M, and reorders the checkers under
-- test.
noncomputable def N.add (a b : N) : N :=
  N.rec (motive := fun _ => N) b (fun _ ih => N.S ih) a

noncomputable def count (m : N) : N :=
  N.rec (motive := fun _ => N) N.O (fun _ ih => N.add ih (N.S N.O)) m

def dropArg (_ : Bool × N) : N := N.O

run_elab do
  let n := 200
  let ty := mkConst ``N
  let num : Nat → Expr := fun k => Id.run do
    let mut e := mkConst ``N.O
    for _ in [:k] do
      e := mkApp (mkConst ``N.S) e
    return e
  let pair : Expr → Expr → Expr := fun a b =>
    mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Bool) ty a b
  let lhs := mkApp (mkConst ``dropArg)
    (pair (mkConst ``Bool.false) (mkApp (mkConst ``count) (num n)))
  let rhs := mkApp (mkConst ``dropArg)
    (pair (mkConst ``Bool.true) (mkApp (mkConst ``count) (num (n + 1))))
  Lean.addDecl (.thmDecl {
    name := `kernel_refute_cheap_first
    levelParams := []
    type := mkApp3 (mkConst ``Eq [1]) ty lhs rhs
    value := mkApp2 (mkConst ``Eq.refl [1]) ty lhs
  })
