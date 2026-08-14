/-
One constant application occurring twice in a problem, once plain and once
under a function that forces it. Here the forcing component comes first, so a
checker visiting components in order reduces the application before comparing
the plain occurrences; `folded-constant-last.lean` swaps them.

From Courant and Leroy, "A Lazy, Concurrent Convertibility Checker",
POPL 2026, section 10, where the two orders cost Rocq 3 × 10⁻⁵s and 0.078s.
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

noncomputable def isZero (m : N) : Bool :=
  N.rec (motive := fun _ => Bool) true (fun _ _ => false) m

noncomputable def tagged (m : N) : Bool × N := (isZero m, m)

run_elab do
  let n := 1000
  let ty := mkConst ``N
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Bool) ty
  let num : Nat → Expr := fun k => Id.run do
    let mut e := mkConst ``N.O
    for _ in [:k] do
      e := mkApp (mkConst ``N.S) e
    return e
  let arg := mkApp (mkConst ``count) (num n)
  let lhs := mkApp (mkConst ``tagged) arg
  let rhs := mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Bool) ty (mkConst ``Bool.false) arg
  Lean.addDecl (.thmDecl {
    name := `kernel_folded_constant_first
    levelParams := []
    type := mkApp3 (mkConst ``Eq [1]) pairTy lhs rhs
    value := mkApp2 (mkConst ``Eq.refl [1]) pairTy lhs
  })
