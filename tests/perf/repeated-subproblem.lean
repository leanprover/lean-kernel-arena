/-
Mechanism: reaching the same convertibility subproblem an exponential number of
times, so that the cost depends on whether convertibility results are shared.

Test case from Courant and Leroy, "A Lazy, Concurrent Convertibility Checker"
(POPL 2026), section 10, where Rocq spends 0.018s and the paper's checker
spends 9 × 10⁻⁵s.
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

noncomputable def perfect (k : N) (t : Tr) : Tr :=
  N.rec (motive := fun _ => Tr → Tr) (fun t => t) (fun _ ih => fun t => ih (Tr.node t t)) k t

run_elab do
  let n := 20
  let ty := mkConst ``Tr
  let leaf := mkConst ``Tr.leaf
  let num : Nat → Expr := fun k => Id.run do
    let mut e := mkConst ``N.O
    for _ in [:k] do
      e := mkApp (mkConst ``N.S) e
    return e
  let lhs := mkApp2 (mkConst ``perfect) (num n) leaf
  let rhs := mkApp2 (mkConst ``perfect) (num (n - 1)) (mkApp2 (mkConst ``Tr.node) leaf leaf)
  Lean.addDecl (.thmDecl {
    name := `kernel_repeated_subproblem
    levelParams := []
    type := mkApp3 (mkConst ``Eq [1]) ty lhs rhs
    value := mkApp2 (mkConst ``Eq.refl [1]) ty lhs
  })
