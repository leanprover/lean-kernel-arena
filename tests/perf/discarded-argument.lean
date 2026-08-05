/-
Mechanism: comparing the arguments of two applications of the same constant
when that constant discards its argument.

Test case from Courant and Leroy, "A Lazy, Concurrent Convertibility Checker"
(POPL 2026), section 10, where Rocq spends 0.14s and the paper's checker
spends 5 × 10⁻⁶s.
-/
import Lean

open Lean Elab Command

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option debug.skipKernelTC true

inductive N where
  | O : N
  | S : N → N

noncomputable def N.add (a b : N) : N :=
  N.rec (motive := fun _ => N) b (fun _ ih => N.S ih) a

noncomputable def count (m : N) : N :=
  N.rec (motive := fun _ => N) N.O (fun _ ih => N.add ih (N.S N.O)) m

def dropArg (_ : N) : N := N.O

run_elab do
  let n := 200
  let ty := mkConst ``N
  let num : Nat → Expr := fun k => Id.run do
    let mut e := mkConst ``N.O
    for _ in [:k] do
      e := mkApp (mkConst ``N.S) e
    return e
  let lhs := mkApp (mkConst ``dropArg) (mkApp (mkConst ``count) (num n))
  let rhs := mkApp (mkConst ``dropArg) (mkApp (mkConst ``count) (num (n + 1)))
  Lean.addDecl (.thmDecl {
    name := `kernel_discarded_argument
    levelParams := []
    type := mkApp3 (mkConst ``Eq [1]) ty lhs rhs
    value := mkApp2 (mkConst ``Eq.refl [1]) ty lhs
  })
