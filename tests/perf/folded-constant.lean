/-
One constant application occurring twice in a problem, reduced for the first
subproblem it appears in. Is its folded form still available for the second?

From Courant and Leroy, "A Lazy, Concurrent Convertibility Checker",
POPL 2026, section 10, where Rocq spends 0.078s and the paper's checker
2 × 10⁻⁴s.
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

noncomputable def isZero (m : N) : Bool :=
  N.rec (motive := fun _ => Bool) true (fun _ _ => false) m

noncomputable def tagged (m : N) : N × Bool := (m, isZero m)

run_elab do
  let n := 1000
  let ty := mkConst ``N
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) ty (mkConst ``Bool)
  let num : Nat → Expr := fun k => Id.run do
    let mut e := mkConst ``N.O
    for _ in [:k] do
      e := mkApp (mkConst ``N.S) e
    return e
  let arg := mkApp (mkConst ``count) (num n)
  let lhs := mkApp (mkConst ``tagged) arg
  let rhs := mkApp4 (mkConst ``Prod.mk [0, 0]) ty (mkConst ``Bool) arg (mkConst ``Bool.false)
  Lean.addDecl (.thmDecl {
    name := `kernel_folded_constant
    levelParams := []
    type := mkApp3 (mkConst ``Eq [1]) pairTy lhs rhs
    value := mkApp2 (mkConst ``Eq.refl [1]) pairTy lhs
  })
