/-
Both sides are the same deeply nested term. Does the checker notice before it
starts unfolding?

From Courant and Leroy, "A Lazy, Concurrent Convertibility Checker",
POPL 2026, section 10, where Rocq spends 2 × 10⁻⁵s and the paper's checker
0.15s, its largest loss to Rocq.
-/
import Lean

open Lean Elab Command

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option debug.skipKernelTC true

inductive N where
  | O : N
  | S : N → N

def f0 (x : N) : N := x
def f1 (x : N) : N := f0 (f0 x)
def f2 (x : N) : N := f1 (f1 x)
def f3 (x : N) : N := f2 (f2 x)
def f4 (x : N) : N := f3 (f3 x)

run_elab do
  let n := 30
  let ty := mkConst ``N
  let mut nest : Expr := mkConst ``N.O
  for _ in [:n] do
    nest := mkApp (mkConst ``f4) nest
  Lean.addDecl (.thmDecl {
    name := `kernel_identical_nesting
    levelParams := []
    type := mkApp3 (mkConst ``Eq [1]) ty nest nest
    value := mkApp2 (mkConst ``Eq.refl [1]) ty nest
  })
