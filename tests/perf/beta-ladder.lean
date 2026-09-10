/-
A ladder of beta redexes over a body that reads every binder.

Structure (for n=3):
  (fun x₁ => (fun x₂ => (fun x₃ => x₁ + (x₂ + (x₃ + 0))) 0) 0) 0

Each redex binds one variable and applies it to `0`, and the innermost body
sums all n of them. Reducing the term to `0` takes n beta steps, and the body
below binder k still holds n - k redexes when that step happens.
-/
import Lean

open Lean Elab Command

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option debug.skipKernelTC true

run_elab do
  let n := 2000
  let nat := mkConst ``Nat
  let zero := mkRawNatLit 0
  -- x₁ + (x₂ + (… + (xₙ + 0))), under n binders: bvar (n-1) is x₁
  let mut b : Expr := zero
  for i in [:n] do
    b := mkApp2 (mkConst ``Nat.add) (.bvar i) b
  -- wrap innermost first: e := (fun x => e) 0
  let mut e := b
  for _ in [:n] do
    e := .app (.lam `x nat e .default) zero
  Lean.addDecl (.thmDecl {
    name := `beta_ladder
    levelParams := []
    type := mkApp3 (mkConst ``Eq [levelOne]) nat e zero
    value := mkApp2 (mkConst ``Eq.refl [levelOne]) nat zero
  })
