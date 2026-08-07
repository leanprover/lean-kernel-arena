/-
A ladder of `let` bindings over a body that reads every binder.

Structure (for n=3):
  let x₁ := 0; let x₂ := 0; let x₃ := 0; x₁ + (x₂ + (x₃ + 0))

Every bound value is `0`, so no value mentions a binder. The body sums all n
bound variables, and the body below binding k still holds n - k bindings when
the kernel reaches that one.
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
  -- x₁ + (x₂ + (… + (xₙ + 0))), under n bindings: bvar (n-1) is x₁
  let mut b : Expr := zero
  for i in [:n] do
    b := mkApp2 (mkConst ``Nat.add) (.bvar i) b
  let mut e := b
  for _ in [:n] do
    e := .letE `x nat zero e false
  Lean.addDecl (.defnDecl {
    name := `let_ladder
    levelParams := []
    type := nat
    value := e
    hints := .regular 0
    safety := .safe
  })
