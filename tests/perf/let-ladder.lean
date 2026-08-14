/-
`let` bindings alternating with additions.

Structure (for n=3):
  let x₃ : Nat := 0
  x₃ + (let x₂ : Nat := 0
        x₂ + (let x₁ : Nat := 0
              x₁ + (x₃ + (x₂ + (x₁ + 0)))))

Every subterm on the spine has `loose_bvar_range > 0`, and the only
application head is `Nat.add`, so this exercises `let` processing alone,
with no beta reduction. Substituting the value into the body before
checking it traverses O(n) nodes at each of the n bindings, for O(n²) in
time and in allocated nodes; recording the binding and looking it up on
demand costs O(1) per binding.

Both the additions between bindings and the references from the innermost
sum are needed. Adjacent `let`s form a telescope that is collected and
substituted in one traversal, and substitution skips subterms with no
loose bvars in O(1), so a sum naming only the outermost binding leaves the
rest of the spine closed.
-/
import Lean

open Lean Elab Command

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option debug.skipKernelTC true

run_elab do
  let nat := mkConst ``Nat
  let n := 2000
  -- Innermost body: xₙ + (xₙ₋₁ + ... + (x₁ + 0))
  let mut body : Expr := mkNatLit 0
  for i in [:n] do
    body := mkApp2 (mkConst ``Nat.add) (.bvar i) body
  -- Wrap in lets, each body adding its own binding to the next let
  for _ in [:n] do
    body := .letE `x nat (mkNatLit 0)
      (mkApp2 (mkConst ``Nat.add) (.bvar 0) body) false
  Lean.addDecl (.defnDecl {
    name := `kernel_quadratic_let_ladder
    levelParams := []
    type := nat
    value := body
    hints := .regular 0
    safety := .safe
  })
