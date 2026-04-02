/-
Stress test for kernel type-checking with DAG sharing + alternating app/binder.

Structure (for n=3):
  wrap2 (fun x₁ : Nat =>
    wrap2 (fun x₂ : Nat =>
      wrap2 (fun x₃ : Nat => x₁ + x₂ + x₃)
            (fun x₃ : Nat => x₁ + x₂ + x₃)
    ) (fun x₂ : Nat =>
      wrap2 (fun x₃ : Nat => x₁ + x₂ + x₃)
            (fun x₃ : Nat => x₁ + x₂ + x₃)
    )
  ) (fun x₁ : Nat =>
    ...same...
  )

Every application head is a constant (`wrap2` or `Nat.add`).
Lambdas appear only as arguments.

`wrap2` takes two identical `(Nat → Nat)` arguments; since both arguments are
the same `Expr` object, the export format records them as a single expression
index (DAG). A checker without an infer cache re-checks shared subterms,
leading to O(2ⁿ) work.

The inner sum references all outer variables, giving each continuation body
`loose_bvar_range > 0`. The kernel calls `infer_lambda` on each continuation
lambda, triggering `instantiate_rev` on the full body. After substitution,
it recursively type-checks the result, which contains the next level's `wrap2`
application. This creates O(n) recursive calls each doing O(n) traversal
= O(n²) total.
-/
import Lean

open Lean Elab Command

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option debug.skipKernelTC true

def wrap2 (f : Nat → Nat) (g : Nat → Nat) : Nat := f 0 + g 0

run_elab do
  let nat := mkConst ``Nat
  let n := 4000
  -- Innermost body: x₁ + x₂ + ... + xₙ
  let mut body : Expr := .bvar (n - 1)
  for i in [1:n] do
    body := mkApp2 (mkConst ``Nat.add) body (.bvar (n - 1 - i))
  -- Wrap in lambdas applied via wrap2, passing each lambda TWICE (DAG).
  -- No beta redexes: every application head is a constant.
  for i in [:n] do
    let lam := Expr.lam (Name.mkSimple s!"x{n - i}") nat body .default
    body := mkApp2 (mkConst ``wrap2) lam lam
  -- body = wrap2 (fun x₁ => ...) (fun x₁ => ...)
  -- where each ... = wrap2 (fun x₂ => ...) (fun x₂ => ...) etc.
  Lean.addDecl (.defnDecl {
    name := `dag_app_binder
    levelParams := []
    type := nat
    value := body
    hints := .regular 0
    safety := .safe
  })
