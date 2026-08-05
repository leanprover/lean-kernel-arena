/-
Mechanism: beta reduction under binders, on two terms whose normal forms are
long and carry no repeated subterms.

Test case from the `conv_eval` benchmark of András Kovács' smalltt, whose
`NatConv` entry compares Church numerals of a given value.
-/
import Lean

open Lean Elab Command

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option debug.skipKernelTC true

def CNat : Type 1 := ∀ (X : Type), (X → X) → X → X

def cmul (a b : CNat) : CNat := fun X s => a X (b X s)

run_elab do
  let n := 120
  let ty := mkConst ``CNat
  -- `fun (X : Type) (s : X → X) (z : X) => s (s (... z))`, k applications of `s`
  let cnum : Nat → Expr := fun k => Id.run do
    let mut body : Expr := .bvar 0
    for _ in [:k] do
      body := mkApp (.bvar 1) body
    let tyX : Expr := .sort (.succ .zero)
    let tyS : Expr := .forallE `x (.bvar 0) (.bvar 1) .default
    return .lam `X tyX (.lam `s tyS (.lam `z (.bvar 1) body .default) .default) .default
  let lhs := mkApp2 (mkConst ``cmul) (cnum n) (cnum (n + 1))
  let rhs := mkApp2 (mkConst ``cmul) (cnum (n + 1)) (cnum n)
  Lean.addDecl (.thmDecl {
    name := `kernel_church_numerals
    levelParams := []
    type := mkApp3 (mkConst ``Eq [2]) ty lhs rhs
    value := mkApp2 (mkConst ``Eq.refl [2]) ty lhs
  })
