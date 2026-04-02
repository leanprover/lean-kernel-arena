/-
Stress test for cascading substitution overhead in kernel `let` processing.

N nested `let` bindings inside a lambda, where each value references the
outer lambda parameter `a` and the previous binding:

  fun (a : Nat → Nat) =>
    let f₁ := fun x => a x
    let f₂ := fun x => a (f₁ x)
    let f₃ := fun x => a (f₂ x)
    let f₄ := fun x => a (f₃ x)
    f₄ 0

The kernel processes each `let` by substituting the value into the body
(`inst(body, [val])`). Each value has a free bvar (references `a`), so
substitution under the remaining inner `let` binders creates shifted copies
of the value.

**Locally-nameless kernel**: substitutes fvars that need no shifting → O(N) total.

**De Bruijn kernel with deferred shifts**: creates `Shift(val, offset)` wrappers
that accumulate. Step k must traverse through O(k) wrappers from previous
substitutions → O(N²) total.

  Step 1: inst substitutes f₁ into the rest. val₁ = `fun x => a x` has a
          free bvar (a). Under inner let binders (offset>0), inst creates
          `Shift(val₁, offset)`.
  Step 2: inst substitutes f₂ (whose expanded value now contains the
          Shift-wrapped val₁). inst must traverse through the wrapper.
  Step k: must traverse through O(k) accumulated Shift layers.
-/
import Lean

open Lean Elab Command

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option debug.skipKernelTC true

run_elab do
  let nat := mkConst ``Nat
  let natToNat := Expr.forallE `_ nat nat .default

  let n := 1000

  -- Build from inside out.
  -- Innermost: fₙ applied to 0
  -- bvar(0) = fₙ at the innermost scope
  let zero := mkNatLit 0
  let mut body : Expr := mkApp (.bvar 0) zero  -- fₙ 0

  -- Wrap with N let bindings, from fₙ (innermost) to f₁ (outermost)
  for i in [:n] do
    -- We're building: let f_{n-i} := val in body
    -- In the current scope (inside the outer lambda for `a`):
    --   bvar(0) = f_{n-i-1} (the previous let, or `a` if i = n-1)
    --   The val will be: fun x => a (f_{n-i-1} x)
    --
    -- In val's scope: `a` is at some bvar index, f_{n-i-1} is at another.
    -- Since we're inside (i) let bindings + the outer lambda:
    --   f_{k-1} = bvar(0), ..., f₁ = bvar(k-2), a = bvar(k-1)  where k = n-i
    -- Inside val's lambda (adding one more binder):
    --   x = bvar(0), f_{k-1} = bvar(1), ..., a = bvar(k)

    let val := if i == n - 1 then
      -- f₁ = fun x => a x
      -- In val's scope: a = bvar(0) (we're in the lambda body, no lets yet)
      -- Inside the lambda: x = bvar(0), a = bvar(1)
      Expr.lam `x nat (mkApp (.bvar 1) (.bvar 0)) .default
    else
      -- f_k = fun x => a (f_{k-1} x)  where k = n - i
      -- In val's scope: f_{k-1} = bvar(0), ..., f₁ = bvar(k-2), a = bvar(k-1)
      -- Inside the lambda: x = bvar(0), f_{k-1} = bvar(1), ..., a = bvar(k)
      let k := n - i
      let aRef := Expr.bvar k
      let prevRef := Expr.bvar 1
      let xRef := Expr.bvar 0
      Expr.lam `x nat (mkApp aRef (mkApp prevRef xRef)) .default

    body := Expr.letE (Name.mkSimple s!"f{n - i}") natToNat val body false

  -- Wrap in the outer lambda: fun (a : Nat → Nat) => body
  body := Expr.lam `a natToNat body .default

  -- The whole thing has type (Nat → Nat) → Nat
  let ty := Expr.forallE `_ natToNat nat .default

  Lean.addDecl (.defnDecl {
    name := `shift_cascade
    levelParams := []
    type := ty
    value := body
    hints := .regular 0
    safety := .safe
  })
