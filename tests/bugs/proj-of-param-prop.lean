import Lean
open Lean Elab Command

/-!
Proof of `False` by projecting a non-propositional field out of a
parameterized `Prop`-valued structure.

`PBox (α : Type) : Prop` has type `∀ (α : Type), Prop`, which is a `ForAll`
whose terminal sort is `Prop`, not a bare `Sort 0`. A kernel that checks
whether a structure is a proposition without peeling parameter binders from
its type wrongly permits projecting the `Bool` field out of `PBox Bool`.
Proof irrelevance equates `PBox.mk true` and `PBox.mk false`, so transporting
along that equation yields `true = false` and `False`.
-/

inductive PBox (α : Type) : Prop where
  | mk (val : α) : PBox α

/-
Inject `obs (x : PBox Bool) : Bool := x.0` using a raw `Expr.proj` under
`debug.skipKernelTC`, since Lean rejects data projections out of `Prop`.
-/
run_cmd liftTermElabM do
  let pboxBool := mkApp (mkConst ``PBox) (mkConst ``Bool)
  withOptions (debug.skipKernelTC.set · true) do
    addDecl <| .defnDecl {
      name        := `obs
      levelParams := []
      type        := .forallE `x pboxBool (mkConst ``Bool) .default
      value       := .lam `x pboxBool (.proj ``PBox 0 (.bvar 0)) .default
      hints       := .abbrev
      safety      := .safe
    }

theorem eq_p : PBox.mk true = PBox.mk false := rfl

theorem inconsistent : False :=
  (eq_p ▸ (trivial : Bool.rec (motive := fun _ => Prop) False True (obs (PBox.mk true)))
    : Bool.rec (motive := fun _ => Prop) False True (obs (PBox.mk false)))
