import Lean
open Lean Elab Command

/-!
Constant application supplying more universe levels than the referenced
declaration declares.

`mono` has `levelParams: []`, and `tooManyLevels` instantiates it as
`mono.{0}` (one universe level instead of zero). Because `mono` is a
theorem, it is never unfolded during type checking, and `tooManyLevels` is
otherwise well-typed. Neither declaration depends on `Init.Prelude`.
-/

theorem mono : ∀ (p : Prop), p → p := fun _ h => h

run_cmd liftTermElabM do
  let ty := (← getConstInfo ``mono).type
  withOptions (debug.skipKernelTC.set · true) do
    addDecl <| .thmDecl {
      name        := `tooManyLevels
      levelParams := []
      type        := ty
      value       := .const ``mono [.zero]
    }
