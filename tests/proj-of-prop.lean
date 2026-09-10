import Lean
open Lean Elab Command

structure Wrapper : Prop where
  mk ::
  p : False

/-
The value we want to add is

    Expr.proj `Wrapper 0 (Wrapper.mk True.intro)

which has a `True.intro : True` sitting in the `Wrapper.mk` slot that
expects a `False`. The elaborator never emits a raw `Expr.proj` from
`(...).p` syntax (it desugars to the projection *function* `Wrapper.p`,
which would get caught at `infer_app`), so we construct the declaration
programmatically and hand it to `addDecl` under `debug.skipKernelTC`.
-/

run_cmd liftTermElabM do
  let badValue : Expr :=
    .proj `Wrapper 0 (mkApp (mkConst ``Wrapper.mk) (mkConst ``True.intro))
  let decl : Declaration := .thmDecl {
    name        := `badFalse
    levelParams := []
    type        := mkConst ``False
    value       := badValue
  }
  withOptions (debug.skipKernelTC.set · true) do
    addDecl decl
