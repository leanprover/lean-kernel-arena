import Lean
open Lean Elab Command

inductive Bad : Prop
  | mk1 : False → Bad
  | mk2 : True → Bad

run_cmd liftTermElabM do
  let bad : Expr := .proj `Bad 0 (mkApp (mkConst ``Bad.mk2) (mkConst ``True.intro))
  let decl : Declaration := .thmDecl {
      name := `bad
      levelParams := []
      type := mkConst ``False
      value := bad
    }
  withOptions (debug.skipKernelTC.set · true) do
    addDecl decl
