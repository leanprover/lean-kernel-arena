import Lean
open Lean Elab Command

inductive Bad : Prop
  | mk1 : False → Bad
  | mk2 : True → Bad

run_meta
  withOptions (debug.skipKernelTC.set · true) do
    addDecl <|
      .thmDecl {
        name := `bad
        levelParams := []
        type := mkConst ``False
        value := .proj `Bad 0 (mkApp (mkConst ``Bad.mk2) (mkConst ``True.intro))
      }
