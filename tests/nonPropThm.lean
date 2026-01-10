import Lean
open Lean Meta Elab Tactic
set_option debug.skipKernelTC true
run_meta
  let decl : TheoremVal := {
    name := `thm
    levelParams := [`u]
    type := mkConst ``PUnit [mkLevelParam `u]
    value := mkConst ``PUnit.unit [mkLevelParam `u] }
  -- First a def, to see if if the rest of the declaration is fine
  addDecl <| .defnDecl { decl with name := `def, hints := .opaque, safety := .safe }
  addDecl (.thmDecl decl)
