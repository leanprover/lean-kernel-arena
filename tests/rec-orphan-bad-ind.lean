module
import all Lean.Environment
import Lean

public section
open Lean Elab Command
set_option Elab.async false

run_cmd do
  let rogue : RecursorVal := {
    name := `rogue
    levelParams := []
    type := mkConst ``False
    all := [`Foo]
    numParams := 0
    numIndices := 0
    numMotives := 0
    numMinors := 0
    rules := []
    k := false
    isUnsafe := false
  }
  modifyEnv fun env => env.lakeAdd (.recInfo rogue)
  liftCoreM <| addDecl <| .thmDecl {
    name := `inconsistent
    levelParams := []
    type := mkConst ``False
    value := mkConst `rogue
  }
