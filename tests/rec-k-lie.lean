module

public import Lean
import all Lean.Environment

open Lean Elab Command

public inductive MyBool | false | true

public noncomputable def disc : MyBool → Prop := fun b => MyBool.rec True False b

run_cmd liftTermElabM do
  let .recInfo rv ← getConstInfo ``MyBool.rec | throwError "MyBool.rec is not a recursor"
  let ci : ConstantInfo := .recInfo { rv with k := true }
  modifyEnv fun env => { env with
    base.public.constants.map₁ := env.base.public.constants.map₁.insert ci.name ci
    base.private.constants.map₁ := env.base.private.constants.map₁.insert ci.name ci
    checked := env.checked.map fun e => { e with constants := e.constants.insert ci.name ci }
  }

public theorem bad : disc MyBool.true := True.intro
