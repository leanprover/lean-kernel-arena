module

public import Lean
import all Lean.Environment

open Lean Elab Command

public inductive MyBool | false | true

public noncomputable def disc : MyBool → Prop := fun b => MyBool.rec True False b

/-- Replaces the constant `ci.name` by `ci`, for the kernel as well as for the elaborator. -/
def replaceConst (env : Environment) (ci : ConstantInfo) : Environment :=
  let update (ac : AsyncConsts) : AsyncConsts :=
    match ac.map.find? ci.name with
    | some a =>
      let a := { a with constInfo := .ofConstantInfo ci }
      { ac with map := ac.map.insert ci.name a
                normalizedTrie := ac.normalizedTrie.insert (privateToUserName ci.name) a }
    | none => ac
  { env with
    asyncConstsMap := env.asyncConstsMap.map update
    checked := env.checked.map fun e => { e with constants := e.constants.insert ci.name ci } }

run_cmd liftTermElabM do
  let .recInfo rv ← getConstInfo ``MyBool.rec | throwError "MyBool.rec is not a recursor"
  let ci : ConstantInfo := .recInfo { rv with k := true }
  modifyEnv (replaceConst · ci)

public theorem bad : disc MyBool.true := True.intro
