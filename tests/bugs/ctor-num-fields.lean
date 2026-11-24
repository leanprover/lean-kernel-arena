module

public import Lean
import all Lean.Environment

open Lean Elab Command

structure S where
  f : Bool

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
  let .ctorInfo cv ← getConstInfo ``S.mk | throwError "S.mk is not a constructor"
  let ci : ConstantInfo := .ctorInfo { cv with numFields := 0 }
  modifyEnv (replaceConst · ci)

theorem h : S.mk true = S.mk false := rfl

public theorem bad : False :=
  show if (S.mk false).f then True else False from h ▸ trivial
