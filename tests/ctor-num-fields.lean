module

public import Lean
import all Lean.Environment

open Lean Elab Command

structure S where
  f : Bool

run_cmd liftTermElabM do
  let .ctorInfo cv ← getConstInfo ``S.mk | throwError "S.mk is not a constructor"
  let ci : ConstantInfo := .ctorInfo { cv with numFields := 0 }
  modifyEnv fun env => { env with
    base.public.constants.map₁ := env.base.public.constants.map₁.insert ci.name ci
    base.private.constants.map₁ := env.base.private.constants.map₁.insert ci.name ci
    checked := env.checked.map fun e => { e with constants := e.constants.insert ci.name ci }
  }

theorem h : S.mk true = S.mk false := rfl

public theorem bad : False :=
  show if (S.mk false).f then True else False from h ▸ trivial
