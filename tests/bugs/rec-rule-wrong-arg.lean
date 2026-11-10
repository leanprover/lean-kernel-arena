module

public import Lean
import all Lean.Environment

open Lean Elab Command Meta

/-- A structure whose field is read by the primitive projection `W.b`. -/
public structure W where
  b : Bool

-- Lie: the rule of `W.rec` passes `true` to the minor premise instead of the field.
--   W.rec motive mk (W.mk b)  ↦  mk true   (instead of `mk b`)
run_cmd liftTermElabM do
  let .recInfo rv ← getConstInfo ``W.rec | throwError "W.rec is not a recursor"
  let rules ← rv.rules.mapM fun r => do
    let rhs ← lambdaTelescope r.rhs fun xs _ => mkLambdaFVars xs (mkApp xs[1]! (mkConst ``Bool.true))
    return { r with rhs }
  let ci : ConstantInfo := .recInfo { rv with rules }
  modifyEnv fun env => { env with
    base.public.constants.map₁ := env.base.public.constants.map₁.insert ci.name ci
    base.private.constants.map₁ := env.base.private.constants.map₁.insert ci.name ci
    checked := env.checked.map fun e => { e with constants := e.constants.insert ci.name ci }
  }

public noncomputable def IsTrue (b : Bool) : Prop :=
  Bool.rec (motive := fun _ => Prop) False True b

-- `wx` has type `{c // c = false}`, as `(W.mk false).b` is `false`, but with
-- the forged rule it reduces to `⟨true, rfl⟩`
public noncomputable def wx : {c : Bool // c = (W.mk false).b} :=
  W.rec (motive := fun w => {c : Bool // c = w.b}) (fun b => ⟨b, rfl⟩) (W.mk false)

public theorem bad : False :=
  Eq.subst (motive := IsTrue) (wx.2 : true = false) True.intro
