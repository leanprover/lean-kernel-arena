module

public import Lean
import all Lean.Environment

open Lean Elab Command Meta

/-- A structure whose field is read by the primitive projection `W.b`. -/
public structure W where
  b : Bool

-- Lie: the rule of `W.rec` passes `true` to the minor premise instead of the field.
--   W.rec motive mk (W.mk b)  ↦  mk true   (instead of `mk b`)
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
  let .recInfo rv ← getConstInfo ``W.rec | throwError "W.rec is not a recursor"
  let rules ← rv.rules.mapM fun r => do
    let rhs ← lambdaTelescope r.rhs fun xs _ => mkLambdaFVars xs (mkApp xs[1]! (mkConst ``Bool.true))
    return { r with rhs }
  let ci : ConstantInfo := .recInfo { rv with rules }
  modifyEnv (replaceConst · ci)

public noncomputable def IsTrue (b : Bool) : Prop :=
  Bool.rec (motive := fun _ => Prop) False True b

-- `wx` has type `{c // c = false}`, as `(W.mk false).b` is `false`, but with
-- the forged rule it reduces to `⟨true, rfl⟩`
public noncomputable def wx : {c : Bool // c = (W.mk false).b} :=
  W.rec (motive := fun w => {c : Bool // c = w.b}) (fun b => ⟨b, rfl⟩) (W.mk false)

public theorem bad : False :=
  Eq.subst (motive := IsTrue) (wx.2 : true = false) True.intro
