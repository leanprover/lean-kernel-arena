module

public import Lean
import all Lean.Environment

open Lean Elab Command

public inductive C (α : Type 1) where
  | c : α → C α

-- `T` is nested (through `C`); its last field is a predicate on types
public inductive T where
  | base : T
  | mk : C T → (Type → Prop) → T

-- Lie: the `T.mk` rule of `T.rec` has one field (instead of two)
run_cmd liftTermElabM do
  let .recInfo rv ← getConstInfo ``T.rec | throwError "T.rec is not a recursor"
  let rules := rv.rules.map fun r => if r.ctor == ``T.mk then { r with nfields := 1 } else r
  let ci : ConstantInfo := .recInfo { rv with rules }
  modifyEnv fun env => { env with
    base.public.constants.map₁ := env.base.public.constants.map₁.insert ci.name ci
    base.private.constants.map₁ := env.base.private.constants.map₁.insert ci.name ci
    checked := env.checked.map fun e => { e with constants := e.constants.insert ci.name ci }
  }

-- `badProp` is `(fun _ => True) Bool`, i.e. `True`. With the rule's field count
-- trusted, the field `fun _ => True` is passed in place of the first field, and
-- the next argument, `Bool`, takes the place of the second one, which the minor
-- premise returns. So `badProp` reduces to `Bool`.
noncomputable def badProp : Prop :=
  @T.rec (fun _ => Type → Prop) (fun _ => PUnit.{2}) (fun _ => True) (fun _ F _ => F)
    (fun _ _ => PUnit.unit)
    (T.mk (C.c T.base) (fun _ => True)) Bool

theorem propRepresentationFalse (P : Prop) (encode : Bool → P)
    (decode : P → Bool)
    (onFalse : decode (encode false) = false)
    (onTrue : decode (encode true) = true) : False := by
  have same : encode false = encode true := Subsingleton.elim _ _
  exact Bool.noConfusion (onFalse.symm.trans ((congrArg decode same).trans onTrue))

public theorem bad : False :=
  propRepresentationFalse badProp (fun b => b) (fun p => p) rfl rfl
