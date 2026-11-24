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
  let .recInfo rv ← getConstInfo ``T.rec | throwError "T.rec is not a recursor"
  let rules := rv.rules.map fun r => if r.ctor == ``T.mk then { r with nfields := 1 } else r
  let ci : ConstantInfo := .recInfo { rv with rules }
  modifyEnv (replaceConst · ci)

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
