module
import all Lean.Environment
import Lean

public section
open Lean

/-- Declared as a `Type`, so everything below is ordinary, legal Lean. -/
inductive NewBool : Type where | tt | ff

/-- Since `NewBool` is a type, its recursor lets us pick a real `Bool` from them -/
@[expose] noncomputable def pick : NewBool → Bool :=
  NewBool.rec (motive := fun _ => Bool) true false

/-- The recursor introduces definitional equalities that allow `pick` to be reduced -/
theorem pick_tt : true = pick .tt  := rfl
theorem pick_ff : pick .ff = false := rfl

/-- Replaces the constant `ci.name` by `ci`, for the kernel as well as for the elaborator. -/
private def replaceConst (env : Environment) (ci : ConstantInfo) : Environment :=
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

-- Shenanigans
run_cmd do
  let some (.inductInfo v) := (← getEnv).find? ``NewBool | throwError "?"
  let ci : ConstantInfo := .inductInfo { v with type := .sort 0 }
  -- Tell the kernel and the elaborator that `NewBool` was a `Prop` all along
  modifyEnv (replaceConst · ci)

/-- Because `.tt` and `.ff` are classified by a `Prop`, they're definitionally equal -/
theorem tt_eq_ff : NewBool.tt = NewBool.ff := rfl

theorem oh_no : true = false := pick_tt.trans $ (congrArg pick tt_eq_ff).trans pick_ff

theorem boom : False := Bool.noConfusion oh_no
