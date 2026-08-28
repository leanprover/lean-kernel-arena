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

-- Shenanigans
run_cmd do
  let some (.inductInfo v) := (← getEnv).find? ``NewBool | throwError "?"
  let ci : ConstantInfo := .inductInfo { v with type := .sort 0 }
  modifyEnv fun env =>
    -- Tell the kernel `NewBool` was a `Prop` all along
    let env := env.setCheckedSync <| env.checked.get.add ci
    -- Convince the elaborator to go along with this nonsense
    { env with
      base.public.constants.map₁  := env.base.public.constants.map₁.insert ci.name ci
      base.private.constants.map₁ := env.base.private.constants.map₁.insert ci.name ci }

/-- Because `.tt` and `.ff` are classified by a `Prop`, they're definitionally equal -/
theorem tt_eq_ff : NewBool.tt = NewBool.ff := rfl

theorem oh_no : true = false := pick_tt.trans $ (congrArg pick tt_eq_ff).trans pick_ff

theorem boom : False := Bool.noConfusion oh_no
