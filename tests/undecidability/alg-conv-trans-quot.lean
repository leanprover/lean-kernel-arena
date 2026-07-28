import Lean
open Lean Meta Elab Tactic

variable {P : Prop} {r : P → P → Prop}
  {α : Sort 1} (f : P → α) (h : ∀ x y, r x y → f x = f y)
  (q : Quot r) (z : P)

set_option debug.skipKernelTC true in
theorem left : Quot.lift f h q = Quot.lift f h (Quot.mk r z) := by
  run_tac closeMainGoalUsing `bogus fun goalType _ => do
    let some (_, lhs, _) := goalType.eq? | throwError "goal is not an equality"
    mkEqRefl lhs

def lift := @Quot.lift
theorem left' : lift f h q = lift f h (Quot.mk r z) :=
  rfl

theorem right : Quot.lift f h (Quot.mk r z) = f z :=
  rfl

set_option debug.skipKernelTC true in
theorem trans : Quot.lift f h q = f z := by
  run_tac closeMainGoalUsing `bogus fun goalType _ => do
    let some (_, lhs, _) := goalType.eq? | throwError "goal is not an equality"
    mkEqRefl lhs
