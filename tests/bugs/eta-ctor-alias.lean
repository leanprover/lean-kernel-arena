import Lean
open Lean Meta Elab Tactic

structure Box where
  val : Bool

@[reducible] def BoxFn := Bool → Box

set_option linter.defProp false
set_option debug.skipKernelTC true in
theorem etaCtorAlias : ∀ f : BoxFn, f = Box.mk :=
  fun f => by
    run_tac closeMainGoalUsing `unchecked fun goalType _ => do
      let some (_, lhs, _) := goalType.eq? | throwError "goal is not an equality"
      mkEqRefl lhs
