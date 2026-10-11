import Lean
open Lean Meta Elab Tactic

set_option debug.skipKernelTC true in
theorem etaRecStruct : ∀ (a : Bool × Bool → Bool),
  @Prod.rec Bool Bool (fun _ => Bool) (fun b c => a (b, c)) = a :=
  fun a => by
    run_tac closeMainGoalUsing `unchecked fun goalType _ => do
      let some (_, _, rhs) := goalType.eq? | throwError "goal is not an equality"
      mkEqRefl rhs
