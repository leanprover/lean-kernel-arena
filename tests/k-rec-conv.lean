import Lean
open Lean Meta Elab Tactic

def T : Type := (y : Nat) → @Eq (Nat → Nat) (fun x => x) (fun _ => y) → Nat

def t2 : T := fun _ _ => 0
def t1 : T := fun y h =>
  @Eq.rec (Nat → Nat) (fun x => x) (fun _ _ => Nat) 0 (fun _ => y) h

set_option debug.skipKernelTC true
theorem bad : @Eq T t1 t2 := by
  run_tac closeMainGoalUsing `bogus fun _goal _ =>
    return mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``T) (mkConst ``t1)
