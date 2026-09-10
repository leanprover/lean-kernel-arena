import Lean
open Lean Meta Elab Tactic

def step (x : Nat) (ih : (y : Nat) → y < x → Bool) : Bool :=
  match x with
  | 0 => true
  | k + 1 => ih k (Nat.lt_succ_self k)

def f (n : Nat) (a : Acc (· < ·) n) : Bool :=
  Acc.rec (fun x _ => step x) a

variable (a : Acc (· < ·) 1)

/-! Failure of algorithmic conversion transitivity -/

theorem left :
    f 1 a =
    f 1 (Acc.intro 1 fun _ => Acc.inv a) :=
  rfl

theorem right :
    f 1 (Acc.intro 1 fun _ => Acc.inv a) =
    f 0 (Acc.inv a (Nat.lt_succ_self 0)) :=
  rfl

set_option debug.skipKernelTC true in
theorem trans :
    f 1 a =
    f 0 (Acc.inv a (Nat.lt_succ_self 0)) := by
  run_tac closeMainGoalUsing `bogus fun goalType _ => do
    let some (_, lhs, _) := goalType.eq? | throwError "goal is not an equality"
    mkEqRefl lhs

/-! Failure of subject reduction -/

def redex (D : Bool → Type)
    (k : D (f 0 (Acc.inv a (Nat.lt_succ_self 0))) → Unit) (x0 : D (f 1 a)) : Unit :=
  (fun y : D (f 1 (Acc.intro 1 fun _ => Acc.inv a)) => k y) x0

set_option debug.skipKernelTC true in
def reduct (D : Bool → Type)
    (k : D (f 0 (Acc.inv a (Nat.lt_succ_self 0))) → Unit) (x0 : D (f 1 a)) : Unit := by
  run_tac closeMainGoalUsing `bogus fun _ _ => do
    let lctx ← getLCtx
    let some kd := lctx.findFromUserName? `k | throwError "no k"
    let some xd := lctx.findFromUserName? `x0 | throwError "no x0"
    return mkApp kd.toExpr xd.toExpr
