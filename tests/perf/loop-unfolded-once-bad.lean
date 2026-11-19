/-
`loop-unfolded-once.lean` with a different test on the right:

    allInK 0 N (fun i => g w i)
      = decide (Nat.allTR (N - 0) (fun k _ => (fun i => g w (i + 1)) (0 + k)) = true)

The right side tests the points `1 … N` instead of `0 … N - 1`. With `g`
free the sides are not equal, and a sound checker must reject. After the same
few steps as in `loop-unfolded-once`, the loop bodies differ in an argument
under a binder, which refutes nothing by itself; the checker must not accept.

`N = 300` here rather than a million: refuting this by unfolding the loop is
far from linear for the official kernel (v4.36.0), about 7 s at `N = 300`
and more than 5 minutes at `N = 1000`.
-/
import Lean

open Lean Elab Tactic

set_option debug.skipKernelTC true

/-- Closes `lhs = rhs` with `Eq.refl rhs`, without a defeq check by the
elaborator: only the checker under test compares the sides. -/
macro "unchecked_rfl" : tactic => `(tactic|
  run_tac closeMainGoalUsing `unchecked fun goalType _ => do
    let some (_, _, rhs) := goalType.eq? | throwError "goal is not an equality"
    Meta.mkEqRefl rhs)

def allInK (lo hi : Nat) (p : Nat → Bool) : Bool := Nat.allTR (hi - lo) fun k _ => p (lo + k)

theorem loop_unfolded_once_bad (w : Nat) (g : Nat → Nat → Bool) :
    allInK 0 300 (fun i => g w i) =
      decide (Nat.allTR (300 - 0) (fun k _ => (fun i => g w (i + 1)) (0 + k)) = true) := by
  unchecked_rfl
