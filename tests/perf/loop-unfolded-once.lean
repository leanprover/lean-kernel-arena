/-
A bounded `∀` over a range, written with a helper, against the helper
unfolded once by hand and wrapped in `decide (· = true)`:

    allInK 0 N (fun i => g w i)
      = decide (Nat.allTR (N - 0) (fun k _ => (fun i => g w i) (0 + k)) = true)

with `N = 1000000` and `g`, `w` free. Unfolding `allInK` once gives exactly
the `Nat.allTR` term on the right, and `decide (b = true)` reduces to `b`
through `instDecidableEqBool`; so a few steps make the sides identical. The
loop itself never needs to run, and cannot finish anyway, since every test
`g w i` is stuck on the free `g`. A checker that instead unfolds
`Nat.allTR` and its tail-recursive `loop` lays out the `&&` of a million
stuck tests, one nested level per point.

Distilled from AxiomMath/CFSG (rev 5437cdc),
`CFSG.Sporadic.HNSchreier.Native.Kernel.orbitTreeCheck_certificate`, where a
`change` leaves `allInKernel 0 1140000 (fun i => …)` against
`decide (Nat.allTR (1140000 - 0) (fun k _ => (fun i => …) (0 + k)) = true)`
over free orbit data.

Cheap path: unfold `allInK` (the higher constant) once, then `decide` and
`instDecidableEqBool` on the other side; never `Nat.allTR.loop`.
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

/-- `p i` holds for all `lo ≤ i < hi`, as in CFSG. -/
def allInK (lo hi : Nat) (p : Nat → Bool) : Bool := Nat.allTR (hi - lo) fun k _ => p (lo + k)

theorem loop_unfolded_once (w : Nat) (g : Nat → Nat → Bool) :
    allInK 0 1000000 (fun i => g w i) =
      decide (Nat.allTR (1000000 - 0) (fun k _ => (fun i => g w i) (0 + k)) = true) := by
  unchecked_rfl
