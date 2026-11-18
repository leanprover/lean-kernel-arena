/-
`unfold-before-literal.lean` with a wrong right side:

    [slowA, 1].sum = slowA + (2 + 0)

Unfolding the sum leaves `slowA + (1 + 0)` against `slowA + (2 + 0)`. The
arguments `1 + 0` and `2 + 0` differ, but that alone refutes nothing (in
general `a + 1` can equal `b + 2`), so a sound checker has to fall back to
evaluation here and reject. This guards the shortcut: comparing arguments
first may only ever answer "equal".
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

/-- `g n a = a + 2^n`, by 2^n unit steps. -/
noncomputable def g (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun a => a + 1) (fun _ ih a => ih (ih a)) n

noncomputable def slowA : Nat := g 19 0

theorem unfold_before_literal_bad : [slowA, 1].sum = slowA + (2 + 0) := by unchecked_rfl
