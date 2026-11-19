/-
A positive companion of `unfold-before-literal.lean` and its `-bad` twin:

    [slowA + 1, 1].sum = slowA + (2 + 0)

This is true: both sides evaluate to `slowA + 2`. But after unfolding the
sum, the left side is `(slowA + 1) + (1 + 0)`, and its arguments differ from
those of `slowA + (2 + 0)`. A checker that compares arguments first sees
that comparison fail, and must then keep going (evaluate, or otherwise
decide the sides) instead of rejecting. Different arguments refute nothing.
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

/-- `g n a = a + 2^n`, by 2^n unit steps. The recursor is applied directly;
no `Nat` literal shortcut applies to the recursion itself. -/
noncomputable def g (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun a => a + 1) (fun _ ih a => ih (ih a)) n

-- Three closed summands of 2^19 steps each, with disjoint intermediate
-- values, so that a checker cannot reuse one evaluation in the next
-- declaration.
noncomputable def slowA : Nat := g 19 0
noncomputable def slowB : Nat := g 19 1048576
noncomputable def slowC : Nat := g 19 2097152

theorem unfold_before_literal_fallback_1 : [slowA + 1, 1].sum = slowA + (2 + 0) := by unchecked_rfl
theorem unfold_before_literal_fallback_2 : slowB + (2 + 0) = [slowB + 1, 1].sum := by unchecked_rfl
theorem unfold_before_literal_fallback_3 : [2, slowC + 1, 1].sum = 2 + (slowC + (2 + 0)) := by unchecked_rfl
