import Lean
open Lean Meta Elab Tactic

/-!
Eta for unit-like types beyond structures with no fields. See `eta-unit-like-*.yaml`.
-/

/-- Closes an equality goal with `Eq.refl` of its right-hand side, unchecked. -/
macro "unchecked_rfl" : tactic => `(tactic|
  run_tac closeMainGoalUsing `unchecked fun goalType _ => do
    let some (_, _, rhs) := goalType.eq? | throwError "goal is not an equality"
    mkEqRefl rhs)

structure UnitField where
  u : Unit

structure ProofField : Type where
  p : True

structure Mixed (A B : Type) where
  b : B
  u : Unit
  t : True
  e : A = B

set_option debug.skipKernelTC true in
theorem unitLikePi (α : Type) (p q : α → Unit) : p = q := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem unitLikeStruct (p q : UnitField) : p = q := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem unitLikeProofField (p q : ProofField) : p = q := by unchecked_rfl

set_option debug.skipKernelTC true in
theorem unitLikeNested (p q : Mixed Nat (Bool → UnitField)) : p = q := by unchecked_rfl
