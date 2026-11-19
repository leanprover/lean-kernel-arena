/-
The argument twin of `proj-applied-struct.lean`: the same sides, but the
applications get different arguments, and the checker must reject:

    (gC slowA c).fn x = (gC' slowA c).fn (x + 1)

Unfolding `gC'` makes the heads identical, and only the arguments `x` and
`x + 1` differ. A checker that takes equal heads as equal without comparing
the arguments accepts this. The existing `proj-applied-struct-bad.lean`
(`= x + c`) checks a different error: a right side that is equal only
propositionally. A sound checker may evaluate `slowA` on the way.
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

-- Three closed values of 2^19 steps each, with disjoint intermediate
-- values, so that a checker cannot reuse one evaluation in the next
-- declaration.
noncomputable def slowA : Nat := g 19 0
noncomputable def slowB : Nat := g 19 1048576
noncomputable def slowC : Nat := g 19 2097152

structure S where
  fn : Nat → Nat
  tag : Nat

/-- Its constructor is reached only after deciding the closed `s = c`. -/
noncomputable def gC (s c : Nat) : S :=
  if s = c then ⟨fun x => x + c, 0⟩ else ⟨fun x => x + c, 1⟩

noncomputable def gC' (s c : Nat) : S := gC s c

theorem proj_applied_struct_arg_bad_1 (c x : Nat) : (gC slowA c).fn x = (gC' slowA c).fn (x + 1) := by
  unchecked_rfl
theorem proj_applied_struct_arg_bad_2 (c x : Nat) : (gC' slowB c).fn (x + 1) = (gC slowB c).fn x := by
  unchecked_rfl
theorem proj_applied_struct_arg_bad_3 (c x : Nat) : (gC slowC c).fn (x + 1) = (gC' slowC c).fn (x + 2) := by
  unchecked_rfl
