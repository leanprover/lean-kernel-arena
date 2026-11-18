/-
`proj-applied-struct.lean` with a right side that holds propositionally but
not definitionally:

    (gC slowA c).fn x = x + c

Both branches of `gC slowA c` have `fn = fun x => x + c`, but the structure
is stuck on `slowA = c` for a free `c`, so no reduction reaches either
branch. A sound checker must reject; it may evaluate `slowA` on the way.
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

structure S where
  fn : Nat → Nat
  tag : Nat

noncomputable def gC (s c : Nat) : S :=
  if s = c then ⟨fun x => x + c, 0⟩ else ⟨fun x => x + c, 1⟩

theorem proj_applied_struct_bad (c x : Nat) : (gC slowA c).fn x = x + c := by unchecked_rfl
