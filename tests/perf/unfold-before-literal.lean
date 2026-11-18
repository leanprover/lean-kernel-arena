/-
A sum of a list against the same sum written out, where one summand is a
closed `Nat` that is expensive to evaluate. Does the checker unfold the sum,
or does `Nat` literal arithmetic evaluate the summand first?

    [slowA, 1].sum = slowA + (1 + 0)

`List.sum` is `foldr (· + ·) 0`, so three unfoldings turn the left side into
the right side, and the sides then agree argument by argument. But both sides
are closed `Nat` terms headed by `+`, and a checker that tries its `Nat`
literal extension before unfolding evaluates the arguments to literals:
`slowA` costs 2^19 unit steps, one evaluation per side or one per declaration.

Distilled from AxiomMath/CFSG (rev 69cb972f587a),
`CertificateChecks.KernelJ2Cover.totalC`, a sum of closed certificate
counts against its value written as a sum; the official kernel (v4.35.0)
needs more than 100 GB there.

The nearest test of Courant and Leroy (POPL 2026) is `args-before-unfold`,
which also has a cheap symbolic path and an expensive evaluation. There the
heads are an ordinary constant, and checkers try arguments before unfolding
it. Here the head is `Nat.add` on closed arguments, which the reference
kernel hands to its literal arithmetic before any unfolding, so the shortcut
that every checker takes is the expensive one.

Cheap path: unfold `List.sum`/`foldr` lazily until both sides are
`slowA + (1 + 0)`, then compare arguments.
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

theorem unfold_before_literal_1 : [slowA, 1].sum = slowA + (1 + 0) := by unchecked_rfl
theorem unfold_before_literal_2 : slowB + (1 + 0) = [slowB, 1].sum := by unchecked_rfl
theorem unfold_before_literal_3 : [2, slowC, 1].sum = 2 + (slowC + (1 + 0)) := by unchecked_rfl
