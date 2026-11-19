/-
A function-valued field of a structure, applied to an argument, against the
same field of an alias of that structure:

    (gC slowA c).fn x = (gC' slowA c).fn x

where `gC' s c := gC s c`, and `gC s c` is `if s = c then ⟨…, 0⟩ else ⟨…, 1⟩`.
Reducing `gC slowA c` to a constructor first decides `slowA = c`, which
evaluates the closed `slowA` (2^19 unit steps), and then is stuck on the
free `c`. So the weak head normal form of the structure is expensive and
useless, while unfolding `gC'` makes the sides identical.

Distilled from AxiomMath/CFSG (rev 69cb972f587a),
`CertificateChecks.KernelSporSch.RuE64.invol_eq`, where the structure is a
group element built from closed certificate data; the official kernel
(v4.35.0) used more than 24 GB there and had not finished after 1.5 hours.

The nearest tests are `proj-cheap-struct` and `proj-stuck-struct`, which
compare projections of an expensive or stuck structure. There the
projections stand alone, and the reference kernel compares two projections
of the same field by their structures, lazily. Here each projection is the
head of an application (`.fn x`), so that rule does not see it: the
reference kernel reaches `whnf_core` with full reduction of projected
structures before it would compare the applications argument by argument.
The test of Courant and Leroy (POPL 2026) closest in spirit is
`args-before-unfold`; their checker has no primitive projections.

Cheap path: unfold `gC'` (or compare the applications' heads `(gC …).fn`
and `(gC' …).fn` lazily), never the structure itself.
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

theorem proj_applied_struct_1 (c x : Nat) : (gC slowA c).fn x = (gC' slowA c).fn x := by
  unchecked_rfl
theorem proj_applied_struct_2 (c x : Nat) : (gC' slowB c).fn x = (gC slowB c).fn x := by
  unchecked_rfl
theorem proj_applied_struct_3 (c x : Nat) : (gC slowC c).fn (x + 1) = (gC' slowC c).fn (x + 1) := by
  unchecked_rfl
