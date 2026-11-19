/-
`false && a` against `false && b`, where `a` and `b` are open terms that are
not definitionally equal and expensive to compare:

    (false && eqA 600 (unpack 600 11 p) (unpack 600 11 q)) = (false && Nat.beq p q)

`&&` is `Bool.and`, a `match` on its first argument, so unfolding it reduces
both sides to `false` at once. But the heads agree, and a checker that
compares the arguments of a shared head before unfolding it compares `a` with
`b`. With `p` and `q` free that comparison cannot succeed: `a` compares
600 points of two permutations unpacked from `p` and `q`, `b` compares the
packed numbers, and reducing a point `Nat.land (Nat.shiftRight p (11 * i)) m`
peels the shift one bit at a time down to the free `p`.

Distilled from AxiomMath/CFSG (rev 5437cdc), `CertificateChecks.Batch27581.p2`,
where after `cases hl : nLetters e.2.2` the branch for `false` is closed by
`rfl` between a check on permutations as arrays and the same check on
permutations packed into `Nat`s (1755 points of 11 bits, with a free `e`);
there the official kernel (v4.35.0) needs 441 s, sokonanoda and Gruszka more
than 8 GB.

The nearest test of Courant and Leroy (POPL 2026) is `discarded-argument`,
where unfolding the shared head also discards differing arguments. There the
head ignores its argument and the arguments are closed numerals that are
cheap to tell apart. Here the head discards its second argument only because
the first one is `false`, and the second arguments are open, so comparing
them can neither evaluate them nor refute them quickly.

Cheap path: unfold `Bool.and` on both sides (`false` against `false`), never
the second arguments.
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

/-- Point `i` of a permutation packed `w` bits per point into `p`, as in CFSG. -/
def pg (w m p i : Nat) : Nat := Nat.land (Nat.shiftRight p (w * i)) m

/-- The permutation packed into `p`, as an array of `n` points. -/
def unpack (n w p : Nat) : Array Nat := Array.ofFn (n := n) fun i => pg w (Nat.shiftLeft 1 w - 1) p i

/-- Equality of two permutations on `n` points, as arrays. -/
def eqA (n : Nat) (t u : Array Nat) : Bool := Nat.all n fun i _ => t[i]! == u[i]!

theorem short_circuit_and_1 (p q : Nat) :
    (false && eqA 600 (unpack 600 11 p) (unpack 600 11 q)) = (false && Nat.beq p q) := by
  unchecked_rfl
theorem short_circuit_and_2 (p q : Nat) :
    (false && Nat.beq p q) = (false && eqA 600 (unpack 600 12 p) (unpack 600 12 q)) := by
  unchecked_rfl
-- The shape of the CFSG goal: a conjunction whose first conjunct is `false`
-- after a case split, nested in a second one.
theorem short_circuit_and_3 (p q : Nat) :
    ((false && eqA 600 (unpack 600 13 p) (unpack 600 13 q)) && Nat.beq q p) =
      ((false && Nat.beq p q) && eqA 600 (unpack 600 13 q) (unpack 600 13 p)) := by
  unchecked_rfl
