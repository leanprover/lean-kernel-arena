/-
An `if` whose condition is a closed `Bool` equality, against the branch it
takes, where that branch is a closed array that is expensive to evaluate:

    (if true = true then piA else tA) = piA

Unfolding `ite` and deciding `true = true` (one step of
`instDecidableEqBool`) reduces the left side to `piA`, and the sides are
identical. But `piA := invCand 300 tA`, the inverse of a permutation table
computed by a `for` loop of `Array.set!`, is defined later and so higher than
`ite`, and a checker that unfolds the higher side first evaluates `piA`
(Θ(n²) list steps) before `ite` ever gets its turn.

Distilled from AxiomMath/CFSG (rev 5437cdc),
`CertificateChecks.Batch27011.optI_eq`, where after `cases o` the true branch
compares `if true = true then piInv else idA 1755` with `piInv`, the inverse
of a 1755-point permutation; there the official kernel (v4.35.0), sokonanoda,
con-ron and con-leche all exceed 8 GB.

The nearest test of Courant and Leroy (POPL 2026) is `unroll-versus-evaluate`,
where one unrolling of one side also gives the other side. There both sides
are applications of recursive functions to numerals, and unfolding the higher
side first happens to be the cheap order. Here the cheap step is on the lower
side, it is `ite` on a `Decidable` instance rather than a recursion, and the
other side is a constant without arguments, so there is nothing to compare
argument by argument.

Cheap path: unfold `ite`, reduce `instDecidableEqBool true true` to
`isTrue _`, take the branch: `piA` against `piA`.
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

/-- The inverse of the permutation table `t` on `n` points, as in CFSG. -/
def invCand (n : Nat) (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate n 0
  for i in [0:n] do
    r := r.set! t[i]! i
  return r

/-- The permutation `i ↦ a * i + 1 (mod n)`, for `a` coprime to `n`. -/
def perm (n a : Nat) : Array Nat := ((List.range n).map fun i => (a * i + 1) % n).toArray

-- Three different tables, so that a checker cannot reuse one evaluation in
-- the next declaration.
def tA : Array Nat := perm 300 7
def tB : Array Nat := perm 300 11
def tC : Array Nat := perm 300 13
def piA : Array Nat := invCand 300 tA
def piB : Array Nat := invCand 300 tB
def piC : Array Nat := invCand 300 tC

theorem ite_taken_branch_1 : (if true = true then piA else tA) = piA := by unchecked_rfl
theorem ite_taken_branch_2 : piB = (if true = true then piB else tB) := by unchecked_rfl
-- The shape of the CFSG proof: a case split on a variable, and the branch
-- for `true` compared with a `Bool.rec` that reduces to `piC` at once.
theorem ite_taken_branch_3 (o : Bool) :
    (if o = true then piC else tC) = Bool.rec (motive := fun _ => Array Nat) tC piC o := by
  cases o <;> unchecked_rfl
