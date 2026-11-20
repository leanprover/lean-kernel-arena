/-
`ite-taken-branch.lean` with the branch the condition does not take:

    (if false = true then piA else tA) = piA

The left side reduces to `tA`, a permutation table, and `piA` is its inverse,
a different array. A sound checker must decide the condition, not assume the
`then` branch because it matches the other side, and reject; refuting
`tA = piA` evaluates `piA` on the way.
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

def invCand (n : Nat) (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate n 0
  for i in [0:n] do
    r := r.set! t[i]! i
  return r

def perm (n a : Nat) : Array Nat := ((List.range n).map fun i => (a * i + 1) % n).toArray

def tA : Array Nat := perm 300 7
def piA : Array Nat := invCand 300 tA

theorem ite_taken_branch_bad : (if false = true then piA else tA) = piA := by unchecked_rfl
