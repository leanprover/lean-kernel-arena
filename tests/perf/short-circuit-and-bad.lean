/-
`short-circuit-and.lean` with `true` in place of `false`:

    (true && eqA 600 (unpack 600 11 p) (unpack 600 11 q)) = (true && Nat.beq p q)

Now `&&` returns its second argument, and the sides differ: `eqA` compares
only the low 600 * 11 bits of `p` and `q`, `Nat.beq` all of them. A sound
checker must reject. This keeps the shortcut honest: unfolding `&&` decides
the sides only when the first argument is `false`.
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

def pg (w m p i : Nat) : Nat := Nat.land (Nat.shiftRight p (w * i)) m

def unpack (n w p : Nat) : Array Nat := Array.ofFn (n := n) fun i => pg w (Nat.shiftLeft 1 w - 1) p i

def eqA (n : Nat) (t u : Array Nat) : Bool := Nat.all n fun i _ => t[i]! == u[i]!

theorem short_circuit_and_bad (p q : Nat) :
    (true && eqA 600 (unpack 600 11 p) (unpack 600 11 q)) = (true && Nat.beq p q) := by
  unchecked_rfl
