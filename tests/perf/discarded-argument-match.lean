/-
`discarded-argument.lean` with `count` and `N.add` written by structural
recursion instead of by applying `N.rec`. The convertibility problem is the
same; the definitions it unfolds now go through `brecOn`, which is what the
equation compiler produces for every recursive Lean function.

From Courant and Leroy, "A Lazy, Concurrent Convertibility Checker",
POPL 2026, section 10, where Rocq spends 0.14s and the paper's checker
5 × 10⁻⁶s.
-/
import Lean

open Lean Elab Command

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option debug.skipKernelTC true

inductive N where
  | O : N
  | S : N → N

def N.add (a b : N) : N :=
  match a with
  | .O => b
  | .S a' => .S (N.add a' b)

def count (m : N) : N :=
  match m with
  | .O => .O
  | .S m' => N.add (count m') (.S .O)

def dropArg (_ : N) : N := N.O

run_elab do
  let n := 200
  let ty := mkConst ``N
  let num : Nat → Expr := fun k => Id.run do
    let mut e := mkConst ``N.O
    for _ in [:k] do
      e := mkApp (mkConst ``N.S) e
    return e
  let lhs := mkApp (mkConst ``dropArg) (mkApp (mkConst ``count) (num n))
  let rhs := mkApp (mkConst ``dropArg) (mkApp (mkConst ``count) (num (n + 1)))
  Lean.addDecl (.thmDecl {
    name := `kernel_discarded_argument_match
    levelParams := []
    type := mkApp3 (mkConst ``Eq [1]) ty lhs rhs
    value := mkApp2 (mkConst ``Eq.refl [1]) ty lhs
  })
