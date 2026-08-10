/-
Two proofs of one proposition, one a constructor and one a computation that
evaluates a numeral before reaching that constructor, compared as the sides
of an equality type. `Eq` gives the comparison a rigid head, so nothing can
be unfolded instead: the checker settles the proofs by their type, or it
evaluates one of them. Does it fire proof irrelevance before it evaluates?

Lean's definitional proof irrelevance has no counterpart in the checker of
Courant and Leroy, so this test is not from their suite.
-/
import Lean

open Lean Elab Command

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option debug.skipKernelTC true

inductive N where
  | O : N
  | S : N → N

-- The definitions below apply the recursor directly. Structural recursion
-- would compile through `brecOn`, whose course-of-values table dominates every
-- cost these tests are about: measured on `discarded-argument`, the `brecOn`
-- form costs 3074M instructions against 17M, and reorders the checkers under
-- test.
noncomputable def N.add (a b : N) : N :=
  N.rec (motive := fun _ => N) b (fun _ ih => N.S ih) a

noncomputable def count (m : N) : N :=
  N.rec (motive := fun _ => N) N.O (fun _ ih => N.add ih (N.S N.O)) m

-- a proof of `True` computed by recursion over its argument: forcing it to a
-- constructor evaluates the numeral
noncomputable def slowTriv (m : N) : True :=
  N.rec (motive := fun _ => True) True.intro (fun _ ih => ih) m

run_elab do
  let n := 200
  let true_ := mkConst ``True
  let num : Nat → Expr := fun k => Id.run do
    let mut e := mkConst ``N.O
    for _ in [:k] do
      e := mkApp (mkConst ``N.S) e
    return e
  let p1 := mkApp (mkConst ``slowTriv) (mkApp (mkConst ``count) (num n))
  let p2 := mkConst ``True.intro
  Lean.addDecl (.thmDecl {
    name := `kernel_irrelevance_before_evaluation
    levelParams := []
    type := mkApp3 (mkConst ``Eq [0]) true_ p1 p2
    value := mkApp2 (mkConst ``Eq.refl [0]) true_ p1
  })
