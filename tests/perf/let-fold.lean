/-
A `let` bound to a closed `Nat` that is expensive to evaluate, whose variable
then meets the kernel's `Nat` literal folding. Does the checker keep the
binding as a variable, or substitute its value and evaluate it?

Structure:
  let d : Nat := bits n 0
  @id (d + 0 = Nat.add d 0) (Eq.refl (d + 0))

The `id` makes the comparison of `d + 0` with `Nat.add d 0` happen while
checking the body of the `let`. The official kernel's lazy delta reduction
folds `Nat` arithmetic only on terms without free variables; with `d` a
let-bound free variable it unfolds `HAdd.hAdd` instead, and never evaluates
`bits n 0`. Substituting the value first makes both sides closed, and the fold
evaluates `bits n 0`, which makes 2^n recursive calls.

Found by con-leche on openai/math, in
`OAI.SquareDifference.source_ordered_contraction`, whose
`let d := Fintype.card TupleVertex` led to an enumeration of permutations.
-/
import Lean

open Lean Elab Command

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option debug.skipKernelTC true

-- `bits n k` makes 2^n recursive calls before it is a literal. It applies the
-- recursor directly: structural recursion would compile through `brecOn`.
noncomputable def bits (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun k => k % 2)
    (fun _ ih k => ih (2 * k) + ih (2 * k + 1)) n

run_elab do
  let n := 16
  let nat := mkConst ``Nat
  let zero := mkNatLit 0
  let instAdd := mkApp2 (mkConst ``instHAdd [0]) nat (mkConst ``instAddNat)
  let lhs : Expr → Expr := fun d =>
    mkAppN (mkConst ``HAdd.hAdd [0, 0, 0]) #[nat, nat, nat, instAdd, d, zero]
  let rhs : Expr → Expr := fun d => mkApp2 (mkConst ``Nat.add) d zero
  let eqTy : Expr → Expr := fun d => mkApp3 (mkConst ``Eq [1]) nat (lhs d) (rhs d)
  let val := mkApp2 (mkConst ``bits) (mkNatLit n) zero
  let body := mkApp2 (mkConst ``id [0]) (eqTy (.bvar 0))
    (mkApp2 (mkConst ``Eq.refl [1]) nat (lhs (.bvar 0)))
  Lean.addDecl (.thmDecl {
    name := `kernel_let_fold
    levelParams := []
    type := eqTy val
    value := .letE `d nat val body false
  })
