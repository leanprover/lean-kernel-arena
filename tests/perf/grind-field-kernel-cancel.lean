module
public import Lean
public meta import Lean
public meta import Lean.Meta.Sym.Arith.ToExpr

/-!
Kernel checking of field certificates that cancel an atom and its inverse across a
polynomial. Each declaration checks a fresh certificate without tactic search or elaboration.

Adapted from `tests/elab_bench/grind_field_kernel_cancel.lean` in the Lean 4 repository, with the
benchmark parameters fixed and deterministic declaration names.
-/

open Lean Meta Grind.CommRing

set_option maxHeartbeats 0

run_meta do
  let n := 64
  let repeats := 20
  for i in [:repeats] do
    let terms := (List.range n).foldl (fun (e : Grind.CommRing.Expr) x =>
      e.add ((Grind.CommRing.Expr.num (Int.ofNat (x + i + 1))).mul (.var (x + 2)))) (.num (-1))
    let a := ((Grind.CommRing.Expr.var 0).pow 2 |>.mul (.var 1)).mul terms
    let b := (Grind.CommRing.Expr.var 0).mul terms
    let invs : InvAtoms := [(1, 0)]
    let cert := mkApp3 (mkConst ``Grind.CommRing.Expr.cancelInvs_cert) (toExpr invs) (toExpr a) (toExpr b)
    let type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) cert (mkConst ``Bool.true)
    let value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    addDecl (.thmDecl { name := .mkSimple s!"cancelInv_{i}", levelParams := [], type, value })
