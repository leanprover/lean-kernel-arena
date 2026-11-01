import Lean
open Lean Elab Command

/-
A nested inductive whose two nested occurrences differ only by a redex:

    inductive NestedRedex
    | leaf : NestedRedex
    | a : List ((fun _ : Bool => NestedRedex) true) → NestedRedex
    | b : List NestedRedex → NestedRedex

The kernel finds nested occurrences syntactically, so `List ((fun _ => NestedRedex) true)`
and `List NestedRedex` become two auxiliary types and `NestedRedex.rec` has three
motives. The elaborator never writes such a field, so the block is built
programmatically and added with `addDecl`; the official kernel accepts it.
-/

run_cmd liftTermElabM do
  let T := mkConst `NestedRedex
  let list (e : Expr) := mkApp (mkConst ``List [0]) e
  let redex := mkApp (.lam `h (mkConst ``Bool) T .default) (mkConst ``Bool.true)
  addDecl <| .inductDecl [] 0 [{
    name := `NestedRedex, type := mkSort 1, ctors := [
      { name := `NestedRedex.leaf, type := T },
      { name := `NestedRedex.a, type := .forallE `x (list redex) T .default },
      { name := `NestedRedex.b, type := .forallE `x (list T) T .default }] }] false

/-
`NestedRedex.rec` reduces through auxiliary recursors that the elaborator does not
see in this file, so the theorem is also built as a term. It counts the `a`/`b`
nodes through all three motives:

    NestedRedex.rec (motive_1 motive_2 motive_3 := fun _ => Nat)
      0 (fun _ ih => ih + 1) (fun _ ih => ih + 10)
      0 (fun _ _ ih₁ ih₂ => ih₁ + ih₂) 0 (fun _ _ ih₁ ih₂ => ih₁ + ih₂)
      (NestedRedex.a [NestedRedex.b [NestedRedex.leaf]]) = 11

Binder types are written with `List NestedRedex`, which is definitionally equal
to the redex form the recursor expects.
-/

run_cmd liftTermElabM do
  let T := mkConst `NestedRedex
  let nat := mkConst ``Nat
  let listT := mkApp (mkConst ``List [0]) T
  let lam (n : Name) (ty body : Expr) := Expr.lam n ty body .default
  let add (a b : Expr) := mkApp2 (mkConst ``Nat.add) a b
  let motive (ty : Expr) := lam `t ty nat
  let sum := lam `h T (lam `t listT (lam `i nat (lam `j nat (add (.bvar 1) (.bvar 0)))))
  let args := #[motive T, motive listT, motive listT,
    mkRawNatLit 0,
    lam `x listT (lam `ih nat (add (.bvar 0) (mkRawNatLit 1))),
    lam `x listT (lam `ih nat (add (.bvar 0) (mkRawNatLit 10))),
    mkRawNatLit 0, sum, mkRawNatLit 0, sum]
  let single (e : Expr) := mkApp3 (mkConst ``List.cons [0]) T e (mkApp (mkConst ``List.nil [0]) T)
  let major := mkApp (mkConst `NestedRedex.a)
    (single (mkApp (mkConst `NestedRedex.b) (single (mkConst `NestedRedex.leaf))))
  let lhs := mkAppN (mkConst `NestedRedex.rec [1]) (args.push major)
  addDecl <| .thmDecl {
    name := `nestedRedex, levelParams := []
    type := mkApp3 (mkConst ``Eq [1]) nat lhs (mkRawNatLit 11)
    value := mkApp2 (mkConst ``Eq.refl [1]) nat lhs }
