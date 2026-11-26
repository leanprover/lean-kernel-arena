module

public import Lean
import all Lean.Environment

open Lean Elab Command Meta

/-!
Proof of `False` from an ordinary safe definition named `Tree.rec_1` hijacking
the auxiliary recursor of a nested inductive type `Tree`.

`Tree : Type` has constructors `leaf : Tree` and `node : Box Tree → Tree`
(`numNested := 1`). Its recursor `Tree.rec`'s rule for `node` calls the
auxiliary recursor `Tree.rec_1.{u}`. We replace `Tree.rec_1` in the
environment with an ordinary safe definition taking 6 arguments and returning
`Pair.mk (fun _ => True) False True.intro` (with `levelParams := [u]`), so the
export emits `def Tree.rec_1.{u}` before `Tree` and omits `Tree.rec_1` from
`Tree`'s `recs` list.

A checker that does not reject a nested inductive when a generated auxiliary
recursor name (`Tree.rec_1`) is missing from the block and occupied by a
non-recursor declaration admits `Tree.rec` with its rule pointing at the
hijacked `def Tree.rec_1`. Projecting `.2` from `Tree.rec` applied to
`Tree.node (Box.mk Tree.leaf)` with motive `Pair (fun p => p)` then yields
`inconsistent : False` without axioms.
-/

public structure Pair (f : Prop → Prop) : Type 1 where
  mk ::
  p : Prop
  h : f p

public structure Box (α : Type) : Type where
  mk ::
  val : α

public inductive Tree : Type where
  | leaf : Tree
  | node : Box Tree → Tree

/-- Replace a constant in the environment without checking it. -/
meta def forge (ci : ConstantInfo) : CommandElabM Unit :=
  modifyEnv fun env => { env with
    base.public.constants.map₁ := env.base.public.constants.map₁.insert ci.name ci
    base.private.constants.map₁ := env.base.private.constants.map₁.insert ci.name ci
    checked := env.checked.map fun e => { e with constants := e.constants.insert ci.name ci }
  }

/-
Replace the kernel-generated auxiliary recursor `Tree.rec_1` with an ordinary
safe definition `Tree.rec_1.{u}` returning `Pair.mk (fun _ => True) False True.intro`.
-/
run_cmd do
  let defn ← liftTermElabM do
    let trueConst := mkConst ``True
    let falseConst := mkConst ``False
    let pairConst := mkConst ``Pair
    let pairMkConst := mkConst ``Pair.mk
    let constTrue : Expr := .lam `p (.sort 0) trueConst .default
    let retTy := mkApp pairConst constTrue
    let retVal := mkApp3 pairMkConst constTrue falseConst (mkConst ``True.intro)
    let rec mkArrows : Nat → Expr → Expr
      | 0, body => body
      | n + 1, body => .forallE `x trueConst (mkArrows n body) .default
    let rec mkLams : Nat → Expr → Expr
      | 0, body => body
      | n + 1, body => .lam `x trueConst (mkLams n body) .default
    return ConstantInfo.defnInfo {
      name        := ``Tree.rec_1
      levelParams := [`u]
      type        := mkArrows 6 retTy
      value       := mkLams 6 retVal
      hints       := .regular 1
      safety      := .safe
    }
  forge defn

/-
Inject `inconsistent : False` projecting field 1 (`h`) from
`Tree.rec.{2} (fun _ => Pair (fun p => p)) (fun _ => Pair (fun p => p))
  (Pair.mk (fun p => p) True True.intro) (fun _ ih => ih) (fun _ ih => ih)
  (Tree.node (Box.mk Tree.leaf))`.
Its static type is `Pair (fun p => p)`, so field 1 has static type `t.0`;
through the hijacked `Tree.rec_1`, `t` reduces to `Pair.mk (fun _ => True) False True.intro`,
so `t.0` reduces to `False`.
-/
run_cmd do
  let decl ← liftTermElabM do
    let idProp : Expr := .lam `p (.sort 0) (.bvar 0) .default
    let pairId := mkApp (mkConst ``Pair) idProp
    let treeTy := mkConst ``Tree
    let boxTreeTy := mkApp (mkConst ``Box) treeTy
    let m1 : Expr := .lam `t treeTy pairId .default
    let m2 : Expr := .lam `b boxTreeTy pairId .default
    let hLeaf := mkApp3 (mkConst ``Pair.mk) idProp (mkConst ``True) (mkConst ``True.intro)
    let hNode : Expr := .lam `b boxTreeTy (.lam `ih pairId (.bvar 0) .default) .default
    let hBox : Expr := .lam `v treeTy (.lam `ih pairId (.bvar 0) .default) .default
    let major := mkApp (mkConst ``Tree.node) (mkApp2 (mkConst ``Box.mk) treeTy (mkConst ``Tree.leaf))
    let recApp := mkAppN (mkConst ``Tree.rec [.succ (.succ .zero)]) #[m1, m2, hLeaf, hNode, hBox, major]
    let proof : Expr := .proj ``Pair 1 recApp
    return ConstantInfo.thmInfo {
      name        := `inconsistent
      levelParams := []
      type        := mkConst ``False
      value       := proof
    }
  forge decl
