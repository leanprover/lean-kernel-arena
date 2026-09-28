import Tutorial.Meta
/-!
The test `bugs/nested-unused-param`: a nested inductive whose nested occurrence has a parameter
that is not type-correct, and does not occur in the auxiliary type of the nested occurrence.

    inductive E : W → Type where
      | mk : (w : W) → L (E w) (C.0 (C.0 w)) → E w

Here `C.0 (C.0 w)` projects out of `w : W` as if it were a `C`. The kernel rejects this since
leanprover/lean4#14577, so the kernel is handed a well-formed variant with `placeholder w` in place
of that projection, and in what it generates, `placeholder w` is replaced by it. Under Lean
v4.29.1, whose kernel accepted the declaration, this reproduces its export exactly.

A hash collision between `pad false 78670` and `pad true 24083` then disguises the bogus projection
enough to make `E` yield a proof of `False`, `boom`.
-/
open Lean

inductive P : Prop where | mk (b : Bool)
structure C where b : Bool
inductive W : Type where | mk (p : P)
inductive L (α : Type) (b : Bool) : Type where | mk
inductive T : Bool → Prop where | mk : T true

opaque placeholder : W → Bool

def pad (e : Expr) (n : Nat) : Expr :=
  mkApp (mkLambda `x .default (mkConst ``Nat) e) (.lit (.natVal n))

/-- The well-formed variant: `E.mk : (w : W) → L (E w) (placeholder w) → E w` -/
def wellFormed : Declaration :=
  let w := mkBVar 0
  .inductDecl [] 1 [{
    name := `E
    type := mkForall `w .default (mkConst ``W) (mkSort 1)
    ctors := [{
      name := `E.mk
      type := mkForall `w .default (mkConst ``W) <|
        mkForall `l .default
          (mkApp2 (mkConst ``L) (mkApp (mkConst `E) w) (mkApp (mkConst ``placeholder) w)) <|
          mkApp (mkConst `E) (mkBVar 1) }] }] false

/-- `placeholder w` becomes `C.0 (C.0 w)` -/
def patch : ConstantInfo → ConstantInfo :=
  mapConstInfoExprs <| Expr.replace fun
    | .app (.const ``placeholder _) w => some (mkProj ``C 0 (mkProj ``C 0 w))
    | _ => none

run_meta addPatchedInductive wellFormed patch

open Elab Command in
elab "mkbug" : command => do
  -- Skip the kernel type-check of the declarations using `E`, which is not well-formed
  let add (d : Declaration) : CommandElabM Unit :=
    liftCoreM <| withOptions (debug.skipKernelTC.set · true) <| addDecl d
  let f := pad (mkConst ``Bool.false) 78670
  let t := pad (mkConst ``Bool.true) 24083
  unless f.hash == t.hash && f.approxDepth == t.approxDepth do
    throwError "hash collision failed"
  let fw := mkApp (mkConst ``W.mk) (mkApp (mkConst ``P.mk) f)
  let tw := mkApp (mkConst ``W.mk) (mkApp (mkConst ``P.mk) t)
  let Et := mkApp (mkConst `E) tw
  let l := mkApp2 (mkConst ``L.mk) Et (mkConst ``Bool.true)
  add <| .defnDecl {
    name := `e, levelParams := [], type := Et,
    value := mkApp2 (mkConst `E.mk) tw l,
    hints := .abbrev, safety := .safe }
  add <| .defnDecl {
    name := `good', levelParams := [],
    type := mkApp (mkConst ``T) t, value := mkConst ``T.mk,
    hints := .abbrev, safety := .safe }
  let Ef := mkApp (mkConst `E) fw
  let Et := mkApp (mkConst `E) tw
  let a := mkApp2 (mkConst `E.mk) fw (mkProj `E 0 (mkConst `e))
  let tl := mkApp2 (mkConst ``L.mk) Et (mkConst ``Bool.true)
  let b := mkApp2 (mkConst `E.mk) tw tl
  let cT := mkApp2 (mkConst ``L) Et t
  let c := mkApp (mkLambda `l .default cT (mkConst ``Unit.unit)) tl
  let fl := mkApp2 (mkConst ``L.mk) Ef f
  let d := mkApp2 (mkConst `E.mk) fw fl
  let v := Expr.letE `a Ef a
    (.letE `b Et b
      (.letE `c (mkConst ``Unit) c
        (.letE `d Ef d (mkConst `good') true) true) true) true
  add <| .thmDecl {
    name := `bad, levelParams := [],
    type := mkApp (mkConst ``T) f, value := v }

mkbug
theorem boom : False := nomatch (bad : T false)
