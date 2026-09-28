import Tutorial.Meta
/-!
The test `corner-cases/nested-nonuniform-param`: a nested inductive whose nested occurrence
supplies something other than the parameter itself in the position of the parameter.

    inductive E : W → Type where
      | mk : (w : W) → L (E ⟨false⟩) → E w

The kernel rejects this since leanprover/lean4#14577, so the kernel is handed the well-formed
`E.mk : (w : W) → L (E w) → E w` instead, and in what it generates, the nested occurrence
`L (E w)` is replaced by `L (E ⟨false⟩)`. Under Lean v4.29.1, whose kernel accepted the
declaration, this reproduces its export exactly.
-/
open Lean

inductive W : Type where | mk (p : Bool)
inductive L (α : Type) : Type where | mk

def wFalse : Expr := mkApp (mkConst ``W.mk) (mkConst ``false)

/-- The well-formed variant: `E.mk : (w : W) → L (E w) → E w` -/
def wellFormed : Declaration :=
  .inductDecl [] 1 [{
    name := `E
    type := mkForall `w .default (mkConst ``W) (mkSort 1)
    ctors := [{
      name := `E.mk
      type := mkForall `w .default (mkConst ``W) <|
        mkForall `l .default (mkApp (mkConst ``L) (mkApp (mkConst `E) (mkBVar 0))) <|
          mkApp (mkConst `E) (mkBVar 1) }] }] false

/--
The nested occurrence `L (E w)` becomes `L (E ⟨false⟩)`, wherever it is `L`, or its constructor
`L.mk`, that is applied to `E w`.
-/
def patch : ConstantInfo → ConstantInfo :=
  mapConstInfoExprs <| Expr.replace fun
    | .app (.const n us) (.app (.const `E vs) _) =>
      if n == ``L || n == ``L.mk then
        some (mkApp (.const n us) (mkApp (.const `E vs) wFalse))
      else none
    | _ => none

run_meta addPatchedInductive wellFormed patch
