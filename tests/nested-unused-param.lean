import Lean
open Lean Elab Command

inductive P : Prop where | mk (b : Bool)
structure C where b : Bool
inductive W : Type where | mk (p : P)
inductive L (α : Type) (b : Bool) : Type where | mk
inductive T : Bool → Prop where | mk : T true

def pad (e : Expr) (n : Nat) : Expr :=
  mkApp (mkLambda `x .default (mkConst ``Nat) e) (.lit (.natVal n))

meta def build : CommandElabM Unit := do
  -- Skip the kernel type-check so that test generation still produces the
  -- malformed declarations (and hence the export) even on a toolchain whose
  -- kernel correctly rejects them. The point of the test is to feed the export
  -- to the arena checkers, not to rely on this kernel accepting it.
  let add (d : Declaration) : CommandElabM Unit :=
    liftCoreM <| withOptions (debug.skipKernelTC.set · true) <| addDecl d
  let f := pad (mkConst ``Bool.false) 78670
  let t := pad (mkConst ``Bool.true) 24083
  unless f.hash == t.hash && f.approxDepth == t.approxDepth do
    throwError "hash collision failed"
  let fw := mkApp (mkConst ``W.mk) (mkApp (mkConst ``P.mk) f)
  let tw := mkApp (mkConst ``W.mk) (mkApp (mkConst ``P.mk) t)
  let w := mkBVar 0
  let Ew := mkApp (mkConst `E) w
  let b := mkProj ``C 0 (mkProj ``C 0 w)
  let l := mkApp2 (mkConst ``L) Ew b
  let Et := mkForall `w .default (mkConst ``W) (mkSort 1)
  let ct := mkForall `w .default (mkConst ``W) <|
    mkForall `l .default l (mkApp (mkConst `E) (mkBVar 1))
  add <| .inductDecl [] 1 [{
    name := `E, type := Et, ctors := [{ name := `E.mk, type := ct }] }] false
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

elab "mkbug" : command => build
mkbug
theorem boom : False := nomatch (bad : T false)
