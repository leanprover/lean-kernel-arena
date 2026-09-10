import Lean
open Lean Elab Command

/-
`MaybeProp` is a structure whose sort is a bare level parameter: a proposition
for `u := 0` and a data type for every other `u`. Lean's `inductive` command
refuses to declare one ("the resulting universe is not `Prop`, but it may be
`Prop` for some parameter values"), but the kernel accepts it, so we hand the
declaration to the kernel directly. The projections built on top of it probe
what a checker does when the fields are taken out again.
-/

def arrow (dom : Expr) (codom : Expr) (n := `x) : Expr :=
  mkForall n BinderInfo.default dom codom

run_cmd liftTermElabM do
  addDecl <| .inductDecl [`u] 0 [
    { name := `MaybeProp
      type := .sort (.param `u)
      ctors := [
        { name := `MaybeProp.mk
          type :=
            arrow (mkConst ``PUnit [.param `u]) (n := `field) <|
            arrow (mkApp3 (mkConst ``Eq [.param `u])
                    (mkConst ``PUnit [.param `u]) (.bvar 0) (.bvar 0)) (n := `proof) <|
            arrow (mkConst ``True) (n := `tail) <|
            mkConst `MaybeProp [.param `u] }] }
    ] false
  addDecl <| .defnDecl {
    name := `projMaybeProp
    levelParams := [`u]
    type := arrow (mkConst `MaybeProp [.param `u]) (mkConst ``PUnit [.param `u])
    value :=
      .lam `x (binderInfo := .default) (mkConst `MaybeProp [.param `u]) <|
      .proj `MaybeProp 0 (.bvar 0)
    hints := .opaque
    safety := .safe
  }
  addDecl <| .defnDecl {
    name := `projMaybePropPast
    levelParams := [`u]
    type := arrow (mkConst `MaybeProp [.param `u]) (mkConst ``True)
    value :=
      .lam `x (binderInfo := .default) (mkConst `MaybeProp [.param `u]) <|
      .proj `MaybeProp 2 (.bvar 0)
    hints := .opaque
    safety := .safe
  }
