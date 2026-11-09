import Lean
open Lean Elab Command

-- A := ∀ P : Prop, P,  B := ∀ P : Prop, P → P
-- theorem openDagContextLeakFalse : ∀ P : Prop, P :=
--   (fun f : A → A =>
--     (fun (g : A → A) (h : B → A) => h (fun P p => p))
--       (fun x : A => f x) (fun y : B => f y))
--   (fun z : A => z)
run_cmd liftTermElabM do
  let prop := mkSort .zero
  let A := mkForall `P .default prop (.bvar 0)
  let B := mkForall `P .default prop (mkForall `p .default (.bvar 0) (.bvar 1))
  let AA := mkForall `x .default A A
  let BA := mkForall `y .default B A
  let idB := mkLambda `P .default prop (mkLambda `p .default (.bvar 0) (.bvar 0))
  let sink := mkLambda `g .default AA (mkLambda `h .default BA (mkApp (.bvar 0) idB))
  -- `f x` and `f y`: the same expression `#1 #0`, under binders of different types
  let fx := mkApp (.bvar 1) (.bvar 0)
  let body := mkApp2 sink (mkLambda `x .default A fx) (mkLambda `y .default B fx)
  let value := mkApp (mkLambda `f .default AA body) (mkLambda `z .default A (.bvar 0))
  let decl : Declaration := .thmDecl {
      name := `openDagContextLeakFalse
      levelParams := []
      type := A
      value
    }
  withOptions (debug.skipKernelTC.set · true) do
    addDecl decl
