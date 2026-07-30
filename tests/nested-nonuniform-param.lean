import Lean
open Lean Elab Command

inductive W : Type where | mk (p : Bool)
inductive L (α : Type) : Type where | mk

meta def build : CommandElabM Unit := do
  -- Skip the kernel type-check so test generation still produces the export
  -- even on a toolchain whose kernel rejects the malformed declaration.
  let add (d : Declaration) : CommandElabM Unit :=
    liftCoreM <| withOptions (debug.skipKernelTC.set · true) <| addDecl d
  let Ef := mkApp (mkConst `E) (mkApp (mkConst ``W.mk) (mkConst ``false))
  let l := mkApp (mkConst ``L) Ef
  let Et := mkForall `w .default (mkConst ``W) (mkSort 1)
  -- E.mk : (w : W) → L (E ⟨false⟩) → E w
  -- The nested occurrence `L (E ⟨false⟩)` uses the constant `⟨false⟩` where the
  -- parameter `w` should be; `⟨false⟩` is type-correct but is not the parameter.
  let ct := mkForall `w .default (mkConst ``W) <|
    mkForall `l .default l (mkApp (mkConst `E) (mkBVar 1))
  add <| .inductDecl [] 1 [{
    name := `E, type := Et, ctors := [{ name := `E.mk, type := ct }] }] false

elab "mkbug" : command => build
mkbug
