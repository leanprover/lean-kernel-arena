import Lean
open Lean Elab Command

-- Inject `strLitUtf8Bad : "é" = String.ofList [Char.ofNat 0xC3, Char.ofNat 0xA9]`
-- with proof `Eq.refl "é"`. The right-hand side lists the two raw UTF-8 bytes
-- of `"é"` (`0xC3`, `0xA9`) rather than its single Unicode codepoint (`0xE9`).
-- `debug.skipKernelTC` lets `addDecl` write the ill-typed theorem to the export.

run_cmd liftTermElabM do
  let lhs := mkStrLit "é"
  let c1 := mkApp (mkConst ``Char.ofNat) (mkNatLit 0xC3)
  let c2 := mkApp (mkConst ``Char.ofNat) (mkNatLit 0xA9)
  let nil := mkApp (mkConst ``List.nil [0]) (mkConst ``Char)
  let cons2 := mkApp3 (mkConst ``List.cons [0]) (mkConst ``Char) c2 nil
  let cons1 := mkApp3 (mkConst ``List.cons [0]) (mkConst ``Char) c1 cons2
  let rhs := mkApp (mkConst ``String.ofList) cons1
  let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``String) lhs rhs
  let val := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``String) lhs
  let decl : Declaration := .thmDecl {
    name := `strLitUtf8Bad
    levelParams := []
    type := ty
    value := val
  }
  withOptions (debug.skipKernelTC.set · true) do
    addDecl decl
