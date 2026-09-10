import Lean
open Lean Elab Command

/-
The semantic level equation `imax u (v + 1) = max u (v + 1)` follows because
the right operand is nonzero. The official kernel does not normalize this
hand-crafted declaration in that form, while other checkers may do so.
-/

set_option debug.skipKernelTC true in
run_cmd liftTermElabM do
  addDecl <| .defnDecl {
    name := `imaxRightOne
    levelParams := [`u]
    type := .sort (.succ (.max (.param `u) (.succ 0)))
    value := .sort (.imax (.param `u) (.succ 0))
    hints := .opaque
    safety := .safe
  }
  addDecl <| .defnDecl {
    name := `imaxRightSucc
    levelParams := [`u, `v]
    type := .sort (.succ (.max (.param `u) (.succ (.param `v))))
    value := .sort (.imax (.param `u) (.succ (.param `v)))
    hints := .opaque
    safety := .safe
  }
