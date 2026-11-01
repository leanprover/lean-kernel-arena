import Lean
open Lean Elab Command

/-
The level equations `imax u v = imax (imax u v) v` and
`imax u v = imax v (imax u v)` hold for every assignment: when `v` is zero
all sides are zero, and otherwise all sides are `max u v`. The official
kernel's level normalization keeps an `imax` whose right operand is neither
zero nor a successor as it is, so it does not identify the two sides.
-/

set_option debug.skipKernelTC true in
run_cmd liftTermElabM do
  let u : Level := .param `u
  let v : Level := .param `v
  addDecl <| .defnDecl {
    name := `imaxAbsorbRight
    levelParams := [`u, `v]
    type := .sort (.succ (.imax (.imax u v) v))
    value := .sort (.imax u v)
    hints := .opaque
    safety := .safe
  }
  addDecl <| .defnDecl {
    name := `imaxAbsorbLeft
    levelParams := [`u, `v]
    type := .sort (.succ (.imax v (.imax u v)))
    value := .sort (.imax u v)
    hints := .opaque
    safety := .safe
  }
