import Lean
open Lean Elab Command

/-
A declaration that names one of the kernel's `_nested` auxiliary types, which a
correct kernel must reject — the check added in leanprover/lean4#14616. This is
*not* a proof of `False`: the declaration is perfectly well-typed, so a kernel
lacking the guard accepts it. It only exercises the reserved-prefix check, the
same thing the upstream test `tests/elab/kernelNestedAuxName.lean` verifies.

The kernel creates auxiliary types under the `_nested` prefix while eliminating
nested inductives; they exist only in a temporary environment. A user
declaration that names such a type is reaching into that machinery, where
`restore_nested` can later give a stored constructor a type it was never checked
against (in a different universe), which is unsound. The kernel therefore
forbids the reserved prefix in `add_inductive` outright, for both `Expr.const`
names and `Expr.proj` structure names.

Here `_nested.KNHost_1` is an ordinary `Prop`-valued constant (a plain `def`, so
it is accepted by every kernel — the guard lives only in `add_inductive`). The
inductive `KNAux : Prop` names it in a constructor field; the field type is just
`True`, so the whole declaration is well-typed. A guarded kernel rejects `KNAux`
for using the reserved `_nested` prefix; an unguarded kernel accepts it.
-/

-- An ordinary constant that merely lives under the reserved `_nested` prefix.
run_cmd liftTermElabM do
  addDecl <| .defnDecl {
    name := `_nested.KNHost_1
    levelParams := []
    type := .sort .zero
    value := .const ``True []
    hints := .abbrev
    safety := .safe }

-- `KNAux : Prop` whose constructor field names `_nested.KNHost_1`. Added under
-- `debug.skipKernelTC` so this file builds regardless of whether the local
-- toolchain already has the #14616 guard; the checker under test replays the
-- export and must reject it.
run_cmd liftTermElabM do
  withOptions (debug.skipKernelTC.set · true) do
    addDecl <| .inductDecl [] 0 [
      { name := `KNAux
        type := .sort .zero
        ctors := [{ name := `KNAux.mk
                    type := .forallE `x (.const `_nested.KNHost_1 [])
                              (.const `KNAux []) .default }] }] false
