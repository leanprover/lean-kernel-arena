import Lean
open Lean Elab Command

/-
A closed proof of `False`, with no axioms, that a kernel accepts iff it tests whether a
sort is `Prop` only syntactically (the bug fixed in leanprover/lean4#14613).

`ImaxProp : Sort (imax 1 0)` is a proposition, since `imax 1 0` normalizes to `0`. The
exploit uses two definitionally equal spellings of that type, each hitting the buggy
syntactic `is_prop` check on the side it needs:

* Proof irrelevance is stated through `ImaxAsProp : Prop := ImaxProp`, whose type is the
  *literal* `Sort 0`. Even the buggy kernel recognizes this as a proposition, so it equates
  `imaxLeft := ImaxProp.mk false` and `imaxRight := ImaxProp.mk true`.

* The data projection `imaxProjBool : ImaxProp → Bool` is stated on `ImaxProp` directly,
  whose type is the *literal* `Sort (imax 1 0)`. The buggy kernel does not recognize this
  as a proposition and so wrongly permits projecting the `Bool` field out of a proof.

Combining them, `imaxProjBool imaxLeft` and `imaxProjBool imaxRight` reduce to `false` and
`true`, yet are equal by congruence on the proof-irrelevance equation — hence `False`.

The companion `ImaxPropDummy` in the same mutual block is needed for the `Bool` field to be
accepted: the kernel checks constructor field universes against the resulting level of the
*first* inductive of the block, and does not recognize the unnormalized `Sort (imax 1 0)`
as a `Prop` (whose fields may come from any universe).
-/

run_cmd liftTermElabM do
  addDecl <| .inductDecl [] 0 [
    { name := `ImaxPropDummy
      type := .sort 0
      ctors := [{ name := `ImaxPropDummy.intro, type := .const `ImaxPropDummy [] }] },
    { name := `ImaxProp
      type := .sort (.imax 1 0)
      ctors := [{ name := `ImaxProp.mk
                  type := .forallE `value (.const ``Bool []) (.const `ImaxProp []) .default }] }
  ] false

/-- A `Prop`-ascribed alias: its type is the literal `Sort 0`. -/
def ImaxAsProp : Prop := ImaxProp

def imaxLeft  : ImaxAsProp := ImaxProp.mk false
def imaxRight : ImaxAsProp := ImaxProp.mk true

/-- Proof irrelevance via the alias: accepted by any kernel, buggy or fixed. -/
theorem imaxIrrel : imaxLeft = imaxRight := rfl

/-
The data projection out of the proposition, which a sound kernel must reject. Added under
`debug.skipKernelTC` so this file builds regardless of whether the local toolchain has the
fix; the checker under test replays it and must reject it.
-/
run_cmd liftTermElabM do
  withOptions (debug.skipKernelTC.set · true) do
    addDecl <| .defnDecl {
      name := `imaxProjBool
      levelParams := []
      type := .forallE `p (.const `ImaxProp []) (.const ``Bool []) .default
      value := .lam `p (.const `ImaxProp []) (.proj `ImaxProp 0 (.bvar 0)) .default
      hints := .abbrev
      safety := .safe }

theorem badFalse : False :=
  (imaxIrrel ▸ (trivial : cond (imaxProjBool imaxLeft) False True)
    : cond (imaxProjBool imaxRight) False True)
