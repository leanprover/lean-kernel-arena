import Lean
open Lean Elab Command

/- A two-field structure whose sort is the bare `Sort (max u v)` (no `max 1`),
   built directly since the `structure` elaborator forces `max 1 _`.  Projecting
   its first field is valid and the official kernel accepts it. -/
run_cmd liftTermElabM do
  addDecl <| .inductDecl [`u, `v] 2 [{
    name := `MaxPair
    type := .forallE `α (.sort (.param `u))
              (.forallE `β (.sort (.param `v))
                (.sort (.max (.param `u) (.param `v))) .default) .default
    ctors := [{
      name := `MaxPair.mk
      type :=
        .forallE `α (.sort (.param `u))
          (.forallE `β (.sort (.param `v))
            (.forallE `fst (.bvar 1)
              (.forallE `snd (.bvar 1)
                (.app (.app (.const `MaxPair [.param `u, .param `v]) (.bvar 3)) (.bvar 2))
                .default) .default) .implicit) .implicit }] }] false

run_cmd liftTermElabM do
  addDecl <| .defnDecl {
    name := `getFst, levelParams := [`u, `v]
    type := .forallE `α (.sort (.param `u))
              (.forallE `β (.sort (.param `v))
                (.forallE `p (.app (.app (.const `MaxPair [.param `u, .param `v]) (.bvar 1)) (.bvar 0))
                  (.bvar 2) .default) .implicit) .implicit
    value := .lam `α (.sort (.param `u))
              (.lam `β (.sort (.param `v))
                (.lam `p (.app (.app (.const `MaxPair [.param `u, .param `v]) (.bvar 1)) (.bvar 0))
                  (.proj `MaxPair 0 (.bvar 0)) .default) .implicit) .implicit
    hints := .regular 1, safety := .safe }
