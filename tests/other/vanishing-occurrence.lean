import Lean
open Lean Elab Command

/-
Two inductive types whose constructor field mentions the type being declared
only inside a redex that reduces it away:

    inductive VanishPos
    | leaf : VanishPos
    | node : (fun _ : Type => Nat) VanishPos → VanishPos

    inductive VanishNeg
    | leaf : VanishNeg
    | node : (fun _ : Type => Nat) (VanishNeg → Nat) → VanishNeg

The kernel's positivity check puts the field in weak head normal form before
looking for occurrences, finds `Nat`, and accepts both; the second one even
though the unreduced field has an occurrence in a negative position. The
elaborator never writes such a field, so the blocks are built programmatically.
-/

run_cmd liftTermElabM do
  let kNat (e : Expr) := mkApp (.lam `X (mkSort 1) (mkConst ``Nat) .default) e
  for (n, field) in [(`VanishPos, fun t => kNat t),
                     (`VanishNeg, fun t => kNat (.forallE `y t (mkConst ``Nat) .default))] do
    let T := mkConst n
    addDecl <| .inductDecl [] 0 [{
      name := n, type := mkSort 1, ctors := [
        { name := n ++ `leaf, type := T },
        { name := n ++ `node, type := .forallE `x (field T) T .default }] }] false
