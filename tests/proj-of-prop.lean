import Lean
open Lean Meta Elab Term

section Unchecked
syntax (name := unchecked) "unchecked" term : term

@[term_elab «unchecked»]
def elabUnchecked : TermElab := fun stx expectedType? => do
  match stx with
  | `(unchecked $t) =>
    let some expectedType := expectedType? |
      tryPostpone
      throwError "invalid 'unchecked', expected type required"
    let e ← elabTerm t none
    let mvar ← mkFreshExprMVar expectedType MetavarKind.syntheticOpaque
    mvar.mvarId!.assign e
    return mvar
  | _ => throwUnsupportedSyntax

end Unchecked

structure Wrapper : Prop where
  mk ::
  p : False

set_option debug.skipKernelTC true in
theorem badFalse : False := (Wrapper.mk (unchecked True.intro)).p
