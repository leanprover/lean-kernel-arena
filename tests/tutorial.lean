-- Tutorial declarations for Lean type theory features
-- Each declaration exercises a specific feature of the type system
import Lean

set_option linter.unusedVariables false

/-- An elaborator that just inserts the term, without regard for the acutal type needed here -/
syntax (name := unchecked) "unchecked" term : term

section
open Lean Meta Elab Term

@[term_elab «unchecked»]
def elabUnchecked : TermElab := fun stx expectedType? => do
  match stx with
  | `(unchecked $t) =>
    let some expectedType := expectedType? |
      tryPostpone
      throwError "invalid 'unchecked', expected type required"
    let e ←  elabTerm t none
    let mvar ← mkFreshExprMVar expectedType MetavarKind.syntheticOpaque
    mvar.mvarId!.assign e
    return mvar
  | _ => throwUnsupportedSyntax

end

-- tut01: Basic definition
def tut01 : Type := Prop

-- tut01bad1: Mismatched types
set_option debug.skipKernelTC true in
def tut01_bad01 : Prop := unchecked Type

-- tut02: Arrow type (function type)
def tut02 : Type := Prop → Prop

-- tut03: Dependent type (forall)
def tut03 : Prop := ∀ (p: Prop), p

-- tut04: Lambda expression
def tut04 : Type → Type → Type := fun x y => x

-- tut05: Lambda reduction (requires two declarations)
def tut05 : tut04 Prop (Prop → Prop) := ∀ p : Prop, p

#print tut05


-- tut06: Universe polymorphism
def tut06f.{u} : Sort u → Sort u → Sort u := fun α β => α
def tut06 : tut06f Prop (Prop → Prop) := ∀ p : Prop, p

-- tut07: Function from Prop to Type (tests imax universe levels)
def tut07a (p : Prop) : Prop := Type → p
def tut07b (α : Type) : Type 1 := Type → α
