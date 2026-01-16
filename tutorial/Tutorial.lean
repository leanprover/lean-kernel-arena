-- Tutorial declarations for Lean type theory features
-- Each declaration exercises a specific feature of the type system

import Tutorial.Meta
set_option linter.unusedVariables false

/-- Basic definition -/
good_def basicDef : Type := Prop

/-- Mismatched types -/
bad_def badDef : Prop := unchecked Type

/-- Arrow type (function type) -/
good_def arrowType : Type := Prop → Prop

/-- Dependent type (forall) -/
good_def dependentType : Prop := ∀ (p: Prop), p

/-- Lambda expression -/
good_def simpleLambda : Type → Type → Type := fun x y => x

/-- Lambda reduction (requires two declarations) -/
good_def betaReduction : simpleLambda Prop (Prop → Prop) := ∀ p : Prop, p

def levelParamF.{u} : Sort u → Sort u → Sort u := fun α β => α
/-- Level parameters -/
good_def levelParams : levelParamF Prop (Prop → Prop) := ∀ p : Prop, p

/-- Duplicate universe paramers -/
bad_decl .defnDecl {
  name := `tut06_bad01
  levelParams := [`u, `u]
  type := .sort 1
  value := .sort 0
  hints := .opaque
  safety := .safe
}

/-- Tests imax type inference -/
good_def imax1 : (p : Prop) → Prop := fun p => Type → p

/-- Tests imax type inference -/
good_def imax2 : (α : Type) → Type 1 := fun α => Type → α
