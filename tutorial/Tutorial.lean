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

/-- String -/
good_def someString : String := "Hello!"

/-- Non-ASCII String -/
good_def someNonASCIIString : String := "🎉 Goals Accomplished"

/-- Not a String -/
bad_def notAString : String := Prop

/-- Nat -/
good_def importantNumber : Nat := 37

/-- Not a Nat -/
bad_def notANat : Nat := Nat

/-- Lambda expression -/
good_def simpleLambda : Type → Type → Type := fun x y => x

/-- Lambda reduction -/
good_def betaReduction : simpleLambda Prop (Prop → Prop) := ∀ p : Prop, p

/-- Lambda reduction under binder -/
good_def betaReduction2 : ∀ (p : Prop), simpleLambda Prop (Prop → Prop) := fun p => p

/-- The type of a declaration has to be a type, not some other expression -/
bad_def nonTypeType : simpleLambda := unchecked Prop

/-- Some level computation -/
good_def levelComp1 : Type 0 := Sort (imax 1 0)

/-- Some level computation -/
good_def levelComp2 : Type 1 := Sort (max 1 0)

/-- Some level computation -/
good_def levelComp3 : Type 2 := Sort (imax 2 1)

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

/-- Some level computation -/
good_def levelComp4.{u} : Type 0 := Sort (imax u 0)

/-- Some level computation -/
good_def levelComp5.{u} : Type u := Sort (imax u u)

/-- Type inference for forall using imax -/
good_def imax1 : (p : Prop) → Prop := fun p => Type → p

/-- Type inference for forall using imax -/
good_def imax2 : (α : Type) → Type 1 := fun α => Type → α

/-- Type inference of local variables -/
good_def inferVar : ∀ (f : Prop) (g : f), f := fun f g => g

/-- Definitional equality between lambdas -/
good_def defEqLambda : ∀ (f : (Prop → Prop) → Prop) (g : (a : Prop → Prop) → f a), f (fun p => p → p) :=
  fun f g => g (fun p => p → p)

/-! Let's build peano arithmetic -/

def N := ∀ α, (α → α) → (α → α)
def N.zero : N := fun α s z => z
def N.succ : N → N := fun n α s z => s (n α s z)

def N.lit0 := N.zero
def N.lit1 := N.succ N.lit0
def N.lit2 := N.succ N.lit1
def N.lit3 := N.succ N.lit2
def N.lit4 := N.succ N.lit3

def N.add : N → N → N := fun n m α s z => n α s (m α s z)
def N.mul : N → N → N := fun n m α s z => n α (m α s) z


/-- Peano arithmetic: 2 = 2 -/
good_thm peano1.{u} : ∀ (t : N → Prop) (v : (n : N) → t n), t N.lit2.{u} :=
  fun t v => v N.lit2.{u}

/-- Peano arithmetic: 1 + 1 = 2 -/
good_thm peano2.{u} : ∀ (t : N → Prop) (v : (n : N) → t n), t N.lit2.{u} :=
  fun t v => v (N.lit1.add N.lit1)

/-- Peano arithmetic: 2 * 2 = 4 -/
good_thm peano3.{u} : ∀ (t : N → Prop) (v : (n : N) → t n), t N.lit4.{u} :=
  fun t v => v (N.lit2.mul N.lit2)
