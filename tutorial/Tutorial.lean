import Tutorial.Meta
set_option linter.unusedVariables false
/-!
Tutorial declarations for Lean type theory features.
Each declaration exercises a specific feature of the type system.

A rendered view of the exported test cases is available at
https://arena.lean-lang.org/tutorial/
-/

axiom aDepProp : Type → Prop
axiom mkADepProp : ∀ t, aDepProp t
axiom aType : Type
axiom aProp : Prop


/-- Basic definition -/
good_def basicDef : Type := Prop

/-- Mismatched types -/
bad_def badDef : Prop := unchecked Type

/-- Arrow type (function type) -/
good_def arrowType : Type := Prop → Prop

/-- Dependent type (forall) -/
good_def dependentType : Prop := ∀ (p: Prop), p

/-- Lambda expression -/
good_def constType : Type → Type → Type := fun x y => x

/-- Lambda reduction -/
good_def betaReduction : constType Prop (Prop → Prop) := ∀ p : Prop, p

/-- Lambda reduction under binder -/
good_def betaReduction2 : ∀ (p : Prop), constType Prop (Prop → Prop) := fun p => p

/-- The binding domain of a forall may need to be reduce before it is a sort -/
good_def forallSortWhnf : Prop := ∀ (p : id Prop) (x : p),  p

/-- The binding domain of a forall has to be a sort -/
bad_decl (.defnDecl {
  name := `forallSortBad
  levelParams := []
  type := .sort 0
  value := arrow (Lean.mkApp2 (Lean.mkConst ``id [2]) (.sort 1) (.sort 0)) <|
    arrow (.bvar 0) <| arrow (.bvar 0) <| .bvar 1
  hints := .opaque
  safety := .safe
})

/-- The type of a declaration has to be a type, not some other expression -/
bad_def nonTypeType : constType := unchecked Prop

/-- The type of a theorem has to be a proposition -/
bad_decl (.thmDecl {
  name := `nonPropThm
  levelParams := []
  type := .sort 0
  value := arrow (.sort 0) (.bvar 0)
})

/-- Some level computation -/
good_decl (.defnDecl {
    name := `levelComp1
    levelParams := []
    type := .sort 1
    value := .sort (.imax 1 0)
    hints := .opaque
    safety := .safe
  })

/-- Some level computation -/
good_decl (.defnDecl {
    name := `levelComp2
    levelParams := []
    type := .sort 2
    value := .sort (.imax 0 1)
    hints := .opaque
    safety := .safe
  })

/-- Some level computation -/
good_decl (.defnDecl {
    name := `levelComp3
    levelParams := []
    type := .sort 3
    value := .sort (.imax 2 1)
    hints := .opaque
    safety := .safe
  })

def levelParamF.{u} : Sort u → Sort u → Sort u := fun α β => α

/-- Level parameters -/
good_def levelParams : levelParamF Prop (Prop → Prop) := ∀ p : Prop, p

/-- Duplicate universe parameters -/
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

/-! Let's build Peano arithmetic -/

def PN := ∀ α, (α → α) → (α → α)
def PN.zero : PN := fun α s z => z
def PN.succ : PN → PN := fun n α s z => s (n α s z)

def PN.lit0 := PN.zero
def PN.lit1 := PN.succ PN.lit0
def PN.lit2 := PN.succ PN.lit1
def PN.lit3 := PN.succ PN.lit2
def PN.lit4 := PN.succ PN.lit3

def PN.add : PN → PN → PN := fun n m α s z => n α s (m α s z)
def PN.mul : PN → PN → PN := fun n m α s z => n α (m α s) z


/-- Peano arithmetic: 2 = 2 -/
good_thm peano1.{u} : ∀ (t : PN → Prop) (v : (n : PN) → t n), t PN.lit2.{u} :=
  fun t v => v PN.lit2.{u}

/-- Peano arithmetic: 1 + 1 = 2 -/
good_thm peano2.{u} : ∀ (t : PN → Prop) (v : (n : PN) → t n), t PN.lit2.{u} :=
  fun t v => v (PN.lit1.add PN.lit1)

/-- Peano arithmetic: 2 * 2 = 4 -/
good_thm peano3.{u} : ∀ (t : PN → Prop) (v : (n : PN) → t n), t PN.lit4.{u} :=
  fun t v => v (PN.lit2.mul PN.lit2)

/-!
Let declarations
-/


/--
Type checking a non-dependent let
-/
-- Use `good_decl` to avoid the elaborator turning lets into haves
good_decl (.defnDecl {
    name := `letType
    levelParams := []
    type := .sort 1
    value := .letE (nondep := false) `x (.sort 1) (.sort 0) ( .bvar 0)
    hints := .opaque
    safety := .safe
  })

/--
Type checking a dependent let
-/
-- Use `good_decl` to avoid the elaborator turning lets into haves
good_decl (.defnDecl {
    name := `letTypeDep
    levelParams := []
    type := (Lean.mkConst `aDepProp).app (.sort 0)
    value := .letE (nondep := false) `x (.sort 1) (.sort 0) <|
             (Lean.mkConst ``mkADepProp).app (.bvar 0)
    hints := .opaque
    safety := .safe
  })

/--
Reducing a let
-/
good_decl (.defnDecl {
    name := `letRed
    levelParams := []
    type := .letE (nondep := false) `x (.sort 1) (.sort 0) <| .bvar 0
    value := Lean.mkConst ``aProp
    hints := .opaque
    safety := .safe
  })

/-!
Inductives. We begin with examples of good and bad inductive types and constructors.
-/

/-- A simple empty inductive type -/
good_def empty : Type := Empty

/-- A simple enumeration inductive type -/
good_def boolType : Type := Bool

structure TwoBool where
  b1 : Bool
  b2 : Bool

/-- A simple product type -/
good_def twoBool : Type := TwoBool

/-- A parametrized product type (no level parameters) -/
good_def andType : Prop → Prop → Prop := And

/-- A parametrized product type (with level parameters)-/
good_def prodType : Type → Type → Type := Prod

/-- A parametrized product type (with more general level parameters)-/
good_def pprodType : Type → Type → Type := PProd

/-- Level-polymorphic unit type -/
good_def pUnitType : Type := PUnit

/-- Equality, as an important indexed non-recursive data type -/
good_def eqType.{u_1} : {α : Sort u_1} → α → α → Prop := @Eq

inductive N : Type where | zero : N | succ : N → N

/-- A recursive inductive data type -/
good_def natDef : Type := N

inductive Color where | r | b
inductive RBTree (α : Type u) : Color → N → Type u where
  | leaf : RBTree α .b .zero
  | red {n} : RBTree α .b n -> α -> RBTree α .b n -> RBTree α .r n
  | black {c1 c2 n} : RBTree α c1 n -> α -> RBTree α c2 n -> RBTree α .b n.succ

/-- A recursive indexed data type -/
good_def rbTreeDef.{u} : Type u → Color → N → Type u := RBTree

/-! Now a bunch of ill-formed inductive types. -/

/-- An inductive type with a non-sort type -/
bad_raw_consts
  let n := `inductBadNonSort
  #[ .inductInfo {
      name := n
      levelParams := []
      type := .const `constType []
      numParams := 0
      numIndices := 0
      all := [n]
      ctors := []
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }]

/-- Another inductive type with a non-sort type -/
bad_raw_consts
  let n := `inductBadNonSort2
  #[ .inductInfo {
      name := n
      levelParams := []
      type := .const `aType []
      numParams := 0
      numIndices := 0
      all := [n]
      ctors := []
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }]

/-- An inductive with duplicate level params -/
bad_raw_consts
  let n := `inductLevelParam
  #[ .inductInfo {
      name := n
      levelParams := [`u, `u]
      type := .sort 1
      numParams := 0
      numIndices := 0
      all := [n]
      ctors := []
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }]

/-- An inductive with too few parameters in the type -/

bad_raw_consts
  let n := `inductTooFewParams
  #[ .inductInfo {
      name := n
      levelParams := []
      type := arrow (.sort 0) (.sort 0)
      numParams := 2
      numIndices := 0
      all := [n]
      ctors := []
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }]


/-- An inductive with a constructor with wrong parameters -/
bad_raw_consts
  let n := `inductWrongCtorParams
  #[ .ctorInfo {
      name := n ++ `mk
      levelParams := []
      type := arrow (.sort 1) ((Lean.mkConst n).app (.const `aProp []))
      numParams := 1
      induct := n
      cidx := 0
      numFields := 0
      isUnsafe := false
  },
  -- The exporter insists on some recursor existing
  dummyRecInfo n,
  .inductInfo {
      name := n
      levelParams := []
      type := arrow (.sort 0) (.sort 1)
      numParams := 1
      numIndices := 0
      all := [n]
      ctors := [n ++ `mk]
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }
  ]

/-- An inductive with a constructor with wrong parameters in result (they are swapped) -/
bad_raw_consts
  let n := `inductWrongCtorResParams
  #[ .ctorInfo {
      name := n ++ `mk
      levelParams := []
      type := arrow (n := `x) (.sort 0) <| arrow (n := `y) (.sort 0) <| Lean.mkApp2 (Lean.mkConst n) (.bvar 0) (.bvar 1)
      numParams := 2
      induct := n
      cidx := 0
      numFields := 0
      isUnsafe := false
  },
  -- The exporter insists on some recursor to exist
  dummyRecInfo n,
  .inductInfo {
      name := n
      levelParams := []
      type := arrow (n := `x) (.sort 0) <| arrow (n := `y) (.sort 0) <| .sort 1
      numParams := 2
      numIndices := 0
      all := [n]
      ctors := [n ++ `mk]
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }
  ]

/-- An inductive with a constructor with wrong level parameters in result (they are swapped) -/
bad_raw_consts
  let n := `inductWrongCtorResLevel
  #[ .ctorInfo {
      name := n ++ `mk
      levelParams := [`u1, `u2]
      type := arrow (n := `x) (.sort 0) <| arrow (n := `y) (.sort 0) <|
        Lean.mkApp2 (Lean.mkConst n [.param `u2,.param `u1]) (.bvar 1) (.bvar 0)
      numParams := 2
      induct := n
      cidx := 0
      numFields := 0
      isUnsafe := false
  },
  -- The exporter insists on some recursor to exist
  dummyRecInfo n,
  .inductInfo {
      name := n
      levelParams := [`u1,`u2]
      type := arrow (n := `x) (.sort 0) <| arrow (n := `y) (.sort 0) <| .sort 1
      numParams := 2
      numIndices := 0
      all := [n]
      ctors := [n ++ `mk]
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }
  ]

/-- A constructor with an unexpected occurrence of the type in index position of a return type. -/
bad_raw_consts
  let n := `inductInIndex
  #[ .ctorInfo {
      name := n ++ `mk
      levelParams := []
      type := Lean.mkApp (Lean.mkConst n) (Lean.mkApp (Lean.mkConst n) (Lean.mkConst ``aProp))
      numParams := 0
      induct := n
      cidx := 0
      numFields := 0
      isUnsafe := false
  },
  -- The exporter insists on some recursor to exist
  dummyRecInfo n,
  .inductInfo {
      name := n
      levelParams := []
      type := arrow (.sort 0) (.sort 0)
      numParams := 0
      numIndices := 1
      all := [n]
      ctors := [n ++ `mk]
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }
  ]

/-- The classic example of an inductive with negative recursive occurrence -/
bad_raw_consts
  let n := `indNeg
  #[ .ctorInfo {
      name := n ++ `mk
      levelParams := []
      type := arrow (arrow (.const n []) (.const n [])) (.const n [])
      numParams := 0
      induct := n
      cidx := 0
      numFields := 1
      isUnsafe := false
  },
  -- The exporter insists on some recursor to exist
  dummyRecInfo n,
  .inductInfo {
      name := n
      levelParams := []
      type := .sort 1
      numParams := 0
      numIndices := 0
      all := [n]
      ctors := [n ++ `mk]
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }
  ]

/--
When checking inductives, we expect the kernel to reduce the types of constructor arguments.
-/
-- This test needs to be written using `good_decl` because the surface syntax does not allow
-- us to control the type of the constructor parameters.
good_decl
  let n := `reduceCtorParam
  .inductDecl (lparams := []) (nparams := 1) (isUnsafe := false) [{
    name := n
    type := arrow (.sort 1) (.sort 1)
    ctors := [{
        name := n ++ `mk
        type :=
          arrow (n := `α) (Lean.mkApp2 (Lean.mkConst ``id [3]) (.sort 2) (.sort 1)) <|
          arrow (Lean.mkApp2 (Lean.mkConst ``constType) ((Lean.mkConst n []).app (.bvar 0)) ((Lean.mkConst n []).app (.bvar 0))) <|
          Lean.mkApp (Lean.mkConst n) (.bvar 1)
    }]
  }]

/--
When checking inductives, we expect the kernel to **not** reduce the type of the constructor itself;
that should be all manifest `forall`s
-/
bad_raw_consts
  let n := `reduceCtorType
  #[ .inductInfo {
      name := n
      levelParams := []
      type := .sort 1
      numParams := 0
      numIndices := 0
      all := [n]
      ctors := [n ++ `mk]
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  },
  dummyRecInfo n,
  .ctorInfo {
      name := n ++ `mk
      levelParams := []
      type := Lean.mkApp2 (.const ``id [2]) (.sort 1) (Lean.mkConst n)
      numParams := 0
      induct := n
      cidx := 0
      numFields := 0
      isUnsafe := false
  }
  ]

/--
When checking inductives, we expect the kernel to **not** reduce the type of the constructor parameters
further than head normal form. Recursive occurrences nested inside the head normal form are considered
negative occurrences, even if they could be reduced to disappear.
-/
bad_raw_consts
  let n := `indNegReducible
  #[ .ctorInfo {
      name := n ++ `mk
      levelParams := []
      type := arrow (arrow (Lean.mkApp2 (.const ``constType []) (.const ``aType []) (.const n [])) (.const n [])) (.const n [])
      numParams := 0
      induct := n
      cidx := 0
      numFields := 1
      isUnsafe := false
  },
  -- The exporter insists on some recursor to exist
  dummyRecInfo n,
  .inductInfo {
      name := n
      levelParams := []
      type := .sort 1
      numParams := 0
      numIndices := 0
      all := [n]
      ctors := [n ++ `mk]
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }
  ]

/--
info: indNegReducible.mk (x : constType aType indNegReducible → indNegReducible) : indNegReducible
-/
#guard_msgs in #check indNegReducible.mk

inductive PredWithTypeField : Prop where
  | mk (α : Type) : PredWithTypeField

/--
An inductive proposition can have constructors with fields of arbitrary level.
-/
good_def predWithTypeField : Prop := PredWithTypeField

inductive TypeWithTypeField : Type 1 where
  | mk (α : Type) : TypeWithTypeField

/--
An inductive type can have fields of level up to that of the inductive.
-/
good_def typeWithTypeField : Type 1 := TypeWithTypeField

inductive TypeWithTypeFieldPoly : Type (u + 1) where
  | mk (α : Type u) : TypeWithTypeFieldPoly
/--
An inductive type can have fields of level up to that of the inductive (polymorphic variant).
-/
good_def typeWithTypeFieldPoly.{u} : Type (u + 1) := TypeWithTypeFieldPoly

/--
An inductive type can have fields of from higher universes.
-/
bad_raw_consts
  let n := `typeWithTooHighTypeField
  #[ .inductInfo {
      name := n
      levelParams := []
      type := .sort 1
      numParams := 0
      numIndices := 0
      all := [n]
      ctors := [n ++ `mk]
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  },
  dummyRecInfo n,
  .ctorInfo {
      name := n ++ `mk
      levelParams := []
      type := arrow (.sort 1) (Lean.mkConst n)
      numParams := 0
      induct := n
      cidx := 0
      numFields := 1
      isUnsafe := false
  }
  ]

/-! Now statically checking the recursors -/

/-- Asserting the type of the generated recursor -/
good_def emptyRec.{u} : ∀ (motive : Empty → Sort u) (x : Empty), motive x := @Empty.rec

/-- Asserting the type of the generated recursor -/
good_def boolRec.{u} : ∀ {motive : Bool → Sort u} (false : motive false) (true : motive true) (t : Bool), motive t := Bool.rec

/-- Asserting the type of the generated recursor -/
good_def twoBoolRec.{u} : ∀ {motive : TwoBool → Sort u} (mk : ∀ b1 b2, motive ⟨b1, b2⟩) (x : TwoBool), motive x := TwoBool.rec

/-- Asserting the type of the generated recursor -/
good_def andRec.{u} : ∀ (p q : Prop) {motive : And p q → Sort u} (mk : ∀ p q, motive (And.intro p q)) (x : And p q), motive x := @And.rec

/-- Asserting the type of the generated recursor -/
good_def prodRec.{u,v,w} : ∀ (α : Type u) (β : Type v) {motive : Prod α β → Sort u} (mk : ∀ p q, motive (.mk p q)) (x : Prod α β), motive x := @Prod.rec

/-- Asserting the type of the generated recursor -/
good_def pprodRec.{u,v,w} : ∀ (α : Sort u) (β : Sort v) {motive : PProd α β → Sort u} (mk : ∀ p q, motive (.mk p q)) (x : PProd α β), motive x := @PProd.rec

/-- Asserting the type of the generated recursor -/
good_def punitRec.{u,w} : ∀ {motive : PUnit.{u} → Sort w} (mk : motive ⟨⟩) (x : PUnit), motive x := @PUnit.rec

/-- Asserting the type of the generated recursor -/
good_def eqRec.{u, u_1} : ∀ {α : Sort u_1} {a : α} {motive : (a' : α) → a = a' → Sort u} (refl : motive a (.refl a)) {a' : α}
  (t : a = a'), motive a' t := @Eq.rec

/-- Asserting the type of the generated recursor -/
good_def nRec.{u}  : ∀ {motive : N → Sort u} (zero : motive N.zero) (succ : (a : N) → motive a → motive a.succ) (t : N), motive t := @N.rec

/-- Asserting the type of the generated recursor -/
good_def rbTreeRef.{u} : ∀ {α : Type u}
  {motive : (a : Color) → (a_1 : N) → RBTree α a a_1 → Sort u},
   motive Color.b N.zero RBTree.leaf →
      ({n : N} →
          (a : RBTree α Color.b n) →
            (a_1 : α) →
              (a_2 : RBTree α Color.b n) →
                motive Color.b n a → motive Color.b n a_2 → motive Color.r n (a.red a_1 a_2)) →
        ({c1 c2 : Color} →
            {n : N} →
              (a : RBTree α c1 n) →
                (a_1 : α) →
                  (a_2 : RBTree α c2 n) → motive c1 n a → motive c2 n a_2 → motive Color.b n.succ (a.black a_1 a_2)) →
          {a : Color} → {a_1 : N} → (t : RBTree α a a_1) → motive a a_1 t := @RBTree.rec

inductive BoolProp : Prop where
  | a : BoolProp
  | b : BoolProp

/-- Inductive predicates eliminate into Prop if they have more than one constructor. -/
good_def boolPropRec : ∀ {motive : BoolProp → Prop} (a : motive BoolProp.a) (b : motive BoolProp.b) (x : BoolProp), motive x := @BoolProp.rec

/-- Inductive predicates eliminate into Prop if they have one constructors and it carries data. -/
good_def existsRec.{u} : ∀ {α : Sort u} {p : α → Prop} {motive : Exists p → Prop} (intro : ∀ (w : α) (h : p w), motive ⟨w,h⟩)
  (t : Exists p), motive t := @Exists.rec


inductive SortElimProp (b : Bool) : Bool → Bool → Prop
  | mk (b1 b2 : Bool) : SortElimProp b b2 b1

/--
Inductive predicates eliminate into Sort if they have one constructors and it carries data, but the data is
known from the type, e.g. a parameter or an index
-/
good_def sortElimPropRec.{u} : ∀ {b : Bool} {motive : ∀ b1 b2, SortElimProp b b1 b2 → Sort u}
  (mk : ∀ b1 b2, motive b2 b1 (.mk b1 b2)) (b1 b2 : Bool) (x : SortElimProp b b1 b2), motive b1 b2 x := @SortElimProp.rec

inductive SortElimProp2 (b : Bool) : Bool → Bool → Prop
  | mk (b1 b2 : Bool) : SortElimProp2 b b2 (id b1)

/--
Inductive predicates eliminate into Sort if they have one constructors and it carries data, but the data is
known from the type, e.g. a parameter or an index. However, it must occur directly in the result type,
with no intervening reduction.
-/
good_def sortElimProp2Rec : ∀ {b : Bool} {motive : ∀ b1 b2, SortElimProp2 b b1 b2 → Prop}
  (mk : ∀ b1 b2, motive b2 b1 (.mk b1 b2)) (b1 b2 : Bool) (x : SortElimProp2 b b1 b2), motive b1 b2 x := @SortElimProp2.rec

/-! Now actually reducing the recursor -/

/-- Reduction behavior of `Bool.rec` -/
good_thm boolRecEqns.{u} :
  (∀ {motive : Bool → Sort u} (falseVal : motive false) (trueVal : motive true),
    Bool.rec falseVal trueVal false = falseVal) ∧
  (∀ {motive : Bool → Sort u} (falseVal : motive false) (trueVal : motive true),
    Bool.rec falseVal trueVal true = trueVal) := by
  constructor <;> intros <;> rfl

/-- Reduction behavior of `Prod.rec` -/
good_thm prodRecEqns.{u} :
  ∀ {α β : Type} {motive : α × β → Sort u} (f : (a : α) → (b : β) → motive (a, b)) (a : α) (b : β),
    Prod.rec f (a, b) = f a b := by
  intros; rfl

-- We define this using the recursor directly, as structural recursion
-- uses projections, which we do not want to expect at this point

noncomputable def N.add : N → N → N
  := N.rec (fun m => m) (fun n ih m => (ih m).succ)

/-- A proof relying on the reduction behavior of N.rec -/
good_thm nRecReduction :
  (∀ m, N.add N.zero m = m) ∧
  (∀ n m, N.add (N.succ n) m = N.succ (N.add n m)) := by
  unfold N.add;
  constructor <;> intros <;> rfl


noncomputable def myListApped {α : Type} (xs ys : List α) : List α :=
  List.recOn xs ys (fun x xs ih => x :: ih)

/-- Reduction behavior of `List.rec` -/
good_thm listRecReduction : ∀ {α : Type} (xs ys : List α),
  (myListApped [] ys = ys) ∧
  (∀ x xs, myListApped (x :: xs) ys = x :: myListApped xs ys) := by
  intros; unfold myListApped; constructor <;> intros <;> rfl

noncomputable def RBTree.id {α : Type} {c : Color} {n : N} (t : RBTree α c n) : RBTree α c n :=
  RBTree.rec .leaf
    (fun _t1 a _t2 ih1 ih2 => RBTree.red ih1 a ih2)
    (fun _t1 a _t2 ih1 ih2 => RBTree.black ih1 a ih2)
    t

/-- Reduction behavior of `RBTree.rec` -/
good_thm RBTree.id_spec : ∀ {α : Type} {c : Color} {n : N} (t : RBTree α c n), t.id = t := by
  intro α c n t
  induction t
  · rfl
  · dsimp [RBTree.id]
    congr
  · dsimp [RBTree.id]
    congr

/-! Projections -/

/-- Type-checking simple projection functions -/
good_consts #[``And.left, ``And.right]

/-- Type-checking projection functions with parameters -/
good_consts #[``Prod.fst, ``Prod.snd]

/-- Type-checking projection functions  -/
good_consts #[``PProd.fst, ``PProd.snd]

/-- Type-checking dependent projection functions  -/
good_consts #[``PSigma.fst, ``PSigma.snd]

/-- Out of range projection -/
bad_raw_consts #[
  .defnInfo {
    name := `projOutOfRange
    levelParams := []
    type := arrow (.sort 0) <| arrow (.sort 0) <|
      arrow (Lean.mkApp2 (Lean.mkConst `And []) (.bvar 1) (.bvar 0)) <| .bvar 2
    value :=
      .lam `x (binderInfo := .default) (.sort 0) <|
      .lam `y (binderInfo := .default) (.sort 0) <|
      .lam `z (binderInfo := .default) (Lean.mkApp2 (Lean.mkConst `And []) (.bvar 1) (.bvar 0)) <|
      .proj `And 2 (.bvar 0)
    hints := .opaque
    safety := .safe
  }
]

/-- Projection out something that is not a structure -/
bad_raw_consts #[
  .defnInfo {
    name := `projNotStruct
    levelParams := []
    type := arrow (Lean.mkConst ``N) <| (Lean.mkConst ``N)
    value :=
      .lam `x (binderInfo := .default) (Lean.mkConst ``N) <|
      .proj `N 0 (.bvar 0)
    hints := .opaque
    safety := .safe
  }
]

inductive PropStructure.{u,v} : Prop where
  | mk (aProof : PUnit.{u}) (someData : PUnit.{v}) (aSecondProof : PUnit.{u})
    (someMoreData : PUnit.{v}) (aProofAboutData : someMoreData = someMoreData)
    (aFinalProof : PUnit.{u})

meta def mkPropStructureTest (n : Lean.Name) (resType : Lean.Expr) (idx : Nat) : Array Lean.ConstantInfo :=
  #[ .defnInfo {
    name := n
    levelParams := []
    type := arrow (Lean.mkConst ``PropStructure [0,1]) resType
    value :=
      .lam `x (binderInfo := .default) (Lean.mkConst ``PropStructure [0,1]) <|
      .proj ``PropStructure idx (.bvar 0)
    hints := .opaque
    safety := .safe
  }]


/-- Projecting out of a proposition

The lean kernel allows projections out of propositions if they precede
all dependent data fields.
-/
good_raw_consts mkPropStructureTest `projProp1 (Lean.mkConst ``PUnit [0]) 0

/-- Projecting out of a proposition

The lean kernel disallows data projections out of propositional structures.
-/
bad_raw_consts mkPropStructureTest `projProp2 (Lean.mkConst ``PUnit [1]) 1

/-- Projecting out of a proposition

The lean kernel allows projections out of propositions if they precede
all dependent data fields. Non-dependent data fields are not relevant.
-/
good_raw_consts mkPropStructureTest `projProp3 (Lean.mkConst ``PUnit [0]) 2

/-- Projecting out of a proposition

The lean kernel disallows data projections out of propositional structures.
-/
bad_raw_consts mkPropStructureTest `projProp4 (Lean.mkConst ``PUnit [1]) 3

/-- Projecting out of a proposition

The lean kernel disallows proof projections out of propositional structures that depend on data.
-/
bad_raw_consts mkPropStructureTest `projProp5
  (Lean.mkApp3 (Lean.mkConst ``Eq [1]) (Lean.mkConst ``PUnit [1]) (.proj ``PropStructure 3 (.bvar 0)) (.proj ``PropStructure 3 (.bvar 0))) 4

/--
Projecting out of a proposition.

The lean kernel rejects any projections out of a proposition that
come after a dependent data field, even if that is not used by the present projection.
-/
bad_raw_consts mkPropStructureTest `projProp6 (Lean.mkConst ``PUnit [0]) 5

inductive ProjDataIndex : N → Prop
  | mk (n : N) (p : True) : ProjDataIndex n

noncomputable def projDataIndexRec := @ProjDataIndex.rec

/--
The recursor for `ProjDataIndex` allows elimination into sort.
-/
good_consts #[``projDataIndexRec]

/--
Projecting out data is not allowed, even if this data appears as an index
and the recursor would allow it.
-/
bad_raw_consts
  #[ .defnInfo {
    name := `projIndexData
    levelParams := []
    type :=
      arrow (Lean.mkConst ``N) <|
      arrow ((Lean.mkConst ``ProjDataIndex).app (.bvar 0)) <|
      (Lean.mkConst ``N)
    value :=
      .lam `x (binderInfo := .default) (Lean.mkConst ``N) <|
      .lam `x (binderInfo := .default) ((Lean.mkConst ``ProjDataIndex).app (.bvar 0)) <|
      .proj ``PropStructure 0 (.bvar 0)
    hints := .opaque
    safety := .safe
  }]

/--
Projecting out data is not allowed, even if this data appears as an index
and the recursor would allow it.

This also forbids projecting out proofs that follow such fields.
-/
bad_raw_consts
  #[ .defnInfo {
    name := `projIndexData2
    levelParams := []
    type :=
      arrow (Lean.mkConst ``N) <|
      arrow ((Lean.mkConst ``ProjDataIndex).app (.bvar 0)) <|
      (Lean.mkConst ``True)
    value :=
      .lam `x (binderInfo := .default) (Lean.mkConst ``N) <|
      .lam `x (binderInfo := .default) ((Lean.mkConst ``ProjDataIndex).app (.bvar 0)) <|
      .proj ``PropStructure 1 (.bvar 0)
    hints := .opaque
    safety := .safe
  }]

/-- Projection reductions -/
good_def projRed : (Prod.mk true false).2 = false := rfl


/--
Rule k for `Eq`:
The recursor reduces even if the major argument is not a constructor,
as long replacing the major argument with a constructor is type correct.
-/
good_thm ruleK : ∀ (h : true = true) (a : Bool),
  Eq.rec (motive := fun _ _ => Bool) a h = a :=
  fun _ a => Eq.refl a

/--
Rule k for `Eq` should not fire if the types of the major argument
do not match that of the constructor.
-/
bad_thm ruleKbad : ∀ (h : true = false) (a : Bool),
  Eq.rec (motive := fun _ _ => Bool) a h = a :=
  fun _ a => unchecked Eq.refl a

/--
Rule k should not fire for `Acc`.
-/
bad_thm ruleKAcc.{u} : ∀ (α : Sort u) (p : α → α → Prop) (x : α) (h : Acc p x) (a : Bool),
  Acc.rec (motive := fun _ _ => Bool) (fun _ _ _=> a) h = a :=
  fun α p x h a => unchecked Eq.refl a

/-- Type checking Nat literals -/
good_decl (.defnDecl {
  name := `aNatLit
  levelParams := {}
  type := Lean.mkConst ``Nat
  value := .lit (.natVal 0)
  hints := .opaque
  safety := .safe
})

/-- Reducing Nat literals -/
good_decl (.thmDecl {
  name := `natLitEq
  levelParams := {}
  type := Lean.mkApp3 (Lean.mkConst ``Eq [1]) (Lean.mkConst ``Nat) (.lit (.natVal 3))
    (Lean.mkApp (Lean.mkConst ``Nat.succ) <|
     Lean.mkApp (Lean.mkConst ``Nat.succ) <|
     Lean.mkApp (Lean.mkConst ``Nat.succ) <|
     Lean.mkConst ``Nat.zero
    )
  value := Lean.mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Nat) (.lit (.natVal 3))
})

/-! Proof irrelevance and unit Eta -/

/--
Proof irrelevance: every `Prop` is a subsingleton, if `p : Prop` then all elements of `p`
are definitionally equal.
-/
good_def proofIrrelevance : ∀ (p : Prop) (h1 h2 : p), h1 = h2 := fun _ _ _ => rfl

/--
Proof irrelevance is limited to Prop: if `p : Type`, then all elements of `p` are *not*
definitionally equal.
-/
bad_def proofIrrelevanceBad : ∀ (p : Type) (h1 h2 : p), h1 = h2 :=
  unchecked (fun (p : Type) (h1 h2 : p) => @rfl p h1)

/--
Proof irrelevance: if `p : A` and `A` is definitionally equal to `Prop`, then all elements of `p`
are still definitionally equal. Just applying proof irrelevance at `Sort 0` isn't sufficient.
-/
good_def proofIrrelevanceWhnf : ∀ (p : id Prop) (h1 h2 : p), h1 = h2 := fun _ _ _ => rfl

/-- Unit eta -/
good_def unitEta1 : ∀ (x y : Unit), x = y := fun _ _ => rfl

/-- Unit eta -/
good_def unitEta2.{u} : ∀ (x y : PUnit.{u}), x = y := fun _ _ => rfl

/-- Unit eta -/
good_def unitEta3 : ∀ (x y : PUnit.{0}), x = y := fun _ _ => rfl

/-- Structure eta -/
good_def structEta.{u} : ∀ (α β : Type u) (x : α × β), x = ⟨x.1, x.2⟩ ∧ ⟨x.1, x.2⟩ = x:= fun _ _ _ => ⟨rfl, rfl⟩

/-! Function eta -/

/-- Function eta for non-dependent functions. -/
good_thm funEta :
  ∀ (α : Type) (β : Type) (f : α → β), (fun x => f x) = f :=
  fun _ _ f => rfl

/-- Function eta for dependent functions (pi types). -/
good_thm funEtaDep :
  ∀ (α : Type) (β : α → Type) (f : ∀ a, β a), (fun a => f a) = f :=
  fun _ _ f => rfl

/-- Eta should not identify functions with different bodies. -/
bad_thm funEtaBad :
  ∀ (α : Type) (β : Type) (g : α → α) (f : α → β), (fun x => f (g x)) = f :=
  fun _ _ _ f => unchecked Eq.refl f

/--
Corner case for function eta:
Does a defeq between a partially applied recursor with rule k and a free
variable trigger eta expansion?

Taking the official kernel as the specification, the answer is no.
See <https://github.com/leanprover/lean4/issues/12520> for a discussion.
-/
bad_def etaRuleK : ∀ (a : true = true → Bool),
  @Eq (true = true → Bool)
    (@Eq.rec Bool true (fun _ _ => Bool) (a (Eq.refl true)) _)
    a :=
  fun a => unchecked Eq.refl a

structure T where
  val : Bool
  proof : True

/--
Corner case for function eta:
Does a defeq between a partially applied constructor trigger eta expansion?

Taking the official kernel as the specification, the answer is no.
See <https://github.com/leanprover/lean4/issues/12520> for a discussion.
-/
bad_def etaCtor :
  ∀ (x : True → T) , (T.mk (x True.intro).val) = x := fun x => unchecked Eq.refl x

/-! Reflexive inductives -/

/--
Rejection: recursive occurrence on the *left* of an arrow,
*behind further arrows* inside a constructor argument.

The constructor argument is a function type `Nat → (I → Nat)`.
-/
bad_raw_consts
  let n := `reflOccLeft
  #[ .ctorInfo {
      name := n ++ `mk
      levelParams := []
      type := arrow (arrow (Lean.mkConst ``Nat) (arrow (.const n []) (Lean.mkConst ``Nat))) (.const n [])
      numParams := 0
      induct := n
      cidx := 0
      numFields := 1
      isUnsafe := false
  },
  dummyRecInfo n,
  .inductInfo {
      name := n
      levelParams := []
      type := .sort 1
      numParams := 0
      numIndices := 0
      all := [n]
      ctors := [n ++ `mk]
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }
  ]

/--
Rejection: recursive occurrence in *index position*, behind a further arrow.

We build an indexed inductive `I : Type → Type` with a constructor argument
`Nat → I (I α)`, so the recursive occurrence appears as an index argument.
-/
bad_raw_consts
  let n := `reflOccInIndex
  #[ .ctorInfo {
      name := n ++ `mk
      levelParams := []
      type :=
        arrow (n := `α) (.sort 1) <|
        arrow (arrow (Lean.mkConst ``Nat) <|
          Lean.mkApp (Lean.mkConst n) (Lean.mkApp (Lean.mkConst n) (.bvar 0))) <|
        Lean.mkApp (Lean.mkConst n) (.bvar 1)
      numParams := 0
      induct := n
      cidx := 0
      numFields := 1
      isUnsafe := false
  },
  dummyRecInfo n,
  .inductInfo {
      name := n
      levelParams := []
      type := arrow (n := `α) (.sort 1) (.sort 1)
      numParams := 0
      numIndices := 1
      all := [n]
      ctors := [n ++ `mk]
      numNested := 0
      isRec := false
      isUnsafe := false
      isReflexive := false
  }
  ]

/--
When checking inductives, we expect the kernel to reduce the types of constructor arguments in all
positive positions.
-/
-- This test needs to be written using `good_decl` because the surface syntax does not allow
-- us to control the type of the constructor parameters.
good_decl
  let n := `reduceCtorParamRefl
  .inductDecl (lparams := []) (nparams := 1) (isUnsafe := false) [{
    name := n
    type := arrow (.sort 1) (.sort 1)
    ctors := [{
        name := n ++ `mk
        type :=
          arrow (n := `α) (Lean.mkApp2 (Lean.mkConst ``id [3]) (.sort 2) (.sort 1)) <|
          arrow (arrow (.bvar 0) (Lean.mkApp2 (Lean.mkConst ``constType) ((Lean.mkConst n []).app (.bvar 1)) ((Lean.mkConst n []).app (.bvar 1)))) <|
          Lean.mkApp (Lean.mkConst n) (.bvar 1)
    }]
  }]

/--
info: reduceCtorParamRefl.mk (α : id Type) (x : α → constType (reduceCtorParamRefl α) (reduceCtorParamRefl α)) :
  reduceCtorParamRefl α
-/
#guard_msgs in #check reduceCtorParamRefl.mk

/--
When checking inductives, we expect the kernel to reduce the types of constructor arguments in all
positive positions.
-/
-- This test needs to be written using `good_decl` because the surface syntax does not allow
-- us to control the type of the constructor parameters.
good_decl
  let n := `reduceCtorParamRefl2
  .inductDecl (lparams := []) (nparams := 1) (isUnsafe := false) [{
    name := n
    type := arrow (.sort 1) (.sort 1)
    ctors := [{
        name := n ++ `mk
        type :=
          arrow (n := `α) (Lean.mkApp2 (Lean.mkConst ``id [3]) (.sort 2) (.sort 1)) <|
          arrow (arrow (.bvar 0) (Lean.mkApp2 (Lean.mkConst ``constType) ((Lean.mkConst n []).app (.bvar 1)) (.bvar 1))) <|
          Lean.mkApp (Lean.mkConst n) (.bvar 1)
    }]
  }]

/--
info: reduceCtorParamRefl2.mk (α : id Type) (x : α → constType (reduceCtorParamRefl2 α) α) : reduceCtorParamRefl2 α
-/
#guard_msgs in #check reduceCtorParamRefl2.mk

/--
A concrete reflexive inductive `Type`: binary trees.

The recursive occurrences live behind further arrows (`Bool → RTree`).
-/
inductive RTree : Type where
  | leaf
  | node (children : Bool → RTree) : RTree

noncomputable def rTreeRec := @RTree.rec

/-- Asserting the type of the generated recursor. -/
good_consts #[``rTreeRec]

noncomputable def RTree.left (t : RTree) : RTree :=
  RTree.rec (motive := fun _ => RTree) .leaf (fun children _ih => children true) t

/-- Reduction behavior of `RTree.rec` on `RTree.mk`. -/
good_thm rtreeRecReduction : ∀ (t1 t2 : RTree),
  (RTree.node (Bool.rec t2 t1)).left = t1 := fun _ _ => rfl

noncomputable def accRecType := @Acc.rec

/-- Asserting the type of `Acc.rec`. -/
good_consts #[``accRecType]

/-! `Acc` and reduction -/

/-- `Acc.rec` reduces on `Acc.intro`. -/
good_thm accRecReduction :
  ∀ {α : Type} (r : α → α → Prop) (a : α)
    (h : ∀ b, r b a → Acc r b) (p : Bool),
    Acc.rec (motive := fun _ _ => Bool) (fun _ _ _ => p) (Acc.intro (x := a) h) = p := by
  intro α r a h p
  rfl

/-- `Acc.rec` does not have structure eta. -/
bad_thm accRecNoEta :
  ∀ {α : Type} (r : α → α → Prop) (a : α)
    (h : Acc r a) (p : Bool),
    Acc.rec (motive := fun _ _ => Bool) (fun _ _ _ => p) h = p :=
  @fun α r a h p => unchecked Eq.refl p

/-! Quotients -/

/-- Asserting the type of `Quot.mk`. -/
good_def quotMkType.{u} :
  ∀ {α : Sort u} (r : α → α → Prop) (a : α), Quot r :=
  @Quot.mk

/-- Asserting the type of `Quot.ind`. -/
good_def quotIndType.{u} :
  ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop}
    (mk : ∀ a : α, β (Quot.mk r a)) (q : Quot r),
      β q :=
  @Quot.ind

/-- Asserting the type of `Quot.lift`. -/
good_def quotLiftType.{u,v} :
  ∀ {α : Sort u} {r : α → α → Prop} {β : Sort v}
    (f : α → β) (h : ∀ (a b : α), r a b → f a = f b),
      Quot r → β :=
  @Quot.lift

/-- Asserting the type of `Quot.sound`. -/
good_def quotSoundType.{u} :
  ∀ {α : Sort u} {r : α → α → Prop} {a b : α},
    r a b → Quot.mk r a = Quot.mk r b :=
  @Quot.sound

/-- Reduction behavior of `Quot.lift` on `Quot.mk`. -/
good_thm quotLiftReduction.{u,v} :
  ∀ {α : Sort u} {r : α → α → Prop} {β : Sort v}
    (f : α → β) (h : ∀ (a b : α), r a b → f a = f b) (a : α),
      Quot.lift f h (Quot.mk r a) = f a := by
  intro α r β f h a
  rfl

/-- Reduction behavior of `Quot.ind` on `Quot.mk`. -/
good_thm quotIndReduction.{u} :
  ∀ {α : Sort u} (r : α → α → Prop) {β : Quot r → Prop}
    (mk : ∀ a : α, β (Quot.mk r a)) (a : α),
      Quot.ind (r := r) (β := β) mk (Quot.mk r a) = mk a := by
  intro α r β mk a
  rfl

/-! ## Name collisions

These test cases use the `renamings` feature to create exports where
two different declarations share the same name, testing that checkers
properly detect and reject name collisions.
-/

def dupDef : Type := Prop
def dupDef2 : Type := Prop
inductive DupInd where | mk
inductive DupInd2 where | mk1 | mk2

/-- Two definitions with the same name -/
bad_consts #[`dupDef2, `dupDef]
  renaming #[(`dupDef, `dup_defs), (`dupDef2, `dup_defs)]

/-- A definition and a constructor with the same name -/
bad_consts #[`dupDef, `DupInd]
  renaming #[(`DupInd, `dup_ind_def), (`DupInd.mk, `dup_ind_def.mk), (`DupInd.rec, `dup_ind_def.rec), (`dupDef, `dup_ind_def)]

/-- A definition and a constructor with the same name -/
bad_consts #[`dupDef, `DupInd]
  renaming #[(`DupInd, `dup_ctor_def), (`DupInd.mk, `dup_ctor_def.mk), (`DupInd.rec, `dup_ctor_def.rec), (`dupDef, `dup_ctor_def.mk)]

/-- A definition and a recursor with the same name -/
bad_consts #[`dupDef, `DupInd]
  renaming #[(`DupInd, `dup_rec_def), (`DupInd.mk, `dup_rec_def.mk), (`DupInd.rec, `dup_rec_def.rec), (`dupDef, `dup_rec_def.rec)]

/--
A definition with the name of a recursor, and the recursor named differently.
This would pass simple checks for duplicate definitions in the parser, but should still
be rejected by the checker.
-/
bad_consts #[`dupDef, `DupInd]
  renaming #[(`DupInd, `dup_rec_def2), (`DupInd.mk, `dup_rec_def2.mk), (`DupInd.rec, `dup_rec_def2.original_rec), (`dupDef, `dup_rec_def2.rec)]

/-- A constructor and a recursor with the same name -/
bad_consts #[`DupInd]
  renaming #[(`DupInd, `dup_ctor_rec), (`DupInd.mk, `dup_ctor_rec.rec), (`DupInd.rec, `dup_ctor_rec.rec)]

/-- An inductive with two constructors with the same name -/
bad_consts #[`DupInd2]
  renaming #[(`DupInd2, `DupConCon), (`DupInd2.mk1, `dup_ind_con_con.mk), (`DupInd2.mk2, `dup_ind_con_con.mk)]
