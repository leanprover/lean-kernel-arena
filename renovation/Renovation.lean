import Renovation.Meta
set_option linter.unusedVariables false
/-!
Tests for the per-inductive feature flags of lean4#16595 (export format 3.2.0).

Each inductive type is written with the usual `inductive` syntax, but the flags it is sent to the
kernel with are given explicitly (all off unless listed):

* `good_inductive flags in inductive ...`: the kernel accepts the block with these flags.
* `bad_inductive flags via wfFlags in inductive ...`: the kernel rejects the block with these
  flags. The constants in the export are those the kernel produces for the block with `wfFlags`,
  with the flags (and the `k` field of the recursors) replaced by `flags`. With `lifted`, the
  well-formed variant lives in `Sort (max 1 l)` rather than `Sort l`, so that its recursor is the
  one with large elimination. With `patch f`, `f` is applied to the exported constants.

The flags are inputs to the kernel: a checker checks that they are allowed, and must not recompute
them. A flag may always be off.
-/

/-! ## `isImpredicative` -/

/-- An impredicative proposition. -/
good_inductive { isImpredicative := true } in
inductive ImpTrue : Prop where
  | intro

/-- An impredicative proposition may have fields in any universe, here in `Type`. -/
good_inductive { isImpredicative := true } in
inductive ImpExists (α : Type) (p : α → Prop) : Prop where
  | intro (w : α) (h : p w)

/--
A proposition that is not impredicative may only have fields in `Prop`, but this one has a field
`w : α` with `α : Type`. Before the flags, this was allowed for every type in `Prop`.
-/
bad_inductive {} via { isImpredicative := true } in
inductive PredExists (α : Type) (p : α → Prop) : Prop where
  | intro (w : α) (h : p w)

/-- An impredicative proposition with a field in an arbitrary universe `Sort u`. -/
good_inductive { isImpredicative := true } in
inductive ImpAnySort.{u} (α : Sort u) : Prop where
  | intro (x : α)

/-- Without `isImpredicative`, a field in `Sort u` is not allowed in `Prop`, as `u ≤ 0` does not hold. -/
bad_inductive {} via { isImpredicative := true } in
inductive PredAnySort.{u} (α : Sort u) : Prop where
  | intro (x : α)

/-- A proposition need not be impredicative if all its fields are proofs. -/
good_inductive {} in
inductive PredAnd (a b : Prop) : Prop where
  | intro (ha : a) (hb : b)

/-- A type in `Type` cannot be impredicative. -/
bad_inductive { isImpredicative := true } via {} in
inductive ImpType : Type where
  | a
  | b

/-- A type in `Sort u` cannot be impredicative: its result level does not normalize to `0`. -/
bad_inductive { isImpredicative := true } via {} in
inductive ImpSort.{u} : Sort u where
  | a

/-- An impredicative type cannot have large elimination. -/
bad_inductive { isImpredicative := true, hasLargeElim := true } via { hasLargeElim := true } in
inductive ImpFalseLarge : Prop

/-- An impredicative type cannot have projections. -/
bad_inductive { isImpredicative := true, hasProjections := true } via { isImpredicative := true } in
inductive ImpAndProj (a b : Prop) : Prop where
  | intro (ha : a) (hb : b)

/-- The types of a mutual block can all be impredicative. -/
good_inductive { isImpredicative := true } in
mutual
inductive ImpMutA : Prop where
  | a
inductive ImpMutB : Prop where
  | b
end

/-- The types of a mutual block must agree on `isImpredicative`. -/
bad_inductive [(`PredMutA, { isImpredicative := true }), (`PredMutB, {})] via {} in
mutual
inductive PredMutA : Prop where
  | a
inductive PredMutB : Prop where
  | b
end

/-! ## `hasLargeElim` -/

/-- A type in `Type` with large elimination: its recursor has a motive into `Sort u`. -/
good_inductive { hasLargeElim := true } in
inductive LBool : Type where
  | t
  | f

/--
A type in `Type` may do without large elimination: its recursor then has a motive into `Prop` only,
and no reduction rules.
-/
good_inductive {} in
inductive SBool : Type where
  | t
  | f

/-- The recursor of a type without large elimination must not eliminate into `Sort u`. -/
bad_inductive {} via { hasLargeElim := true } patch id in
inductive SBoolLargeRec : Type where
  | t
  | f

/-- The recursor of a type without large elimination must not have reduction rules. -/
bad_inductive {} via { hasLargeElim := true }
  patch (ConstantInfo.mapRec RecursorVal.motiveToProp) in
inductive SBoolRules : Type where
  | t
  | f

/--
A type in `Type` with large elimination can be eliminated into `Type`; this uses the reduction rule
of its recursor.
-/
good_def lBoolElim : Eq (@LBool.rec (fun _ => Type) Nat Bool LBool.t) Nat := rfl

/-- A proposition with two constructors cannot have large elimination. -/
bad_inductive { hasLargeElim := true } via { hasLargeElim := true } lifted in
inductive LOr (a b : Prop) : Prop where
  | inl (h : a)
  | inr (h : b)

/-- A proposition with two constructors without large elimination. -/
good_inductive {} in
inductive SOr (a b : Prop) : Prop where
  | inl (h : a)
  | inr (h : b)

/-- A proposition without constructors can have large elimination. -/
good_inductive { hasLargeElim := true } in
inductive LFalse : Prop

/-- A proposition with one constructor without fields can have large elimination with `isK`. -/
good_inductive { isK := true, hasLargeElim := true } in
inductive LTrueK : Prop where
  | intro

/-- A proposition with one constructor without fields can have large elimination with `hasEta`. -/
good_inductive { hasProjections := true, hasEta := true, hasLargeElim := true } in
inductive LTrueEta : Prop where
  | intro

/-- A proposition with one constructor needs `isK` or `hasEta` for large elimination. -/
bad_inductive { hasLargeElim := true } via { isK := true, hasLargeElim := true } in
inductive LTrueNone : Prop where
  | intro

/-- A proposition with one constructor whose fields are proofs can have large elimination with `hasEta`. -/
good_inductive { hasProjections := true, hasEta := true, hasLargeElim := true } in
inductive LAnd (a b : Prop) : Prop where
  | intro (ha : a) (hb : b)

/-- Like `LAnd`, but without `hasEta`, so it cannot have large elimination. -/
bad_inductive { hasProjections := true, hasLargeElim := true }
  via { hasProjections := true, hasEta := true, hasLargeElim := true } in
inductive LAndNoEta (a b : Prop) : Prop where
  | intro (ha : a) (hb : b)

/--
A recursive proposition with one constructor cannot have `hasEta` (it is recursive) nor `isK` (its
constructor has a field), so it cannot have large elimination either. Before the flags, it had
large elimination, as all its fields occur in the result type.
-/
bad_inductive { hasLargeElim := true } via { hasLargeElim := true } lifted in
inductive LRec : Prop where
  | intro (h : LRec)

/--
Like `Acc`, but over a proposition, so that it need not be impredicative. It no longer has large
elimination, as it has indices and so cannot have projections and eta, and its constructor has
fields, so it cannot be `isK`.
-/
bad_inductive { hasLargeElim := true } via { hasLargeElim := true } lifted in
inductive LAcc {α : Prop} (r : α → α → Prop) : α → Prop where
  | intro (x : α) (h : ∀ y, r y x → LAcc r y) : LAcc r x

/-- `Acc` itself, impredicative and without large elimination. -/
good_inductive { isImpredicative := true } in
inductive SAcc.{u} {α : Sort u} (r : α → α → Prop) : α → Prop where
  | intro (x : α) (h : ∀ y, r y x → SAcc r y) : SAcc r x

/-- Large elimination for a proposition is only allowed if the block has exactly one type. -/
bad_inductive { hasLargeElim := true } via { hasLargeElim := true } lifted in
mutual
inductive LMutFalseA : Prop
inductive LMutFalseB : Prop
end

/-- A mutual block in `Type` can have large elimination. -/
good_inductive { hasLargeElim := true } in
mutual
inductive LMutA : Type where
  | a (b : LMutB)
  | nil
inductive LMutB : Type where
  | b (a : LMutA)
end

/-- The types of a mutual block must agree on `hasLargeElim`. -/
bad_inductive [(`LMixA, { hasLargeElim := true }), (`LMixB, {})] via { hasLargeElim := true } in
mutual
inductive LMixA : Type where
  | a (b : LMixB)
  | nil
inductive LMixB : Type where
  | b (a : LMixA)
end

/-- A type in `Sort u` might be a proposition, so with two constructors it cannot have large elimination. -/
bad_inductive { hasLargeElim := true } via { hasLargeElim := true } lifted in
inductive LPolyTwo.{u} : Sort u where
  | a
  | b

/-- A type in `Sort u` without large elimination. -/
good_inductive {} in
inductive SPolyTwo.{u} : Sort u where
  | a
  | b

/-- A type in `Sort (max 1 u)` is never a proposition, so it can have large elimination. -/
good_inductive { hasLargeElim := true } in
inductive LPolyMax.{u} : Sort (max 1 u) where
  | a
  | b

/-- A type in `Sort (u + 1)` is never a proposition, so it can have large elimination. -/
good_inductive { hasLargeElim := true } in
inductive LPolySucc.{u} : Sort (u + 1) where
  | a
  | b

/-- A type in `Sort u` with one constructor without fields can have large elimination with `hasEta`. -/
good_inductive { hasProjections := true, hasEta := true, hasLargeElim := true } in
inductive LPolyUnit.{u} : Sort u where
  | a

/-- The motive's universe parameter is called `u` if that name is free. -/
good_inductive { hasLargeElim := true } in
inductive LNameV.{v} (α : Sort v) : Type where
  | mk

/-- The motive's universe parameter is called `u_1` if `u` is taken. -/
good_inductive { hasLargeElim := true } in
inductive LNameU.{u} (α : Sort u) : Type where
  | mk

/-- The motive's universe parameter is called `u_2` if `u` and `u_1` are taken. -/
good_inductive { hasLargeElim := true } in
inductive LNameU1.{u, u_1} (α : Sort u) (β : Sort u_1) : Type where
  | mk

/-! ## `isK` -/

/-- Like `Eq`, with `isK` and large elimination. -/
good_inductive { isK := true, hasLargeElim := true } in
inductive KEq.{u} {α : Sort u} (a : α) : α → Prop where
  | refl : KEq a a

/-- K-like reduction: the recursor of `KEq` reduces even if the major premise is a variable. -/
good_def kEqK : ∀ (h : KEq 0 0), Eq (@KEq.rec Nat 0 (fun _ _ => Nat) 5 0 h) 5 :=
  fun h => unchecked (Eq.refl 5)

/-- Like `Eq`, but without `isK`, and hence without large elimination. -/
good_inductive {} in
inductive SEq.{u} {α : Sort u} (a : α) : α → Prop where
  | refl : SEq a a

/-- Like `Eq`, but without `isK`, so it cannot have large elimination. -/
bad_inductive { hasLargeElim := true } via { isK := true, hasLargeElim := true } in
inductive LEqNoK.{u} {α : Sort u} (a : α) : α → Prop where
  | refl : LEqNoK a a

/-- `isK` without large elimination. -/
good_inductive { isK := true } in
inductive KTrue : Prop where
  | intro

/-- A type in `Type` cannot be `isK`. -/
bad_inductive { isK := true, hasLargeElim := true } via { hasLargeElim := true } in
inductive KType : Type where
  | intro

/-- A type in `Sort u` cannot be `isK`. -/
bad_inductive { isK := true } via {} in
inductive KSort.{u} : Sort u where
  | intro

/-- A type with two constructors cannot be `isK`. -/
bad_inductive { isK := true } via {} in
inductive KTwo : Prop where
  | a
  | b

/-- A type without constructors cannot be `isK`. -/
bad_inductive { isK := true } via {} in
inductive KEmpty : Prop

/-- A type whose constructor has a field cannot be `isK`. -/
bad_inductive { isK := true } via {} in
inductive KField (p : Prop) : Prop where
  | intro (h : p)

/-- A type whose constructor has a field cannot be `isK`, even if the field is determined by an index. -/
bad_inductive { isImpredicative := true, isK := true } via { isImpredicative := true } in
inductive KIndexField : Prop → Prop where
  | intro (p : Prop) : KIndexField (p → p)

/-- A mutual block cannot be `isK`, not even its first type. -/
bad_inductive [(`KMutFirstA, { isK := true }), (`KMutFirstB, {})] via {} in
mutual
inductive KMutFirstA : Prop where
  | a
inductive KMutFirstB : Prop where
  | b
end

/-- Only the first type of a mutual block may be marked `isK`. -/
bad_inductive [(`KMutSecondA, {}), (`KMutSecondB, { isK := true })] via {} in
mutual
inductive KMutSecondA : Prop where
  | a
inductive KMutSecondB : Prop where
  | b
end

/-- The recursor's `k` field must be the `isK` flag: here the flag is set, but `k` is not. -/
bad_inductive { isK := true } patch (ConstantInfo.mapRec ({ · with k := false })) in
inductive KRecNotK : Prop where
  | intro

/-- The recursor's `k` field must be the `isK` flag: here `k` is set, but the flag is not. -/
bad_inductive {} patch (ConstantInfo.mapRec ({ · with k := true })) in
inductive KRecK : Prop where
  | intro

/-! ## `hasProjections` -/

/-- A structure with projections. -/
good_inductive { hasProjections := true, hasEta := true, hasLargeElim := true } in
inductive PPair : Type where
  | mk (a : Nat) (b : Bool)

/-- Projecting out of a type with `hasProjections`. -/
good_def pPairFst : PPair → Nat := fun p => proj% PPair 0 p

/-- A structure without projections. -/
good_inductive { hasLargeElim := true } in
inductive PNoProj : Type where
  | mk (a : Nat) (b : Bool)

/-- Projecting out of a type without `hasProjections` is not allowed. -/
bad_def pNoProjFst : PNoProj → Nat := fun p => unchecked (proj% PNoProj 0 p)

/-- A type with two constructors cannot have projections. -/
bad_inductive { hasProjections := true, hasLargeElim := true } via { hasLargeElim := true } in
inductive PTwoCtors : Type where
  | a (n : Nat)
  | b

/-- A type without constructors cannot have projections. -/
bad_inductive { hasProjections := true, hasLargeElim := true } via { hasLargeElim := true } in
inductive PNoCtors : Type

/-- A type with indices cannot have projections. -/
bad_inductive { hasProjections := true, hasLargeElim := true } via { hasLargeElim := true } in
inductive PIndexed : Bool → Type where
  | mk (n : Nat) : PIndexed true

/-- Projecting a proof out of a proposition with projections. -/
good_def lAndLeft : ∀ (a b : Prop), LAnd a b → a := fun a b h => proj% LAnd 0 h

/-- An impredicative proposition, which hence has no projections. -/
good_inductive { isImpredicative := true } in
inductive ImpAnd (a b : Prop) : Prop where
  | intro (ha : a) (hb : b)

/--
Projecting out of an impredicative proposition is not allowed, not even a proof. Before the flags,
projecting a proof out of a structure in `Prop` was allowed.
-/
bad_def impAndLeft : ∀ (a b : Prop), ImpAnd a b → a := fun a b h => unchecked (proj% ImpAnd 0 h)

/-- Projecting a non-proof out of an impredicative proposition is not allowed either. -/
bad_def impExistsWit : ∀ (p : Nat → Prop), ImpExists Nat p → Nat :=
  fun p h => unchecked (proj% ImpExists 0 h)

/-- A structure with parameters and projections. -/
good_inductive { hasProjections := true, hasEta := true, hasLargeElim := true } in
inductive PBox (α : Type) : Type where
  | mk (x : α)

/-- Projecting out of a structure with parameters. -/
good_def pBoxGet : ∀ (α : Type), PBox α → α := fun α b => proj% PBox 0 b

/-- A proposition with projections, but without eta and large elimination. -/
good_inductive { hasProjections := true } in
inductive PAndNoEta (a b : Prop) : Prop where
  | intro (ha : a) (hb : b)

/-- Projecting out of a proposition with projections, but without eta. -/
good_def pAndNoEtaRight : ∀ (a b : Prop), PAndNoEta a b → b := fun a b h => proj% PAndNoEta 1 h

/-! ## `hasEta` -/

/-- Structure eta for a type with `hasEta`. -/
good_def pPairEta : ∀ (x : PPair), Eq x (PPair.mk (proj% PPair 0 x) (proj% PPair 1 x)) :=
  fun x => unchecked (Eq.refl x)

/-- Structure eta for a type with `hasEta` and parameters. -/
good_def pBoxEta : ∀ (α : Type) (x : PBox α), Eq x (PBox.mk (proj% PBox 0 x)) :=
  fun α x => unchecked (Eq.refl x)

/-- A structure with projections, but without eta. -/
good_inductive { hasProjections := true, hasLargeElim := true } in
inductive NEPair : Type where
  | mk (a : Nat) (b : Bool)

/-- No structure eta for a type without `hasEta`. -/
bad_def nEPairEta : ∀ (x : NEPair), Eq x (NEPair.mk (proj% NEPair 0 x) (proj% NEPair 1 x)) :=
  fun x => unchecked (Eq.refl x)

/-- A type cannot have eta without projections. -/
bad_inductive { hasEta := true, hasLargeElim := true } via { hasLargeElim := true } in
inductive ENoProj : Type where
  | mk (a : Nat)

/-- A recursive type cannot have eta. -/
bad_inductive { hasProjections := true, hasEta := true, hasLargeElim := true }
  via { hasProjections := true, hasLargeElim := true } in
inductive ERec : Type where
  | mk (f : Nat → ERec)

/-- A recursive type can have projections. -/
good_inductive { hasProjections := true, hasLargeElim := true } in
inductive PRec : Type where
  | mk (n : Nat) (f : Nat → PRec)

/-- A unit-like type with eta. -/
good_inductive { hasProjections := true, hasEta := true, hasLargeElim := true } in
inductive EUnit : Type where
  | mk

/-- Any two values of a unit-like type with `hasEta` are definitionally equal. -/
good_def eUnitEq : ∀ (x y : EUnit), Eq x y := fun x y => unchecked (Eq.refl x)

/-- Every value of a unit-like type with `hasEta` is definitionally equal to its constructor. -/
good_def eUnitMk : ∀ (x : EUnit), Eq x EUnit.mk := fun x => unchecked (Eq.refl x)

/-- A unit-like type with projections, but without eta. -/
good_inductive { hasProjections := true, hasLargeElim := true } in
inductive NEUnit : Type where
  | mk

/--
Two values of a unit-like type without `hasEta` are not definitionally equal. Before the flags, this
held for every non-recursive type with one constructor without fields and no indices.
-/
bad_def nEUnitEq : ∀ (x y : NEUnit), Eq x y := fun x y => unchecked (Eq.refl x)

/-- A value of a unit-like type without `hasEta` is not definitionally equal to its constructor. -/
bad_def nEUnitMk : ∀ (x : NEUnit), Eq x NEUnit.mk := fun x => unchecked (Eq.refl x)

/-- A unit-like type without projections (and hence without eta). -/
good_inductive { hasLargeElim := true } in
inductive NPUnit : Type where
  | mk

/-- Two values of a unit-like type without `hasEta` are not definitionally equal. -/
bad_def nPUnitEq : ∀ (x y : NPUnit), Eq x y := fun x y => unchecked (Eq.refl x)

/-! ## Nested inductive types -/

/-
The containers are declared as usual, so that the elaborator can build its auxiliary constructions
for the nested types. It gives `NList` only large elimination, and `NBox` and `NPBox` projections,
eta and large elimination.
-/
inductive NList (α : Type) : Type where
  | nil
  | cons (a : α) (t : NList α)

inductive NBox (α : Type) : Type where
  | mk (x : α)

inductive NPBox (p : Prop) : Prop where
  | mk (h : p)

/-- A nested inductive type. -/
good_inductive { hasLargeElim := true } in
inductive NTree : Type where
  | node (cs : NList NTree)

/-- A nested inductive type without large elimination; its auxiliary type does not have it either. -/
good_inductive {} in
inductive NTreeSmall : Type where
  | node (cs : NList NTreeSmall)

/-- Nested through a structure; the auxiliary type for `NBox NBTree` gets projections, but no eta. -/
good_inductive { hasLargeElim := true } in
inductive NBTree : Type where
  | leaf
  | node (b : NBox NBTree)

/-- A nested inductive type with one constructor can have projections. -/
good_inductive { hasProjections := true, hasLargeElim := true } in
inductive NBProj : Type where
  | mk (n : Nat) (b : NBox NBProj)

/-- A nested inductive type is recursive, so it cannot have eta. -/
bad_inductive { hasProjections := true, hasEta := true, hasLargeElim := true }
  via { hasProjections := true, hasLargeElim := true } in
inductive NBEta : Type where
  | mk (n : Nat) (b : NBox NBEta)

/-- A proposition nested through a proposition with projections. -/
good_inductive {} in
inductive NPTree : Prop where
  | node (b : NPBox NPTree)
  | leaf

/--
An impredicative proposition nested through a proposition with projections: the auxiliary type for
`NPBox NPImpTree` would be impredicative (copied from `NPImpTree`) and have projections (copied from
`NPBox`), which is not allowed.
-/
bad_inductive { isImpredicative := true } via {} in
inductive NPImpTree : Prop where
  | node (b : NPBox NPImpTree)
  | leaf
