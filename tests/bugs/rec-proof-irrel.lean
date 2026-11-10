module

public import Lean
import all Lean.Environment

open Lean Elab Command Meta

/-!
Each `bad*` theorem below is a proof of `False` from a forged recursor: a
right-hand side of a rule, or the recursor's type, contains an ill-typed proof.

A checker that compares such data with the data it derives itself up to
definitional equality, without type checking it first, can be fooled by proof
irrelevance: two proofs are equal if their types are, and when inferring a
type in "infer only" mode, a checker typically does not check the arguments of
an application. So the forgery has the right type as far as the comparison can
tell.

The tests `bugs/rec-rule-proof-irrel`, `bugs/rec-rule-proof-irrel-nested` and
`bugs/rec-type-proof-irrel` each export one of the `bad*` theorems.
-/

-- Otherwise Lean turns the index of `Box` into a parameter
set_option inductive.autoPromoteIndices false in
/--
A proposition whose proofs carry a `Bool` that can be read back: the field of
`Box.mk` occurs in the index, so `Box` eliminates into every universe.
-/
public inductive Box : Bool → Prop
  | mk (b : Bool) : Box b

public noncomputable def read {b : Bool} (h : Box b) : Bool :=
  Box.rec (motive := fun _ _ => Bool) (fun b => b) h

public theorem read_eq {b : Bool} (h : Box b) : read h = b :=
  Box.rec (motive := fun b h => read h = b) (fun _ => rfl) h

public noncomputable def IsTrue (b : Bool) : Prop :=
  Bool.rec (motive := fun _ => Prop) False True b

/-- A proof of `Box false` that reduces to `Box.mk true` gives `False`. -/
public theorem key (h : Box false) (e : read h = true) : False :=
  Eq.subst (motive := IsTrue) (e.symm.trans (read_eq h)) True.intro

/-- Replace a constant in the environment, without checking it. -/
meta def forge (ci : ConstantInfo) : CommandElabM Unit :=
  modifyEnv fun env => { env with
    base.public.constants.map₁ := env.base.public.constants.map₁.insert ci.name ci
    base.private.constants.map₁ := env.base.private.constants.map₁.insert ci.name ci
    checked := env.checked.map fun e => { e with constants := e.constants.insert ci.name ci }
  }

/--
In the rule of `recName` for `ctor`, replace the body of the right-hand side,
a proof of some `T`, by `forgery T`.
-/
meta def forgeRule (recName ctor : Name) (forgery : Expr → Expr) : CommandElabM Unit := do
  let ci ← liftTermElabM do
    let .recInfo rv ← getConstInfo recName | throwError "{recName} is not a recursor"
    let rules ← rv.rules.mapM fun r => do
      if r.ctor != ctor then return r
      let rhs ← lambdaTelescope r.rhs fun xs body => do
        mkLambdaFVars xs (forgery (← inferType body))
      return { r with rhs }
    return ConstantInfo.recInfo { rv with rules }
  forge ci

/-- `Box.mk true`, a proof of `Box true` -/
meta def boxMkTrue : Expr := mkApp (mkConst ``Box.mk) (mkConst ``Bool.true)

/-- `@id T (Box.mk true)`, which a checker that does not check the argument takes for a proof of `T` -/
meta def fakeApp (T : Expr) : Expr := mkApp2 (mkConst ``id [.zero]) T boxMkTrue

/-
The proofs of `Box false` that reduce to `Box.mk true` are definitions rather
than theorems, so that the elaborator unfolds them when checking `bad*`.
-/
set_option linter.defProp false

/-! ## Rule

`J` has two constructors, so `J.rec` eliminates only into `Prop`, and the
right-hand sides of its rules are proofs. The rule for `J.j1` becomes
```
J.rec motive h₁ h₂ J.j1  ↦  @id (motive J.j1) (Box.mk true)
```
which infers to `motive J.j1` as long as the argument of `id` is not checked.
Then `junkApp : Box false` reduces to `Box.mk true`.
-/

public inductive J : Prop
  | j1 | j2

public noncomputable def junkApp : Box false :=
  J.rec (motive := fun _ => Box false) (Box.mk false) (Box.mk false) J.j1

run_cmd forgeRule ``J.rec ``J.j1 fakeApp

public theorem badApp : False := key junkApp rfl

/-! ## Rule of a nested inductive

As in the first case, but for the auxiliary recursor of a nested inductive,
which checkers often handle separately. `N` is nested through `And`, so the
auxiliary type `N ∧ N` is a `Prop` as well, and `N` has two constructors, so
it eliminates only into `Prop`. The rule of `N.rec_1` for `And.intro` becomes
```
N.rec_1 motive_1 motive_2 n1 n2 intro (And.intro l r)
  ↦  @id (motive_2 (And.intro l r)) (Box.mk true)
```
-/

public inductive N : Prop
  | n1 : N
  | n2 : N ∧ N → N

public noncomputable def junkNested : Box false :=
  N.rec_1 (motive_1 := fun _ => True) (motive_2 := fun _ => Box false)
    trivial (fun _ _ => trivial) (fun _ _ _ _ => Box.mk false) ⟨N.n1, N.n1⟩

run_cmd forgeRule ``N.rec_1 ``And.intro fakeApp

public theorem badNested : False := key junkNested rfl

/-! ## Type of the recursor

`Q` is indexed by a proof, so the minor premise of `Q.rec` mentions one:
```
Q.rec : {motive : (h : Box false) → Q h → Sort u} → motive (Box.mk false) Q.mk →
  {h : Box false} → (t : Q h) → motive h t
```
In the type of the minor premise, replace `Box.mk false` by
`@id (Box false) (Box.mk true)`. Then `rfl` proves the minor premise for the
motive `fun h _ => read h = true`, and `Q.rec` turns that into
`read (Box.mk false) = true`.
-/

public inductive Q : Box false → Prop
  | mk : Q (Box.mk false)

run_cmd do
  let ci ← liftTermElabM do
    let .recInfo rv ← getConstInfo ``Q.rec | throwError "Q.rec is not a recursor"
    let boxMkFalse := mkApp (mkConst ``Box.mk) (mkConst ``Bool.false)
    let fake := fakeApp (← inferType boxMkFalse)
    let type := rv.type.replace fun e => if e == boxMkFalse then some fake else none
    if type == rv.type then throwError "Box.mk false does not occur in the type of Q.rec"
    return ConstantInfo.recInfo { rv with type }
  forge ci

-- `rfl` with an explicit type, as the inferred one would contain the ill-typed proof
public theorem badRecType : False :=
  key (Box.mk false) (Q.rec (motive := fun h _ => read h = true) (rfl : true = true) Q.mk)
