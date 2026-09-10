/-
Projecting data out of a `Prop`, exploiting that a kernel can disagree with
itself about whether the structure lives in `Prop`.

As in `rec-missing-ih.lean`, `RecClass.rcA`, `rcB` and `rcC` are three functions
`Bool → Bool` for which definitional equality is not transitive (`rcA ≡ rcB` and
`rcB ≡ rcC` by proof irrelevance on an `Acc` argument, but `rcA ≢ rcC`), and in
the affected kernels the union-find defeq cache closes that relation
transitively while only being consulted for expressions with equal hashes.  So
whether `rcA ≡ rcC` holds depends on the hash of the surrounding term, and the
constants and paddings here are chosen so that the hashes collide exactly for
the free variable `_kernel_fresh.0`.

`Native64ResultSortGate` is a K-like inductive predicate whose `rec` is used as
the *result sort* of the inductive family `Native64ResultSortOwner`: the sort
`Gate.rec x (fun .. => Type) Prop requested h` reduces to `Prop` only if the
requested indices are definitionally equal to those of `Gate.intro`.  This is
made to happen in one context and to fail in another:

* `Native64ResultSort.asProp` is checked against a *constant* standing for
  `∀ x h, Prop`, so `_kernel_fresh.0` is introduced for `x` — the hashes collide,
  `Owner x h : Prop` is accepted, and `Native64ResultSortLeak.proposition` is a
  genuine `Prop` as far as every later declaration is concerned.
* `Native64ResultSortLeak.observe` projects field 0 out of that proposition.  Here
  the sort of the closed term `Owner false closedGate` is needed, and that one is
  stuck (no free variable, hence no collision), so the affected kernels do not
  see a proposition and permit the projection of the `Bool` field.

Proof irrelevance then identifies two `Owner.mk` applications with different
`Bool` fields, and observing them gives `False`.
-/
import Lean

open Lean

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option debug.skipKernelTC true

namespace RecClass

def rcStep (x : Bool) (n : Nat) (ih : (m : Nat) → m < n → Bool) : Bool :=
  match n with
  | 0 => x
  | k + 1 => ih k (Nat.lt_succ_self k)

def rcRun (x : Bool) (n : Nat) (h : Acc (· < ·) n) : Bool :=
  Acc.rec (fun m _ => rcStep x m) h

opaque rcOpaque : Acc (· < ·) 1 := Nat.lt_wfRel.wf.apply 1
def rcA (x : Bool) := rcRun x 1 rcOpaque
def rcB (x : Bool) := rcRun x 1 (Acc.intro 1 fun _ => Acc.inv rcOpaque)
def rcC (x : Bool) := rcRun x 0 (Acc.inv rcOpaque (Nat.lt_succ_self 0))

theorem run_eq (x : Bool) (n : Nat) (h : Acc (· < ·) n) : rcRun x n h = x := by
  induction h with
  | intro n smaller ih =>
    cases n with
    | zero => rfl
    | succ n => simpa only [rcRun, rcStep] using ih n (Nat.lt_succ_self n)

theorem a_eq (x : Bool) : rcA x = x := run_eq x _ _
theorem b_eq (x : Bool) : rcB x = x := run_eq x _ _
theorem c_eq (x : Bool) : rcC x = x := run_eq x _ _

theorem transport (G : Bool → Bool → Bool → Bool → Prop)
    (a b c : Bool) (ab : a = b) (bc : b = c) (h : G c b a c) : G b a a a := by
  cases ab
  cases bc
  exact h

theorem observedProofsFalse (P : Prop) (observe : P → Bool) (p q : P)
    (onFalse : observe p = false) (onTrue : observe q = true) : False := by
  have same : p = q := proof_irrel p q
  exact Bool.noConfusion (onFalse.symm.trans ((congrArg observe same).trans onTrue))

end RecClass

namespace Core64SortRepro

private def a : Name := .num (.num `Native64SortGateA 1) 2023879994
private def b : Name := .num (.num `Native64SortGateB 0) 3766726852
private def c : Name := .num (.num `Native64SortGateC 2) 1809645719
private def gate : Name := `Native64ResultSortGate
private def owner : Name := `Native64ResultSortOwner
private def bool := mkConst ``Bool

private def checked (env : Environment) (decl : Declaration) : CoreM Environment := do
  match env.addDeclCore 800000 decl none (doCheck := false) with
  | .ok next => return next
  | .error err => throwError "{err.toMessageData (← getOptions)}"

private def define (env : Environment) (name : Name) (type value : Expr) :
    CoreM Environment :=
  checked env (.defnDecl {
    name, levelParams := [], type, value, hints := .abbrev, safety := .safe })

private def pad (salt : Nat) (e : Expr) : Expr :=
  mkApp (mkLambda `salt .default (mkConst ``Nat) (e.liftLooseBVars 0 1)) (mkNatLit salt)

private def values (x : Expr) : Array Expr :=
  let px := pad 125330 x
  let qx := pad 26537 (mkApp (mkLambda `z .default bool (.bvar 0)) x)
  #[mkApp (mkConst a) px, mkApp (mkConst b) px, mkApp (mkConst c) qx]

private def canonical (v : Array Expr) : Array Expr := #[v[2]!, v[1]!, v[0]!, v[2]!]
private def requested (v : Array Expr) : Array Expr := #[v[1]!, v[0]!, v[0]!, v[0]!]
private def gateType (x : Expr) : Expr :=
  mkAppN (mkConst gate) (#[x] ++ requested (values x))

private def gateDecl : Declaration :=
  let x := mkBVar 0
  let result := mkAppN (mkConst gate) (#[x] ++ canonical (values x))
  .inductDecl [] 1 [{
    name := gate
    type := (List.range 5).foldr (fun _ body => mkForall `bit .default bool body) (mkSort 0)
    ctors := [{name := .str gate "intro", type := mkForall `x .default bool result}]
  }] false

private def resultSort (x h : Expr) : Expr :=
  let majorType := mkAppN (mkConst gate)
    #[x.liftLooseBVars 0 4, .bvar 3, .bvar 2, .bvar 1, .bvar 0]
  let motive := (List.range 4).foldr
    (fun _ body => mkLambda `index .default bool body)
    (mkLambda `proof .default majorType (mkSort 1))
  mkAppN (mkConst (.str gate "rec") [Level.succ (Level.succ Level.zero)])
    (#[x, motive, mkSort 0] ++ requested (values x) ++ #[h])

private def ownerDecl : Declaration :=
  let type := mkForall `x .default bool <|
    mkForall `h .default (gateType (.bvar 0)) (resultSort (.bvar 1) (.bvar 0))
  let result := mkApp2 (mkConst owner) (.bvar 2) (.bvar 1)
  let ctorType := mkForall `x .default bool <|
    mkForall `h .default (gateType (.bvar 0)) <| mkForall `bit .default bool result
  .inductDecl [] 2 [{
    name := owner, type
    ctors := [{name := .str owner "mk", type := ctorType}]
  }] false

private def symm (left right proof : Expr) : Expr :=
  mkAppN (mkConst ``Eq.symm [(Level.succ Level.zero)]) #[bool, left, right, proof]
private def trans (left middle right first second : Expr) : Expr :=
  mkAppN (mkConst ``Eq.trans [(Level.succ Level.zero)]) #[bool, left, middle, right, first, second]

private def closedWitness (x : Expr) : Expr :=
  let v := values x
  let av := v[0]!
  let bv := v[1]!
  let cv := v[2]!
  let ae := mkApp (mkConst ``RecClass.a_eq) av.appArg!
  let be := mkApp (mkConst ``RecClass.b_eq) bv.appArg!
  let ce := mkApp (mkConst ``RecClass.c_eq) cv.appArg!
  mkAppN (mkConst ``RecClass.transport)
    #[mkApp (mkConst gate) x, av, bv, cv,
      trans av x bv ae (symm bv x be),
      trans bv x cv be (symm cv x ce),
      mkApp (mkConst (.str gate "intro")) x]

run_meta do
  let mut env ← getEnv
  for (name, value) in [(a, ``RecClass.rcA), (b, ``RecClass.rcB), (c, ``RecClass.rcC)] do
    env ← checked env (.defnDecl {
      name, levelParams := [], type := mkForall `x .default bool bool,
      value := mkConst value, hints := .regular 1021, safety := .safe })
  env ← checked env gateDecl
  env ← checked env ownerDecl

  -- Check the generic Prop alias while its first local is _kernel_fresh.0.
  -- Hiding its function type behind a constant preserves that local numbering.
  let aliasType := mkForall `x .default bool <|
    mkForall `h .default (gateType (.bvar 0)) (mkSort 0)
  let .ok aliasSort := Kernel.check env {} aliasType | throwError "invalid alias type"
  env ← define env `Native64ResultSort.asPropType aliasSort aliasType
  let body := mkApp2 (mkConst ``id [(Level.succ Level.zero)]) (mkSort 0)
    (mkApp2 (mkConst owner) (.bvar 1) (.bvar 0))
  let value := mkLambda `x .default bool <|
    mkLambda `h .default (gateType (.bvar 0)) body
  env ← define env `Native64ResultSort.asProp (mkConst `Native64ResultSort.asPropType) value

  let falseBit := mkConst ``Bool.false
  let trueBit := mkConst ``Bool.true
  env ← checked env (.opaqueDecl {
    name := `Native64ResultSort.closedGate, levelParams := [],
    type := gateType falseBit, value := closedWitness falseBit, isUnsafe := false })
  let h := mkConst `Native64ResultSort.closedGate
  let carrier := mkApp2 (mkConst `Native64ResultSort.asProp) falseBit h
  env ← define env `Native64ResultSortLeak.proposition (mkSort 0) carrier
  let prop := mkConst `Native64ResultSortLeak.proposition

  -- The proposition is genuine, but infer_proj treats its stuck inferred sort
  -- as permission to extract the constructor's hidden Bool field.
  env ← define env `Native64ResultSortLeak.observe
    (mkForall `p .default prop bool)
    (mkLambda `p .default prop (mkProj owner 0 (.bvar 0)))
  let ctor := mkApp2 (mkConst (.str owner "mk")) falseBit h
  env ← define env `Native64ResultSortLeak.falseProof prop (mkApp ctor falseBit)
  env ← define env `Native64ResultSortLeak.trueProof prop (mkApp ctor trueBit)
  let refl (bit : Expr) := mkApp2 (mkConst ``Eq.refl [(Level.succ Level.zero)]) bool bit
  env ← checked env (.thmDecl {
    name := `inconsistent, levelParams := [], type := mkConst ``False,
    value := mkAppN (mkConst ``RecClass.observedProofsFalse)
      #[prop, mkConst `Native64ResultSortLeak.observe,
        mkConst `Native64ResultSortLeak.falseProof, mkConst `Native64ResultSortLeak.trueProof,
        refl falseBit, refl trueBit] })
  setEnv env

  -- Self-checks, so that this test fails loudly rather than silently becoming
  -- benign if a future toolchain changes hashing or the fresh-variable numbering.
  let collide (x : Expr) : Bool := (values x)[0]!.hash == (values x)[2]!.hash
  unless collide (.fvar ⟨.num `_kernel_fresh 0⟩) do
    logWarning "required collision at _kernel_fresh.0 changed"
  if collide falseBit then
    logWarning "unexpected collision for the closed instantiation"
  unless Kernel.isDefEq env {} (resultSort falseBit h) (mkSort 0) matches .ok false do
    logWarning "the result sort of Native64ResultSortOwner is no longer stuck"
  logInfo "Native64ResultSortOwner's result sort is a Prop under `_kernel_fresh.0` \
    and stuck for the closed term; field 0 of the resulting proposition is a Bool."

end Core64SortRepro
