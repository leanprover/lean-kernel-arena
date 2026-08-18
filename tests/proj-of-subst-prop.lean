/-
Projecting data out of a `Prop`, by substituting a proof of one proposition for
a proof of a definitionally equal one.

`a`, `b` and `c` are three `Bool`s built from `Acc.rec` for which definitional
equality is not transitive: `a ≡ b` and `b ≡ c` (proof irrelevance on the `Acc`
argument, `b` after some iota steps), but `a ≢ c`.  Consequently `P := a = b`
and `Q := a = c` are definitionally equal types whose inhabitants behave
differently under `Eq.rec`:

* `gate h`, for `h : P`, K-reduces to `Prop`, since that reduction only needs
  the type of `h` to match the type `a = a` of `Eq.refl a`, i.e. `b ≡ a`.
* `gate witness`, for the closed `witness : Q`, stays stuck, as that would need
  `c ≡ a`.

So the inductive family `Owner : ∀ (h : P), gate h` is a family of propositions
— its recursor only eliminates into `Prop` — while `Owner witness`, which is
well-typed because `Q ≡ P`, is a type whose sort does not reduce to `Prop`.  The
projection `observe` then extracts the `Bool` field from an inhabitant of that
proposition, and proof irrelevance identifies two inhabitants carrying different
`Bool`s.

Nothing here depends on the kernel's definitional-equality cache: the
comparisons above come out the same way in fresh type-checker sessions.
-/
import Lean

open Lean

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option debug.skipKernelTC true

namespace PR14806Subst

def step (x : Bool) (n : Nat) (ih : (m : Nat) → m < n → Bool) : Bool :=
  match n with
  | 0 => x
  | k + 1 => ih k (Nat.lt_succ_self k)

def run (x : Bool) (n : Nat) (h : Acc (· < ·) n) : Bool :=
  Acc.rec (fun m _ => step x m) h

opaque seed : Acc (· < ·) 1 := Nat.lt_wfRel.wf.apply 1
def a := run false 1 seed
def b := run false 1 (Acc.intro 1 fun _ => Acc.inv seed)
def c := run false 0 (Acc.inv seed (Nat.lt_succ_self 0))

theorem run_eq (x : Bool) (n : Nat) (h : Acc (· < ·) n) : run x n h = x := by
  induction h with
  | intro n smaller ih =>
    cases n with
    | zero => rfl
    | succ n => simpa only [run, step] using ih n (Nat.lt_succ_self n)

def P : Prop := a = b
def Q : Prop := a = c
def R : Prop := a = a

opaque witness : Q := (run_eq false _ _).trans (run_eq false _ _).symm

def gate (h : P) : Type :=
  Eq.rec (motive := fun _ _ => Type) Prop h

theorem observedProofsFalse (T : Prop) (observe : T → Bool) (p q : T)
    (onFalse : observe p = false) (onTrue : observe q = true) : False := by
  have same : p = q := proof_irrel p q
  exact Bool.noConfusion (onFalse.symm.trans ((congrArg observe same).trans onTrue))

private def checked (env : Environment) (decl : Declaration) : CoreM Environment := do
  match env.addDeclCore 0 decl none (doCheck := false) with
  | .ok next => return next
  | .error err => throwError "{err.toMessageData (← getOptions)}"

private def define (env : Environment) (name : Name) (type value : Expr) : CoreM Environment :=
  checked env (.defnDecl {
    name := name, levelParams := [], type := type, value := value,
    hints := .abbrev, safety := .safe })

end PR14806Subst

run_meta do
  let mut env ← getEnv
  let owner := `PR14806Subst.Owner
  let p := mkConst ``PR14806Subst.P
  let bool := mkConst ``Bool
  let gate := mkConst ``PR14806Subst.gate
  let ownerType := mkForall `h .default p (mkApp gate (.bvar 0))
  let ctorType := mkForall `h .default p <|
    mkForall `bit .default bool (mkApp (mkConst owner) (.bvar 1))
  env ← PR14806Subst.checked env (.inductDecl [] 1 [{
    name := owner, type := ownerType,
    ctors := [{name := .str owner "mk", type := ctorType}]
  }] false)
  let some (.recInfo ri) := env.toKernelEnv.find? (mkRecName owner)
    | throwError "missing owner recursor"
  unless ri.levelParams.isEmpty do
    logWarning "Owner unexpectedly permits large elimination"

  env ← PR14806Subst.define env `PR14806Subst.asProp
    (mkForall `h .default p (mkSort 0))
    (mkLambda `h .default p (mkApp (mkConst owner) (.bvar 0)))
  let witness := mkConst ``PR14806Subst.witness
  let carrier := mkApp (mkConst `PR14806Subst.asProp) witness
  env ← PR14806Subst.define env `PR14806Subst.proposition (mkSort 0) carrier
  let prop := mkConst `PR14806Subst.proposition
  env ← PR14806Subst.define env `PR14806Subst.observe
    (mkForall `proof .default prop bool)
    (mkLambda `proof .default prop (mkProj owner 0 (.bvar 0)))
  let ctor := mkApp (mkConst (.str owner "mk")) witness
  let falseBit := mkConst ``Bool.false
  let trueBit := mkConst ``Bool.true
  env ← PR14806Subst.define env `PR14806Subst.falseProof prop (mkApp ctor falseBit)
  env ← PR14806Subst.define env `PR14806Subst.trueProof prop (mkApp ctor trueBit)
  let refl (bit : Expr) := mkApp2 (mkConst ``Eq.refl [(Level.succ Level.zero)]) bool bit
  env ← PR14806Subst.checked env (.thmDecl {
    name := `inconsistent, levelParams := [], type := mkConst ``False,
    value := mkAppN (mkConst ``PR14806Subst.observedProofsFalse)
      #[prop, mkConst `PR14806Subst.observe,
        mkConst `PR14806Subst.falseProof, mkConst `PR14806Subst.trueProof,
        refl falseBit, refl trueBit] })
  setEnv env
  logInfo m!"Owner is a family of propositions, yet a Bool was projected out of \
    PR14806Subst.proposition; axioms of `inconsistent`: {(← collectAxioms `inconsistent)}"
