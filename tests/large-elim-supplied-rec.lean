module
public import Lean
import all Lean.Environment

open Lean

/-- Non-dependent arrow `d → c`. -/
private def arrow (d c : Expr) : Expr := .forallE `a d c .default

/--
Insert raw `ConstantInfo`s straight into the environment, bypassing the kernel.

This is needed because the soundness bug we want to exhibit lives in a recursor
that does **large elimination of a `Prop`**: the inductive compiler will never
generate such a recursor, and `Declaration` has no constructor for a hand-built
one, so we cannot go through `addDecl` (even with `debug.skipKernelTC`). We hand
the malformed constants to the external checker directly via the export.
-/
private def addConstInfos [Monad m] [MonadEnv m] (cis : Array ConstantInfo) : m Unit := do
  for ci in cis do
    modifyEnv fun env => { env with
      base.public.constants.map₁ := env.base.public.constants.map₁.insert ci.name ci
      base.private.constants.map₁ := env.base.private.constants.map₁.insert ci.name ci
      checked := env.checked.map fun e => { e with constants := e.constants.insert ci.name ci }
    }

/-
We build, out of `Expr`:

  inductive PropTwo : Prop where | a | b
  PropTwo.rec : {motive : PropTwo → Sort u} → motive a → motive b → (t : PropTwo) → motive t
                                  ^^^^^^^^ large elimination — illegal for a 2-ctor Prop

and then, using that recursor:

  discriminate : PropTwo → Bool := PropTwo.rec (fun _ => Bool) true false
  decode       : Bool → Prop    := Bool.rec False True       -- decode true = True, decode false = False
  ab_eq        : PropTwo.a = PropTwo.b                       -- proof irrelevance
  discr_eq     : discriminate a = discriminate b             -- congrArg discriminate ab_eq
  falseViaLargeElim : False                                  -- transport True.intro along discr_eq

`discriminate a` reduces to `true` and `discriminate b` to `false`, so `discr_eq`
is really a proof of `true = false`; transporting `True.intro : decode true`
along it lands in `decode false = False`.
-/
run_cmd do
  let n := `PropTwo
  let P     : Expr := .const n []
  let a     : Expr := .const (n ++ `a) []
  let b     : Expr := .const (n ++ `b) []
  let prec  : Expr := .const (n ++ `rec) []
  let bool  : Expr := .const ``Bool []

  -- PropTwo.rec : {motive : PropTwo → Sort 1} → motive a → motive b → (t : PropTwo) → motive t
  let motiveTy : Expr := arrow P (.sort 1)
  let maTy     : Expr := .app (.bvar 0) a                  -- under [motive]
  let mbTy     : Expr := .app (.bvar 1) b                  -- under [motive, ma]
  let recTy : Expr :=
    .forallE `motive motiveTy
      (arrow (.app (.bvar 0) a)
        (arrow (.app (.bvar 1) b)
          (.forallE `t P (.app (.bvar 3) (.bvar 0)) .default)))
      .implicit
  -- reduction rules: rec motive ma mb a ↦ ma, rec motive ma mb b ↦ mb
  let rhsA : Expr := .lam `motive motiveTy (.lam `ma maTy (.lam `mb mbTy (.bvar 1) .default) .default) .implicit
  let rhsB : Expr := .lam `motive motiveTy (.lam `ma maTy (.lam `mb mbTy (.bvar 0) .default) .default) .implicit

  -- discriminate : PropTwo → Bool := PropTwo.rec (fun _ => Bool) true false
  let motiveBool : Expr := .lam `x P bool .default
  let discrVal : Expr :=
    .lam `x P (mkApp4 prec motiveBool (.const ``Bool.true []) (.const ``Bool.false []) (.bvar 0)) .default
  let discr : Expr := .const `discriminate []

  -- decode : Bool → Prop := Bool.rec (fun _ => Prop) False True
  let motiveProp : Expr := .lam `x bool (.sort 0) .default
  let decodeVal : Expr := mkApp3 (.const ``Bool.rec [1]) motiveProp (.const ``False []) (.const ``True [])
  let decode : Expr := .const `decode []

  -- ab_eq : @Eq PropTwo a b := @Eq.refl PropTwo a   (well-typed only by proof irrelevance)
  let abEqTy  : Expr := mkApp3 (.const ``Eq [0]) P a b
  let abEqVal : Expr := mkApp2 (.const ``Eq.refl [0]) P a
  let abEq : Expr := .const `ab_eq []

  -- discr_eq : @Eq Bool (discriminate a) (discriminate b) := congrArg discriminate ab_eq
  let discrA : Expr := .app discr a
  let discrB : Expr := .app discr b
  let discrEqTy  : Expr := mkApp3 (.const ``Eq [1]) bool discrA discrB
  let discrEqVal : Expr := mkAppN (.const ``congrArg [0, 1]) #[P, bool, a, b, discr, abEq]
  let discrEq : Expr := .const `discr_eq []

  -- falseViaLargeElim : False := discr_eq ▸ (True.intro : decode (discriminate a))
  let motiveEq : Expr :=
    .lam `x bool
      (.lam `h (mkApp3 (.const ``Eq [1]) bool discrA (.bvar 0)) (.app decode (.bvar 1)) .default)
      .default
  let falseVal : Expr :=
    mkAppN (.const ``Eq.rec [0, 1]) #[bool, discrA, motiveEq, .const ``True.intro [], discrB, discrEq]

  let mkDef (nm : Name) (type value : Expr) : ConstantInfo :=
    .defnInfo { name := nm, levelParams := [], type, value, hints := .opaque, safety := .safe }

  addConstInfos #[
    .inductInfo {
      name := n, levelParams := [], type := .sort 0
      numParams := 0, numIndices := 0, all := [n], ctors := [n ++ `a, n ++ `b]
      numNested := 0, isRec := false, isUnsafe := false, isReflexive := false
    },
    .ctorInfo {
      name := n ++ `a, levelParams := [], type := P
      numParams := 0, induct := n, cidx := 0, numFields := 0, isUnsafe := false
    },
    .ctorInfo {
      name := n ++ `b, levelParams := [], type := P
      numParams := 0, induct := n, cidx := 1, numFields := 0, isUnsafe := false
    },
    .recInfo {
      name := n ++ `rec, levelParams := [], all := [n], type := recTy
      numParams := 0, numIndices := 0, numMotives := 1, numMinors := 2
      rules := [ { ctor := n ++ `a, nfields := 0, rhs := rhsA },
                 { ctor := n ++ `b, nfields := 0, rhs := rhsB } ]
      k := false, isUnsafe := false
    },
    mkDef `discriminate (arrow P bool) discrVal,
    mkDef `decode (arrow bool (.sort 0)) decodeVal,
    mkDef `ab_eq abEqTy abEqVal,
    mkDef `discr_eq discrEqTy discrEqVal,
    mkDef `falseViaLargeElim (.const ``False []) falseVal
  ]
