module
public import Lean
import all Lean.Environment

open Lean

private def arrow (d c : Expr) : Expr := .forallE `a d c .default

private def addConstInfos [Monad m] [MonadEnv m] (cis : Array ConstantInfo) : m Unit := do
  for ci in cis do
    modifyEnv fun env => { env with
      base.public.constants.map₁ := env.base.public.constants.map₁.insert ci.name ci
      base.private.constants.map₁ := env.base.private.constants.map₁.insert ci.name ci
      checked := env.checked.map fun e => { e with constants := e.constants.insert ci.name ci }
    }

/-
A 2-constructor inductive whose sort is `Sort (imax 1 0)`.  Since `imax _ 0 = 0`
for every right argument, this IS `Prop` — but it is not *syntactically* `Sort 0`.
It is shipped with a large-elimination recursor (motive into `Sort 1`), which is
unsound for a ≥2-ctor Prop and which Lean rejects.
-/
run_cmd do
  let n := `ImaxProp
  let prop : Expr := .sort (.imax (.succ .zero) .zero)   -- Sort (imax 1 0) ≡ Prop
  let P    : Expr := .const n []
  let a    : Expr := .const (n ++ `a) []
  let b    : Expr := .const (n ++ `b) []

  -- ImaxProp.rec : {motive : ImaxProp → Sort 1} → motive a → motive b → (t) → motive t
  let motiveTy : Expr := arrow P (.sort 1)
  let recTy : Expr :=
    .forallE `motive motiveTy
      (arrow (.app (.bvar 0) a)
        (arrow (.app (.bvar 1) b)
          (.forallE `t P (.app (.bvar 3) (.bvar 0)) .default)))
      .implicit
  let rhsA : Expr := .lam `motive motiveTy (.lam `ma (.app (.bvar 0) a) (.lam `mb (.app (.bvar 1) b) (.bvar 1) .default) .default) .implicit
  let rhsB : Expr := .lam `motive motiveTy (.lam `ma (.app (.bvar 0) a) (.lam `mb (.app (.bvar 1) b) (.bvar 0) .default) .default) .implicit

  addConstInfos #[
    .inductInfo {
      name := n, levelParams := [], type := prop
      numParams := 0, numIndices := 0, all := [n], ctors := [n ++ `a, n ++ `b]
      numNested := 0, isRec := false, isUnsafe := false, isReflexive := false
    },
    .ctorInfo { name := n ++ `a, levelParams := [], type := P, numParams := 0, induct := n, cidx := 0, numFields := 0, isUnsafe := false },
    .ctorInfo { name := n ++ `b, levelParams := [], type := P, numParams := 0, induct := n, cidx := 1, numFields := 0, isUnsafe := false },
    .recInfo {
      name := n ++ `rec, levelParams := [], all := [n], type := recTy
      numParams := 0, numIndices := 0, numMotives := 1, numMinors := 2
      rules := [ { ctor := n ++ `a, nfields := 0, rhs := rhsA },
                 { ctor := n ++ `b, nfields := 0, rhs := rhsB } ]
      k := false, isUnsafe := false
    }
  ]
