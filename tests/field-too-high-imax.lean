module
public import Lean
import all Lean.Environment

open Lean

private def addConstInfos [Monad m] [MonadEnv m] (cis : Array ConstantInfo) : m Unit := do
  for ci in cis do
    modifyEnv fun env => { env with
      base.public.constants.map₁ := env.base.public.constants.map₁.insert ci.name ci
      base.private.constants.map₁ := env.base.private.constants.map₁.insert ci.name ci
      checked := env.checked.map fun e => { e with constants := e.constants.insert ci.name ci }
    }

/-
`inductive Foo : Type 0` with `mk (a : Sort (imax 1 1)) : Foo`.

`imax 1 1 = max 1 1 = 1`, so the field's type is `Sort 1 = Type 0`, whose own
universe is `Sort 2`.  An inductive at `Type 0` (`Sort 1`) may not hold a field
whose type lives at `Sort 2` — this is the same test as the tutorial
`typeWithTooHighTypeField`.
-/
run_cmd do
  let n := `Foo
  let foo : Expr := .const n []
  -- field type Sort (imax 1 1) ≡ Sort 1 = Type 0 ; inductive Foo : Type 0
  let fieldTy : Expr := .sort (.imax (.succ .zero) (.succ .zero))
  let mkTy : Expr := .forallE `a fieldTy foo .default
  addConstInfos #[
    .inductInfo {
      name := n, levelParams := [], type := .sort (.succ .zero)   -- Foo : Type 0 (Sort 1)
      numParams := 0, numIndices := 0, all := [n], ctors := [n ++ `mk]
      numNested := 0, isRec := false, isUnsafe := false, isReflexive := false
    },
    .ctorInfo {
      name := n ++ `mk, levelParams := [], type := mkTy
      numParams := 0, induct := n, cidx := 0, numFields := 1, isUnsafe := false
    },
    -- placeholder recursor so lean4export assembles the full inductive block
    -- (cf. tutorial 066 dummyRecInfo); irrelevant to the field-universe check.
    .recInfo {
      name := n ++ `rec, levelParams := [], type := .sort 0, all := [n]
      numParams := 0, numIndices := 0, numMotives := 0, numMinors := 0
      rules := [], k := false, isUnsafe := false
    }
  ]
