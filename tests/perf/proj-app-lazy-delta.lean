import Lean

/-!
From leanprover/lean4#16613: comparing two *applied* projections `s.1 a =?= t.1 a`,
where one delta step makes `s` and `t` syntactically equal, but reducing either
structure to a constructor is expensive.

The theorems are added with `addDecl`, so that only the kernel checks that the
hypothesis and the conclusion agree; the elaborator never compares them.
-/

open Lean Meta Elab Term

/-- A structure with one predicate field, like Mathlib's `Set`. -/
structure PSet (α : Type) where
  Mem : α → Prop

instance : Membership α (PSet α) := ⟨fun s a => s.Mem a⟩

def loop : Nat → Nat → Nat
  | 0, acc => acc
  | n+1, acc => loop n (acc + 1)

/-- Θ(n) to evaluate. -/
def slow (n : Nat) : Nat := loop n 0

/-- Reducing `big n` to a constructor evaluates `slow n`. -/
def big (n : Nat) : PSet Nat :=
  match slow n with
  | 0 => ⟨fun _ => True⟩
  | _ => ⟨fun a => a = 0⟩

/-- `small` unfolds to `big 100000` in one delta step. -/
def small : PSet Nat := big 100000

/-- Add the theorem `fun xs h => h : ∀ xs, P → Q` with `addDecl`. -/
def addIdentityTheorem (name : Name) (stmt : Term) : TermElabM Unit := do
  let type ← elabType stmt
  synthesizeSyntheticMVarsNoPostponing
  let type ← instantiateMVars type
  let value ← forallTelescope type fun xs _ => mkLambdaFVars xs xs.back!
  addDecl (.thmDecl { name, levelParams := [], type, value })

elab "#add_identity_theorem " name:ident " : " stmt:term : command =>
  Command.liftTermElabM <| addIdentityTheorem name.getId stmt

-- `a ∈ small` unfolds to the applied projection `small.1 a`.
#add_identity_theorem proj_app_lazy_delta : ∀ a : Nat, a ∈ small → a ∈ big 100000
