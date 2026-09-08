/-- The binary magma operation, written `◇`. -/
class Magma (α : Type _) where
  op : α → α → α

@[inherit_doc] infix:65 " ◇ " => Magma.op

namespace MemoFinOp

private def extractDigits (s : String) : List Nat :=
  s.toList.filterMap fun c =>
    if c.isDigit then some (c.toNat - '0'.toNat) else none

def finOpTable (s : String) (i j : Fin n) : Fin n :=
  let vals := extractDigits s
  let idx := i.val * n + j.val
  ⟨(vals.getD idx 0) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

end MemoFinOp

@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ ((x ◇ (y ◇ z)) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = x ◇ (((y ◇ x) ◇ y) ◇ z)

abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open MemoFinOp

def countermodel : Goal := by
  let m : Magma (Fin 4) := {
    op := finOpTable "[0,0,0,0],[0,0,2,3],[0,0,0,0],[0,1,2,0]"
  }
  refine ⟨Fin 4, m, ?_⟩
  decide
