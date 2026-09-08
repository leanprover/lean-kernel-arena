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

@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (((z ◇ w) ◇ y) ◇ x) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ (z ◇ y)) ◇ x) ◇ y

abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G

set_option maxHeartbeats 10000000

open MemoFinOp

set_option maxRecDepth 10000 in
def countermodel : Goal := by
  let m : Magma (Fin 9) := {
    op := finOpTable "[0,1,2,3,4,5,7,8,6],[7,1,2,3,4,5,6,8,0],[1,8,2,3,4,5,6,7,0],[1,2,0,3,4,5,6,7,8],[0,2,3,1,4,5,6,7,8],[0,1,3,4,2,5,6,7,8],[0,1,2,4,5,3,6,7,8],[0,1,2,3,5,6,4,7,8],[0,1,2,3,4,6,7,5,8]"
  }
  refine ⟨Fin 9, m, ?_⟩
  decide
