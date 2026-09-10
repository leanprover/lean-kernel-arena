/-- The binary magma operation, written `◇`. -/
class Magma (α : Type _) where
  op : α → α → α

@[inherit_doc] infix:65 " ◇ " => Magma.op

@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ (w ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = x ◇ x

abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace countermodel

def op (x y : Fin 7) : Fin 7 :=
  ⟨Nat.mod (Nat.add (Nat.mul 0 x.val) (Nat.mul 0 y.val)) 7, Nat.mod_lt _ (by decide)⟩

instance inst : Magma (Fin 7) := ⟨op⟩

end countermodel

def countermodel : Goal := by
  refine ⟨Fin 7, countermodel.inst, ?_⟩
  constructor
  · decide
  · intro h
    exact (of_decide_eq_false rfl) (h (1 : Fin 7))
