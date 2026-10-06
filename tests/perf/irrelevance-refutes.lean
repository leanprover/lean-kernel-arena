/-!
Two proofs of different propositions, each a recursion over a literal, as the
last arguments of two applications of one function. A checker that reaches the
proofs must take proof irrelevance's negative answer as final: two proofs of
propositions that are not defeq are not defeq. Unfolding the proofs instead
evaluates the recursions.

Distilled from `decide +kernel` on `Rat` arithmetic, where the proofs are
`Nat.gcd_dvd` terms by well-founded recursion.
-/

-- Θ(m) to unfold to `rfl`
noncomputable def slowRefl (m : Nat) : m = m :=
  Nat.rec (motive := fun _ => m = m) rfl (fun _ ih => ih) m

-- ignores both arguments
def f (m : Nat) (_h : m = m) : Nat := 0

theorem irrelevance_refutes : f 100000 (slowRefl 100000) = f 100001 (slowRefl 100001) := rfl
