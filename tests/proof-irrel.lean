axiom A : Type
axiom a : A
axiom b : A
axiom P : Prop
axiom Q : P → Prop
axiom foo : ∀ h : A → P, Q (h b)
theorem bar : ∀ h : A → P, Q (h a) := foo
