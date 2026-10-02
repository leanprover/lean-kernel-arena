/-!
Distilled from a Palomar submission (roos-j/lean-spherical, theorem
`Auto.Spherical.RS.lintegral_pow_iSup_waveInt_le`), where two sums
`∑ ν ∈ Finset.range (2 ^ 17), …` under `Complex.re` are compared that differ
only in an instance argument.
-/

structure C where
  re : Nat
  im : Nat

def N : Nat := 2 ^ 17

-- Reducing `S _` to a constructor takes Θ(N) steps: `List.range N` is a
-- tail-recursive loop that has to finish before `foldr` can start.
def S (_ : Unit) : C := (List.range N).foldr (fun i acc => ⟨i + acc.re, 0⟩) ⟨0, 0⟩

def u : Unit := ()

theorem proj_cheap_struct : (S u).re = (S ()).re := rfl
