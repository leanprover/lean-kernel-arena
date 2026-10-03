/-!
The counterpart of `proj-cheap-struct`: two projections whose structs are
*not* equal, but whose projected fields are.
-/

def loop : Nat → Nat → Nat
  | 0, acc => acc
  | n+1, acc => loop n (acc + 1)

-- Θ(n) to evaluate
def slow (n : Nat) : Nat := loop n 0

def P (a : Nat) : Nat × Nat := (0, a)
def Q (a : Nat) : Nat × Nat := (0, a)

theorem proj_lazy_struct : (P (slow 100000)).1 = (Q (slow 100001)).1 := rfl
