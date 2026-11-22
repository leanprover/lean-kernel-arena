-- Kernel Nat-literal shift ops with shift counts exceeding 64-bit signed integers.
-- Both `Nat.shiftRight 42 (2^64)` and `Nat.shiftLeft 0 (2^64)` legitimately reduce
-- to `0`, without overflowing a machine-word shift count or computing `2^(2^64)`.
--
-- We test both closed applications (direct `rfl`) and open applications placed in
-- the major premise of `Nat.rec` (so closed-term evaluators cannot bypass the
-- kernel's `whnf` Nat-literal reduction path).

def const42 (_ : Nat) : Nat := nat_lit 42
def const0 (_ : Nat) : Nat := nat_lit 0

def isZero (k : Nat) : Prop :=
  Nat.rec (motive := fun _ => Prop) True (fun _ _ => False) k

theorem natShiftRightHuge :
    Nat.shiftRight (nat_lit 42) (nat_lit 18446744073709551616) = nat_lit 0 :=
  rfl

theorem natShiftLeftZeroHuge :
    Nat.shiftLeft (nat_lit 0) (nat_lit 18446744073709551616) = nat_lit 0 :=
  rfl

theorem natShiftRightHugeOpen (n : Nat) :
    isZero (Nat.shiftRight (const42 n) (nat_lit 18446744073709551616)) := by
  dsimp only [const42, isZero]
  exact True.intro

theorem natShiftLeftZeroHugeOpen (n : Nat) :
    isZero (Nat.shiftLeft (const0 n) (nat_lit 18446744073709551616)) := by
  dsimp only [const0, isZero]
  exact True.intro
