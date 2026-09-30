/-!
A definitional equality under a projection whose structure argument is
stuck, distilled from con-leche's `ConLeche.nestRoot_datF._f` (a fuel-bridge
lemma of its own proof library, where the checker ran out of memory).

`step c n x : Nat × Nat` is structural recursion on the fuel `n`; for a
variable `x` every level is stuck on `match x`, and each of the two
branches reads `.1` of two recursive calls. The declaration to check is

    (step (id c) N x).1 = (step c N x).1   -- by rfl

The two sides differ only in the argument `id c` vs `c`. After unfolding
`Prod.fst`, a kernel that keeps a stuck projection's structure argument as it
is (the reference kernel: `reduce_proj` fails and `whnf_core` returns the
input) compares `step (id c) N x =?= step c N x` with `step` at the head of
both sides, tries the arguments first, and is done after one unfolding of
`id`. A kernel that replaces the stuck structure argument by its weak head
normal form (`(match x with …).1`) has lost the `step` head: it can only
compare the two unfolded bodies, whose branches hold the next level's
recursive calls under `.1` again, so it unrolls the whole recursion tree:
**exponential in N**.
-/

def step (c : Nat) : Nat → Nat → Nat × Nat
  | 0, x => (x + c, c)
  | n+1, x => match x with
    | 0 => ((step c n 1).1 + (step c n 2).1, 0)
    | k+1 => ((step c n k).1 + (step c n (k+2)).1, k)

theorem step12 (c x : Nat) : (step (id c) 12 x).1 = (step c 12 x).1 := rfl
theorem step16 (c x : Nat) : (step (id c) 16 x).1 = (step c 16 x).1 := rfl
theorem step20 (c x : Nat) : (step (id c) 20 x).1 = (step c 20 x).1 := rfl
