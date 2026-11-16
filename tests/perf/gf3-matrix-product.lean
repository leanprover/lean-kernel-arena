/-!
# GF(3) matrix products by kernel reduction

A self-contained kernel benchmark, modelled on the theorem `ck97` of the CFSG module
`Certificates.Kernel.Sporadic.Fi24Seven.C06` (AxiomMath/CFSG).  `ck97` checks one chunk of a
straight-line program over 781×781 matrices over GF(3): it multiplies the matrices along a word
(`prodV`) with `mul3s`, by kernel reduction.  This file keeps that computation and nothing else:

* `mul3s` and `mulLoop3` are CFSG's (`CFSG/Certificates/Kernel/Orders/Mat3.lean`), unchanged.  A
  matrix is a pair of bit-sliced `Nat`s of 609961 bits each (`x1 + x2 <<< N`: the entries equal to 1,
  the entries equal to 2), row-major.  One product runs 781 steps; each step shifts, masks,
  multiplies and xors numbers of about 609961 bits.
* `prodV` is CFSG's (`Certificates/Data/Kernel/Spor/SlpMat.lean`): the right fold of `MUL` over
  the letters of a word, one product per letter after the first.
* `word` is the letter pattern of `ck97`'s node (87 letters over the chunk's 14 inputs).  The
  inputs are not CFSG's matrices: `G k` is generated here from two powers `Nat.pow b 32000`.
* The theorem states the product of the first 4 letters (3 products), modulo 2^61 - 1.  The
  fingerprint was computed outside Lean (the same algorithm in Python, itself checked against
  schoolbook GF(3) multiplication).

The kernel's whnf caches keep every product's intermediates until the end of the declaration,
so the memory grows with the number of products, about 1 GiB each.  The official kernel
(v4.35.0) checks `big` in about 17 G instructions and 3.5 GiB.
-/

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option debug.skipKernelTC true

namespace Gf3Bench

noncomputable def strictN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k 0) (fun n _ => k (Nat.succ n)) y

noncomputable def mulLoop3 (d N CI RM A1 A2 B1 B2 : Nat) : Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ x1 x2 => Nat.add x1 (Nat.shiftLeft x2 N))
    (fun _ ih k x1 x2 =>
      (fun a1 a2 b1 b2 => (fun q m => (fun t => strictN (Nat.xor (Nat.lor x2 m) t) (fun z1 =>
          strictN (Nat.xor (Nat.lor x1 q) t) (fun z2 => ih (Nat.succ k) z1 z2)))
          (Nat.xor (Nat.lor x1 m) (Nat.lor x2 q)))
        (Nat.add (Nat.mul a1 b1) (Nat.mul a2 b2)) (Nat.add (Nat.mul a1 b2) (Nat.mul a2 b1)))
      (Nat.land (Nat.shiftRight A1 k) CI) (Nat.land (Nat.shiftRight A2 k) CI)
      (Nat.land (Nat.shiftRight B1 (Nat.mul d k)) RM) (Nat.land (Nat.shiftRight B2 (Nat.mul d k)) RM))

noncomputable def mul3s (d N LO CI RM A B : Nat) : Nat :=
  strictN (Nat.land A LO) (fun A1 => strictN (Nat.shiftRight A N) (fun A2 =>
    strictN (Nat.land B LO) (fun B1 => strictN (Nat.shiftRight B N) (fun B2 =>
      mulLoop3 d N CI RM A1 A2 B1 B2 d (nat_lit 0) (nat_lit 0) (nat_lit 0)))))

noncomputable def prodV (mul : Nat → Nat → Nat) (ONE : Nat) (f : Nat → Nat)
    (cs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) ONE
    (fun c cs' ih => List.rec (motive := fun _ => Nat) (f c) (fun _ _ _ => mul (f c) ih) cs') cs

noncomputable def rep1 (s n : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul s n)) (nat_lit 1))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) s) (nat_lit 1))

/-- The matrices' size and the constants `mul3s` takes, as in CFSG's `BrFi24`. -/
noncomputable def D : Nat := nat_lit 781
noncomputable def N : Nat := nat_lit 609961
noncomputable def LO : Nat := Nat.sub (Nat.shiftLeft 1 N) 1
noncomputable def RM : Nat := Nat.sub (Nat.shiftLeft 1 D) 1
noncomputable def CI : Nat := rep1 D D
noncomputable def ONE : Nat := rep1 (Nat.succ D) D
noncomputable def MUL : Nat → Nat → Nat := mul3s D N LO CI RM

/-- `N` pseudo-random bits from the power `b ^ 32000`. -/
noncomputable def rnd (b : Nat) : Nat :=
  Nat.land (Nat.shiftRight (Nat.pow b (nat_lit 32000)) (nat_lit 20000)) LO

/-- A matrix from two random bit strings `u`, `v`: entry 1 where `u` alone is set, 2 where `v`
alone is set, 0 elsewhere. -/
noncomputable def gen (b : Nat) : Nat :=
  (fun u v => Nat.add (Nat.land u (Nat.xor v LO)) (Nat.shiftLeft (Nat.land v (Nat.xor u LO)) N))
    (rnd b) (rnd (Nat.succ b))

/-- The 14 input matrices. -/
noncomputable def G (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (gen (nat_lit 1000029)) (Nat.beq k (nat_lit 13)))
    (gen (nat_lit 1000027)) (Nat.beq k (nat_lit 12)))
    (gen (nat_lit 1000025)) (Nat.beq k (nat_lit 11)))
    (gen (nat_lit 1000023)) (Nat.beq k (nat_lit 10)))
    (gen (nat_lit 1000021)) (Nat.beq k (nat_lit 9)))
    (gen (nat_lit 1000019)) (Nat.beq k (nat_lit 8)))
    (gen (nat_lit 1000017)) (Nat.beq k (nat_lit 7)))
    (gen (nat_lit 1000015)) (Nat.beq k (nat_lit 6)))
    (gen (nat_lit 1000013)) (Nat.beq k (nat_lit 5)))
    (gen (nat_lit 1000011)) (Nat.beq k (nat_lit 4)))
    (gen (nat_lit 1000009)) (Nat.beq k (nat_lit 3)))
    (gen (nat_lit 1000007)) (Nat.beq k (nat_lit 2)))
    (gen (nat_lit 1000005)) (Nat.beq k (nat_lit 1)))
    (gen (nat_lit 1000003)) (Nat.beq k (nat_lit 0))

/-- The letter pattern of `ck97`'s node. -/
noncomputable def word : List Nat := [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 2, 3, 2, 3, 3, 3, 2, 3, 4, 5, 6, 5, 5, 6, 6, 6, 5, 4, 6, 7, 8, 9, 9, 9, 8, 10, 10, 11, 11, 12, 12, 10, 13]

noncomputable def takeL (l : List Nat) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun c _ ih j => Nat.rec (motive := fun _ => List Nat) List.nil (fun i _ => List.cons c (ih i)) j) l

/-- The product of the first `m` letters of `word`, modulo 2^61 - 1. -/
noncomputable def fp (m : Nat) : Nat := Nat.mod (prodV MUL ONE G (takeL word m)) (nat_lit 2305843009213693951)

/-- 3 products. -/
theorem big : Nat.beq (fp (nat_lit 4)) (nat_lit 361572011084151223) = true := by decide +kernel

end Gf3Bench
