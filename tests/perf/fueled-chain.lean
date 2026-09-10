/-!
A definitional equality that is exponential in a checker whose pointer equality
misses alpha-equivalent terms, distilled from con-leche's fuel-bridge (`_datF`)
lemmas.

`Fueled α` packages a fuel-indexed family `p : Nat → M α` with a proof whose
type mentions `p` twice, under binders (con-leche's is monotonicity in the
fuel; here it is trivially true, which changes nothing). A `_datF` lemma says
that running a monadic function in `Fueled` and extracting at fuel `F` is the
same as running it in `M`, and is proved by unfolding and rewriting with the
`atF` lemmas for `bind`/`pure`/`throw`/`ite`.

What is left for the kernel is a definitional equality between two monadic
programs that differ only in the monad instance, under one binder per `bind`,
with a `do`-notation join point per `unless … throw` guard. If the checker does
not recognise the unfolded program and the literal one as equal outright, it
compares them structurally; that unfolds `Fueled`'s `bind` to `Subtype.mk p h`,
proof irrelevance compares the *types* of the `h`s, and those mention the
rest of the program twice — so every guard multiplies the work by ~4.

`chainN` has N `lift` binds, each followed by an `unless … throw` guard.
Without the guards (pure binds) the comparison is cheap for every checker.
-/

abbrev M := Except Unit

def Fueled (α : Type) : Type :=
  {p : Nat → M α // ∀ (f f' : Nat) (v : α), p f = .ok v → p f' = .ok v → p f' = .ok v}

namespace Fueled

instance : Monad Fueled where
  pure a := ⟨fun _ => pure a, fun _ _ _ _ h => h⟩
  bind x f := ⟨fun F => x.val F >>= fun a => (f a).val F, fun _ _ _ _ h => h⟩

instance : MonadExceptOf Unit Fueled where
  throw e := ⟨fun _ => throw e, fun _ _ _ _ h => h⟩
  tryCatch _ _ := ⟨fun _ => throw (), fun _ _ _ _ h => h⟩

theorem atF_bind {α β : Type} (x : Fueled α) (f : α → Fueled β) (F : Nat) :
    (x >>= f).val F = x.val F >>= fun a => (f a).val F := rfl

theorem atF_pure {α : Type} (a : α) (F : Nat) : (pure a : Fueled α).val F = pure a := rfl

theorem atF_throw {α : Type} (e : Unit) (F : Nat) : (throw e : Fueled α).val F = throw e := rfl

theorem atF_ite {α : Type} {c : Prop} [Decidable c] (x y : Fueled α) (F : Nat) :
    (if c then x else y).val F = if c then x.val F else y.val F := by
  by_cases hc : c <;> simp [hc]

end Fueled

variable {m : Type → Type} [Monad m] [MonadExceptOf Unit m]

def lift {α : Type} (o : Option α) : m α :=
  match o with
  | some a => pure a
  | none => throw ()

theorem lift_atF {α : Type} (o : Option α) (F : Nat) :
    (lift o : Fueled α).val F = (lift o : M α) := by
  cases o <;> rfl

def chain6 (n : Nat) : m Unit := do
  let a1 ← lift (some (n + 1))
  unless a1 = n + 1 do
    throw ()
  let a2 ← lift (some (a1 + 1))
  unless a2 = a1 + 1 do
    throw ()
  let a3 ← lift (some (a2 + 1))
  unless a3 = a2 + 1 do
    throw ()
  let a4 ← lift (some (a3 + 1))
  unless a4 = a3 + 1 do
    throw ()
  let a5 ← lift (some (a4 + 1))
  unless a5 = a4 + 1 do
    throw ()
  let a6 ← lift (some (a5 + 1))
  unless a6 = a5 + 1 do
    throw ()
  pure ()

theorem chain6_datF (n F : Nat) :
    (chain6 (m := Fueled) n).val F = chain6 (m := M) n := by
  unfold chain6
  simp only [Fueled.atF_bind, Fueled.atF_pure, Fueled.atF_throw, Fueled.atF_ite, lift_atF]

def chain9 (n : Nat) : m Unit := do
  let a1 ← lift (some (n + 1))
  unless a1 = n + 1 do
    throw ()
  let a2 ← lift (some (a1 + 1))
  unless a2 = a1 + 1 do
    throw ()
  let a3 ← lift (some (a2 + 1))
  unless a3 = a2 + 1 do
    throw ()
  let a4 ← lift (some (a3 + 1))
  unless a4 = a3 + 1 do
    throw ()
  let a5 ← lift (some (a4 + 1))
  unless a5 = a4 + 1 do
    throw ()
  let a6 ← lift (some (a5 + 1))
  unless a6 = a5 + 1 do
    throw ()
  let a7 ← lift (some (a6 + 1))
  unless a7 = a6 + 1 do
    throw ()
  let a8 ← lift (some (a7 + 1))
  unless a8 = a7 + 1 do
    throw ()
  let a9 ← lift (some (a8 + 1))
  unless a9 = a8 + 1 do
    throw ()
  pure ()

theorem chain9_datF (n F : Nat) :
    (chain9 (m := Fueled) n).val F = chain9 (m := M) n := by
  unfold chain9
  simp only [Fueled.atF_bind, Fueled.atF_pure, Fueled.atF_throw, Fueled.atF_ite, lift_atF]

def chain12 (n : Nat) : m Unit := do
  let a1 ← lift (some (n + 1))
  unless a1 = n + 1 do
    throw ()
  let a2 ← lift (some (a1 + 1))
  unless a2 = a1 + 1 do
    throw ()
  let a3 ← lift (some (a2 + 1))
  unless a3 = a2 + 1 do
    throw ()
  let a4 ← lift (some (a3 + 1))
  unless a4 = a3 + 1 do
    throw ()
  let a5 ← lift (some (a4 + 1))
  unless a5 = a4 + 1 do
    throw ()
  let a6 ← lift (some (a5 + 1))
  unless a6 = a5 + 1 do
    throw ()
  let a7 ← lift (some (a6 + 1))
  unless a7 = a6 + 1 do
    throw ()
  let a8 ← lift (some (a7 + 1))
  unless a8 = a7 + 1 do
    throw ()
  let a9 ← lift (some (a8 + 1))
  unless a9 = a8 + 1 do
    throw ()
  let a10 ← lift (some (a9 + 1))
  unless a10 = a9 + 1 do
    throw ()
  let a11 ← lift (some (a10 + 1))
  unless a11 = a10 + 1 do
    throw ()
  let a12 ← lift (some (a11 + 1))
  unless a12 = a11 + 1 do
    throw ()
  pure ()

theorem chain12_datF (n F : Nat) :
    (chain12 (m := Fueled) n).val F = chain12 (m := M) n := by
  unfold chain12
  simp only [Fueled.atF_bind, Fueled.atF_pure, Fueled.atF_throw, Fueled.atF_ite, lift_atF]
