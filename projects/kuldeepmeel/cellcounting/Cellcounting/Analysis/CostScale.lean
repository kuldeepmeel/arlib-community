import Cellcounting.Model.Run
import Cellcounting.Interface.Encoding
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-!
# The cost scale: shared vocabulary for the running-time proof of `fpras_time`

INTERNAL.  The paper bounds the bit cost of every execution by one polynomial in
`L`, `ε⁻¹` and `log δ⁻¹` (`sections/introduction.tex:30-33`,
`sections/algorithm.tex:692-706`).  The proof in `Analysis/CostProof.lean`
splits the program `Program.fpras` at its natural seams and bounds each piece by
a power of one scale.  This file fixes the vocabulary those pieces share.

* **Primitive prices** (`steps_*`): what each charged primitive of
  `Model/Operations.lean` costs under the theorem's rate `rate`.  The primitives
  are sealed, but their prices are definitional, so each is proved by exhibiting
  the underlying `Charged.opMany`.
* **Loops with invariants** (`repeatFor_inv`, `foldl_inv`, `repeatWhile_inv`):
  arlib's loop lemmas need a uniform price for every round.  The program's
  rounds cost more as their state grows, so these versions carry an invariant
  indexed by the round number.
* **Sizes** (`bitLen_*`, `ratLen_*`): elementary bounds on binary lengths.
* **The interface of the cost proof**: `costScale` (the theorem's polynomial
  base), the prefix values `prepR … prepPS` and the prefix price `prepCost` of
  `Program.fpras` (S0–S4, through `p`), the size predicates `CtxSize`, `PmSize`,
  and the penalty predicates `ProfileValid`, `FreeValid`, `PenaltyOK`.

`PenaltyOK` is where the semantics enters the time bound.  The bin walk's
Metropolis trials read `⌊a D(w)/H⌋ - ⌊a D(v)/H⌋` fair bits, and the ratio samples
compute `2^{⌊aD/H⌋ - ⌊(a+1)D/H⌋}` exactly.  Both are polynomial only because
`0 ≤ D ≤ H` on the extended free box (`lem:forest`, `sections/scales.tex:131-158`;
used for exactly this at `sections/evaluation.tex:45-50, 386-393`).  A crude size
bound on `D` is exponential in `L`, so no purely syntactic argument gives the
time bound.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Program
open Cellcounting.Model.Operations

/-! ## Primitive prices -/

section Prices

/-- INTERNAL: `Charged.val_bind` for `Prog`, proved by the lemma rather than by `rfl`, so
that `simp` emits a rewrite step and the kernel does not unfold program literals (such as
`SRat.lit (1/16)`) while replaying it. -/
theorem costVb {α β : Type} (p : Prog α) (f : α → Prog β) : (p >>= f).val = (f p.val).val :=
  Charged.val_bind p f

/-- INTERNAL: `Charged.val_pure` for `Prog`, proved by the lemma rather than by `rfl`. -/
theorem costVp {α : Type} (a : α) : (pure a : Prog α).val = a :=
  Charged.val_pure a

/-- INTERNAL: the price of the opcode `Op.bit` under the unit rate. -/
private theorem steps_opMany_bit {α : Type} (k : ℕ) (a : α) :
    Charged.steps rate (Charged.opMany Op.bit k a : Prog α) = k := by
  rw [Charged.steps_opMany]; simp [rate]

/-- INTERNAL: price of `SNat.lit`. -/
@[simp] theorem steps_SNat_lit (k : ℕ) : Charged.steps rate (SNat.lit k) = bitLen k :=
  steps_opMany_bit _ _

/-- INTERNAL: price of `SNat.add`. -/
@[simp] theorem steps_SNat_add (x y : SNat) :
    Charged.steps rate (SNat.add x y) = bitLen x.get + bitLen y.get :=
  steps_opMany_bit _ (SNat.add x y).val

/-- INTERNAL: price of `SNat.sub`. -/
@[simp] theorem steps_SNat_sub (x y : SNat) :
    Charged.steps rate (SNat.sub x y) = bitLen x.get + bitLen y.get :=
  steps_opMany_bit _ (SNat.sub x y).val

/-- INTERNAL: price of `SNat.mul`. -/
@[simp] theorem steps_SNat_mul (x y : SNat) :
    Charged.steps rate (SNat.mul x y) = bitLen x.get * bitLen y.get :=
  steps_opMany_bit _ (SNat.mul x y).val

/-- INTERNAL: price of `SNat.div`. -/
@[simp] theorem steps_SNat_div (x y : SNat) :
    Charged.steps rate (SNat.div x y) = bitLen x.get * bitLen y.get :=
  steps_opMany_bit _ (SNat.div x y).val

/-- INTERNAL: price of `SNat.mod`. -/
@[simp] theorem steps_SNat_mod (x y : SNat) :
    Charged.steps rate (SNat.mod x y) = bitLen x.get * bitLen y.get :=
  steps_opMany_bit _ (SNat.mod x y).val

/-- INTERNAL: price of `SNat.le`. -/
@[simp] theorem steps_SNat_le (x y : SNat) :
    Charged.steps rate (SNat.le x y) = bitLen x.get + bitLen y.get :=
  steps_opMany_bit _ (SNat.le x y).val

/-- INTERNAL: price of `SNat.lt`. -/
@[simp] theorem steps_SNat_lt (x y : SNat) :
    Charged.steps rate (SNat.lt x y) = bitLen x.get + bitLen y.get :=
  steps_opMany_bit _ (SNat.lt x y).val

/-- INTERNAL: price of `SNat.eq`. -/
@[simp] theorem steps_SNat_eq (x y : SNat) :
    Charged.steps rate (SNat.eq x y) = bitLen x.get + bitLen y.get :=
  steps_opMany_bit _ (SNat.eq x y).val

/-- INTERNAL: price of `SNat.bitLen`. -/
@[simp] theorem steps_SNat_bitLen (x : SNat) :
    Charged.steps rate (SNat.bitLen x) = bitLen x.get :=
  steps_opMany_bit _ (SNat.bitLen x).val

/-- INTERNAL: price of `SNat.size`. -/
@[simp] theorem steps_SNat_size (x : SNat) :
    Charged.steps rate (SNat.size x) = bitLen x.get :=
  steps_opMany_bit _ (SNat.size x).val

/-- INTERNAL: price of `SNat.pow2`. -/
@[simp] theorem steps_SNat_pow2 (x : SNat) :
    Charged.steps rate (SNat.pow2 x) = x.get + 1 :=
  steps_opMany_bit _ (SNat.pow2 x).val

/-- INTERNAL: price of `SNat.toRat`. -/
@[simp] theorem steps_SNat_toRat (x : SNat) :
    Charged.steps rate (SNat.toRat x) = bitLen x.get :=
  steps_opMany_bit _ (SNat.toRat x).val

/-- INTERNAL: price of `SNat.index`. -/
@[simp] theorem steps_SNat_index (x : SNat) :
    Charged.steps rate (SNat.index x) = bitLen x.get :=
  steps_opMany_bit _ (SNat.index x).val

/-- INTERNAL: price of `SNat.inputLength`. -/
@[simp] theorem steps_SNat_inputLength (I : Instance) (ε δ : ℚ) :
    Charged.steps rate (SNat.inputLength I ε δ) = inputLength I ε δ :=
  steps_opMany_bit _ (SNat.inputLength I ε δ).val

/-- INTERNAL: price of `SRat.lit`. -/
@[simp] theorem steps_SRat_lit (q : ℚ) : Charged.steps rate (SRat.lit q) = ratLen q :=
  steps_opMany_bit _ (SRat.lit q).val

/-- INTERNAL: price of `SRat.add`. -/
@[simp] theorem steps_SRat_add (x y : SRat) :
    Charged.steps rate (SRat.add x y) = (ratLen x.get + 1) * (ratLen y.get + 1) :=
  steps_opMany_bit _ (SRat.add x y).val

/-- INTERNAL: price of `SRat.sub`. -/
@[simp] theorem steps_SRat_sub (x y : SRat) :
    Charged.steps rate (SRat.sub x y) = (ratLen x.get + 1) * (ratLen y.get + 1) :=
  steps_opMany_bit _ (SRat.sub x y).val

/-- INTERNAL: price of `SRat.mul`. -/
@[simp] theorem steps_SRat_mul (x y : SRat) :
    Charged.steps rate (SRat.mul x y) = (ratLen x.get + 1) * (ratLen y.get + 1) :=
  steps_opMany_bit _ (SRat.mul x y).val

/-- INTERNAL: price of `SRat.div`. -/
@[simp] theorem steps_SRat_div (x y : SRat) :
    Charged.steps rate (SRat.div x y) = (ratLen x.get + 1) * (ratLen y.get + 1) :=
  steps_opMany_bit _ (SRat.div x y).val

/-- INTERNAL: price of `SRat.le`. -/
@[simp] theorem steps_SRat_le (x y : SRat) :
    Charged.steps rate (SRat.le x y) = (ratLen x.get + 1) * (ratLen y.get + 1) :=
  steps_opMany_bit _ (SRat.le x y).val

/-- INTERNAL: price of `SRat.lt`. -/
@[simp] theorem steps_SRat_lt (x y : SRat) :
    Charged.steps rate (SRat.lt x y) = (ratLen x.get + 1) * (ratLen y.get + 1) :=
  steps_opMany_bit _ (SRat.lt x y).val

/-- INTERNAL: price of `SRat.floor`. -/
@[simp] theorem steps_SRat_floor (x : SRat) :
    Charged.steps rate (SRat.floor x) = (ratLen x.get + 1) * (ratLen x.get + 1) :=
  steps_opMany_bit _ (SRat.floor x).val

/-- INTERNAL: price of `SRat.natFloor`. -/
@[simp] theorem steps_SRat_natFloor (x : SRat) :
    Charged.steps rate (SRat.natFloor x) = (ratLen x.get + 1) * (ratLen x.get + 1) :=
  steps_opMany_bit _ (SRat.natFloor x).val

/-- INTERNAL: price of `SRat.natCeil`. -/
@[simp] theorem steps_SRat_natCeil (x : SRat) :
    Charged.steps rate (SRat.natCeil x) = (ratLen x.get + 1) * (ratLen x.get + 1) :=
  steps_opMany_bit _ (SRat.natCeil x).val

/-- INTERNAL: price of `SRat.zpow2`. -/
@[simp] theorem steps_SRat_zpow2 (x : SRat) :
    Charged.steps rate (SRat.zpow2 x) = ratLen x.get + (⌊x.get⌋ : ℤ).natAbs + 1 :=
  steps_opMany_bit _ (SRat.zpow2 x).val

/-- INTERNAL: price of `SRat.output`. -/
@[simp] theorem steps_SRat_output (x : SRat) :
    Charged.steps rate (SRat.output x) = ratLen x.get :=
  steps_opMany_bit _ (SRat.output x).val

/-- INTERNAL: price of a list read. -/
@[simp] theorem steps_get {α : Type} [Inhabited α] (l : List α) (i : ℕ) :
    Charged.steps rate (Model.Operations.get l i) = i + 1 :=
  steps_opMany_bit _ _

/-- INTERNAL: price of a list write. -/
@[simp] theorem steps_set {α : Type} (l : List α) (i : ℕ) (a : α) :
    Charged.steps rate (Model.Operations.set l i a) = i + 1 :=
  steps_opMany_bit _ _

/-- INTERNAL: price of an append. -/
@[simp] theorem steps_push {α : Type} (l : List α) (a : α) :
    Charged.steps rate (Model.Operations.push l a) = l.length + 1 :=
  steps_opMany_bit _ _

/-- INTERNAL: price of an allocation. -/
@[simp] theorem steps_replicate {α : Type} (k : ℕ) (a : α) :
    Charged.steps rate (Model.Operations.replicate k a) = k + 1 :=
  steps_opMany_bit _ _

/-- INTERNAL: price of a position equality test. -/
@[simp] theorem steps_idxEq (i j : ℕ) :
    Charged.steps rate (Model.Operations.idxEq i j) = bitLen i + bitLen j :=
  steps_opMany_bit _ _

/-- INTERNAL: price of a position comparison. -/
@[simp] theorem steps_idxLt (i j : ℕ) :
    Charged.steps rate (Model.Operations.idxLt i j) = bitLen i + bitLen j :=
  steps_opMany_bit _ _

/-- INTERNAL: price of reading one fair bit. -/
@[simp] theorem steps_flip (a : ℕ) (c : Coins ℕ) :
    Charged.steps rate (Coins.flip a c : Prog Bool) = 1 := by
  simp [Charged.steps, rate]

end Prices

/-! ## Loops with invariants -/

section Loops

theorem steps_foldl_cons' {β ι : Type} (f : β → ι → Prog β) (a : ι) (l : List ι) (b : β) :
    Charged.steps rate (Charged.foldl f (a :: l) b) =
      Charged.steps rate (f b a) + Charged.steps rate (Charged.foldl f l (f b a).val) := by
  simp [Charged.steps, Charged.cost_foldl_cons]

theorem foldl_inv {β ι : Type} (f : β → ι → Prog β) (P : ℕ → β → Prop) (k : ℕ) (l : List ι)
    (i₀ : ℕ) (b : β) (hb : P i₀ b)
    (h : ∀ i b a, i₀ ≤ i → i < i₀ + l.length → a ∈ l → P i b →
      P (i + 1) (f b a).val ∧ Charged.steps rate (f b a) ≤ k) :
    P (i₀ + l.length) (Charged.foldl f l b).val ∧
      Charged.steps rate (Charged.foldl f l b) ≤ l.length * k := by
  induction l generalizing i₀ b with
  | nil => simpa [Charged.steps] using hb
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := h i₀ b a le_rfl (by simp) (by simp) hb
    obtain ⟨ih1, ih2⟩ := ih (i₀ + 1) (f b a).val h1 (fun i b' a' hi hi' ha' hP =>
      h i b' a' (by omega) (by simp at hi' ⊢; omega) (List.mem_cons_of_mem _ ha') hP)
    refine ⟨?_, ?_⟩
    · simpa [Nat.add_assoc, Nat.add_comm 1] using ih1
    · rw [steps_foldl_cons']; simp only [List.length_cons]; nlinarith

theorem foldl_range'_inv {β : Type} (f : β → ℕ → Prog β) (P : ℕ → β → Prop) (k N : ℕ)
    (h : ∀ r b, r < N → P r b → P (r + 1) (f b r).val ∧ Charged.steps rate (f b r) ≤ k) :
    ∀ n s b, s + n ≤ N → P s b →
      P (s + n) (Charged.foldl f (List.range' s n) b).val ∧
        Charged.steps rate (Charged.foldl f (List.range' s n) b) ≤ n * k := by
  intro n
  induction n with
  | zero => intro s b _ hb; simpa [Charged.steps] using hb
  | succ n ih =>
    intro s b hs hb
    obtain ⟨h1, h2⟩ := h s b (by omega) hb
    obtain ⟨ih1, ih2⟩ := ih (s + 1) (f b s).val (by omega) h1
    refine ⟨?_, ?_⟩
    · simpa [List.range'_succ, Nat.add_assoc, Nat.add_comm 1] using ih1
    · rw [List.range'_succ, steps_foldl_cons']; nlinarith

theorem repeatFor_inv {β : Type} (f : ℕ → β → Prog β) (P : ℕ → β → Prop) (k n : ℕ) (b : β)
    (hb : P 0 b)
    (h : ∀ r b, r < n → P r b → P (r + 1) (f r b).val ∧ Charged.steps rate (f r b) ≤ k) :
    P n (Charged.repeatFor f n b).val ∧ Charged.steps rate (Charged.repeatFor f n b) ≤ n * k := by
  have := foldl_range'_inv (fun b r => f r b) P k n h n 0 b (by omega) hb
  simpa [Charged.repeatFor, List.range_eq_range'] using this

/-- INTERNAL: an invariant preserved by every round of a fold holds at its end (values
only). -/
theorem foldl_val_inv {β ι : Type} (P : β → Prop) (f : β → ι → Prog β)
    (h : ∀ b a, P b → P (f b a).val) : ∀ (l : List ι) (b : β), P b →
      P (Charged.foldl f l b).val := by
  intro l
  induction l with
  | nil => intro b hb; simpa using hb
  | cons a l ih => intro b hb; simpa using ih _ (h b a hb)

/-- INTERNAL: the `Charged.repeatFor` form of `foldl_val_inv`. -/
theorem repeatFor_val_inv {β : Type} (P : β → Prop) (f : ℕ → β → Prog β)
    (h : ∀ i b, P b → P (f i b).val) (n : ℕ) (b : β) (hb : P b) :
    P (Charged.repeatFor f n b).val :=
  foldl_val_inv P _ (fun b a hb => h a b hb) _ b hb

/-- INTERNAL: one round of an early-exit fold, value and price. -/
theorem foldlWhile_cons_val_steps {β : Type} (f : β → ℕ → Prog (Option β)) (i : ℕ)
    (xs : List ℕ) (a : β) :
    (Charged.foldlWhile f (i :: xs) a).val =
        (match (f a i).val with
         | none => a
         | some a' => (Charged.foldlWhile f xs a').val) ∧
      Charged.steps rate (Charged.foldlWhile f (i :: xs) a) =
        (match (f a i).val with
         | none => Charged.steps rate (f a i)
         | some a' => Charged.steps rate (f a i) +
             Charged.steps rate (Charged.foldlWhile f xs a')) := by
  cases h : (f a i).val <;>
    simp [Charged.foldlWhile, Charged.val, Charged.steps, Charged.cost] at h ⊢ <;> simp [h]

/-- INTERNAL: an early-exit fold over `range' s n`, with a round-indexed invariant. -/
theorem foldlWhile_range'_inv {β : Type} (f : β → ℕ → Prog (Option β)) (P : ℕ → β → Prop)
    (k N : ℕ)
    (h : ∀ r b, r < N → P r b → Charged.steps rate (f b r) ≤ k ∧
      ∀ b', (f b r).val = some b' → P (r + 1) b') :
    ∀ n s b, s + n ≤ N → P s b →
      (∃ r, s ≤ r ∧ r ≤ s + n ∧ P r (Charged.foldlWhile f (List.range' s n) b).val) ∧
        Charged.steps rate (Charged.foldlWhile f (List.range' s n) b) ≤ n * k := by
  intro n
  induction n with
  | zero =>
    intro s b _ hb
    exact ⟨⟨s, le_rfl, by simp, by simpa using hb⟩, by simp [Charged.steps]⟩
  | succ n ih =>
    intro s b hs hb
    obtain ⟨h1, h2⟩ := h s b (by omega) hb
    rw [List.range'_succ]
    obtain ⟨hval, hst⟩ := foldlWhile_cons_val_steps f s (List.range' (s + 1) n) b
    cases hv : (f b s).val with
    | none =>
      rw [hv] at hval hst
      refine ⟨⟨s, le_rfl, by omega, by rw [hval]; exact hb⟩, ?_⟩
      rw [hst]; nlinarith
    | some b' =>
      rw [hv] at hval hst
      obtain ⟨⟨r, hr1, hr2, hr3⟩, ih2⟩ := ih (s + 1) b' (by omega) (h2 b' hv)
      refine ⟨⟨r, by omega, by omega, by rw [hval]; exact hr3⟩, ?_⟩
      rw [hst]; nlinarith

theorem repeatWhile_inv {β : Type} (f : ℕ → β → Prog (Option β)) (P : ℕ → β → Prop) (k n : ℕ)
    (b : β) (hb : P 0 b)
    (h : ∀ r b, r < n → P r b → Charged.steps rate (f r b) ≤ k ∧
      ∀ b', (f r b).val = some b' → P (r + 1) b') :
    (∃ r ≤ n, P r (Charged.repeatWhile f n b).val) ∧
      Charged.steps rate (Charged.repeatWhile f n b) ≤ n * k := by
  have := foldlWhile_range'_inv (fun b r => f r b) P k n h n 0 b (by omega) hb
  obtain ⟨⟨r, -, hr2, hr3⟩, h2⟩ := this
  refine ⟨⟨r, by omega, ?_⟩, ?_⟩
  · simpa [Charged.repeatWhile, List.range_eq_range'] using hr3
  · simpa [Charged.repeatWhile, List.range_eq_range'] using h2

end Loops

/-! ## Sizes -/

section Sizes

/-- INTERNAL: size arithmetic. -/
theorem one_le_bitLen (k : ℕ) : 1 ≤ bitLen k := by simp [bitLen]

/-- INTERNAL: size arithmetic. -/
theorem lt_two_pow_bitLen (k : ℕ) : k < 2 ^ bitLen k := by
  unfold bitLen
  calc k < 2 ^ Nat.size k := Nat.lt_size_self k
    _ ≤ 2 ^ (Nat.size k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- INTERNAL: size arithmetic. -/
theorem bitLen_le_of_lt_two_pow {k t : ℕ} (h : k < 2 ^ t) : bitLen k ≤ t + 1 := by
  unfold bitLen; have := Nat.size_le.2 h; omega

/-- INTERNAL: size arithmetic. -/
theorem bitLen_mono {a b : ℕ} (h : a ≤ b) : bitLen a ≤ bitLen b := by
  unfold bitLen; have := Nat.size_le_size h; omega

/-- INTERNAL: size arithmetic. -/
theorem bitLen_le_succ (k : ℕ) : bitLen k ≤ k + 1 := by
  apply bitLen_le_of_lt_two_pow
  exact Nat.lt_two_pow_self

/-- INTERNAL: size arithmetic. -/
theorem bitLen_mul_le (a b : ℕ) : bitLen (a * b) ≤ bitLen a + bitLen b := by
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have : a * b < 2 ^ (Nat.size a + Nat.size b) := by
    rw [pow_add]
    calc a * b ≤ a * (2 ^ Nat.size b) := Nat.mul_le_mul_left _ hb.le
      _ < 2 ^ Nat.size a * 2 ^ Nat.size b := by
          apply Nat.mul_lt_mul_of_pos_right ha (by positivity)
  have := bitLen_le_of_lt_two_pow this
  unfold bitLen at *; omega

/-- INTERNAL: size arithmetic. -/
theorem bitLen_add_le (a b : ℕ) : bitLen (a + b) ≤ max (bitLen a) (bitLen b) + 1 := by
  have ha := lt_two_pow_bitLen a
  have hb := lt_two_pow_bitLen b
  have : a + b < 2 ^ (max (bitLen a) (bitLen b) + 1) := by
    rw [pow_succ]
    have h1 : 2 ^ bitLen a ≤ 2 ^ max (bitLen a) (bitLen b) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have h2 : 2 ^ bitLen b ≤ 2 ^ max (bitLen a) (bitLen b) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    omega
  have h := bitLen_le_of_lt_two_pow this
  -- bitLen ≤ max + 2 from this; sharpen using sizes directly
  unfold bitLen at *
  have hsa := Nat.lt_size_self a
  have hsb := Nat.lt_size_self b
  have : a + b < 2 ^ (max (Nat.size a) (Nat.size b) + 1) := by
    rw [pow_succ]
    have h1 : 2 ^ Nat.size a ≤ 2 ^ max (Nat.size a) (Nat.size b) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have h2 : 2 ^ Nat.size b ≤ 2 ^ max (Nat.size a) (Nat.size b) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    omega
  have := Nat.size_le.2 this
  omega

/-- INTERNAL: size arithmetic. -/
theorem bitLen_add_le' (a b : ℕ) : bitLen (a + b) ≤ bitLen a + bitLen b := by
  have := bitLen_add_le a b
  have := one_le_bitLen a; have := one_le_bitLen b
  omega

/-- INTERNAL: size arithmetic. -/
theorem bitLen_pow_le (a n : ℕ) : bitLen (a ^ n) ≤ n * bitLen a + 2 := by
  induction n with
  | zero => simp [bitLen]
  | succ n ih =>
    rw [pow_succ]
    have := bitLen_mul_le (a ^ n) a
    nlinarith

/-- INTERNAL: size arithmetic. -/
theorem bitLen_two_pow (n : ℕ) : bitLen (2 ^ n) = n + 2 := by
  simp [bitLen, Nat.size_pow]

/-- INTERNAL: size arithmetic. -/
theorem ratLen_natCast (n : ℕ) : ratLen (n : ℚ) = bitLen n + 2 := by
  simp [ratLen, bitLen]

/-- INTERNAL: size arithmetic. -/
theorem ratLen_intCast (z : ℤ) : ratLen (z : ℚ) = bitLen z.natAbs + 2 := by
  simp [ratLen, bitLen]

/-- INTERNAL: size arithmetic. -/
theorem ratLen_zero : ratLen 0 = 3 := by simp [ratLen, bitLen]

/-- INTERNAL: size arithmetic. -/
theorem three_le_ratLen (q : ℚ) : 3 ≤ ratLen q := by
  unfold ratLen
  have h1 := one_le_bitLen q.num.natAbs
  have h2 : 2 ≤ bitLen q.den := by
    have := bitLen_mono (Nat.one_le_iff_ne_zero.2 q.den_nz)
    simpa [bitLen] using this
  omega

/-- INTERNAL: a rational with denominator dividing `D` and numerator `a` has length at most
`bitLen |a| + bitLen D`. -/
theorem ratLen_le_of_mul_eq {q : ℚ} {D : ℕ} (hD : 0 < D) {a : ℤ} (h : q * D = a) :
    ratLen q ≤ bitLen a.natAbs + bitLen D := by
  have hq : q = Rat.divInt a D := by
    rw [Rat.divInt_eq_div]; field_simp; push_cast; linarith
  have hD' : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  have hden : q.den ≤ D := by
    have := Rat.den_dvd a D
    rw [← hq] at this
    exact Nat.le_of_dvd hD (by exact_mod_cast this)
  have hnum : q.num.natAbs ≤ a.natAbs := by
    by_cases ha : a = 0
    · subst ha; simp at h; rcases h with h | h
      · simp [h]
      · exact absurd h (by exact_mod_cast hD.ne')
    · have := Rat.num_dvd a hD'
      rw [← hq] at this
      exact Int.natAbs_le_of_dvd_ne_zero this ha
  unfold ratLen
  have := bitLen_mono hden
  have := bitLen_mono hnum
  omega

/-- INTERNAL: size arithmetic. -/
theorem ratLen_mul_le (x y : ℚ) : ratLen (x * y) ≤ ratLen x + ratLen y := by
  have hD : 0 < x.den * y.den := Nat.mul_pos x.den_pos y.den_pos
  have h : x * y * ((x.den * y.den : ℕ) : ℚ) = ((x.num * y.num : ℤ) : ℚ) := by
    push_cast
    have hx := Rat.mul_den_eq_num x
    have hy := Rat.mul_den_eq_num y
    calc x * y * (↑x.den * ↑y.den) = (x * ↑x.den) * (y * ↑y.den) := by ring
      _ = _ := by rw [hx, hy]
  have := ratLen_le_of_mul_eq hD h
  have h1 := bitLen_mul_le x.num.natAbs y.num.natAbs
  have h2 := bitLen_mul_le x.den y.den
  rw [Int.natAbs_mul] at this
  unfold ratLen at this ⊢; omega

/-- INTERNAL: size arithmetic. -/
theorem ratLen_inv (x : ℚ) : ratLen x⁻¹ = ratLen x := by
  by_cases hx : x = 0
  · simp [hx]
  · have h1 : x.num ≠ 0 := Rat.num_ne_zero.2 hx
    simp only [ratLen, Rat.num_inv, Rat.den_inv_of_ne_zero hx, Int.natAbs_mul,
      Int.natAbs_sign_of_ne_zero h1, one_mul, Int.natAbs_natCast]
    omega

/-- INTERNAL: size arithmetic. -/
theorem ratLen_div_le (x y : ℚ) : ratLen (x / y) ≤ ratLen x + ratLen y := by
  rw [div_eq_mul_inv]
  have := ratLen_mul_le x y⁻¹
  rw [ratLen_inv] at this; exact this

/-- INTERNAL: size arithmetic. -/
theorem ratLen_neg (x : ℚ) : ratLen (-x) = ratLen x := by
  simp [ratLen]

/-- INTERNAL: size arithmetic. -/
theorem abs_le_natAbs_num (x : ℚ) : |x| ≤ (x.num.natAbs : ℚ) := by
  have h := Rat.mul_den_eq_num x
  have hd : (1 : ℚ) ≤ x.den := by exact_mod_cast x.den_pos
  have : |x| * x.den = |(x.num : ℚ)| := by
    rw [← h, abs_mul, abs_of_pos (by positivity : (0 : ℚ) < x.den)]
  rw [Nat.cast_natAbs, Int.cast_abs, ← this]
  nlinarith [abs_nonneg x]

/-- INTERNAL: size arithmetic. -/
theorem abs_lt_two_pow_ratLen (x : ℚ) : |x| < 2 ^ ratLen x := by
  have h1 := abs_le_natAbs_num x
  have h2 : x.num.natAbs < 2 ^ ratLen x :=
    lt_of_lt_of_le (lt_two_pow_bitLen _)
      (Nat.pow_le_pow_right (by norm_num) (by unfold ratLen; omega))
  calc |x| ≤ _ := h1
    _ < _ := by exact_mod_cast h2

/-- INTERNAL: size arithmetic. -/
theorem bitLen_natCeil_le (q : ℚ) : bitLen ⌈q⌉₊ ≤ ratLen q + 2 := by
  apply bitLen_le_of_lt_two_pow
  rcases le_or_gt q 0 with h | h
  · rw [Nat.ceil_eq_zero.2 h]; positivity
  · have h1 : (⌈q⌉₊ : ℚ) < q + 1 := Nat.ceil_lt_add_one h.le
    have h2 := abs_lt_two_pow_ratLen q
    have h3 : q ≤ |q| := le_abs_self q
    have h4 : (2 : ℚ) ^ (ratLen q + 1) = 2 ^ ratLen q * 2 := by rw [pow_succ]
    have h5 : (1 : ℚ) ≤ 2 ^ ratLen q := one_le_pow₀ (by norm_num)
    have : (⌈q⌉₊ : ℚ) < 2 ^ (ratLen q + 1) := by linarith
    exact_mod_cast this

/-- INTERNAL: size arithmetic. -/
theorem bitLen_natFloor_le (q : ℚ) : bitLen ⌊q⌋₊ ≤ ratLen q + 1 := by
  apply bitLen_le_of_lt_two_pow
  have h2 := abs_lt_two_pow_ratLen q
  rcases le_or_gt q 0 with h | h
  · rw [Nat.floor_eq_zero.2 (by linarith)]; positivity
  · have h1 : (⌊q⌋₊ : ℚ) ≤ q := Nat.floor_le h.le
    have h3 : q ≤ |q| := le_abs_self q
    have : (⌊q⌋₊ : ℚ) < 2 ^ ratLen q := by linarith
    exact_mod_cast this

/-- INTERNAL: size arithmetic. -/
theorem size_sub_one_le_clog (x : ℕ) : Nat.size (x - 1) ≤ Nat.clog 2 x := by
  rw [Nat.size_le]
  have := Nat.le_pow_clog (by norm_num : 1 < 2) x
  have : 0 < 2 ^ Nat.clog 2 x := by positivity
  omega
end Sizes

/-! ## The interface of the cost proof -/

section Interface

/-- INTERNAL: the base of the theorem's polynomial,
`L + ⌈ε⁻¹⌉ + ⌈log₂ ⌈δ⁻¹⌉⌉ + 1`, exactly as `fpras_time` writes it.
TEXLINE: sections/introduction.tex:30-33 -/
def costScale (I : Instance) (ε δ : ℚ) : ℕ :=
  inputLength I ε δ + ⌈ε⁻¹⌉₊ + Nat.clog 2 ⌈δ⁻¹⌉₊ + 1

/-- INTERNAL: the margins `r` as `Program.fpras` reads them (S0). -/
noncomputable def prepR (I : Instance) : List SNat := (readList (List.ofFn I.r)).val

/-- INTERNAL: the margins `c` as `Program.fpras` reads them (S0). -/
noncomputable def prepC (I : Instance) : List SNat := (readList (List.ofFn I.c)).val

/-- INTERNAL: the bounds `b` as `Program.fpras` reads them (S0). -/
noncomputable def prepB (I : Instance) : List (List SNat) :=
  (readMatrix (List.ofFn fun i => List.ofFn fun j => I.b i j)).val

/-- INTERNAL: the outcome of the feasibility test S1 inside `Program.fpras`. -/
noncomputable def prepFeasible (I : Instance) : Bool :=
  (feasible I.m I.n (prepR I) (prepC I) (prepB I)).val

/-- INTERNAL: the tightened instance S2 computed by `Program.fpras`. -/
noncomputable def prepT (I : Instance) : Tight :=
  (tighten I.m I.n (prepR I) (prepC I) (prepB I)).val

/-- INTERNAL: the parameters S3 computed by `Program.fpras`. -/
noncomputable def prepPm (I : Instance) (ε δ : ℚ) : Params :=
  (params I.m I.n (inputLen I ε δ).val (SRat.lit ε).val).val

/-- INTERNAL: the oracle context S4 computed by `Program.fpras`. -/
noncomputable def prepCtx (I : Instance) (ε δ : ℚ) : Ctx :=
  (buildCtx I.m I.n (prepT I) (prepPm I ε δ)).val

/-- INTERNAL: the sealed `p = Σ_{s small} b_s` computed by `Program.fpras`. -/
noncomputable def prepPS (I : Instance) (ε δ : ℚ) : SNat :=
  (Charged.foldl (fun acc (e : Entry) => SNat.add acc e.2.2) (prepCtx I ε δ).small
    (SNat.lit 0).val).val

/-- INTERNAL: the price of the prefix S0–S4 of `Program.fpras`, through the
computation of `p`, in the order the program performs it.  The feasibility test
is the last term charged on an infeasible input; the rest is charged only on a
feasible one. -/
noncomputable def prepCost (I : Instance) (ε δ : ℚ) : ℕ :=
  Charged.steps rate (inputLen I ε δ) +
  Charged.steps rate (readList (List.ofFn I.r)) +
  Charged.steps rate (readList (List.ofFn I.c)) +
  Charged.steps rate (readMatrix (List.ofFn fun i => List.ofFn fun j => I.b i j)) +
  Charged.steps rate (feasible I.m I.n (prepR I) (prepC I) (prepB I)) +
  Charged.steps rate (tighten I.m I.n (prepR I) (prepC I) (prepB I)) +
  Charged.steps rate (SRat.lit ε) +
  Charged.steps rate (params I.m I.n (inputLen I ε δ).val (SRat.lit ε).val) +
  Charged.steps rate (buildCtx I.m I.n (prepT I) (prepPm I ε δ)) +
  Charged.steps rate (SNat.lit 0) +
  Charged.steps rate (Charged.foldl (fun acc (e : Entry) => SNat.add acc e.2.2)
    (prepCtx I ε δ).small (SNat.lit 0).val)

/-- INTERNAL: every size of an oracle context that the price of an oracle call or
of an annealing run depends on, bounded by `S`.  Loop counts and indices are
bounded as numbers; input-sized integers (margins, large bounds, `M_f`) by their
binary length; small bounds (`b < W`) as numbers. -/
structure CtxSize (S : ℕ) (C : Ctx) : Prop where
  m_le : C.m ≤ S
  n_le : C.n ≤ S
  rows_bits : ∀ x ∈ C.rows, bitLen x.get ≤ S
  cols_bits : ∀ x ∈ C.cols, bitLen x.get ≤ S
  nSmall_le : C.nSmall ≤ S
  small_le : ∀ e ∈ C.small, e.1 ≤ S ∧ e.2.1 ≤ S ∧ e.2.2.get ≤ S
  nFree_le : C.nFree ≤ S
  free_le : ∀ e ∈ C.free, e.1 ≤ S ∧ e.2.1 ≤ S ∧ bitLen e.2.2.get ≤ S
  nTree_le : C.nTree ≤ S
  tree_le : ∀ e ∈ C.tree, e.1 ≤ S ∧ e.2.1 ≤ S ∧ bitLen e.2.2.get ≤ S
  order_length : C.order.length ≤ S
  order_le : ∀ vt ∈ C.order, vt.1 ≤ S ∧ vt.2 ≤ S
  roots_length : C.roots.length ≤ S
  roots_le : ∀ v ∈ C.roots, v ≤ S
  Mf_bits : bitLen C.Mf.get ≤ S
  d_le : C.d.get ≤ S
  B_pos : 1 ≤ C.B.get
  B_le : C.B.get ≤ S
  H_pos : 1 ≤ C.H.get
  H_le : C.H.get ≤ S
  Aq_eq : ∃ A : ℕ, C.Aq.get = A ∧ A ≤ S
  Hq_eq : C.Hq.get = C.H.get
  Bq_eq : C.Bq.get = C.B.get

/-- INTERNAL: the values of the parameters of `eq:parameters` bounded by `S`. -/
structure PmSize (S : ℕ) (Pm : Params) : Prop where
  d_le : Pm.d.get ≤ S
  K_le : Pm.K.get ≤ S
  A_le : Pm.A.get ≤ S
  B_le : Pm.B.get ≤ S
  W_le : Pm.W.get ≤ S
  H_le : Pm.H.get ≤ S

/-- INTERNAL: a box-valid small-count profile (`sections/scales.tex:105-110`,
"box-valid integer small profile" of `lem:forest`): `x_s, y_s ∈ {0..b_s}` for
every small cell `s`, read the way `Program.penalty` reads them. -/
def ProfileValid (C : Ctx) (x y : List SNat) : Prop :=
  ∀ k < C.nSmall, (x.getD k default).get ≤ (C.small.getD k default).2.2.get ∧
    (y.getD k default).get ≤ (C.small.getD k default).2.2.get

/-- INTERNAL: a free vector in the extended free box `∏_{e ∈ F} [0, b_e + 1]` of
`lem:forest` (`sections/scales.tex:133-135`), read the way `Program.penalty`
reads it. -/
def FreeValid (C : Ctx) (zf : List SRat) : Prop :=
  ∀ k < C.nFree, 0 ≤ (zf.getD k default).get ∧
    (zf.getD k default).get ≤ (C.free.getD k default).2.2.get + 1

/-- INTERNAL: the penalty computed by the program is at most `S` in absolute
value on every box-valid profile and every point of the extended free box.
For the program's own context this is `0 ≤ D ≤ H` of `lem:forest`
(`sections/scales.tex:145-148`) together with `H ≤ S`.
TEXLINE: sections/evaluation.tex:45-50 -/
def PenaltyOK (S : ℕ) (C : Ctx) : Prop :=
  ∀ (x y : List SNat) (zf : List SRat), ProfileValid C x y → FreeValid C zf →
    |(penalty C x y zf).val.get| ≤ S

/-- INTERNAL: `CtxSize` is monotone in the bound. -/
theorem CtxSize.mono {S T : ℕ} {C : Ctx} (h : CtxSize S C) (hST : S ≤ T) : CtxSize T C where
  m_le := h.m_le.trans hST
  n_le := h.n_le.trans hST
  rows_bits x hx := (h.rows_bits x hx).trans hST
  cols_bits x hx := (h.cols_bits x hx).trans hST
  nSmall_le := h.nSmall_le.trans hST
  small_le e he := by
    obtain ⟨a, b, c⟩ := h.small_le e he; exact ⟨a.trans hST, b.trans hST, c.trans hST⟩
  nFree_le := h.nFree_le.trans hST
  free_le e he := by
    obtain ⟨a, b, c⟩ := h.free_le e he; exact ⟨a.trans hST, b.trans hST, c.trans hST⟩
  nTree_le := h.nTree_le.trans hST
  tree_le e he := by
    obtain ⟨a, b, c⟩ := h.tree_le e he; exact ⟨a.trans hST, b.trans hST, c.trans hST⟩
  order_length := h.order_length.trans hST
  order_le vt hvt := by
    obtain ⟨a, b⟩ := h.order_le vt hvt; exact ⟨a.trans hST, b.trans hST⟩
  roots_length := h.roots_length.trans hST
  roots_le v hv := (h.roots_le v hv).trans hST
  Mf_bits := h.Mf_bits.trans hST
  d_le := h.d_le.trans hST
  B_pos := h.B_pos
  B_le := h.B_le.trans hST
  H_pos := h.H_pos
  H_le := h.H_le.trans hST
  Aq_eq := by obtain ⟨A, hA, hA'⟩ := h.Aq_eq; exact ⟨A, hA, hA'.trans hST⟩
  Hq_eq := h.Hq_eq
  Bq_eq := h.Bq_eq

/-- INTERNAL: `PmSize` is monotone in the bound. -/
theorem PmSize.mono {S T : ℕ} {Pm : Params} (h : PmSize S Pm) (hST : S ≤ T) : PmSize T Pm where
  d_le := h.d_le.trans hST
  K_le := h.K_le.trans hST
  A_le := h.A_le.trans hST
  B_le := h.B_le.trans hST
  W_le := h.W_le.trans hST
  H_le := h.H_le.trans hST

/-- INTERNAL: `PenaltyOK` is monotone in the bound. -/
theorem PenaltyOK.mono {S T : ℕ} {C : Ctx} (h : PenaltyOK S C) (hST : S ≤ T) :
    PenaltyOK T C := fun x y zf hxy hz =>
  (h x y zf hxy hz).trans (by exact_mod_cast hST)

end Interface

end Cellcounting.Analysis
