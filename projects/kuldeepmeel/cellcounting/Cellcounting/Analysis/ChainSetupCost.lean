import Cellcounting.Analysis.ChainSize

/-!
# The setup S8 costs a polynomial number of bit operations and has polynomial sizes

`Cellcounting.Analysis.chainSetup_cost`: for a context with `CtxSize S C`, parameters
with `PmSize S Pm`, `p ≤ S`, and `ε` with `ε⁻¹, ratLen ε ≤ S`, the setup
`Program.chainSetup` costs at most `S ^ c`, its chain and phase parameters satisfy
`ChainSize (S ^ c)`, its initial multipliers `w^(0)` satisfy `WSize (S ^ c)`, and
`C(0)` has length at most `S ^ c`, for one fixed `c`.

Route: the pair-label loop runs `nSmall ≤ S` rounds of `b_s ≤ S` pushes, so the
computed `p = Σ b_s ≤ S²` and `pairCell` lists cell `s` exactly `b_s` times (giving
`pairCell_length`, `pairCell_lt`, `pairCell_count`); every straight-line parameter
(`q = W², K_obs, τ, B_ret, N_av, J_*`) is a product of boundedly many factors `≤ S`
or `≤ ε⁻¹ ≤ S` times constants `≤ 10⁸ ≤ 2^27 ≤ S^27`; `ξ⁻¹ = 200 000 (H + 1) J_*/ε`;
`k_acc = Nat.size (⌈ξ⁻¹⌉ - 1) ≤ bitLen ⌈ξ⁻¹⌉`.  The `w^(0)` entries are `0`, `6` or
`6 (b_i + 1)/(b_l + 2)`, of length `O(log S)`; `C(0) = M_f ∏ (b_s + 1)` has
`bitLen ≤ S + nSmall·(bitLen S + 1)`.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Model
open Cellcounting.Program
open Cellcounting.Model.Operations
open Cellcounting.Interface

/-- INTERNAL: peel one bind of a straight-line program, accumulating its price. -/
theorem bind_step {α β : Type} {p : Prog α} {f : α → Prog β} {a acc X : ℕ} {Q : β → Prop}
    (h1 : Charged.steps rate p ≤ a)
    (h2 : Charged.steps rate (f p.val) + (acc + a) ≤ X ∧ Q (f p.val).val) :
    Charged.steps rate (p >>= f) + acc ≤ X ∧ Q (p >>= f).val := by
  rw [Charged.steps_bind, costVb]; exact ⟨by omega, h2.2⟩

/-- INTERNAL: `2 S^a ≤ S^(a+1)` for `S ≥ 2`. -/
theorem pow_succ_ge {S a : ℕ} (hS : 2 ≤ S) : 2 * S ^ a ≤ S ^ (a + 1) := by
  rw [pow_succ]; exact Nat.mul_le_mul_left _ hS |>.trans_eq' (by ring)

/-- INTERNAL: `1 ≤ S^a` for `S ≥ 2`. -/
theorem one_le_pow' {S a : ℕ} (hS : 2 ≤ S) : 1 ≤ S ^ a := Nat.one_le_pow _ _ (by omega)

/-- INTERNAL: `S^a` is monotone in `a` for `S ≥ 2`. -/
theorem pow_mono' {S a b : ℕ} (hS : 2 ≤ S) (h : a ≤ b) : S ^ a ≤ S ^ b :=
  Nat.pow_le_pow_right (by omega) h

/-- INTERNAL: a number at most `S^a` has length at most `S^(a+1)`. -/
theorem bitLen_le_pow {S a x : ℕ} (hS : 2 ≤ S) (hx : x ≤ S ^ a) : bitLen x ≤ S ^ (a + 1) := by
  have := bitLen_le_succ x
  have := pow_succ_ge (a := a) hS
  have := one_le_pow' (a := a) hS
  omega

/-- INTERNAL: value and price of `SNat.mul` on operands bounded by powers of `S`. -/
theorem snat_mul_le {S a b : ℕ} (hS : 2 ≤ S) {x y : SNat} (hx : x.get ≤ S ^ a) (hy : y.get ≤ S ^ b) :
    (SNat.mul x y).val.get ≤ S ^ (a + b) ∧ Charged.steps rate (SNat.mul x y) ≤ S ^ (a + b + 2) := by
  refine ⟨by rw [SNat.get_mul, pow_add]; exact Nat.mul_le_mul hx hy, ?_⟩
  rw [steps_SNat_mul, show a + b + 2 = (a + 1) + (b + 1) by ring, pow_add]
  exact Nat.mul_le_mul (bitLen_le_pow hS hx) (bitLen_le_pow hS hy)

/-- INTERNAL: value and price of `SNat.add` on operands at most `S^a`. -/
theorem snat_add_le {S a : ℕ} (hS : 2 ≤ S) {x y : SNat} (hx : x.get ≤ S ^ a) (hy : y.get ≤ S ^ a) :
    (SNat.add x y).val.get ≤ S ^ (a + 1) ∧ Charged.steps rate (SNat.add x y) ≤ S ^ (a + 2) := by
  have h1 := pow_succ_ge (a := a) hS
  have h2 : 2 * S ^ (a + 1) ≤ S ^ (a + 2) := pow_succ_ge hS
  refine ⟨by rw [SNat.get_add]; omega, ?_⟩
  rw [steps_SNat_add]
  have := bitLen_le_pow hS hx; have := bitLen_le_pow hS hy
  omega

/-- INTERNAL: value and price of a literal at most `S^a`. -/
theorem snat_lit_le {S a k : ℕ} (hS : 2 ≤ S) (hk : k ≤ S ^ a) :
    (SNat.lit k).val.get ≤ S ^ a ∧ Charged.steps rate (SNat.lit k) ≤ S ^ (a + 1) :=
  ⟨by rw [SNat.get_lit]; exact hk, by rw [steps_SNat_lit]; exact bitLen_le_pow hS hk⟩

/-- INTERNAL: length and price of `SNat.toRat` on an operand at most `S^a`. -/
theorem snat_toRat_le {S a : ℕ} (hS : 2 ≤ S) {x : SNat} (hx : x.get ≤ S ^ a) :
    ratLen (SNat.toRat x).val.get ≤ S ^ (a + 2) ∧ Charged.steps rate (SNat.toRat x) ≤ S ^ (a + 1) := by
  refine ⟨?_, by rw [steps_SNat_toRat]; exact bitLen_le_pow hS hx⟩
  rw [SNat.get_toRat, ratLen_natCast]
  have := bitLen_le_pow hS hx
  have : 2 * S ^ (a + 1) ≤ S ^ (a + 2) := pow_succ_ge hS
  have : S ^ 1 ≤ S ^ (a + 1) := pow_mono' hS (by omega)
  rw [pow_one] at this
  omega

/-- INTERNAL: price of a binary `SRat` operation on operands of length at most `S^a`. -/
theorem srat_bin_le {S a : ℕ} (hS : 2 ≤ S) {x y : ℚ} (hx : ratLen x ≤ S ^ a) (hy : ratLen y ≤ S ^ a) :
    (ratLen x + 1) * (ratLen y + 1) ≤ S ^ (2 * a + 2) := by
  have := pow_succ_ge (a := a) hS
  have := one_le_pow' (a := a) hS
  rw [show 2 * a + 2 = (a + 1) + (a + 1) by ring, pow_add]
  exact Nat.mul_le_mul (by omega) (by omega)

/-- INTERNAL: length of a product of rationals of length at most `S^a`. -/
theorem srat_mul_len {S a : ℕ} (hS : 2 ≤ S) {x y : ℚ} (hx : ratLen x ≤ S ^ a) (hy : ratLen y ≤ S ^ a) :
    ratLen (x * y) ≤ S ^ (a + 1) := by
  have := ratLen_mul_le x y; have := pow_succ_ge (a := a) hS; omega

/-- INTERNAL: length of a quotient of rationals of length at most `S^a`. -/
theorem srat_div_len {S a : ℕ} (hS : 2 ≤ S) {x y : ℚ} (hx : ratLen x ≤ S ^ a) (hy : ratLen y ≤ S ^ a) :
    ratLen (x / y) ≤ S ^ (a + 1) := by
  have := ratLen_div_le x y; have := pow_succ_ge (a := a) hS; omega

/-- INTERNAL: a constant `c ≤ 2^a` is at most `S^a`. -/
theorem const_le_pow {S : ℕ} (hS : 2 ≤ S) (c a : ℕ) (hc : c ≤ 2 ^ a) : c ≤ S ^ a :=
  hc.trans (Nat.pow_le_pow_left hS a)

/-- INTERNAL: `b` pushes of `s` append `b` copies of `s`. -/
theorem pushes_val (s n : ℕ) (l : List ℕ) :
    (Charged.repeatFor (fun _ acc => Operations.push acc s) n l : Prog (List ℕ)).val =
      l ++ List.replicate n s ∧
    Charged.steps rate (Charged.repeatFor (fun _ acc => Operations.push acc s) n l : Prog (List ℕ)) ≤
      n * (l.length + n + 1) := by
  have := repeatFor_inv (fun _ (acc : List ℕ) => (Operations.push acc s : Prog (List ℕ)))
    (fun r acc => acc = l ++ List.replicate r s) (l.length + n + 1) n l (by simp)
    (fun r acc hr hacc => by
      subst hacc
      refine ⟨by simp [List.replicate_succ', List.append_assoc], ?_⟩
      rw [steps_push]; simp; omega)
  exact this

/-- INTERNAL: arithmetic for `lab_facts`. -/
theorem lab_arith (S : ℕ) (hS : 2 ≤ S) : S * (S * S + S + 1) + 5 * S + 1 ≤ S ^ 5 := by
  obtain ⟨t, rfl⟩ : ∃ t, S = t + 2 := ⟨S - 2, by omega⟩
  ring_nf; omega

/-- INTERNAL: the pair-label loop of `Program.chainSetup`: `pairCell` lists cell `s` exactly
`b_s` times, `p = Σ b_s ≤ S²`, first labels `≤ S²`, and the price is at most `S⁶`. -/
theorem lab_facts (S : ℕ) (C : Ctx) (hS : 2 ≤ S) (hC : CtxSize S C) :
    let L := (Charged.repeatFor (fun s (st : List ℕ × List ℕ × List SNat × ℕ) => do
      let e ← Operations.get C.small s
      let bI ← SNat.index e.2.2
      let firsts ← Operations.push st.2.1 st.2.2.2
      let bs ← Operations.push st.2.2.1 e.2.2
      let cells ← Charged.repeatFor (fun _ acc => Operations.push acc s) bI st.1
      pure (cells, firsts, bs, st.2.2.2 + bI)) C.nSmall ([], [], [], 0) :
        Prog (List ℕ × List ℕ × List SNat × ℕ))
    L.val.1.length = L.val.2.2.2 ∧ L.val.2.2.2 ≤ S ^ 2 ∧ (∀ c ∈ L.val.1, c < C.nSmall) ∧
    (∀ t < C.nSmall, L.val.1.count t = (C.small.getD t default).2.2.get) ∧
    (∀ f ∈ L.val.2.1, f ≤ S ^ 2) ∧ (∀ b ∈ L.val.2.2.1, b.get ≤ S) ∧
    L.val.2.2.1.length = C.nSmall ∧ Charged.steps rate L ≤ S ^ 6 := by
  intro L
  have hn := hC.nSmall_le
  have hb : ∀ s, (C.small.getD s default).2.2.get ≤ S := fun s =>
    getD_pred_of_forall (fun e : Entry => e.2.2.get ≤ S) C.small s
      (fun e he => (hC.small_le e he).2.2) (by
        show ((default : Entry).2.2).get ≤ S
        exact (show ((default : Entry).2.2).get = 0 from rfl) ▸ Nat.zero_le S)
  let P := fun r (st : List ℕ × List ℕ × List SNat × ℕ) => st.1.length = st.2.2.2 ∧ st.2.2.2 ≤ r * S ∧
      (∀ c ∈ st.1, c < r) ∧
      (∀ t, st.1.count t = if t < r then (C.small.getD t default).2.2.get else 0) ∧
      (∀ f ∈ st.2.1, f ≤ st.2.2.2) ∧ (∀ b ∈ st.2.2.1, b.get ≤ S) ∧ st.2.2.1.length = r ∧
      st.2.1.length = r
  have key : P C.nSmall L.val ∧ Charged.steps rate L ≤ C.nSmall * S ^ 5 := repeatFor_inv _
    (fun r (st : List ℕ × List ℕ × List SNat × ℕ) => st.1.length = st.2.2.2 ∧ st.2.2.2 ≤ r * S ∧
      (∀ c ∈ st.1, c < r) ∧
      (∀ t, st.1.count t = if t < r then (C.small.getD t default).2.2.get else 0) ∧
      (∀ f ∈ st.2.1, f ≤ st.2.2.2) ∧ (∀ b ∈ st.2.2.1, b.get ≤ S) ∧ st.2.2.1.length = r ∧
      st.2.1.length = r)
    (S ^ 5) C.nSmall ([], [], [], 0) (by simp) (by
      rintro r ⟨cells, firsts, bs, acc⟩ hr ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩
      dsimp only at i1 i2 i3 i4 i5 i6 i7 i8 ⊢
      simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, val_get, steps_get,
        SNat.val_index, steps_SNat_index, val_push, steps_push]
      obtain ⟨pv, pc⟩ := pushes_val r (C.small.getD r default).2.2.get cells
      rw [pv]
      have hbr := hb r
      generalize hbd : (C.small.getD r default).2.2.get = b at hbr pc ⊢
      have hrS : r < S := lt_of_lt_of_le hr hn
      have hacc : acc ≤ S * S := i2.trans (Nat.mul_le_mul_right _ hrS.le)
      refine ⟨⟨by simp [i1], by rw [Nat.add_mul]; omega, ?_, ?_, ?_, ?_, by simp [i7], by simp [i8]⟩, ?_⟩
      · intro c hc
        rcases List.mem_append.1 hc with hc | hc
        · exact Nat.lt_succ_of_lt (i3 c hc)
        · rw [(List.mem_replicate.1 hc).2]; omega
      · intro t
        rw [List.count_append, List.count_replicate, i4 t]
        by_cases htr : t = r
        · subst htr; simp [← hbd, List.getD_eq_getElem?_getD]
        · by_cases htr' : t < r
          · simp [htr', Ne.symm htr, show t < r + 1 by omega]
          · simp [htr', Ne.symm htr, show ¬ t < r + 1 by omega]
      · intro f hf
        rcases List.mem_append.1 hf with hf | hf
        · exact (i5 f hf).trans (Nat.le_add_right _ _)
        · simp at hf; omega
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact i6 x hx
        · simp at hx; rw [hx]; exact hb r
      · have hb1 := bitLen_le_succ b
        have e1 : b * (acc + b + 1) ≤ S * (S * S + S + 1) := Nat.mul_le_mul hbr (by omega)
        have e2 := lab_arith S hS
        rw [i1] at pc
        omega)
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, -⟩, h8⟩ := key
  refine ⟨h1, h2.trans (by rw [sq]; exact Nat.mul_le_mul_right _ hn), h3, fun t ht => ?_,
    fun f hf => (h5 f hf).trans (h2.trans (by rw [sq]; exact Nat.mul_le_mul_right _ hn)), h6, h7,
    h8.trans ?_⟩
  · rw [h4 t]; simp [ht]
  · have : S ^ 6 = S * S ^ 5 := by ring
    rw [this]; exact Nat.mul_le_mul_right _ hn

/-- INTERNAL: `ratLen n ≤ n + 3`. -/
theorem ratLen_nat_le (n : ℕ) : ratLen (n : ℚ) ≤ n + 3 := by
  rw [ratLen_natCast]; have := bitLen_le_succ n; omega

/-- INTERNAL: `2S + 15 ≤ S⁵` for `S ≥ 2`. -/
theorem lin_le_pow5 (S : ℕ) (hS : 2 ≤ S) : 2 * S + 15 ≤ S ^ 5 := by
  obtain ⟨t, rfl⟩ : ∃ t, S = t + 2 := ⟨S - 2, by omega⟩
  ring_nf; omega

/-- INTERNAL: the initial multipliers `w^(0)` (`0`, `6` or `6 (b_i + 1)/(b_l + 2)`) have length
at most `S⁵`, and their double loop costs at most `S²⁰`. -/
theorem w0_facts (S p : ℕ) (hS : 2 ≤ S) (hp : p ≤ S ^ 2) (pc : List ℕ) (sb : List SNat)
    (hpc : ∀ c ∈ pc, c < S) (hsb : ∀ b ∈ sb, b.get ≤ S) (one c2 : SNat) (six : SRat)
    (hone : one.get = 1) (hc2 : c2.get = 2) (hsix : six.get = 6)
    (tab : List (List SRat)) (htab : WSize 3 tab) :
    let W := (Charged.repeatFor (fun i acc =>
      Charged.repeatFor (fun l acc' => do
        let diag ← idxEq i l
        if diag then pure acc' else do
          let si ← Operations.get pc i
          let sl ← Operations.get pc l
          let same ← idxEq si sl
          if same then set2 acc' i l six else do
            let bi ← Operations.get sb si
            let bl ← Operations.get sb sl
            let bi1 ← SNat.add bi one
            let bl2 ← SNat.add bl c2
            let bi1q ← SNat.toRat bi1
            let bl2q ← SNat.toRat bl2
            let t ← SRat.mul six bi1q
            let v ← SRat.div t bl2q
            set2 acc' i l v) p acc) p tab : Prog (List (List SRat)))
    WSize (S ^ 5) W.val ∧ Charged.steps rate W ≤ S ^ 20 := by
  intro W
  have hS5 : 32 ≤ S ^ 5 := by have := Nat.pow_le_pow_left hS 5; norm_num at this; omega
  have hk : 100 * (S + 10) ^ 2 * S ^ 4 ≤ S ^ 20 := by
    obtain ⟨t, rfl⟩ : ∃ t, S = t + 2 := ⟨S - 2, by omega⟩
    ring_nf; omega
  have key : WSize (S ^ 5) W.val ∧ Charged.steps rate W ≤ p * (p * (100 * (S + 10) ^ 2)) := by
    refine repeatFor_inv _ (fun _ (acc : List (List SRat)) => WSize (S ^ 5) acc)
      (p * (100 * (S + 10) ^ 2)) p tab (htab.mono (by omega)) ?_
    intro i acc hi hacc
    beta_reduce
    refine repeatFor_inv _ (fun _ (acc' : List (List SRat)) => WSize (S ^ 5) acc')
      (100 * (S + 10) ^ 2) p acc hacc ?_
    intro l acc' hl hacc'
    beta_reduce
    have hiS : i < S ^ 2 := lt_of_lt_of_le hi hp
    have hlS : l < S ^ 2 := lt_of_lt_of_le hl hp
    have hbi : bitLen i ≤ S ^ 2 + 1 := (bitLen_le_succ _).trans (by omega)
    have hbl : bitLen l ≤ S ^ 2 + 1 := (bitLen_le_succ _).trans (by omega)
    have hsq : S ^ 2 ≤ (S + 10) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hsq' : S + 10 ≤ (S + 10) ^ 2 := Nat.le_self_pow (by norm_num) _
    simp only [Charged.steps_bind, costVb, steps_idxEq, val_idxEq]
    by_cases hd : i = l
    · simp only [hd, decide_true, ↓reduceIte, Charged.steps_pure, costVp]
      exact ⟨hacc', by omega⟩
    simp only [hd, decide_false, Bool.false_eq_true, ↓reduceIte, Charged.steps_bind, costVb,
      val_get, steps_get, steps_idxEq, val_idxEq]
    have hsi : pc.getD i default < S ∨ pc.getD i default = 0 :=
      getD_pred_of_forall (fun c => c < S ∨ c = 0) pc i (fun c hc => Or.inl (hpc c hc))
        (Or.inr rfl)
    have hsl : pc.getD l default < S ∨ pc.getD l default = 0 :=
      getD_pred_of_forall (fun c => c < S ∨ c = 0) pc l (fun c hc => Or.inl (hpc c hc))
        (Or.inr rfl)
    have hsi' : pc.getD i default ≤ S := by omega
    have hsl' : pc.getD l default ≤ S := by omega
    have hbsi : bitLen (pc.getD i default) ≤ S + 1 := (bitLen_le_succ _).trans (by omega)
    have hbsl : bitLen (pc.getD l default) ≤ S + 1 := (bitLen_le_succ _).trans (by omega)
    have hr6 : ratLen six.get ≤ 6 := by rw [hsix]; decide
    by_cases hs : pc.getD i default = pc.getD l default
    · simp only [hs, decide_true, ↓reduceIte, steps_set2]
      refine ⟨set2_pred (fun x : SRat => ratLen x.get ≤ S ^ 5) _ _ _ _ hacc' (by omega), ?_⟩
      omega
    simp only [hs, decide_false, Bool.false_eq_true, ↓reduceIte, Charged.steps_bind, costVb,
      val_get, steps_get, steps_SNat_add, SNat.get_add, steps_SNat_toRat, SNat.get_toRat,
      steps_SRat_mul, SRat.get_mul, steps_SRat_div, SRat.get_div, steps_set2, hone, hc2]
    have hb1 : (sb.getD (pc.getD i default) default).get ≤ S :=
      getD_pred_of_forall (fun b : SNat => b.get ≤ S) sb _ hsb (by simp)
    have hb2 : (sb.getD (pc.getD l default) default).get ≤ S :=
      getD_pred_of_forall (fun b : SNat => b.get ≤ S) sb _ hsb (by simp)
    have hb2' : bitLen 2 = 3 := by decide
    have hb1' : bitLen 1 = 2 := by decide
    have hsq2 : (S + 10) ^ 2 = (S + 10) * (S + 10) := sq _
    refine ⟨set2_pred (fun x : SRat => ratLen x.get ≤ S ^ 5) _ _ _ _ hacc' ?_, ?_⟩
    · simp only [SRat.get_div, SRat.get_mul, SNat.get_toRat, SNat.get_add, hone, hc2]
      generalize (sb.getD (pc.getD i default) default).get = x at *
      generalize (sb.getD (pc.getD l default) default).get = y at *
      have r1 := ratLen_nat_le (x + 1)
      have r2 := ratLen_nat_le (y + 2)
      have m1 := ratLen_mul_le six.get ((x + 1 : ℕ) : ℚ)
      have m2 := ratLen_div_le (six.get * ((x + 1 : ℕ) : ℚ)) ((y + 2 : ℕ) : ℚ)
      push_cast at m1 m2 r1 r2 ⊢
      have := lin_le_pow5 S hS
      omega
    · generalize (sb.getD (pc.getD i default) default).get = x at *
      generalize (sb.getD (pc.getD l default) default).get = y at *
      have r1 := ratLen_nat_le (x + 1)
      have r2 := ratLen_nat_le (y + 2)
      have m1 := ratLen_mul_le six.get ((x + 1 : ℕ) : ℚ)
      have bx := bitLen_le_succ x
      have by' := bitLen_le_succ y
      have bx1 := bitLen_le_succ (x + 1)
      have by2 := bitLen_le_succ (y + 2)
      have e1 : (ratLen six.get + 1) * (ratLen ((x + 1 : ℕ) : ℚ) + 1) ≤ (S + 10) * (S + 10) :=
        Nat.mul_le_mul (by omega) (by omega)
      have e2 : (ratLen (six.get * ((x + 1 : ℕ) : ℚ)) + 1) * (ratLen ((y + 2 : ℕ) : ℚ) + 1) ≤
          (2 * (S + 10)) * (S + 10) := Nat.mul_le_mul (by omega) (by omega)
      push_cast at e1 e2
      clear hacc' hacc hsb hpc htab
      linarith
  obtain ⟨k1, k2⟩ := key
  refine ⟨k1, k2.trans ?_⟩
  have : p * (p * (100 * (S + 10) ^ 2)) ≤ S ^ 2 * (S ^ 2 * (100 * (S + 10) ^ 2)) :=
    Nat.mul_le_mul hp (Nat.mul_le_mul_right _ hp)
  have : S ^ 2 * (S ^ 2 * (100 * (S + 10) ^ 2)) = 100 * (S + 10) ^ 2 * S ^ 4 := by ring
  omega

/-- INTERNAL: `C(0) = M_f ∏ (b_s + 1)` has length at most `S⁴` and costs at most `S⁸`. -/
theorem c0_facts (S : ℕ) (hS : 2 ≤ S) (Mf : SNat) (hMf : bitLen Mf.get ≤ S) (sb : List SNat)
    (hsb : ∀ b ∈ sb, b.get ≤ S) (hlen : sb.length ≤ S) (one : SNat) (hone : one.get = 1) :
    let F := (Charged.foldl (fun acc (b : SNat) => do
      let b1' ← SNat.add b one
      SNat.mul acc b1') sb Mf : Prog SNat)
    ratLen (F.val.get : ℚ) ≤ S ^ 4 ∧ Charged.steps rate F ≤ S ^ 8 := by
  intro F
  have key : bitLen F.val.get ≤ S + sb.length * (S + 2) ∧
      Charged.steps rate F ≤ sb.length * ((S + 3) + (S + S * (S + 2)) * (S + 2)) := by
    have := foldl_inv (fun acc (b : SNat) => (do
      let b1' ← SNat.add b one
      SNat.mul acc b1' : Prog SNat)) (fun r (acc : SNat) => bitLen acc.get ≤ S + r * (S + 2))
      ((S + 3) + (S + S * (S + 2)) * (S + 2)) sb 0 Mf (by simpa using hMf) ?_
    · simpa using this
    intro i acc b hi hi' hb hacc
    simp only [Charged.steps_bind, costVb, steps_SNat_add, steps_SNat_mul, SNat.get_add,
      SNat.get_mul, hone]
    have hbS := hsb b hb
    have hb1 : bitLen (b.get + 1) ≤ S + 2 := (bitLen_le_succ _).trans (by omega)
    have hbb : bitLen b.get ≤ S + 1 := (bitLen_le_succ _).trans (by omega)
    have hm := bitLen_mul_le acc.get (b.get + 1)
    have hi2 : i * (S + 2) ≤ S * (S + 2) := Nat.mul_le_mul_right _ (by omega)
    have e1 : bitLen acc.get * bitLen (b.get + 1) ≤ (S + S * (S + 2)) * (S + 2) :=
      Nat.mul_le_mul (by omega) hb1
    have hb1' : bitLen 1 = 2 := by decide
    refine ⟨by rw [Nat.add_mul]; omega, by omega⟩
  obtain ⟨k1, k2⟩ := key
  have hl2 : sb.length * (S + 2) ≤ S * (S + 2) := Nat.mul_le_mul_right _ hlen
  have hl3 : sb.length * ((S + 3) + (S + S * (S + 2)) * (S + 2)) ≤
      S * ((S + 3) + (S + S * (S + 2)) * (S + 2)) := Nat.mul_le_mul_right _ hlen
  have a1 : S + S * (S + 2) + 2 ≤ S ^ 4 := by
    obtain ⟨t, rfl⟩ : ∃ t, S = t + 2 := ⟨S - 2, by omega⟩
    ring_nf; omega
  have a2 : S * ((S + 3) + (S + S * (S + 2)) * (S + 2)) ≤ S ^ 8 := by
    obtain ⟨t, rfl⟩ : ∃ t, S = t + 2 := ⟨S - 2, by omega⟩
    ring_nf; omega
  refine ⟨by rw [ratLen_natCast]; omega, by omega⟩

/-- INTERNAL: peel one bind, carrying a property of its value. -/
theorem bind_step' {α β : Type} {p : Prog α} {f : α → Prog β} {a acc X : ℕ} {Q : β → Prop}
    (P : α → Prop) (h1 : Charged.steps rate p ≤ a) (hP : P p.val)
    (h2 : ∀ v, P v → Charged.steps rate (f v) + (acc + a) ≤ X ∧ Q (f v).val) :
    Charged.steps rate (p >>= f) + acc ≤ X ∧ Q (p >>= f).val :=
  bind_step h1 (h2 _ hP)


/-- INTERNAL: `Nat.size n ≤ n`. -/
theorem size_le_self (n : ℕ) : Nat.size n ≤ n := by
  have := bitLen_le_succ n; unfold bitLen at this; omega

/-- INTERNAL: value and price of `Program.clog2`. -/
theorem clog2_le (x : SNat) : (clog2 x).val.get = Nat.size (x.get - 1) ∧
    Charged.steps rate (clog2 x) ≤ 2 * bitLen x.get + 4 := by
  unfold clog2
  simp only [Charged.steps_bind, costVb, steps_SNat_lit, steps_SNat_sub, steps_SNat_size,
    SNat.get_lit, SNat.get_sub, SNat.get_size]
  refine ⟨by first | trivial | rfl, ?_⟩
  have := bitLen_mono (Nat.sub_le x.get 1)
  have : bitLen 1 = 2 := by decide
  omega

/-- INTERNAL: `N_av = ⌈n_3 / η²⌉ ≤ S⁸³` with `η = ε/h`, `h ≤ S¹⁰`, `ε⁻¹ ≤ S`. -/
theorem nav_bound (S : ℕ) (hS : 2 ≤ S) (ε : ℚ) (hε : 0 < ε) (hεi : ε⁻¹ ≤ S) (n : ℕ)
    (hn : n ≤ S ^ 60) (h : ℕ) (hh : 1 ≤ h) (hhS : h ≤ S ^ 10) :
    ⌈(n : ℚ) / (ε / (h : ℚ) * (ε / (h : ℚ)))⌉₊ ≤ S ^ 83 := by
  apply Nat.ceil_le.2
  have hh0 : (0 : ℚ) < h := by exact_mod_cast hh
  have key : (n : ℚ) / (ε / h * (ε / h)) = n * (h * ε⁻¹) ^ 2 := by
    field_simp
  rw [key]
  have hS0 : (0 : ℚ) ≤ S := by positivity
  have a1 : (h : ℚ) * ε⁻¹ ≤ (S : ℚ) ^ 10 * S :=
    mul_le_mul (by exact_mod_cast hhS) hεi (by positivity) (by positivity)
  have a2 : ((h : ℚ) * ε⁻¹) ^ 2 ≤ ((S : ℚ) ^ 10 * S) ^ 2 := pow_le_pow_left₀ (by positivity) a1 2
  have a3 : (n : ℚ) ≤ (S : ℚ) ^ 60 := by exact_mod_cast hn
  have a4 : (n : ℚ) * (h * ε⁻¹) ^ 2 ≤ (S : ℚ) ^ 60 * ((S : ℚ) ^ 10 * S) ^ 2 :=
    mul_le_mul a3 a2 (by positivity) (by positivity)
  have a5 : (S : ℚ) ^ 60 * ((S : ℚ) ^ 10 * S) ^ 2 = (S : ℚ) ^ 82 := by ring
  have a6 : (S : ℚ) ^ 82 ≤ (S : ℚ) ^ 83 := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ S)) (by norm_num)
  push_cast
  linarith

/-- INTERNAL: `ξ⁻¹ = J h/ε ≤ S¹¹⁷`. -/
theorem xi_bound (S : ℕ) (hS : 2 ≤ S) (ε : ℚ) (hε : 0 < ε) (hεi : ε⁻¹ ≤ S) (J : ℕ)
    (hJ : J ≤ S ^ 106) (h : ℕ) (hhS : h ≤ S ^ 10) :
    (ε / (h : ℚ) / (J : ℚ))⁻¹ ≤ ((S ^ 117 : ℕ) : ℚ) := by
  have key : (ε / (h : ℚ) / (J : ℚ))⁻¹ = J * h * ε⁻¹ := by
    simp only [div_eq_mul_inv, mul_inv, inv_inv]; ring
  rw [key]
  have a1 : (J : ℚ) * h ≤ (S : ℚ) ^ 106 * S ^ 10 :=
    mul_le_mul (by exact_mod_cast hJ) (by exact_mod_cast hhS) (by positivity) (by positivity)
  have a2 : (J : ℚ) * h * ε⁻¹ ≤ (S : ℚ) ^ 106 * S ^ 10 * S :=
    mul_le_mul a1 hεi (by positivity) (by positivity)
  have a3 : (S : ℚ) ^ 106 * S ^ 10 * S = (S : ℚ) ^ 117 := by ring
  push_cast
  linarith

/-- INTERNAL: what the setup's output must satisfy at size `T`. -/
def SetupQ (T : ℕ) (C : Ctx) (r : Chain × Phase × List (List SRat) × SRat) : Prop :=
  ChainSize T C r.1 r.2.1 ∧ WSize T r.2.2.1 ∧ ratLen r.2.2.2.get ≤ T

/-- INTERNAL: the explicit bound behind `chainSetup_cost`, at `c = 250`.
TEXLINE: sections/algorithm.tex:526-560 -/
theorem chainSetup_main (S : ℕ) (C : Ctx) (Pm : Params) (pS : SNat) (εS : SRat)
    (hS : 2 ≤ S) (hC : CtxSize S C) (hPm : PmSize S Pm) (hpS : pS.get ≤ S)
    (hε : 0 < εS.get) (hεi : εS.get⁻¹ ≤ S) (hεl : ratLen εS.get ≤ S) :
    Charged.steps rate (chainSetup C Pm pS εS) + 0 ≤ S ^ 250 ∧
    SetupQ (S ^ 250) C (chainSetup C Pm pS εS).val := by
  have U : ∀ e, e ≤ 240 → S ^ e ≤ S ^ 240 := fun e he => pow_mono' hS he
  have h_W : Pm.W.get ≤ S ^ 1 := by rw [pow_one]; exact hPm.W_le
  have h_H : Pm.H.get ≤ S ^ 1 := by rw [pow_one]; exact hPm.H_le
  have h_K : Pm.K.get ≤ S ^ 1 := by rw [pow_one]; exact hPm.K_le
  have h_d : Pm.d.get ≤ S ^ 1 := by rw [pow_one]; exact hPm.d_le
  have h_pS : pS.get ≤ S ^ 1 := by rw [pow_one]; exact hpS
  unfold chainSetup
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := lab_facts S C hS hC
  refine bind_step' (fun v : List ℕ × List ℕ × List SNat × ℕ => v.1.length = v.2.2.2 ∧
      v.2.2.2 ≤ S ^ 2 ∧ (∀ c ∈ v.1, c < C.nSmall) ∧
      (∀ t < C.nSmall, v.1.count t = (C.small.getD t default).2.2.get) ∧
      (∀ f ∈ v.2.1, f ≤ S ^ 2) ∧ (∀ b ∈ v.2.2.1, b.get ≤ S) ∧ v.2.2.1.length = C.nSmall)
    (l8.trans (U 6 (by norm_num))) ⟨l1, l2, l3, l4, l5, l6, l7⟩ ?_
  rintro ⟨pc, cf, sb, p⟩ ⟨f1, f2, f3, f4, f5, f6, f7⟩
  dsimp only at f1 f2 f3 f4 f5 f6 f7 ⊢
  -- one
  refine bind_step' (fun v : SNat => v.get = 1) ((snat_lit_le (a := 0) hS (by simp)).2.trans
    (U 1 (by norm_num))) (SNat.get_lit 1) ?_
  intro one hone
  have h_one : one.get ≤ S ^ 1 := by rw [hone]; exact one_le_pow' hS
  -- H1 = H + 1
  refine bind_step' (fun v : SNat => v.get = Pm.H.get + 1 ∧ v.get ≤ S ^ 2)
    ((snat_add_le hS h_H h_one).2.trans (U 3 (by norm_num)))
    ⟨by rw [SNat.get_add, hone], (snat_add_le hS h_H h_one).1⟩ ?_
  rintro H1 ⟨hH1e, h_H1⟩
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 2)
    ((snat_mul_le hS h_W h_W).2.trans (U _ (by norm_num))) (snat_mul_le hS h_W h_W).1 ?_
  intro q h_q
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 4)
    ((snat_mul_le hS h_q h_q).2.trans (U _ (by norm_num))) (snat_mul_le hS h_q h_q).1 ?_
  intro q2 h_q2
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 6)
    ((snat_mul_le hS h_q2 h_q).2.trans (U _ (by norm_num))) (snat_mul_le hS h_q2 h_q).1 ?_
  intro q3 h_q3
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 3)
    ((snat_lit_le hS (const_le_pow hS 8 3 (by norm_num))).2.trans (U _ (by norm_num))) (snat_lit_le hS (const_le_pow hS 8 3 (by norm_num))).1 ?_
  intro c8 h_c8
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 4)
    ((snat_mul_le hS h_c8 h_pS).2.trans (U _ (by norm_num))) (snat_mul_le hS h_c8 h_pS).1 ?_
  intro p8 h_p8
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 8)
    ((snat_mul_le hS h_p8 h_q2).2.trans (U _ (by norm_num))) (snat_mul_le hS h_p8 h_q2).1 ?_
  intro p8q2 h_p8q2
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 9)
    ((snat_add_le hS (h_one.trans (pow_mono' hS (by norm_num : 1 ≤ 8))) (h_p8q2.trans (pow_mono' hS (by norm_num : 8 ≤ 8)))).2.trans (U _ (by norm_num))) (snat_add_le hS (h_one.trans (pow_mono' hS (by norm_num : 1 ≤ 8))) (h_p8q2.trans (pow_mono' hS (by norm_num : 8 ≤ 8)))).1 ?_
  intro cp1 h_cp1
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 10)
    ((snat_mul_le hS h_pS h_cp1).2.trans (U _ (by norm_num))) (snat_mul_le hS h_pS h_cp1).1 ?_
  intro Cp h_Cp
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 5)
    ((snat_lit_le hS (const_le_pow hS 32 5 (by norm_num))).2.trans (U _ (by norm_num))) (snat_lit_le hS (const_le_pow hS 32 5 (by norm_num))).1 ?_
  intro c32 h_c32
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 6)
    ((snat_mul_le hS h_c32 h_pS).2.trans (U _ (by norm_num))) (snat_mul_le hS h_c32 h_pS).1 ?_
  intro p32 h_p32
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 12)
    ((snat_mul_le hS h_p32 h_q3).2.trans (U _ (by norm_num))) (snat_mul_le hS h_p32 h_q3).1 ?_
  intro p32q3 h_p32q3
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 13)
    ((snat_add_le hS (h_c8.trans (pow_mono' hS (by norm_num : 3 ≤ 12))) (h_p32q3.trans (pow_mono' hS (by norm_num : 12 ≤ 12)))).2.trans (U _ (by norm_num))) (snat_add_le hS (h_c8.trans (pow_mono' hS (by norm_num : 3 ≤ 12))) (h_p32q3.trans (pow_mono' hS (by norm_num : 12 ≤ 12)))).1 ?_
  intro Cd h_Cd
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 4)
    ((snat_lit_le hS (const_le_pow hS 9 4 (by norm_num))).2.trans (U _ (by norm_num))) (snat_lit_le hS (const_le_pow hS 9 4 (by norm_num))).1 ?_
  intro c9 h_c9
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 1 ∧ v.get = 2)
    ((snat_lit_le hS (const_le_pow hS 2 1 (by norm_num))).2.trans (U _ (by norm_num))) ⟨(snat_lit_le hS (const_le_pow hS 2 1 (by norm_num))).1, SNat.get_lit 2⟩ ?_
  intro c2 ⟨h_c2, e_c2⟩
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 14)
    ((snat_mul_le hS h_c9 h_Cp).2.trans (U _ (by norm_num))) (snat_mul_le hS h_c9 h_Cp).1 ?_
  intro t9 h_t9
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 14)
    ((snat_mul_le hS h_c2 h_Cd).2.trans (U _ (by norm_num))) (snat_mul_le hS h_c2 h_Cd).1 ?_
  intro t2 h_t2
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 15)
    ((snat_add_le hS (h_t9.trans (pow_mono' hS (by norm_num : 14 ≤ 14))) (h_t2.trans (pow_mono' hS (by norm_num : 14 ≤ 14)))).2.trans (U _ (by norm_num))) (snat_add_le hS (h_t9.trans (pow_mono' hS (by norm_num : 14 ≤ 14))) (h_t2.trans (pow_mono' hS (by norm_num : 14 ≤ 14)))).1 ?_
  intro t92 h_t92
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 2)
    ((snat_mul_le hS h_pS h_pS).2.trans (U _ (by norm_num))) (snat_mul_le hS h_pS h_pS).1 ?_
  intro p2 h_p2
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 4)
    ((snat_mul_le hS h_p2 h_p2).2.trans (U _ (by norm_num))) (snat_mul_le hS h_p2 h_p2).1 ?_
  intro p4 h_p4
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 4)
    ((snat_lit_le hS (const_le_pow hS 10 4 (by norm_num))).2.trans (U _ (by norm_num))) (snat_lit_le hS (const_le_pow hS 10 4 (by norm_num))).1 ?_
  intro c10 h_c10
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 8)
    ((snat_mul_le hS h_c10 h_p4).2.trans (U _ (by norm_num))) (snat_mul_le hS h_c10 h_p4).1 ?_
  intro p4d h_p4d
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 23)
    ((snat_mul_le hS h_p4d h_t92).2.trans (U _ (by norm_num))) (snat_mul_le hS h_p4d h_t92).1 ?_
  intro Kobs h_Kobs
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 8 ∧ v.get = 200)
    ((snat_lit_le hS (const_le_pow hS 200 8 (by norm_num))).2.trans (U _ (by norm_num))) ⟨(snat_lit_le hS (const_le_pow hS 200 8 (by norm_num))).1, SNat.get_lit 200⟩ ?_
  intro c200 ⟨h_c200, e_c200⟩
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 10 ∧ v.get = 200 * (Pm.H.get + 1))
    ((snat_mul_le hS h_c200 h_H1).2.trans (U _ (by norm_num))) ⟨(snat_mul_le hS h_c200 h_H1).1, by simp only [SNat.get_mul]; rw [e_c200, hH1e]⟩ ?_
  intro h200 ⟨h_h200, e_h200⟩
  refine bind_step' (fun v : SRat => v.get = ((200 * (Pm.H.get + 1) : ℕ) : ℚ) ∧ ratLen v.get ≤ S ^ 12)
    ((snat_toRat_le hS h_h200).2.trans (U _ (by norm_num)))
    ⟨by rw [SNat.get_toRat, e_h200], (snat_toRat_le hS h_h200).1⟩ ?_
  rintro h200q ⟨e_h200q, h_h200q⟩
  have hε12 : ratLen εS.get ≤ S ^ 12 := hεl.trans (by simpa using pow_mono' hS (by norm_num : 1 ≤ 12))
  refine bind_step' (fun v : SRat => v.get = εS.get / ((200 * (Pm.H.get + 1) : ℕ) : ℚ) ∧
      ratLen v.get ≤ S ^ 13)
    (by simp only [steps_SRat_div]; exact (srat_bin_le hS hε12 h_h200q).trans (U _ (by norm_num)))
    ⟨by rw [SRat.get_div, e_h200q], by rw [SRat.get_div]; exact srat_div_len hS hε12 h_h200q⟩ ?_
  rintro η ⟨e_η, h_η⟩
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 3)
    ((snat_lit_le hS (const_le_pow hS 5 3 (by norm_num))).2.trans (U _ (by norm_num))) (snat_lit_le hS (const_le_pow hS 5 3 (by norm_num))).1 ?_
  intro c5 h_c5
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 2)
    ((snat_add_le hS (h_H.trans (pow_mono' hS (by norm_num : 1 ≤ 1))) (h_pS.trans (pow_mono' hS (by norm_num : 1 ≤ 1)))).2.trans (U _ (by norm_num))) (snat_add_le hS (h_H.trans (pow_mono' hS (by norm_num : 1 ≤ 1))) (h_pS.trans (pow_mono' hS (by norm_num : 1 ≤ 1)))).1 ?_
  intro s1 h_s1
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 3)
    ((snat_add_le hS (h_s1.trans (pow_mono' hS (by norm_num : 2 ≤ 2))) (h_K.trans (pow_mono' hS (by norm_num : 1 ≤ 2)))).2.trans (U _ (by norm_num))) (snat_add_le hS (h_s1.trans (pow_mono' hS (by norm_num : 2 ≤ 2))) (h_K.trans (pow_mono' hS (by norm_num : 1 ≤ 2)))).1 ?_
  intro s2 h_s2
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 4)
    ((snat_add_le hS (h_s2.trans (pow_mono' hS (by norm_num : 3 ≤ 3))) (h_c5.trans (pow_mono' hS (by norm_num : 3 ≤ 3)))).2.trans (U _ (by norm_num))) (snat_add_le hS (h_s2.trans (pow_mono' hS (by norm_num : 3 ≤ 3))) (h_c5.trans (pow_mono' hS (by norm_num : 3 ≤ 3)))).1 ?_
  intro s3 h_s3
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 24)
    ((snat_mul_le hS h_c2 h_Kobs).2.trans (U _ (by norm_num))) (snat_mul_le hS h_c2 h_Kobs).1 ?_
  intro k2 h_k2
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 28)
    ((snat_mul_le hS h_k2 h_s3).2.trans (U _ (by norm_num))) (snat_mul_le hS h_k2 h_s3).1 ?_
  intro τ h_τ
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 11)
    ((snat_lit_le hS (const_le_pow hS 2000 11 (by norm_num))).2.trans (U _ (by norm_num))) (snat_lit_le hS (const_le_pow hS 2000 11 (by norm_num))).1 ?_
  intro c2000 h_c2000
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 4)
    ((snat_mul_le hS h_H1 h_H1).2.trans (U _ (by norm_num))) (snat_mul_le hS h_H1 h_H1).1 ?_
  intro H1sq h_H1sq
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 13)
    ((snat_mul_le hS h_c2000 h_p2).2.trans (U _ (by norm_num))) (snat_mul_le hS h_c2000 h_p2).1 ?_
  intro b1 h_b1
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 17)
    ((snat_mul_le hS h_b1 h_H1sq).2.trans (U _ (by norm_num))) (snat_mul_le hS h_b1 h_H1sq).1 ?_
  intro b2 h_b2
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 45)
    ((snat_mul_le hS h_b2 h_τ).2.trans (U _ (by norm_num))) (snat_mul_le hS h_b2 h_τ).1 ?_
  intro Bret h_Bret
  refine bind_step' (fun v : ℕ => v = Bret.get)
    (by simp only [steps_SNat_index]; exact (bitLen_le_pow hS h_Bret).trans (U _ (by norm_num)))
    (SNat.val_index Bret) ?_
  rintro BretN e_BretN
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 8)
    ((snat_mul_le hS h_p4 h_p4).2.trans (U _ (by norm_num))) (snat_mul_le hS h_p4 h_p4).1 ?_
  intro p8d h_p8d
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 27)
    ((snat_lit_le hS (const_le_pow hS 100000000 27 (by norm_num))).2.trans (U _ (by norm_num))) (snat_lit_le hS (const_le_pow hS 100000000 27 (by norm_num))).1 ?_
  intro c1e8 h_c1e8
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 35)
    ((snat_mul_le hS h_c1e8 h_p8d).2.trans (U _ (by norm_num))) (snat_mul_le hS h_c1e8 h_p8d).1 ?_
  intro n1 h_n1
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 58)
    ((snat_mul_le hS h_n1 h_Kobs).2.trans (U _ (by norm_num))) (snat_mul_le hS h_n1 h_Kobs).1 ?_
  intro n2 h_n2
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 60)
    ((snat_mul_le hS h_n2 h_H1).2.trans (U _ (by norm_num))) (snat_mul_le hS h_n2 h_H1).1 ?_
  intro n3 h_n3
  refine bind_step' (fun v : SRat => v.get = (n3.get : ℚ) ∧ ratLen v.get ≤ S ^ 62)
    ((snat_toRat_le hS h_n3).2.trans (U _ (by norm_num)))
    ⟨SNat.get_toRat n3, (snat_toRat_le hS h_n3).1⟩ ?_
  rintro n3q ⟨e_n3q, h_n3q⟩
  refine bind_step' (fun v : SRat => v.get = η.get * η.get ∧ ratLen v.get ≤ S ^ 14)
    (by simp only [steps_SRat_mul]; exact (srat_bin_le hS h_η h_η).trans (U _ (by norm_num)))
    ⟨SRat.get_mul η η, by rw [SRat.get_mul]; exact srat_mul_len hS h_η h_η⟩ ?_
  rintro η2 ⟨e_η2, h_η2⟩
  have h_η2' : ratLen η2.get ≤ S ^ 62 := h_η2.trans (pow_mono' hS (by norm_num))
  refine bind_step' (fun v : SRat => v.get = n3q.get / η2.get ∧ ratLen v.get ≤ S ^ 63)
    (by simp only [steps_SRat_div]; exact (srat_bin_le hS h_n3q h_η2').trans (U _ (by norm_num)))
    ⟨SRat.get_div n3q η2, by rw [SRat.get_div]; exact srat_div_len hS h_n3q h_η2'⟩ ?_
  rintro navq ⟨e_navq, h_navq⟩
  refine bind_step' (fun v : SNat => v.get = ⌈navq.get⌉₊)
    (by simp only [steps_SRat_natCeil]; exact (srat_bin_le hS h_navq h_navq).trans (U _ (by norm_num)))
    (SRat.get_natCeil navq) ?_
  rintro Nav e_Nav
  have h_Nav : Nav.get ≤ S ^ 83 := by
    rw [e_Nav, e_navq, e_n3q, e_η2, e_η]
    exact nav_bound S hS εS.get hε hεi n3.get h_n3 (200 * (Pm.H.get + 1)) (by omega)
      (by rw [← e_h200]; exact h_h200)
  refine bind_step' (fun v : ℕ => v = Nav.get)
    (by simp only [steps_SNat_index]; exact (bitLen_le_pow hS h_Nav).trans (U _ (by norm_num)))
    (SNat.val_index Nav) ?_
  rintro NavN e_NavN
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 7 ∧ v.get = 100)
    ((snat_lit_le hS (const_le_pow hS 100 7 (by norm_num))).2.trans (U _ (by norm_num))) ⟨(snat_lit_le hS (const_le_pow hS 100 7 (by norm_num))).1, SNat.get_lit 100⟩ ?_
  intro c100 ⟨h_c100, e_c100⟩
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 84)
    ((snat_add_le hS (h_Bret.trans (pow_mono' hS (by norm_num : 45 ≤ 83))) (h_Nav.trans (pow_mono' hS (by norm_num : 83 ≤ 83)))).2.trans (U _ (by norm_num))) (snat_add_le hS (h_Bret.trans (pow_mono' hS (by norm_num : 45 ≤ 83))) (h_Nav.trans (pow_mono' hS (by norm_num : 83 ≤ 83)))).1 ?_
  intro j1 h_j1
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 85)
    ((snat_add_le hS (h_j1.trans (pow_mono' hS (by norm_num : 84 ≤ 84))) (h_pS.trans (pow_mono' hS (by norm_num : 1 ≤ 84)))).2.trans (U _ (by norm_num))) (snat_add_le hS (h_j1.trans (pow_mono' hS (by norm_num : 84 ≤ 84))) (h_pS.trans (pow_mono' hS (by norm_num : 1 ≤ 84)))).1 ?_
  intro j2 h_j2
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 86)
    ((snat_add_le hS (h_j2.trans (pow_mono' hS (by norm_num : 85 ≤ 85))) (h_d.trans (pow_mono' hS (by norm_num : 1 ≤ 85)))).2.trans (U _ (by norm_num))) (snat_add_le hS (h_j2.trans (pow_mono' hS (by norm_num : 85 ≤ 85))) (h_d.trans (pow_mono' hS (by norm_num : 1 ≤ 85)))).1 ?_
  intro j3 h_j3
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 87 ∧ 1 ≤ v.get)
    ((snat_add_le hS (h_j3.trans (pow_mono' hS (by norm_num : 86 ≤ 86))) (h_one.trans (pow_mono' hS (by norm_num : 1 ≤ 86)))).2.trans (U _ (by norm_num))) ⟨(snat_add_le hS (h_j3.trans (pow_mono' hS (by norm_num : 86 ≤ 86))) (h_one.trans (pow_mono' hS (by norm_num : 1 ≤ 86)))).1, by simp only [SNat.get_add]; rw [hone]; omega⟩ ?_
  intro j4 ⟨h_j4, e_j4⟩
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 9 ∧ 1 ≤ v.get)
    ((snat_mul_le hS h_c100 h_H1).2.trans (U _ (by norm_num))) ⟨(snat_mul_le hS h_c100 h_H1).1, by simp only [SNat.get_mul]; rw [e_c100, hH1e]; omega⟩ ?_
  intro h100 ⟨h_h100, e_h100⟩
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 96 ∧ 1 ≤ v.get)
    ((snat_mul_le hS h_h100 h_j4).2.trans (U _ (by norm_num))) ⟨(snat_mul_le hS h_h100 h_j4).1, by simp only [SNat.get_mul]; exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))⟩ ?_
  intro Jstar ⟨h_Jstar, e_Jstar⟩
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 10 ∧ v.get = 1000)
    ((snat_lit_le hS (const_le_pow hS 1000 10 (by norm_num))).2.trans (U _ (by norm_num))) ⟨(snat_lit_le hS (const_le_pow hS 1000 10 (by norm_num))).1, SNat.get_lit 1000⟩ ?_
  intro c1000 ⟨h_c1000, e_c1000⟩
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 106 ∧ 1 ≤ v.get)
    ((snat_mul_le hS h_c1000 h_Jstar).2.trans (U _ (by norm_num))) ⟨(snat_mul_le hS h_c1000 h_Jstar).1, by simp only [SNat.get_mul]; rw [e_c1000]; omega⟩ ?_
  intro J1000 ⟨h_J1000, e_J1000⟩
  refine bind_step' (fun v : SRat => v.get = (J1000.get : ℚ) ∧ ratLen v.get ≤ S ^ 108)
    ((snat_toRat_le hS h_J1000).2.trans (U _ (by norm_num)))
    ⟨SNat.get_toRat J1000, (snat_toRat_le hS h_J1000).1⟩ ?_
  rintro Jq ⟨e_Jq, h_Jq⟩
  have h_η' : ratLen η.get ≤ S ^ 108 := h_η.trans (pow_mono' hS (by norm_num))
  refine bind_step' (fun v : SRat => v.get = η.get / Jq.get ∧ ratLen v.get ≤ S ^ 109)
    (by simp only [steps_SRat_div]; exact (srat_bin_le hS h_η' h_Jq).trans (U _ (by norm_num)))
    ⟨SRat.get_div η Jq, by rw [SRat.get_div]; exact srat_div_len hS h_η' h_Jq⟩ ?_
  rintro ξ ⟨e_ξ, h_ξ⟩
  have hr1 : ratLen (1 : ℚ) = 4 := by
    have h := ratLen_natCast 1; push_cast at h; rw [h]; decide
  have h4 : 4 ≤ S ^ 2 := by have := Nat.pow_le_pow_left hS 2; norm_num at this; omega
  refine bind_step' (fun v : SRat => v.get = 1 ∧ ratLen v.get ≤ S ^ 109)
    (by simp only [steps_SRat_lit, hr1]; exact h4.trans (U _ (by norm_num)))
    ⟨SRat.get_lit 1, by rw [SRat.get_lit, hr1]; exact h4.trans (pow_mono' hS (by norm_num))⟩ ?_
  rintro oneQ ⟨e_oneQ, h_oneQ⟩
  refine bind_step' (fun v : SRat => v.get = oneQ.get / ξ.get ∧ ratLen v.get ≤ S ^ 110)
    (by simp only [steps_SRat_div]; exact (srat_bin_le hS h_oneQ h_ξ).trans (U _ (by norm_num)))
    ⟨SRat.get_div oneQ ξ, by rw [SRat.get_div]; exact srat_div_len hS h_oneQ h_ξ⟩ ?_
  rintro invξ ⟨e_invξ, h_invξ⟩
  refine bind_step' (fun v : SNat => v.get = ⌈invξ.get⌉₊)
    (by simp only [steps_SRat_natCeil]; exact (srat_bin_le hS h_invξ h_invξ).trans (U _ (by norm_num)))
    (SRat.get_natCeil invξ) ?_
  rintro cξ e_cξ
  have hξpos : 0 < ξ.get := by
    rw [e_ξ, e_η, e_Jq]
    have : (0 : ℚ) < J1000.get := by exact_mod_cast e_J1000
    positivity
  have hξinv : ξ.get⁻¹ ≤ ((S ^ 117 : ℕ) : ℚ) := by
    rw [e_ξ, e_η, e_Jq]
    exact xi_bound S hS εS.get hε hεi J1000.get h_J1000 (200 * (Pm.H.get + 1))
      (by rw [← e_h200]; exact h_h200)
  have h_cξ : cξ.get ≤ S ^ 118 := by
    rw [e_cξ, e_invξ, e_oneQ, one_div]
    apply Nat.ceil_le.2
    refine hξinv.trans ?_
    exact_mod_cast pow_mono' hS (by norm_num)
  have hcl : 2 * bitLen cξ.get + 4 ≤ S ^ 240 := by
    have : bitLen cξ.get ≤ S ^ 119 := bitLen_le_pow hS h_cξ
    have : 2 * S ^ 119 ≤ S ^ 120 := pow_succ_ge hS
    have : 2 * S ^ 120 ≤ S ^ 121 := pow_succ_ge hS
    have := U 121 (by norm_num)
    have : S ^ 2 ≤ S ^ 120 := pow_mono' hS (by norm_num)
    omega
  refine bind_step' (fun v : SNat => v.get ≤ S ^ 118)
    ((clog2_le cξ).2.trans hcl)
    (by rw [(clog2_le cξ).1]; exact (size_le_self _).trans ((Nat.sub_le _ _).trans h_cξ)) ?_
  rintro kAccS h_kAccS
  refine bind_step' (fun v : ℕ => v = kAccS.get)
    (by simp only [steps_SNat_index]; exact (bitLen_le_pow hS h_kAccS).trans (U _ (by norm_num)))
    (SNat.val_index kAccS) ?_
  rintro kAcc e_kAcc
  refine bind_step' (fun v : ℕ => v = Pm.H.get)
    (by simp only [steps_SNat_index]; exact (bitLen_le_pow hS h_H).trans (U _ (by norm_num)))
    (SNat.val_index Pm.H) ?_
  rintro Hn e_Hn
  have hr6 : ratLen (6 : ℚ) = 6 := by decide
  have h6 : 6 ≤ S ^ 3 := by have := Nat.pow_le_pow_left hS 3; norm_num at this; omega
  refine bind_step' (fun v : SRat => v.get = 6)
    (by simp only [steps_SRat_lit, hr6]; exact h6.trans (U _ (by norm_num))) (SRat.get_lit 6) ?_
  rintro six e_six
  refine bind_step' (fun v : SRat => v.get = 0)
    (by simp only [steps_SRat_lit, ratLen_zero]; exact (show 3 ≤ S ^ 2 by omega).trans (U _ (by norm_num)))
    (SRat.get_lit 0) ?_
  rintro zeroQ e_zeroQ
  have hp3 : p + 1 ≤ S ^ 240 := by
    have : 2 * S ^ 2 ≤ S ^ 3 := pow_succ_ge hS
    have := U 3 (by norm_num); omega
  refine bind_step' (fun v : List SRat => v = List.replicate p zeroQ)
    (by simp only [steps_replicate]; exact hp3) (val_replicate p zeroQ) ?_
  rintro row e_row
  refine bind_step' (fun v : List (List SRat) => v = List.replicate p row)
    (by simp only [steps_replicate]; exact hp3) (val_replicate p row) ?_
  rintro tab e_tab
  have htab : WSize 3 tab := by
    rw [e_tab, e_row]
    intro r hr x hx
    rw [List.mem_replicate] at hr; rw [hr.2, List.mem_replicate] at hx
    rw [hx.2, e_zeroQ, ratLen_zero]
  have hpcS : ∀ c ∈ pc, c < S := fun c hc => lt_of_lt_of_le (f3 c hc) hC.nSmall_le
  obtain ⟨w1, w2⟩ := w0_facts S p hS f2 pc sb hpcS f6 one c2 six hone e_c2 e_six tab htab
  refine bind_step' (fun v : List (List SRat) => WSize (S ^ 5) v) (w2.trans (U _ (by norm_num)))
    w1 ?_
  rintro w0 h_w0
  obtain ⟨c1, c2'⟩ := c0_facts S hS C.Mf hC.Mf_bits sb f6 (f7 ▸ hC.nSmall_le) one hone
  refine bind_step' (fun v : SNat => ratLen (v.get : ℚ) ≤ S ^ 4) (c2'.trans (U _ (by norm_num)))
    c1 ?_
  rintro c0 h_c0
  refine bind_step' (a := S ^ 240) (fun v : SRat => ratLen v.get ≤ S ^ 4)
    (by simp only [steps_SNat_toRat]; rw [ratLen_natCast] at h_c0; have := U 4 (by norm_num); omega)
    (by rw [SNat.get_toRat]; exact h_c0) ?_
  rintro C0 h_C0
  simp only [Charged.steps_pure, costVp]
  have M : ∀ e, e ≤ 250 → S ^ e ≤ S ^ 250 := fun e he => pow_mono' hS he
  have h1024 : 1024 * S ^ 240 ≤ S ^ 250 := by
    have : 2 ^ 10 ≤ S ^ 10 := Nat.pow_le_pow_left hS 10
    have : S ^ 250 = S ^ 10 * S ^ 240 := by rw [← pow_add]
    rw [this]; exact Nat.mul_le_mul_right _ (by norm_num at *; omega)
  refine ⟨by omega, ?_⟩
  have hS1 : S ≤ S ^ 250 := by simpa using M 1 (by norm_num)
  refine ⟨⟨f2.trans (M 2 (by norm_num)), hpS.trans hS1, rfl, hC.nSmall_le.trans hS1, f1, f3,
    fun t ht => (f4 t ht).le, fun f hf => (f5 f hf).trans (M 2 (by norm_num)),
    fun b hb => (f6 b hb).trans hS1, hξpos, hξinv.trans (by exact_mod_cast M 117 (by norm_num)),
    h_ξ.trans (M 109 (by norm_num)), by rw [e_kAcc]; exact h_kAccS.trans (M 118 (by norm_num)),
    h_kAccS.trans (M 118 (by norm_num)), h_τ.trans (M 28 (by norm_num)),
    h_Bret.trans (M 45 (by norm_num)), by rw [e_BretN]; exact h_Bret.trans (M 45 (by norm_num)),
    h_Nav.trans (M 83 (by norm_num)), by rw [e_NavN]; exact h_Nav.trans (M 83 (by norm_num)),
    by rw [e_Hn]; exact hPm.H_le.trans hS1⟩, h_w0.mono (M 5 (by norm_num)),
    h_C0.trans (M 4 (by norm_num))⟩

/-- **The setup S8 is polynomial.**
INTERNAL: the setup half of the resource bound of `lem:bounded-implementation`.
TEXLINE: sections/algorithm.tex:526-560 ("All quantities in eq:alg-phase-parameters and
eq:alg-bit-parameters, including `ξ⁻¹`, are …" polynomial) -/
theorem chainSetup_cost : ∃ c : ℕ, ∀ (S : ℕ) (C : Ctx) (Pm : Params) (pS : SNat) (εS : SRat),
    2 ≤ S → CtxSize S C → PmSize S Pm → pS.get ≤ S →
    0 < εS.get → εS.get⁻¹ ≤ S → ratLen εS.get ≤ S →
    Charged.steps rate (chainSetup C Pm pS εS) ≤ S ^ c ∧
    ChainSize (S ^ c) C (chainSetup C Pm pS εS).val.1 (chainSetup C Pm pS εS).val.2.1 ∧
    WSize (S ^ c) (chainSetup C Pm pS εS).val.2.2.1 ∧
    ratLen (chainSetup C Pm pS εS).val.2.2.2.get ≤ S ^ c := by
  refine ⟨250, fun S C Pm pS εS hS hC hPm hpS hε hεi hεl => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := chainSetup_main S C Pm pS εS hS hC hPm hpS hε hεi hεl
  exact ⟨by simpa using h1, h2, h3, h4⟩

end Cellcounting.Analysis
