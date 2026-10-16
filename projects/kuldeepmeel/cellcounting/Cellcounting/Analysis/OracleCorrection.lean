import Cellcounting.Analysis.BinLaw
import Cellcounting.Analysis.PenaltyLipschitz
import Cellcounting.Analysis.Contamination
import Cellcounting.Analysis.Pow2Approx

/-!
# The mean of one correction sample (`eq:oracle-correction`)

`evaluation.tex:95-125`: draw a bin `v ~ π_j`, then a uniform integer point `z ∈ I_v`,
and observe `T(v, z) = α_v 2^β` with `α_v = B^e |I_v| / M_f` and
`β = ⌊jD(v)/H⌋ - jD(z)/H`; the oracle uses the bisection value of `2^β`.

`corrLaw` is that observation under the ideal laws (`binLaw`, `idealOffsets`), and
`corr_mean` computes its mean: it is within relative error `σ` of
`E T = B^e h_j(x, y) / (M_f S_j)`, it is at least `(1 - σ)/8`, and every observation
lies in `[0, 16]`.  The ingredients are the decomposition of the free box into the
integer bins (`sum_bins`), the bin populations `1/2 ≤ α_v ≤ 2`
(`eq:bin-populations`, `alpha_bounds`), and `β ∈ [-2, 2]` from the Lipschitz bound
for `D` (`beta_bounds`).
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal
open Classical

/-! ### One coordinate of a bin -/

section coord

/-- INTERNAL: `a ⌈/⌉ B ≤ z ↔ a ≤ B z`. -/
theorem ceilDiv_le_iff' {B : ℕ} (hB : 0 < B) (a z : ℕ) : a ⌈/⌉ B ≤ z ↔ a ≤ B * z :=
  ceilDiv_le_iff_le_mul hB

/-- INTERNAL: `a ≤ B ⌈a/B⌉`. -/
theorem le_mul_ceilDiv {B : ℕ} (hB : 0 < B) (a : ℕ) : a ≤ B * (a ⌈/⌉ B) :=
  (ceilDiv_le_iff_le_mul hB).1 le_rfl

/-- INTERNAL: `B ⌈a/B⌉ < a + B`. -/
theorem mul_ceilDiv_lt {B : ℕ} (hB : 0 < B) (a : ℕ) : B * (a ⌈/⌉ B) < a + B := by
  rcases Nat.eq_zero_or_pos (a ⌈/⌉ B) with h | h
  · rw [h]; omega
  · obtain ⟨c, hc⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
    have h1 : ¬ (a ⌈/⌉ B ≤ c) := by omega
    rw [ceilDiv_le_iff_le_mul hB] at h1
    rw [hc, Nat.mul_succ]
    omega

/-- INTERNAL: the bin of an integer point: `⌊B z / N⌋ = v ↔ ⌈Nv/B⌉ ≤ z < ⌈N(v+1)/B⌉`. -/
theorem div_eq_iff_mem_bin {B N : ℕ} (hB : 0 < B) (hN : 0 < N) (z v : ℕ) :
    B * z / N = v ↔ N * v ⌈/⌉ B ≤ z ∧ z < N * (v + 1) ⌈/⌉ B := by
  rw [ceilDiv_le_iff' hB, ← not_le, ceilDiv_le_iff' hB, Nat.div_eq_iff hN]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [mul_comm]; exact h1, ?_⟩
    rw [not_le]
    have : N * (v + 1) = v * N + N := by ring
    omega
  · rintro ⟨h1, h2⟩
    rw [not_le] at h2
    refine ⟨by rw [mul_comm]; exact h1, ?_⟩
    have : N * (v + 1) = v * N + N := by ring
    omega

end coord

/-! ### The free box is the disjoint union of the bins -/

/-- INTERNAL: a sum over the integer box `∏_k {0, …, N_k - 1}` is a sum over the bins
`u ∈ {0, …, B-1}^e` of the sums over their integer intervals
`[⌈N_k u_k/B⌉, ⌈N_k (u_k+1)/B⌉)`.
TEXLINE: sections/evaluation.tex:52-61 -/
theorem sum_bins {e : ℕ} (B : ℕ) (hB : 0 < B) (N : Fin e → ℕ) (hN : ∀ k, 0 < N k)
    (F : (Fin e → ℕ) → ℝ) :
    ∑ u ∈ Fintype.piFinset (fun _ : Fin e => Finset.range B),
      ∑ o ∈ Fintype.piFinset (fun k => Finset.range (N k * (u k + 1) ⌈/⌉ B - N k * u k ⌈/⌉ B)),
        F (fun k => N k * u k ⌈/⌉ B + o k) =
    ∑ z ∈ Fintype.piFinset (fun k => Finset.range (N k)), F z := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Fintype.piFinset (fun k => Finset.range (N k)))
    (g := fun z k => B * z k / N k) (t := Fintype.piFinset (fun _ : Fin e => Finset.range B))]
  · refine Finset.sum_congr rfl fun u hu => ?_
    have hfib : (Fintype.piFinset (fun k => Finset.range (N k))).filter
        (fun z => (fun k => B * z k / N k) = u) =
        (Fintype.piFinset (fun k => Finset.range (N k * (u k + 1) ⌈/⌉ B - N k * u k ⌈/⌉ B))).image
          (fun o k => N k * u k ⌈/⌉ B + o k) := by
      ext z
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hz, hzu⟩
        refine ⟨fun k => z k - N k * u k ⌈/⌉ B, fun k => ?_, ?_⟩
        · have := (div_eq_iff_mem_bin hB (hN k) (z k) (u k)).1 (congrFun hzu k)
          dsimp only; omega
        · funext k
          have := (div_eq_iff_mem_bin hB (hN k) (z k) (u k)).1 (congrFun hzu k)
          simp only; omega
      · rintro ⟨o, ho, rfl⟩
        have hu' := Fintype.mem_piFinset.1 hu
        refine ⟨fun k => ?_, funext fun k => ?_⟩
        · have h1 := ho k
          have h2 : B * (N k * u k ⌈/⌉ B + o k) < N k * (u k + 1) := by
            have := (ceilDiv_le_iff' hB (N k * (u k + 1)) (N k * u k ⌈/⌉ B + o k)).not.1
              (by omega)
            omega
          have h3 : u k + 1 ≤ B := Finset.mem_range.1 (hu' k)
          have h4 : N k * (u k + 1) ≤ N k * B := Nat.mul_le_mul_left _ h3
          have h5 : B * (N k * u k ⌈/⌉ B + o k) < B * N k := by nlinarith
          exact Nat.lt_of_mul_lt_mul_left h5
        · have h1 := ho k
          exact (div_eq_iff_mem_bin hB (hN k) _ (u k)).2 ⟨by dsimp only; omega, by dsimp only; omega⟩
    rw [hfib, Finset.sum_image]
    intro o₁ _ o₂ _ h
    funext k
    have := congrFun h k
    simp only at this
    omega
  · intro z hz
    simp only [Fintype.mem_piFinset, Finset.mem_range] at hz ⊢
    intro k
    exact (Nat.div_lt_iff_lt_mul (hN k)).2 (by
      have := hz k
      exact Nat.mul_lt_mul_of_pos_left this hB)

/-! ### Products of factors near one -/

/-- INTERNAL: `e` factors within `c` of one, with `e c ≤ 1/100`, have product in `[1/2, 2]`.
TEXLINE: sections/evaluation.tex:62-69 -/
theorem prod_near_one (e : ℕ) (r : ℕ → ℝ) (c : ℝ) (hc0 : 0 ≤ c) (hce : (e : ℝ) * c ≤ 1 / 100)
    (hr : ∀ k < e, 1 - c ≤ r k ∧ r k ≤ 1 + c) :
    1 / 2 ≤ ∏ k ∈ Finset.range e, r k ∧ ∏ k ∈ Finset.range e, r k ≤ 2 := by
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he; norm_num
  have hc1 : c ≤ 1 / 100 := by
    have : (1 : ℝ) ≤ e := by exact_mod_cast he
    nlinarith
  have hlow : (1 - c) ^ e ≤ ∏ k ∈ Finset.range e, r k := by
    rw [show (1 - c) ^ e = ∏ _k ∈ Finset.range e, (1 - c) by simp]
    exact Finset.prod_le_prod₀ (fun _ _ => by linarith) (fun k hk => (hr k (Finset.mem_range.1 hk)).1)
  have hup : ∏ k ∈ Finset.range e, r k ≤ (1 + c) ^ e := by
    rw [show (1 + c) ^ e = ∏ _k ∈ Finset.range e, (1 + c) by simp]
    exact Finset.prod_le_prod₀ (fun k hk => by linarith [(hr k (Finset.mem_range.1 hk)).1])
      (fun k hk => (hr k (Finset.mem_range.1 hk)).2)
  have hbern : 1 - (e : ℝ) * c ≤ (1 - c) ^ e := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -c by linarith) e
    rw [sub_eq_add_neg, sub_eq_add_neg]; nlinarith
  have hprod : (1 + c) ^ e * (1 - c) ^ e ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  refine ⟨by linarith, hup.trans ?_⟩
  have h99 : (99 : ℝ) / 100 ≤ (1 - c) ^ e := by linarith
  have hpos : 0 < (1 - c) ^ e := by linarith
  have : (1 + c) ^ e ≤ 1 / (1 - c) ^ e := by
    rw [le_div_iff₀ hpos]; exact hprod
  calc (1 + c) ^ e ≤ 1 / (1 - c) ^ e := this
    _ ≤ 1 / (99 / 100) := by gcongr
    _ ≤ 2 := by norm_num

end Cellcounting.Analysis
