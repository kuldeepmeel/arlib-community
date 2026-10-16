import Cellcounting.Analysis.PmfClose

/-!
# The finite-bit uniform integer draw (`lem:dyadic-integer-draw`)

`evaluation.tex:356-371`: for `M > 0` and `ζ > 0`, `Pseudocode.dyadicDraw M ζ`
reads `k` fair bits as `Y` uniform on `[0, 2^k)`, with `M 2^{-k} ≤ ζ`, and returns
`⌊M Y / 2^k⌋`.  Every output `y < M` has at least `2^k/M - 1` preimages, so the
uniform law on `[0, M)` exceeds the draw by at most `2^{-k}` at each point, and by
at most `M 2^{-k} ≤ ζ` in total.

`idealDraw M` is the exact uniform law on `[0, M)`, read as the point mass at `0`
when `M = 0`, which is also what `dyadicDraw 0 ζ` returns.
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal

/-- INTERNAL: the exact uniform draw on `[0, M)` (the point mass at `0` if `M = 0`). -/
noncomputable def idealDraw (M : ℕ) : PMF ℕ :=
  if h : 0 < M then PMF.uniformOfFinset (Finset.range M) (Finset.nonempty_range_iff.2 h.ne')
  else PMF.pure 0

/-- INTERNAL: `uniformBits` with its nonemptiness proof in `Finset.Nonempty` form. -/
theorem uniformBits_eq (k : ℕ) :
    uniformBits k = PMF.uniformOfFinset (Finset.range (2 ^ k))
      (Finset.nonempty_range_iff.2 (Nat.two_pow_pos k).ne') := rfl

/-- INTERNAL: every value `y < M` of `⌊M Y / K⌋`, `Y < K`, has at least
`K / M - 1` preimages. -/
theorem card_preimage_div (M K y : ℕ) (hM : 0 < M) (hy : y < M) :
    K ≤ ((Finset.range K).filter fun Y => M * Y / K = y).card * M + M := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp
  set a := (y * K + M - 1) / M with ha
  set b := ((y + 1) * K + M - 1) / M with hb
  have ha1 : y * K ≤ M * a := by
    have h1 := Nat.div_add_mod (y * K + M - 1) M
    have h2 := Nat.mod_lt (y * K + M - 1) hM
    rw [← ha] at h1; omega
  have ha2 : M * a ≤ y * K + M - 1 := by
    have h1 := Nat.div_add_mod (y * K + M - 1) M
    rw [← ha] at h1; omega
  have hb1 : (y + 1) * K ≤ M * b := by
    have h1 := Nat.div_add_mod ((y + 1) * K + M - 1) M
    have h2 := Nat.mod_lt ((y + 1) * K + M - 1) hM
    rw [← hb] at h1; omega
  have hb2 : M * b ≤ (y + 1) * K + M - 1 := by
    have h1 := Nat.div_add_mod ((y + 1) * K + M - 1) M
    rw [← hb] at h1; omega
  clear_value a b
  have hbK : b ≤ K := by
    by_contra h
    have : M * (K + 1) ≤ M * b := Nat.mul_le_mul_left _ (by omega)
    have h3 : (y + 1) * K ≤ M * K := Nat.mul_le_mul_right _ hy
    rw [mul_add, mul_one] at this
    omega
  have hsub : Finset.Ico a b ⊆ (Finset.range K).filter fun Y => M * Y / K = y := by
    intro Y hY
    rw [Finset.mem_Ico] at hY
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have hY1 : M * a ≤ M * Y := Nat.mul_le_mul_left _ hY.1
    have hY2 : M * (Y + 1) ≤ M * b := Nat.mul_le_mul_left _ hY.2
    rw [Nat.div_eq_iff hK]
    constructor
    · linarith
    · rw [mul_add, mul_one] at hY2
      have : (y + 1) * K = y * K + K := by ring
      omega
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hcard
  have hab : M * (b - a) + M * a = M * b := by
    rw [← mul_add]; congr 1
    have : a ≤ b := by
      by_contra h
      have h4 : M * (b + 1) ≤ M * a := Nat.mul_le_mul_left _ (by omega)
      rw [mul_add, mul_one] at h4
      have : (y + 1) * K = y * K + K := by ring
      omega
    omega
  have : M * (b - a) ≤ M * ((Finset.range K).filter fun Y => M * Y / K = y).card :=
    Nat.mul_le_mul_left _ hcard
  have e1 : (y + 1) * K = y * K + K := by ring
  have e2 : ((Finset.range K).filter fun Y => M * Y / K = y).card * M =
      M * ((Finset.range K).filter fun Y => M * Y / K = y).card := Nat.mul_comm _ _
  omega

/-- **`lem:dyadic-integer-draw`**: the dyadic draw is within total variation `ζ`
of the uniform law on `[0, M)`.
PAPER: sections/evaluation.tex:356-371 -/
theorem dyadicDraw_close (M : ℕ) (ζ : ℚ) (hζ : 0 < ζ) :
    PClose (idealDraw M) (dyadicDraw M ζ) (ENNReal.ofReal ζ) := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    have : dyadicDraw 0 ζ = PMF.pure 0 := by
      simp only [dyadicDraw, zero_mul, Nat.zero_div]
      exact PMF.map_const _ _
    rw [this, idealDraw, dif_neg (lt_irrefl 0)]
    exact PClose.refl _ _
  set k := Nat.clog 2 ⌈(M : ℚ) / ζ⌉₊ with hk
  set K := 2 ^ k with hK
  have hKpos : 0 < K := Nat.two_pow_pos k
  -- `M ≤ ζ K`
  have hMK : (M : ℚ) ≤ ζ * K := by
    have h1 : ⌈(M : ℚ) / ζ⌉₊ ≤ K := Nat.le_pow_clog one_lt_two _
    have h2 : (M : ℚ) / ζ ≤ K := (Nat.le_ceil _).trans (by exact_mod_cast h1)
    rwa [div_le_iff₀ hζ, mul_comm] at h2
  refine PClose.of_pointwise (fun y => if y < M then (K : ℝ≥0∞)⁻¹ else 0) ?_ ?_
  · intro y
    rw [idealDraw, dif_pos hM]
    by_cases hy : y < M
    · rw [if_pos hy, PMF.uniformOfFinset_apply_of_mem _ (Finset.mem_range.2 hy), Finset.card_range]
      rw [← PMF.toOuterMeasure_apply_singleton, dyadicDraw, PMF.toOuterMeasure_map_apply,
        uniformBits_eq, PMF.toOuterMeasure_uniformOfFinset_apply, Finset.card_range]
      rw [← hK]
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      have hc := card_preimage_div M K y hM hy
      generalize hcd : ((Finset.range K).filter fun Y => M * Y / K = y).card = c at hc
      convert (show (M : ℝ≥0∞)⁻¹ ≤ (c : ℝ≥0∞) / (K : ℝ≥0∞) + (K : ℝ≥0∞)⁻¹ by
        rw [div_eq_mul_inv, ← add_one_mul, ← div_eq_mul_inv]
        rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp; omega)) (Or.inl (by simp))]
        rw [mul_comm, ← div_eq_mul_inv,
          ENNReal.div_le_iff_le_mul (Or.inl (by simp; omega)) (Or.inl (by simp))]
        exact_mod_cast (show K ≤ (c + 1) * M by rw [add_one_mul]; exact hc)) using 3
    · rw [PMF.uniformOfFinset_apply_of_notMem _ (by simpa using hy)]
      exact zero_le
  · rw [tsum_eq_sum (s := Finset.range M) (fun y hy => by
      rw [Finset.mem_range] at hy; simp [hy])]
    rw [Finset.sum_congr rfl (fun y hy => if_pos (Finset.mem_range.1 hy)), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    rw [← div_eq_mul_inv, ENNReal.div_le_iff_le_mul (Or.inl (by simp; omega)) (Or.inl (by simp))]
    rw [show ((M : ℕ) : ℝ≥0∞) = ENNReal.ofReal (M : ℝ) by simp,
      show ((K : ℕ) : ℝ≥0∞) = ENNReal.ofReal (K : ℝ) by simp,
      ← ENNReal.ofReal_mul (by exact_mod_cast hζ.le)]
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast hMK

end Cellcounting.Analysis
