import Cellcounting.Interface.Pseudocode

/-!
# Parameter arithmetic for the contamination bound

The numerical facts about `eq:parameters` (`scales.tex:48-87`) that the proof of
`prop:contamination` uses: `K ≥ 1`, `γ > 0`, `A γ ≥ 4K`, `H > 0`,
`4 d γ K = ε/128` and `2^{-3K} ≤ ε/128`.
-/

namespace Cellcounting.Analysis

open Pseudocode

variable (I : Instance) (ε δ : ℚ)

theorem KParam_ge : 20 ≤ KParam I ε δ := by
  unfold KParam; omega

theorem dParam_ge : 2 ≤ dParam I := by
  unfold dParam; omega

theorem γParam_pos (hε : 0 < ε) : 0 < γParam I ε δ := by
  unfold γParam
  have := KParam_ge I ε δ; have := dParam_ge I
  have hK : (0 : ℚ) < KParam I ε δ := by exact_mod_cast (by omega : 0 < KParam I ε δ)
  have hd : (0 : ℚ) < dParam I := by exact_mod_cast (by omega : 0 < dParam I)
  positivity

theorem γParam_le_one (hε : 0 < ε) (hε1 : ε < 1) : γParam I ε δ ≤ 1 := by
  unfold γParam
  have hK : (20 : ℚ) ≤ KParam I ε δ := by exact_mod_cast KParam_ge I ε δ
  have hd : (2 : ℚ) ≤ dParam I := by exact_mod_cast (dParam_ge I)
  rw [div_le_one (by positivity)]
  nlinarith

/-- INTERNAL: `A γ ≥ 4K` (`A = ⌈4K/γ⌉`).
TEXLINE: sections/scales.tex:48-56 -/
theorem AParam_mul_γ (hε : 0 < ε) : 4 * (KParam I ε δ : ℚ) ≤ AParam I ε δ * γParam I ε δ := by
  have hγ := γParam_pos I ε δ hε
  have h := Nat.le_ceil ((4 * KParam I ε δ : ℚ) / γParam I ε δ)
  unfold AParam
  rw [div_le_iff₀ hγ] at h
  exact h

theorem AParam_pos (hε : 0 < ε) : 0 < AParam I ε δ := by
  have h := AParam_mul_γ I ε δ hε
  have := KParam_ge I ε δ
  have hK : (20 : ℚ) ≤ KParam I ε δ := by exact_mod_cast this
  by_contra h0
  push Not at h0
  have : AParam I ε δ = 0 := by omega
  rw [this] at h; push_cast at h; linarith

theorem HParam_pos (hε : 0 < ε) : 0 < HParam I ε δ := by
  unfold HParam
  have := AParam_pos I ε δ hε; have := dParam_ge I
  positivity

/-- INTERNAL: `4 d γ K = ε / 128`.
TEXLINE: sections/integer-signatures.tex:540-544 -/
theorem four_d_γ_K (hε : 0 < ε) :
    4 * (dParam I : ℚ) * γParam I ε δ * KParam I ε δ = ε / 128 := by
  unfold γParam
  have := KParam_ge I ε δ; have := dParam_ge I
  have hK : (0 : ℚ) < KParam I ε δ := by exact_mod_cast (by omega : 0 < KParam I ε δ)
  have hd : (0 : ℚ) < dParam I := by exact_mod_cast (by omega : 0 < dParam I)
  field_simp; ring

/-- INTERNAL: `2^{-3K} ≤ ε/128`, as `128 ≤ ε 2^{3K}` (`eq:capacity-product`).
TEXLINE: sections/scales.tex:72-87 -/
theorem two_pow_three_K (hε : 0 < ε) : (128 : ℚ) ≤ ε * 2 ^ (3 * KParam I ε δ) := by
  set c := Nat.clog 2 ⌈ε⁻¹⌉₊
  have hc : ⌈ε⁻¹⌉₊ ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) _
  have hK : c + 7 ≤ 3 * KParam I ε δ := by unfold KParam; omega
  have h1 : (ε⁻¹ : ℚ) ≤ 2 ^ c := by
    calc ε⁻¹ ≤ (⌈ε⁻¹⌉₊ : ℚ) := Nat.le_ceil _
      _ ≤ ((2 ^ c : ℕ) : ℚ) := by exact_mod_cast hc
      _ = 2 ^ c := by push_cast; ring
  have h2 : (2 : ℚ) ^ (c + 7) ≤ 2 ^ (3 * KParam I ε δ) :=
    pow_le_pow_right₀ (by norm_num) hK
  have h3 : (1 : ℚ) ≤ ε * 2 ^ c := by
    have := mul_le_mul_of_nonneg_left h1 hε.le
    rwa [mul_inv_cancel₀ hε.ne'] at this
  calc (128 : ℚ) ≤ ε * 2 ^ c * 128 := by linarith
    _ = ε * 2 ^ (c + 7) := by ring
    _ ≤ ε * 2 ^ (3 * KParam I ε δ) := mul_le_mul_of_nonneg_left h2 hε.le

end Cellcounting.Analysis
