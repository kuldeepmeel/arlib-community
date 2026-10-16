import Cellcounting.Interface.Pseudocode
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The bisection approximation of `2^β`

`evaluation.tex:417-448`: for `β ∈ [-2, 2]`, `Pseudocode.pow2Approx` rounds `β`
to the grid `h/s'` (`s' = 2^{oKs} ≥ 32/σ`, so `|β - h/s'| ≤ σ/64`) and bisects
`[0, 8]` to depth `⌈log₂ (512/σ)⌉`, comparing `mid^{s'}` with `2^h`.  The
returned lower endpoint is within `σ/64` of `2^{h/s'}`, and `2^{h/s'}` is within
relative error `σ/64` of `2^β ≥ 1/4`.  Hence the returned value has relative error
at most `σ` (`pow2Approx_close`).
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: the bisection step of `pow2Approx`, for power `n` and target `t`. -/
def bisectStep (n : ℕ) (t : ℚ) (st : ℚ × ℚ) : ℚ × ℚ :=
  if ((st.1 + st.2) / 2) ^ n ≤ t then ((st.1 + st.2) / 2, st.2) else (st.1, (st.1 + st.2) / 2)

/-- INTERNAL: the bisection invariant: `lo ≥ 0`, `lo^n ≤ t < hi^n`, width `8/2^D`. -/
theorem bisect_spec (n : ℕ) (hn : 0 < n) (t : ℚ) (ht : 0 ≤ t) (ht8 : t < 8 ^ n) (D : ℕ) :
    0 ≤ ((bisectStep n t)^[D] (0, 8)).1 ∧ ((bisectStep n t)^[D] (0, 8)).1 ^ n ≤ t ∧
      t < ((bisectStep n t)^[D] (0, 8)).2 ^ n ∧
      ((bisectStep n t)^[D] (0, 8)).2 - ((bisectStep n t)^[D] (0, 8)).1 = 8 / 2 ^ D := by
  induction D with
  | zero =>
    simp only [Function.iterate_zero, id, pow_zero, div_one]
    refine ⟨le_rfl, ?_, ht8, by norm_num⟩
    rw [zero_pow hn.ne']; exact ht
  | succ D ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    rw [Function.iterate_succ_apply']
    set st := (bisectStep n t)^[D] (0, 8)
    unfold bisectStep
    split_ifs with hm
    · refine ⟨by have : st.1 ≤ st.2 := by
                  have : (0:ℚ) < 8 / 2 ^ D := by positivity
                  linarith
                 linarith, hm, h2, ?_⟩
      simp only
      rw [pow_succ, ← div_div]; linarith
    · push_neg at hm
      refine ⟨h0, h1, hm, ?_⟩
      simp only
      rw [pow_succ, ← div_div]; linarith

/-- INTERNAL: `|2^u - 1| ≤ |u|` for `|u| ≤ 1`. -/
theorem abs_two_rpow_sub_one_le (u : ℝ) (hu : |u| ≤ 1) : |(2 : ℝ) ^ u - 1| ≤ |u| := by
  rcases le_total 0 u with h | h
  · have h1 : (1 + 1 : ℝ) ^ u ≤ 1 + u * 1 :=
      rpow_one_add_le_one_add_mul_self (by norm_num) h (by rw [abs_of_nonneg h] at hu; exact hu)
    have h2 : (1 : ℝ) ≤ 2 ^ u := Real.one_le_rpow (by norm_num) h
    norm_num at h1
    rw [abs_of_nonneg (by linarith), abs_of_nonneg h]; linarith
  · have hu' : -1 ≤ u := by rw [abs_of_nonpos h] at hu; linarith
    have h1 : (1 + 1 : ℝ) ^ (-u) ≤ 1 + (-u) * 1 :=
      rpow_one_add_le_one_add_mul_self (by norm_num) (by linarith) (by linarith)
    norm_num at h1
    have h2 : (2 : ℝ) ^ u ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) h
    have h3 : (2 : ℝ) ^ u * 2 ^ (-u) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    have h4 : (0 : ℝ) < 2 ^ u := by positivity
    rw [abs_of_nonpos (by linarith), abs_of_nonpos h]
    nlinarith

/-- INTERNAL: the bisection approximation of `2^β` has relative error at most `σ`
for `β ∈ [-2, 2]` and `0 < σ ≤ 1/200`.
TEXLINE: sections/evaluation.tex:417-448 -/
theorem pow2Approx_close (I : Instance) (ε δ ξin : ℚ) (hσ : 0 < oSigma I ε δ ξin)
    (hσ1 : oSigma I ε δ ξin ≤ 1 / 200) (β : ℚ) (hβ1 : -2 ≤ β) (hβ2 : β ≤ 2) :
    |(pow2Approx I ε δ ξin β : ℝ) - (2 : ℝ) ^ (β : ℝ)| ≤
      (oSigma I ε δ ξin : ℝ) * (2 : ℝ) ^ (β : ℝ) := by
  set σ := oSigma I ε δ ξin with hσdef
  set K := oKs I ε δ ξin
  set n : ℕ := 2 ^ K with hn
  set h : ℤ := ⌊β * 2 ^ K + 1 / 2⌋ with hh
  set D := oDepth I ε δ ξin
  have hnpos : 0 < n := Nat.two_pow_pos K
  -- `s' = n ≥ 32/σ`
  have hn32 : (32 : ℚ) / σ ≤ n := by
    have h1 : ⌈(32 : ℚ) / σ⌉₊ ≤ 2 ^ K := Nat.le_pow_clog one_lt_two _
    exact (Nat.le_ceil _).trans (by rw [hn]; exact_mod_cast h1)
  have hnq : (n : ℚ) = 2 ^ K := by rw [hn]; push_cast; ring
  -- the rounding: `|h - β n| ≤ 1/2`
  have hr1 : (h : ℚ) ≤ β * n + 1 / 2 := by rw [hnq]; exact Int.floor_le _
  have hr2 : β * n + 1 / 2 < h + 1 := by rw [hnq]; exact Int.lt_floor_add_one _
  have hnpos' : (0 : ℚ) < n := by exact_mod_cast hnpos
  have hσn : σ * n ≥ 32 := by rwa [div_le_iff₀ hσ, mul_comm] at hn32
  -- `|h/n| ≤ 2`, more precisely `-2 ≤ h/n ≤ 2 + 1/(2n)`; we use `|h/n - β| ≤ 1/(2n)`
  have hdev : |(h : ℚ) / n - β| ≤ σ / 64 := by
    rw [abs_le]
    constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ hnpos']
      have : σ / 64 * n ≥ 1 / 2 := by nlinarith
      nlinarith
    · rw [sub_le_iff_le_add, div_le_iff₀ hnpos']
      have : σ / 64 * n ≥ 1 / 2 := by nlinarith
      nlinarith
  -- target `t = 2^h` lies below `8^n`
  set t : ℚ := (2 : ℚ) ^ h with ht
  have htpos : 0 < t := by positivity
  have hh_le : h ≤ 2 * n := by
    have : (h : ℚ) < 2 * n + 1 := by nlinarith
    have : (h : ℚ) < ((2 * n + 1 : ℤ) : ℚ) := by push_cast; linarith
    have := Int.cast_lt.1 this
    omega
  have ht8 : t < 8 ^ n := by
    rw [ht, show (8 : ℚ) ^ n = 2 ^ ((3 * n : ℕ) : ℤ) by
      rw [zpow_natCast, pow_mul]; norm_num]
    apply zpow_lt_zpow_right₀ (by norm_num)
    push_cast; omega
  obtain ⟨hlo0, hlo, hhi, hw⟩ := bisect_spec n hnpos t htpos.le ht8 D
  have hpa : pow2Approx I ε δ ξin β = ((bisectStep n t)^[D] (0, 8)).1 := rfl
  rw [hpa]
  set lo := ((bisectStep n t)^[D] (0, 8)).1
  set hi := ((bisectStep n t)^[D] (0, 8)).2
  -- `T1 = 2^{h/n}`
  set T1 : ℝ := (2 : ℝ) ^ ((h : ℝ) / n) with hT1
  have hT1pos : 0 < T1 := by positivity
  have hT1n : T1 ^ n = (t : ℝ) := by
    rw [hT1, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), div_mul_cancel₀ _
      (by exact_mod_cast hnpos.ne'), Real.rpow_intCast, ht]
    push_cast; rfl
  have hloT : (lo : ℝ) ≤ T1 := by
    have : (lo : ℝ) ^ n ≤ T1 ^ n := by rw [hT1n]; exact_mod_cast hlo
    exact (pow_le_pow_iff_left₀ (by exact_mod_cast hlo0) hT1pos.le hnpos.ne').1 this
  have hThi : T1 < hi := by
    have : T1 ^ n < (hi : ℝ) ^ n := by rw [hT1n]; exact_mod_cast hhi
    have hhi0 : (0 : ℝ) ≤ hi := by
      have : (0 : ℚ) ≤ hi := by
        have : (0 : ℚ) < 8 / 2 ^ D := by positivity
        linarith
      exact_mod_cast this
    exact (pow_lt_pow_iff_left₀ hT1pos.le hhi0 hnpos.ne').1 this
  -- width `8/2^D ≤ σ/64`
  have hD : (512 : ℚ) / σ ≤ 2 ^ D := by
    have h1 : ⌈(512 : ℚ) / σ⌉₊ ≤ 2 ^ D := Nat.le_pow_clog one_lt_two _
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hwidth : (8 : ℚ) / 2 ^ D ≤ σ / 64 := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hσ] at hD
    nlinarith
  have hlo_close : |(lo : ℝ) - T1| ≤ (σ : ℝ) / 64 := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have : ((hi : ℚ) : ℝ) - lo = ((8 / 2 ^ D : ℚ) : ℝ) := by rw [← hw]; push_cast; ring
    have hw' : ((8 / 2 ^ D : ℚ) : ℝ) ≤ ((σ / 64 : ℚ) : ℝ) := by exact_mod_cast hwidth
    push_cast at hw' this ⊢
    linarith
  -- `T1 = 2^β · 2^{h/n - β}`
  have hβr1 : (-2 : ℝ) ≤ β := by exact_mod_cast hβ1
  have h2β : (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (β : ℝ) := by
    have : (2 : ℝ) ^ (-2 : ℝ) ≤ (2 : ℝ) ^ (β : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hβr1
    rw [show (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 by
      rw [Real.rpow_neg (by norm_num)]; norm_num] at this
    exact this
  have hdev' : |((h : ℝ) / n) - β| ≤ (σ : ℝ) / 64 := by
    have : (((h : ℚ) / n - β : ℚ) : ℝ) = (h : ℝ) / n - β := by push_cast; ring
    rw [← this]
    exact_mod_cast hdev
  have hσr : (σ : ℝ) ≤ 1 / 200 := by
    have := (Rat.cast_le (K := ℝ)).2 hσ1; push_cast at this; exact this
  have hσr0 : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hT1split : T1 = (2 : ℝ) ^ (β : ℝ) * (2 : ℝ) ^ ((h : ℝ) / n - β) := by
    rw [hT1, ← Real.rpow_add (by norm_num)]; congr 1; ring
  have hrel := abs_two_rpow_sub_one_le ((h : ℝ) / n - β) (by linarith [hdev'])
  have hT1close : |T1 - (2 : ℝ) ^ (β : ℝ)| ≤ (2 : ℝ) ^ (β : ℝ) * ((σ : ℝ) / 64) := by
    rw [hT1split, show (2 : ℝ) ^ (β : ℝ) * (2 : ℝ) ^ ((h : ℝ) / n - β) - (2 : ℝ) ^ (β : ℝ) =
      (2 : ℝ) ^ (β : ℝ) * ((2 : ℝ) ^ ((h : ℝ) / n - β) - 1) by ring, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (β : ℝ))]
    exact mul_le_mul_of_nonneg_left (hrel.trans hdev') (by positivity)
  calc |(lo : ℝ) - (2 : ℝ) ^ (β : ℝ)| ≤ |(lo : ℝ) - T1| + |T1 - (2 : ℝ) ^ (β : ℝ)| :=
        abs_sub_le _ _ _
    _ ≤ (σ : ℝ) / 64 + (2 : ℝ) ^ (β : ℝ) * ((σ : ℝ) / 64) := add_le_add hlo_close hT1close
    _ ≤ (σ : ℝ) * (2 : ℝ) ^ (β : ℝ) := by nlinarith

/-- INTERNAL: the bisection approximation never exceeds `8`.
TEXLINE: sections/evaluation.tex:449-456 -/
theorem pow2Approx_le_eight (I : Instance) (ε δ ξin β : ℚ) : pow2Approx I ε δ ξin β ≤ 8 := by
  set n : ℕ := 2 ^ oKs I ε δ ξin
  set t : ℚ := (2 : ℚ) ^ ⌊β * 2 ^ oKs I ε δ ξin + 1 / 2⌋
  have key : ∀ D : ℕ, 0 ≤ ((bisectStep n t)^[D] (0, 8)).1 ∧
      ((bisectStep n t)^[D] (0, 8)).1 ≤ ((bisectStep n t)^[D] (0, 8)).2 ∧
      ((bisectStep n t)^[D] (0, 8)).2 ≤ 8 := by
    intro D
    induction D with
    | zero => norm_num
    | succ D ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      rw [Function.iterate_succ_apply']
      set st := (bisectStep n t)^[D] (0, 8)
      unfold bisectStep
      split_ifs <;> refine ⟨?_, ?_, ?_⟩ <;> simp only <;> linarith
  have hpa : pow2Approx I ε δ ξin β = ((bisectStep n t)^[oDepth I ε δ ξin] (0, 8)).1 := rfl
  rw [hpa]
  obtain ⟨-, h1, h2⟩ := key (oDepth I ε δ ξin)
  linarith

end Cellcounting.Analysis
