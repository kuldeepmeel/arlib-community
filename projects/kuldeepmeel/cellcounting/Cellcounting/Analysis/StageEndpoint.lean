import Cellcounting.Analysis.RefChainLaw
import Cellcounting.Analysis.StageStep
import Cellcounting.Analysis.RefMuMin
import Cellcounting.Analysis.TraceRelativeMixing
import Cellcounting.Model.Prior

/-!
# One trace stage ends within `(3/2) μ_a` (`lem:trace` with `eq:alg-minimum-mass`)

`stage_endpoint_le`: with good multipliers at `a < H`, from any transversal `x`, the
probability that `N` underlying transitions (`stageStep`) complete the `τ` trace steps at
`y` is at most `(3/2) μ_a(y)`, for every `N`.  In the paper (`algorithm.tex:285-291`) this
is `eq:trace-relative-mixing` of `lem:trace` at `s = τ` (`trace_relative_mixing`), with
`μ_min ≥ 2^{-M}` (`eq:alg-minimum-mass`, `refMu_min`, `M = H + p + K`) and
`τ = 2 K_obs (M + 5)`: the relative error is at most `2^M exp(-2(M+5)) ≤ e^{-10} ≤ 1/2`
(`stage_num_bound`).
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal

/-- INTERNAL: `2^M exp(-2(M+5)) ≤ 1/2`, the numerical step of `algorithm.tex:287-290`.
TEXLINE: sections/algorithm.tex:287-290 -/
theorem stage_num_bound (M : ℕ) :
    Real.exp (-(2 * ((M : ℝ) + 5))) / (1 / 2 : ℝ) ^ M ≤ 1 / 2 := by
  rw [div_le_iff₀ (by positivity)]
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have h2M : (2 : ℝ) ^ M ≤ Real.exp M := by
    rw [← Real.exp_one_pow]; exact pow_le_pow_left₀ (by norm_num) h2 M
  have h10 : (2 : ℝ) ≤ Real.exp 10 := by
    have := Real.add_one_le_exp (10 : ℝ); linarith
  have key : Real.exp (-(2 * ((M : ℝ) + 5))) * Real.exp M * Real.exp 10 ≤ 1 := by
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_one_iff]
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hhalf : (1 / 2 : ℝ) ^ M * 2 ^ M = 1 := by rw [← mul_pow]; norm_num
  have he : 0 < Real.exp (-(2 * ((M : ℝ) + 5))) := Real.exp_pos _
  have hp : 0 < (1 / 2 : ℝ) ^ M := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2M he.le, Real.exp_pos (M : ℝ),
    mul_le_mul_of_nonneg_left h10 (mul_pos he (Real.exp_pos (M : ℝ))).le]

/-- INTERNAL: `τ` trace steps of `P_{a, w}` from any transversal, truncated after `N`
underlying transitions, end at `y` with probability at most `(3/2) μ_a(y)` (the paper's
"endpoint law at most `2μ_a`", with the constant its relative-error bound gives).
TEXLINE: sections/algorithm.tex:285-291 -/
theorem stage_endpoint_le (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (a : ℕ) (ha : a < HParam I ε δ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ a w) (x : Finset ℕ)
    (hx : x ∈ transStates I ε δ) (N : ℕ) (y : Finset ℕ) :
    loop (fun _ => stageStep I ε δ a w) N (0, x) (τParam I ε δ, y) ≤
      3 / 2 * ENNReal.ofReal (refMu I ε δ a y) := by
  set M := HParam I ε δ + pSmall I ε δ + KParam I ε δ with hM
  have hm0 : (0 : ℝ) < (1 / 2 : ℝ) ^ M := by positivity
  have hmin := refMu_min hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp a ha.le
  refine (trace_relative_mixing hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp a ha w hgood _ hm0
    hmin x hx N y).trans ?_
  -- The relative error `exp(-τ/K_obs) 2^M` is at most `1/2`.
  have hK : (0 : ℝ) < KobsParam I ε δ := by
    have hp' : 0 < pSmall I ε δ := Nat.pos_of_ne_zero hp
    have : 0 < KobsParam I ε δ := by unfold KobsParam CdParam; positivity
    exact_mod_cast this
  have hτK : (τParam I ε δ : ℝ) / (KobsParam I ε δ : ℝ) = 2 * ((M : ℝ) + 5) := by
    rw [div_eq_iff hK.ne', hM, τParam]; push_cast; ring
  have herr : Real.exp (-((τParam I ε δ : ℝ) / (KobsParam I ε δ : ℝ))) / (1 / 2 : ℝ) ^ M ≤
      1 / 2 := by
    rw [hτK]; exact stage_num_bound M
  by_cases hy : y ∈ transStates I ε δ
  · have hμ : 0 ≤ refMu I ε δ a y := hm0.le.trans (hmin y hy)
    rw [show (3 / 2 : ℝ≥0∞) = ENNReal.ofReal (3 / 2) by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num,
      ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith
  · simp [refMu, hy]

end Cellcounting.Analysis
