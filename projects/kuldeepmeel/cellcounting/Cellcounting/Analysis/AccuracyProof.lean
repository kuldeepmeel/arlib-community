import Cellcounting.Model.Run
import Cellcounting.Model.Prior
import Arlib.Computation.ChargedPMF
import Mathlib.Data.Nat.Log
import Cellcounting.Meta.ModelClosure
import Cellcounting.Interface.Encoding
import Cellcounting.Interface.Pseudocode
import Cellcounting.Interface.ProgramModel
import Cellcounting.Analysis.MedianAmplification
import Cellcounting.Analysis.ZeroRunGood
import Cellcounting.Analysis.AnnealRunGood

/-!
# Accuracy of the FPRAS (`thm:main`, accuracy clause)

The final assembly of `algorithm.tex:607-690`, over the pseudocode law
`Pseudocode.fpras` (the bridge `output_eq_fpras` identifies it with the
program's output law).

* Infeasible input: the law is `pure 0` and `Z = 0`, so the event has
  probability one.
* Feasible input: one run lands in `[(1-ε)Z, (1+ε)Z]` with probability at least
  `3/4` (`zeroRun_good` for `p = 0`, `annealRun_good` for `p ≥ 1`), and
  `median_amplification` turns this into `1 - 2^{-s} ≥ 1 - δ`, with
  `s = ⌈log₂ ⌈δ⁻¹⌉⌉`.
-/

namespace Cellcounting.Analysis

/-- INTERNAL: `2^{-s} ≤ δ` for `s = ⌈log₂ ⌈δ⁻¹⌉⌉`, in `ENNReal`.
TEXLINE: sections/algorithm.tex:684-690 -/
theorem inv_two_pow_sRep_le (δ : ℚ) (hδ : 0 < δ) :
    ((2 : ENNReal) ^ Pseudocode.sRep δ)⁻¹ ≤ ENNReal.ofReal (δ : ℝ) := by
  have hc : (⌈δ⁻¹⌉₊ : ℕ) ≤ 2 ^ Pseudocode.sRep δ := Nat.le_pow_clog (by norm_num) _
  have h1 : δ⁻¹ ≤ (2 : ℚ) ^ Pseudocode.sRep δ := by
    calc δ⁻¹ ≤ (⌈δ⁻¹⌉₊ : ℚ) := Nat.le_ceil _
      _ ≤ _ := by exact_mod_cast hc
  have h2 : ((2 : ℝ) ^ Pseudocode.sRep δ)⁻¹ ≤ (δ : ℝ) := by
    have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
    have h1r : (δ : ℝ)⁻¹ ≤ (2 : ℝ) ^ Pseudocode.sRep δ := by exact_mod_cast h1
    rw [inv_le_comm₀ (by positivity) hδr]
    exact h1r
  calc ((2 : ENNReal) ^ Pseudocode.sRep δ)⁻¹
      = ENNReal.ofReal (((2 : ℝ) ^ Pseudocode.sRep δ)⁻¹) := by
        rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal h2

/-- Proof-side owner for `Cellcounting.fpras_accurate`; its statement is fixed by the proof charter.
PAPER: sections/introduction.tex:24-28 -/
theorem fpras_accurate_owner (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m) (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1) : ENNReal.ofReal (1 - (δ : ℝ)) ≤ (output I ε δ).toOuterMeasure {Zhat | (1 - ε) * (I.Z : ℚ) ≤ Zhat ∧ Zhat ≤ (1 + ε) * (I.Z : ℚ)} := by
  rw [(output_eq_fpras I ε δ).1]
  unfold Pseudocode.fpras
  by_cases hfeas : Pseudocode.feasible I
  · rw [if_pos hfeas]
    have hμ : (3 / 4 : ENNReal) ≤
        (if Pseudocode.pSmall I ε δ = 0 then Pseudocode.zeroRun I ε δ
          else Pseudocode.annealRun I ε δ).toOuterMeasure
          {Zhat | (1 - ε) * (I.Z : ℚ) ≤ Zhat ∧ Zhat ≤ (1 + ε) * (I.Z : ℚ)} := by
      by_cases hp : Pseudocode.pSmall I ε δ = 0
      · rw [if_pos hp]
        refine le_trans ?_ (zeroRun_good hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp)
        have h : (3 / 4 : ℝ) ≤ 15 / 16 := by norm_num
        simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4),
          ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 16),
          ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal h
      · rw [if_neg hp]
        exact annealRun_good hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp
    refine le_trans ?_ (median_amplification _ _ _ (Pseudocode.sRep δ) hμ)
    rw [ENNReal.ofReal_sub _ (by exact_mod_cast hδ.le), ENNReal.ofReal_one]
    exact tsub_le_tsub_left (inv_two_pow_sRep_le δ hδ) 1
  · rw [if_neg hfeas]
    have hZ : I.Z = 0 := by
      have : I.Omega = ∅ := Finset.not_nonempty_iff_eq_empty.1 hfeas
      simp [Instance.Z, this]
    rw [PMF.toOuterMeasure_pure_apply, if_pos (by simp [hZ])]
    exact ENNReal.ofReal_le_one.2 (by linarith [(by exact_mod_cast hδ : (0 : ℝ) < δ)])

end Cellcounting.Analysis
