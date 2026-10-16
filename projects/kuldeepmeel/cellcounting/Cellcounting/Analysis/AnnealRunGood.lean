import Cellcounting.Interface.Pseudocode
import Cellcounting.Model.Prior
import Cellcounting.Analysis.Contamination
import Cellcounting.Analysis.ReferenceAccuracy
import Cellcounting.Analysis.ImplementationCoupling

/-!
# A single run succeeds when `p ≥ 1`

The `p ≥ 1` branch of the final assembly (`algorithm.tex:612-645`): one
annealing run lands in `[(1-ε)Z, (1+ε)Z]` with probability at least `3/4`
(the paper proves "greater than `3/4`").

The proof follows the paper and is complete relative to three children:

* `reference_accuracy` (`prop:annealing`, `ReferenceAccuracy.lean`): the exact
  reference experiment `refRun` gives `Z_ref > 0` and
  `|log(Z_ref / C(H))| ≤ 4Hη` with probability `≥ 49/50`;
* `implementation_coupling` (`lem:bounded-implementation`,
  `ImplementationCoupling.lean`): a joint law of `(Ẑ, Z_ref)` under which
  `Z_ref > 0` forces `Ẑ > 0` and `|log(Ẑ / Z_ref)| ≤ 4Hξ`, except with
  probability `≤ 10 J_* ξ = η/100 ≤ 1/100`;
* `contamination` (`prop:contamination`, `Contamination.lean`):
  `Z ≤ C(H) ≤ (1 + ε/32) Z`.

On the intersection of the two good events, `|log(Ẑ / C(H))| ≤ H(4η + 4ξ) ≤ ε/16`
(`anneal_param_bounds`), and `mem_interval_of_log_close` turns this and the
contamination bound into `(1-ε)Z ≤ Ẑ ≤ (1+ε)Z`, using `e^{-ε/16} ≥ 1 - ε/16` and
`e^{ε/16} ≤ 1 + ε/8`.  The failure mass is at most `1/50 + 1/100 ≤ 1/4`.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: a set and its complement carry total mass one under a `PMF`. -/
theorem pmf_toOuterMeasure_add_compl {α : Type*} (μ : PMF α) (s : Set α) :
    μ.toOuterMeasure s + μ.toOuterMeasure sᶜ = 1 := by
  simp only [PMF.toOuterMeasure_apply]
  rw [← ENNReal.tsum_add]
  simp [Set.indicator_self_add_compl_apply]

/-- INTERNAL: the parameter arithmetic of `algorithm.tex:621-627`:
`H(4η + 4ξ) ≤ ε/16` and `10 J_* ξ = η/100 ≤ 1/100`.
TEXLINE: sections/algorithm.tex:621-627 -/
theorem anneal_param_bounds (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (hε1 : ε < 1) :
    4 * (HParam I ε δ : ℝ) * (ηParam I ε δ : ℝ) + 4 * (HParam I ε δ : ℝ) * (ξParam I ε δ : ℝ)
        ≤ (ε : ℝ) / 16 ∧
      10 * (JstarParam I ε δ : ℝ) * (ξParam I ε δ : ℝ) ≤ 1 / 100 := by
  have hJ : (1 : ℝ) ≤ (JstarParam I ε δ : ℝ) := by
    have : 0 < JstarParam I ε δ := by unfold JstarParam; positivity
    exact_mod_cast this
  set H : ℝ := (HParam I ε δ : ℝ) with hH
  set J : ℝ := (JstarParam I ε δ : ℝ) with hJdef
  have hH0 : 0 ≤ H := by positivity
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  have hε1r : (ε : ℝ) < 1 := by exact_mod_cast hε1
  have hη : (ηParam I ε δ : ℝ) = ε / (200 * (H + 1)) := by
    simp [ηParam, hH]
  have hξ : (ξParam I ε δ : ℝ) = (ηParam I ε δ : ℝ) / (1000 * J) := by
    simp [ξParam, hJdef]
  have hη0 : 0 ≤ (ηParam I ε δ : ℝ) := by rw [hη]; positivity
  have h4η : 4 * H * (ηParam I ε δ : ℝ) ≤ ε / 50 := by
    rw [hη, show 4 * H * (ε / (200 * (H + 1))) = (ε / 50) * (H / (H + 1)) by
      field_simp; ring]
    have : H / (H + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  have hξη : (ξParam I ε δ : ℝ) ≤ (ηParam I ε δ : ℝ) := by
    rw [hξ, div_le_iff₀ (by positivity)]; nlinarith
  have hξ0 : 0 ≤ (ξParam I ε δ : ℝ) := by rw [hξ]; positivity
  refine ⟨?_, ?_⟩
  · have : 4 * H * (ξParam I ε δ : ℝ) ≤ 4 * H * (ηParam I ε δ : ℝ) := by
      have : 0 ≤ 4 * H := by positivity
      exact mul_le_mul_of_nonneg_left hξη this
    linarith
  · have hJ0 : 0 < J := by linarith
    rw [hξ, show 10 * J * ((ηParam I ε δ : ℝ) / (1000 * J)) = (ηParam I ε δ : ℝ) / 100 by
      field_simp; ring, hη]
    rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

/-- INTERNAL: the deterministic step of `algorithm.tex:621-641`: a positive
reference value within `exp(±a)` of `C(H)`, an implemented value within `exp(±b)`
of it, `a + b ≤ ε/16`, and `Z ≤ C(H) ≤ (1 + ε/32) Z` place the implemented value
in `[(1-ε)Z, (1+ε)Z]`.
TEXLINE: sections/algorithm.tex:621-641 -/
theorem mem_interval_of_log_close (Z CH Zr Zh a b ε : ℝ) (hZ : 0 < Z) (hε : 0 < ε) (hε1 : ε < 1)
    (hlo : Z ≤ CH) (hhi : CH ≤ (1 + ε / 32) * Z) (hZr : 0 < Zr)
    (hr : |Real.log (Zr / CH)| ≤ a) (hZh : 0 < Zh) (hh : |Real.log (Zh / Zr)| ≤ b)
    (hab : a + b ≤ ε / 16) :
    (1 - ε) * Z ≤ Zh ∧ Zh ≤ (1 + ε) * Z := by
  have hCH : 0 < CH := lt_of_lt_of_le hZ hlo
  have hsplit : Real.log (Zh / CH) = Real.log (Zh / Zr) + Real.log (Zr / CH) := by
    rw [Real.log_div hZh.ne' hZr.ne', Real.log_div hZr.ne' hCH.ne',
      Real.log_div hZh.ne' hCH.ne']; ring
  set t := ε / 16 with ht
  have habs : |Real.log (Zh / CH)| ≤ t := by
    rw [hsplit]; exact (abs_add_le _ _).trans (by linarith)
  have hq : 0 < Zh / CH := div_pos hZh hCH
  have hup : Zh / CH ≤ Real.exp t := by
    rw [← Real.log_le_iff_le_exp hq]; exact (le_abs_self _).trans habs
  have hdn : Real.exp (-t) ≤ Zh / CH := by
    rw [← Real.le_log_iff_exp_le hq]; linarith [neg_abs_le (Real.log (Zh / CH))]
  rw [div_le_iff₀ hCH] at hup
  rw [le_div_iff₀ hCH] at hdn
  have he1 : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  have he2 : Real.exp t ≤ 1 + 2 * t := by
    have h := Real.abs_exp_sub_one_le (x := t) (by rw [abs_le]; constructor <;> linarith)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)] at h
    linarith [le_abs_self (Real.exp t - 1)]
  have ht0 : 0 ≤ t := by linarith
  have hexp0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  constructor
  · -- `Ẑ ≥ e^{-t} C(H) ≥ (1 - t) C(H) ≥ (1 - t) Z ≥ (1 - ε) Z`
    have h1 : (1 - t) * Z ≤ (1 - t) * CH := mul_le_mul_of_nonneg_left hlo (by linarith)
    have h2 : (1 - t) * CH ≤ Real.exp (-t) * CH := mul_le_mul_of_nonneg_right he1 hCH.le
    nlinarith
  · -- `Ẑ ≤ e^{t} C(H) ≤ (1 + ε/8)(1 + ε/32) Z ≤ (1 + ε) Z`
    have h1 : Real.exp t * CH ≤ (1 + 2 * t) * CH := mul_le_mul_of_nonneg_right he2 hCH.le
    have h2 : (1 + 2 * t) * CH ≤ (1 + 2 * t) * ((1 + ε / 32) * Z) :=
      mul_le_mul_of_nonneg_left hhi (by linarith)
    nlinarith

/-- **Single run, `p ≥ 1`.**  With probability at least `3/4` one annealing run
lands in `[(1-ε)Z, (1+ε)Z]`.
PAPER: sections/algorithm.tex:612-645 -/
theorem annealRun_good (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : Pseudocode.feasible I) (hp : Pseudocode.pSmall I ε δ ≠ 0) :
    (3 / 4 : ENNReal) ≤ (Pseudocode.annealRun I ε δ).toOuterMeasure
      {Zhat | (1 - ε) * (I.Z : ℚ) ≤ Zhat ∧ Zhat ≤ (1 + ε) * (I.Z : ℚ)} := by
  obtain ⟨hZlo, hZhi⟩ := contamination hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas
  have href := reference_accuracy hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp
  obtain ⟨ν, hfst, hsnd, hcpl⟩ := implementation_coupling hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp
  obtain ⟨hlog, hJξ⟩ := anneal_param_bounds I ε δ hε hε1
  set CH := Cpart I ε δ (HParam I ε δ)
  set Gr : Set ℝ := {Zr | 0 < Zr ∧ |Real.log (Zr / CH)| ≤
    4 * (HParam I ε δ : ℝ) * (ηParam I ε δ : ℝ)} with hGr
  set Gc : Set (ℚ × ℝ) := {q | 0 < q.2 → 0 < (q.1 : ℝ) ∧
    |Real.log ((q.1 : ℝ) / q.2)| ≤ 4 * (HParam I ε δ : ℝ) * (ξParam I ε δ : ℝ)} with hGc
  set E : Set ℚ := {Zhat | (1 - ε) * (I.Z : ℚ) ≤ Zhat ∧ Zhat ≤ (1 + ε) * (I.Z : ℚ)}
  have hZpos : (0 : ℝ) < I.Z := by
    have : 0 < I.Z := Finset.card_pos.2 hfeas
    exact_mod_cast this
  -- On both good events the output lies in the interval.
  have hsub : Prod.snd ⁻¹' Gr ∩ Gc ⊆ Prod.fst ⁻¹' E := by
    rintro ⟨zh, zr⟩ ⟨⟨hzr, hr⟩, hc⟩
    obtain ⟨hzh, hh⟩ := hc hzr
    have h := mem_interval_of_log_close (I.Z : ℝ) CH zr (zh : ℝ) _ _ (ε : ℝ) hZpos
      (by exact_mod_cast hε) (by exact_mod_cast hε1) hZlo hZhi hzr hr hzh hh hlog
    simp only [Set.mem_preimage, E, Set.mem_setOf_eq]
    constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  -- Failure of the reference event has mass at most `1/50`.
  have hA : ν.toOuterMeasure (Prod.snd ⁻¹' Gr)ᶜ ≤ 1 / 50 := by
    rw [← Set.preimage_compl, ← PMF.toOuterMeasure_map_apply, hsnd]
    have h1 := pmf_toOuterMeasure_add_compl (refRun I ε δ) Gr
    have h2 : (1 / 50 : ENNReal) + 49 / 50 = 1 := by
      rw [ENNReal.div_add_div_same, show (1 : ENNReal) + 49 = 50 by norm_num,
        ENNReal.div_self (by norm_num) (by norm_num)]
    have h3 : (refRun I ε δ).toOuterMeasure Grᶜ + 49 / 50 ≤ 1 / 50 + 49 / 50 := by
      rw [h2, ← h1, add_comm]; gcongr
    exact (ENNReal.add_le_add_iff_right (ENNReal.div_lt_top (by norm_num) (by norm_num)).ne).1 h3
  -- Failure of the coupling event has mass at most `1/100`.
  have hB : ν.toOuterMeasure Gcᶜ ≤ 1 / 100 := by
    refine le_trans hcpl ?_
    have : ENNReal.ofReal (1 / 100) = 1 / 100 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    rw [← this]; exact ENNReal.ofReal_le_ofReal hJξ
  have htot := pmf_toOuterMeasure_add_compl ν (Prod.snd ⁻¹' Gr ∩ Gc)
  have hU : ν.toOuterMeasure (Prod.snd ⁻¹' Gr ∩ Gc)ᶜ ≤ 1 / 50 + 1 / 100 := by
    rw [Set.compl_inter]
    exact (MeasureTheory.measure_union_le _ _).trans (add_le_add hA hB)
  have hsmall : (1 / 50 + 1 / 100 : ENNReal) ≤ 1 / 4 := by
    have e : ∀ k : ℕ, 0 < k → (1 / (k : ENNReal)) = ENNReal.ofReal (1 / (k : ℝ)) := by
      intro k hk
      rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hk)]; simp
    rw [show (50 : ENNReal) = ((50 : ℕ) : ENNReal) by norm_num,
      show (100 : ENNReal) = ((100 : ℕ) : ENNReal) by norm_num,
      show (4 : ENNReal) = ((4 : ℕ) : ENNReal) by norm_num, e 50 (by norm_num),
      e 100 (by norm_num), e 4 (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hkey : (3 / 4 : ENNReal) + 1 / 4 ≤ ν.toOuterMeasure (Prod.snd ⁻¹' Gr ∩ Gc) + 1 / 4 := by
    rw [ENNReal.div_add_div_same, show (3 : ENNReal) + 1 = 4 by norm_num,
      ENNReal.div_self (by norm_num) (by norm_num)]
    calc (1 : ENNReal) = _ := htot.symm
      _ ≤ _ := by gcongr; exact hU.trans hsmall
  have hmain := (ENNReal.add_le_add_iff_right (ENNReal.div_lt_top (by norm_num) (by norm_num)).ne).1 hkey
  rw [← hfst, PMF.toOuterMeasure_map_apply]
  exact hmain.trans (MeasureTheory.measure_mono hsub)

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · assembled · closed against `contamination`, `reference_accuracy`, `implementation_coupling` (all open)
-/
