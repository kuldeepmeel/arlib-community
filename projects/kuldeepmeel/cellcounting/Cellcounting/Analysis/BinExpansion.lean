import Cellcounting.Analysis.BinDensity
import Cellcounting.Analysis.IntegralInterpolation

/-!
# Expansion of the smaller side (`eq:bin-expansion`)

`Cellcounting.Analysis.bin_expansion`: if the union `S` of the bins of `T` carries at most
the continuous mass of the other bins, then its sup-norm `r`-neighbourhood `N` in the cube
has mass `μ(N) ≥ 2^t μ(S)`, `t = 1/(4dB)`. This is `lem:integral-interpolation`
(`integral_interpolation_pi`) applied to `f = 1_S ϱ_a`, `g = 1_{D₀} ϱ_a`, `h = 1_N ϱ_a`:
`ϱ_a` is log-concave (`binPhi_convex`), and `(1-t)x + ty` lies within `tB = r` of `x`.
-/

namespace Cellcounting.Analysis

open Pseudocode MeasureTheory Set
open scoped ENNReal
open Classical

variable (I : Instance) (ε δ : ℚ)

/-- **Expansion** (`eq:bin-expansion`): `μ(M) ≥ 2^t μ(S)` for the smaller side `S`,
with `M ⊆ binNbhd T`.
PAPER: sections/evaluation.tex:226-237 -/
theorem bin_expansion (hε : 0 < ε) (a : ℕ) (x y : ℕ → ℕ) {T : Finset (ℕ → ℕ)}
    (hT : T ⊆ binSet I ε δ)
    (hhalf : binMass I ε δ a x y (binSide I ε δ T) ≤
      binMass I ε δ a x y (binSide I ε δ (binSet I ε δ \ T))) :
    ENNReal.ofReal ((2 : ℝ) ^ (1 / (4 * (dParam I : ℝ) * BParam I ε δ))) *
        binMass I ε δ a x y (binSide I ε δ T) ≤
      binMass I ε δ a x y (binNbhd I ε δ T) := by
  have hd : (2 : ℝ) ≤ dParam I := by exact_mod_cast dParam_ge I
  have hBn : 0 < BParam I ε δ := by
    have := AParam_pos I ε δ hε; have := dParam_ge I; unfold BParam; positivity
  have hB1 : (1 : ℝ) ≤ BParam I ε δ := by exact_mod_cast hBn
  set B : ℝ := (BParam I ε δ : ℝ) with hBdef
  set t : ℝ := 1 / (4 * (dParam I : ℝ) * B) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := by rw [ht, div_lt_one (by positivity)]; nlinarith
  have htB : t * B = binRad I := by unfold binRad; rw [ht]; field_simp
  set S := binSide I ε δ T with hSdef
  set S' := binSide I ε δ (binSet I ε δ \ T) with hS'def
  set D := binCube I ε δ with hDdef
  set N := binNbhd I ε δ T with hNdef
  set ρ := binRho I ε δ a x y with hρ
  have hρm : Measurable ρ := measurable_binRho I ε δ a x y
  have hSm : MeasurableSet S :=
    Finset.measurableSet_biUnion _ fun v _ => measurableSet_binBox I ε δ v
  have hS'm : MeasurableSet S' :=
    Finset.measurableSet_biUnion _ fun v _ => measurableSet_binBox I ε δ v
  have hDm : MeasurableSet D := MeasurableSet.univ_pi fun _ => measurableSet_Ico
  have hNm : MeasurableSet N := by
    refine hDm.inter (IsOpen.measurableSet ?_)
    have : {z | ∃ x ∈ S, ‖z - x‖ < binRad I} = ⋃ x ∈ S, Metric.ball x (binRad I) := by
      ext z; simp [Metric.mem_ball, dist_eq_norm]
    rw [this]; exact isOpen_biUnion fun _ _ => Metric.isOpen_ball
  have hSD : S ⊆ D := binSide_subset_cube I ε δ hT
  have hS'D : S' ⊆ D := binSide_subset_cube I ε δ Finset.sdiff_subset
  have hdisj : Disjoint S S' := by
    rw [Set.disjoint_left]; intro z hz hz'
    simp only [hSdef, hS'def, binSide, mem_iUnion] at hz hz'
    obtain ⟨v, hv, hzv⟩ := hz
    obtain ⟨w, hw, hzw⟩ := hz'
    rw [Finset.mem_sdiff] at hw
    have hvw : v ≠ w := fun h => hw.2 (h ▸ hv)
    exact Set.disjoint_left.1 (binBox_disjoint I ε δ (hT hv) hw.1 hvw) hzv hzw
  have h2S : 2 * binMass I ε δ a x y S ≤ binMass I ε δ a x y D := by
    calc 2 * binMass I ε δ a x y S
        = binMass I ε δ a x y S + binMass I ε δ a x y S := two_mul _
      _ ≤ binMass I ε δ a x y S + binMass I ε δ a x y S' := add_le_add_right hhalf _
      _ = binMass I ε δ a x y (S ∪ S') := (lintegral_union hS'm hdisj).symm
      _ ≤ binMass I ε δ a x y D := lintegral_mono_set (union_subset hSD hS'D)
  have hcube : ∀ z ∈ D, ∀ i, 0 ≤ z i ∧ z i < B := fun z hz i => by
    have := hz i (mem_univ _); simpa [hBdef] using this
  have hbd : ∀ (X : Set (Fin (nFree I ε δ) → ℝ)), X ⊆ D → ∀ z,
      X.indicator ρ z ≠ 0 → ∀ i, |z i| ≤ B := fun X hX z hz i => by
    have h := hcube z (hX (Set.mem_of_indicator_ne_zero hz)) i
    exact abs_le.2 ⟨by linarith, h.2.le⟩
  have hle : ∀ (X : Set (Fin (nFree I ε δ) → ℝ)) z, X.indicator ρ z ≤ 1 := fun X z =>
    (indicator_le_self X ρ z).trans (binRho_le_one I ε δ a x y z)
  have hfgh : ∀ u w, S.indicator ρ u ^ (1 - t) * D.indicator ρ w ^ t ≤
      N.indicator ρ ((1 - t) • u + t • w) := by
    intro u w
    by_cases hu : u ∈ S
    swap
    · rw [indicator_of_notMem hu, ENNReal.zero_rpow_of_pos (by linarith), zero_mul]
      exact bot_le
    by_cases hw : w ∈ D
    swap
    · rw [indicator_of_notMem hw, ENNReal.zero_rpow_of_pos ht0, mul_zero]
      exact bot_le
    have hzN : (1 - t) • u + t • w ∈ N := by
      refine ⟨fun i _ => ?_, u, hu, ?_⟩
      · have h1 := hcube u (hSD hu) i
        have h2 := hcube w hw i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mem_Ico]
        constructor <;> nlinarith
      · have hzu : (1 - t) • u + t • w - u = t • (w - u) := by
          ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
        rw [hzu, norm_smul, Real.norm_of_nonneg ht0.le, ← htB]
        refine mul_lt_mul_of_pos_left ?_ ht0
        refine (pi_norm_lt_iff (by linarith)).2 fun i => ?_
        have h1 := hcube u (hSD hu) i
        have h2 := hcube w hw i
        rw [Pi.sub_apply, Real.norm_eq_abs, abs_lt]
        constructor <;> linarith
    rw [indicator_of_mem hu, indicator_of_mem hw, indicator_of_mem hzN, hρ]
    unfold binRho
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) ht0.le,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.rpow_mul two_pos.le, ← Real.rpow_mul two_pos.le, ← Real.rpow_add two_pos]
    refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    have := binPhi_convex I ε δ a x y u w (1 - t) t (by linarith) ht0.le (by ring)
    linarith
  have key := integral_interpolation_pi (nFree I ε δ) ht0 ht1 (S.indicator ρ) (D.indicator ρ)
    (N.indicator ρ) (hρm.indicator hSm) (hρm.indicator hDm) (hρm.indicator hNm)
    ENNReal.one_ne_top (hle S) (hle D) (hbd S hSD) (hbd D le_rfl) hfgh
  rw [lintegral_indicator hSm, lintegral_indicator hDm, lintegral_indicator hNm] at key
  change binMass I ε δ a x y S ^ (1 - t) * binMass I ε δ a x y D ^ t ≤
    binMass I ε δ a x y N at key
  by_cases h0 : binMass I ε δ a x y S = 0
  · rw [h0, mul_zero]; exact bot_le
  have hTop : binMass I ε δ a x y S ≠ ⊤ := (binMass_side_lt_top I ε δ a x y hT).ne
  have h2 : ENNReal.ofReal ((2 : ℝ) ^ t) = (2 : ℝ≥0∞) ^ t := by
    rw [← ENNReal.ofReal_rpow_of_pos two_pos, ENNReal.ofReal_ofNat]
  calc ENNReal.ofReal ((2 : ℝ) ^ t) * binMass I ε δ a x y S
      = (2 : ℝ≥0∞) ^ t * binMass I ε δ a x y S ^ ((1 - t) + t) := by
        rw [h2, sub_add_cancel, ENNReal.rpow_one]
    _ = binMass I ε δ a x y S ^ (1 - t) * (2 * binMass I ε δ a x y S) ^ t := by
        rw [ENNReal.rpow_add _ _ h0 hTop, ENNReal.mul_rpow_of_nonneg _ _ ht0.le]; ring
    _ ≤ binMass I ε δ a x y S ^ (1 - t) * binMass I ε δ a x y D ^ t := by gcongr
    _ ≤ binMass I ε δ a x y N := key

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `integral_interpolation_pi` with `f = 1_S ϱ`, `g = 1_{D₀} ϱ`, `h = 1_N ϱ`; `hhalf` gives `μ(D₀) ≥ 2μ(S)`; no `sorry`
-/
