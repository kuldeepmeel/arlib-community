import Cellcounting.Interface.Pseudocode
import Cellcounting.Model.Prior
import Cellcounting.Analysis.Contamination
import Cellcounting.Analysis.WeightOracle

/-!
# A single run succeeds when `p = 0`

The `p = 0` branch of the final assembly (`algorithm.tex:654-668`): one weight
oracle call at `h_H(∅)` with tolerance `ε/32` and failure probability `1/16`
lands in `[(1-ε)Z, (1+ε)Z]` with probability at least `15/16`.

`zeroRun` is a genuine randomized oracle call, not a point mass.  The proof
follows the paper and is complete relative to two children:

* `weight_oracle_accurate` (`prop:weight-oracle`, `WeightOracle.lean`): the
  call is within `(1 ± ε/32) h_H(0, 0)` with probability `≥ 1 - 1/16`;
* `contamination` (`prop:contamination`, `Contamination.lean`):
  `Z ≤ C(H) ≤ (1 + ε/32) Z`.

`p = 0` means there are no small cells (`nSmall_eq_zero_of_pSmall`), so the
penalty ignores the small profile and `C(H) = h_H(0, 0)`
(`cpart_eq_hWeight_of_pSmall_zero`).  Then `(1 - ε/32) C(H) ≥ (1 - ε) Z` and
`(1 + ε/32) C(H) ≤ (1 + ε/32)² Z ≤ (1 + ε) Z`.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: `p = 0` forces the small-cell list to be empty, since every
retained cell has a positive bound.
TEXLINE: sections/scales.tex:258-262 -/
theorem nSmall_eq_zero_of_pSmall (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ = 0) :
    nSmall I ε δ = 0 := by
  unfold nSmall
  rw [List.length_eq_zero_iff, List.eq_nil_iff_forall_not_mem]
  intro e he
  have hpos : 0 < e.2.2 := by
    have hr : e ∈ retained I := List.mem_of_mem_filter he
    simp only [retained, List.mem_flatMap, List.mem_filterMap] at hr
    obtain ⟨i, -, j, -, hj⟩ := hr
    split_ifs at hj with h
    · cases hj; exact h
  unfold pSmall at hp
  have : e.2.2 = 0 := List.sum_eq_zero_iff.1 hp _ (List.mem_map_of_mem he)
  omega

/-- INTERNAL: with no small cells the penalty does not depend on the small
profile. -/
theorem penalty_eq_of_nSmall_zero (I : Instance) (ε δ : ℚ) (h0 : nSmall I ε δ = 0)
    (x y x' y' : ℕ → ℕ) (z : ℕ → ℚ) :
    penalty I ε δ x y z = penalty I ε δ x' y' z := by
  have hb : baseLoad I ε δ x y z = baseLoad I ε δ x' y' z := by
    funext v; simp [baseLoad, h0]
  simp only [penalty, treeValues, hb]

/-- INTERNAL: for `p = 0` the single small profile is empty and
`C(H) = h_H(∅)`, read at the zero profile the oracle is called with.
TEXLINE: sections/algorithm.tex:654-656 -/
theorem cpart_eq_hWeight_of_pSmall_zero (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ = 0)
    (j : ℕ) : Cpart I ε δ j = hWeight I ε δ j (fun _ => 0) (fun _ => 0) := by
  have h0 := nSmall_eq_zero_of_pSmall I ε δ hp
  have hterm : ∀ x ∈ smallBox I ε δ,
      hWeight I ε δ j (extendN x) (fun s => smallB I ε δ s - extendN x s) =
        hWeight I ε δ j (fun _ => 0) (fun _ => 0) := by
    intro x _
    simp only [hWeight]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [penalty_eq_of_nSmall_zero I ε δ h0 _ _ (fun _ => 0) (fun _ => 0)]
  have hcard : (smallBox I ε δ).card = 1 := by
    have : IsEmpty (Fin (nSmall I ε δ)) := ⟨fun i => by have := i.2; omega⟩
    simp [smallBox]
  rw [Cpart, Finset.sum_congr rfl hterm, Finset.sum_const, hcard, one_smul]

/-- **Single run, `p = 0`.**  With probability at least `15/16` the single
oracle call lands in `[(1-ε)Z, (1+ε)Z]`.
PAPER: sections/algorithm.tex:654-668 -/
theorem zeroRun_good (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : Pseudocode.feasible I) (hp : Pseudocode.pSmall I ε δ = 0) :
    (15 / 16 : ENNReal) ≤ (Pseudocode.zeroRun I ε δ).toOuterMeasure
      {Zhat | (1 - ε) * (I.Z : ℚ) ≤ Zhat ∧ Zhat ≤ (1 + ε) * (I.Z : ℚ)} := by
  obtain ⟨hZlo, hZhi⟩ := contamination hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas
  have h0 := nSmall_eq_zero_of_pSmall I ε δ hp
  have horc := weight_oracle_accurate hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas
    (fun _ => 0) (fun _ => 0) (by intro s hs; omega) (by simp [h0, hp])
    (HParam I ε δ) le_rfl (ε / 32) (1 / 16) (by positivity) (by linarith) (by norm_num)
    (by norm_num)
  rw [← cpart_eq_hWeight_of_pSmall_zero I ε δ hp] at horc
  set CH := Cpart I ε δ (HParam I ε δ)
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  have hε1r : (ε : ℝ) < 1 := by exact_mod_cast hε1
  have hZ0 : (0 : ℝ) ≤ I.Z := Nat.cast_nonneg _
  have hsub : {h : ℚ | (1 - ((ε / 32 : ℚ) : ℝ)) * CH ≤ (h : ℝ) ∧
      (h : ℝ) ≤ (1 + ((ε / 32 : ℚ) : ℝ)) * CH} ⊆
      {Zhat | (1 - ε) * (I.Z : ℚ) ≤ Zhat ∧ Zhat ≤ (1 + ε) * (I.Z : ℚ)} := by
    rintro h ⟨hlo, hhi⟩
    push_cast at hlo hhi
    have h1 : (1 - (ε : ℝ)) * I.Z ≤ (h : ℝ) := by nlinarith
    have h2 : (h : ℝ) ≤ (1 + (ε : ℝ)) * I.Z := by nlinarith
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have h15 : ENNReal.ofReal (1 - ((1 / 16 : ℚ) : ℝ)) = 15 / 16 := by
    rw [show (1 - ((1 / 16 : ℚ) : ℝ)) = 15 / 16 by push_cast; norm_num,
      ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  rw [h15] at horc
  exact horc.trans (MeasureTheory.measure_mono hsub)

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · assembled · closed against `contamination`, `weight_oracle_accurate` (both open); `zeroRun` is an oracle call, not a point mass
-/
