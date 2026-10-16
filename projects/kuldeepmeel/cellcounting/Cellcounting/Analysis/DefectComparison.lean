import Cellcounting.Analysis.SelPairs
import Cellcounting.Analysis.DefectInequalities
import Cellcounting.Analysis.LiftComparison
import Cellcounting.Model.Prior

/-!
# The defect comparison `eq:defect-comparison` (`transport.tex:470-482`)

For distinct labels `i, t, l < p`,
`c_it c_tl ≤ q² c̃_it c̃_tl ≤ q² C c̃_il ≤ q³ C c_il`: the lift comparison
`eq:lift-comparison` on the defect classes (`lift_defect_le`), and the three-pair
defect inequality `eq:defect-three-pair` (`defect_three_pair`) for the second lift
`f̃_j` at the empty assignment, where `z_∅ = Σ_A f̃ = Σ_A f = C` (`lift_trans_eq`).
-/

namespace Cellcounting.Analysis

open Pseudocode Finset

/-- INTERNAL: `f̃_j ≥ 0`. -/
theorem dc_fTilde_nonneg (I : Instance) (ε δ : ℚ) (j : ℕ) (S : Finset ℕ) :
    0 ≤ fTilde I ε δ j S := by
  unfold fTilde
  refine mul_nonneg ?_ (Finset.prod_nonneg fun s _ => by positivity)
  exact Finset.sum_nonneg fun z _ => by positivity

/-- INTERNAL: the empty assignment with all pairs unassigned is valid. -/
theorem dc_root_valid (p : ℕ) : AsgValid p ∅ (List.range p) :=
  ⟨List.nodup_range, fun t ht => List.mem_range.1 ht, by simp, by simp,
    fun t ht => by simp [ht]⟩

open Classical in
/-- INTERNAL: on a defect class, the masses of the two lifts are within `q`:
`c_il ≤ q c̃_il` and `c̃_il ≤ q c_il`.
TEXLINE: sections/signatures.tex:62-78 -/
theorem dc_cDef_lift (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (j : ℕ) (i l : ℕ) (hi : i < pSmall I ε δ) (hl : l < pSmall I ε δ)
    (hil : i ≠ l) :
    cDef I ε δ j i l ≤
        (qParam I ε δ : ℝ) * defMass (fTilde I ε δ j) ∅ (List.range (pSmall I ε δ)) i l ∧
      defMass (fTilde I ε δ j) ∅ (List.range (pSmall I ε δ)) i l ≤
        (qParam I ε δ : ℝ) * cDef I ε δ j i l := by
  rw [defMass_root_eq I ε δ _ i l hi hl hil]
  unfold cDef
  rw [Finset.mul_sum, Finset.mul_sum]
  constructor
  · exact Finset.sum_le_sum fun S hS => (lift_defect_le hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas
      j S i l (mem_filter.1 hS).2).1
  · exact Finset.sum_le_sum fun S hS => (lift_defect_le hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas
      j S i l (mem_filter.1 hS).2).2

/-- **Defect comparison** (`eq:defect-comparison`): `c_it c_tl ≤ q³ C c_il` for
distinct labels `i, t, l < p`.
PAPER: sections/transport.tex:476-482 -/
theorem defect_comparison (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (j : ℕ) (hj : j ≤ HParam I ε δ) (i t l : ℕ)
    (hi : i < pSmall I ε δ) (ht : t < pSmall I ε δ) (hl : l < pSmall I ε δ)
    (hit : i ≠ t) (htl : t ≠ l) (hil : i ≠ l) :
    cDef I ε δ j i t * cDef I ε δ j t l ≤
      (qParam I ε δ : ℝ) ^ 3 * Cpart I ε δ j * cDef I ε δ j i l := by
  classical
  have hp : pSmall I ε δ ≠ 0 := by omega
  set T := List.range (pSmall I ε δ)
  set q : ℝ := (qParam I ε δ : ℝ) with hqdef
  have hq : 0 ≤ q := Nat.cast_nonneg _
  set ct := fun a b => defMass (fTilde I ε δ j) ∅ T a b with hct
  have hct0 : ∀ a b, a < pSmall I ε δ → b < pSmall I ε δ → a ≠ b → 0 ≤ ct a b := by
    intro a b ha hb hab
    simp only [hct]
    rw [defMass_root_eq I ε δ _ a b ha hb hab]
    exact Finset.sum_nonneg fun S _ => dc_fTilde_nonneg I ε δ j S
  have hc0 : ∀ a b, 0 ≤ cDef I ε δ j a b := td_cDef_nonneg I ε δ j
  have h1 := dc_cDef_lift hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas j i t hi ht hit
  have h2 := dc_cDef_lift hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas j t l ht hl htl
  have h4 := dc_cDef_lift hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas j i l hi hl hil
  -- `z_∅ = Σ_A f̃ = Σ_A f = C`
  have hz : trMass (fTilde I ε δ j) ∅ T = Cpart I ε δ j := by
    rw [trMass_root_eq, ← transMass_eq_Cpart]
    unfold transMass
    refine Finset.sum_congr rfl fun S hS => ?_
    unfold transStates at hS
    exact lift_trans_eq I ε δ j S (mem_filter.1 hS).2
  have h3 := defect_three_pair hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj ∅ T
    (dc_root_valid _) i t l (List.mem_range.2 hi) (List.mem_range.2 ht) (List.mem_range.2 hl)
    hit htl hil
  rw [hz] at h3
  have hC := td_Cpart_pos I ε δ j
  have e1 := hct0 i t hi ht hit
  have e2 := hct0 t l ht hl htl
  have e3 := hct0 i l hi hl hil
  -- `c_it c_tl ≤ q² c̃_it c̃_tl`
  have s1 : cDef I ε δ j i t * cDef I ε δ j t l ≤ (q * ct i t) * (q * ct t l) :=
    mul_le_mul h1.1 h2.1 (hc0 t l) (mul_nonneg hq e1)
  -- `q² c̃_it c̃_tl ≤ q² C c̃_il ≤ q³ C c_il`
  have s2 : (q * ct i t) * (q * ct t l) ≤ q ^ 2 * (Cpart I ε δ j * ct i l) := by
    have := mul_le_mul_of_nonneg_left h3 (sq_nonneg q)
    simp only [hct] at this ⊢
    nlinarith
  have s3 : q ^ 2 * (Cpart I ε δ j * ct i l) ≤
      q ^ 2 * (Cpart I ε δ j * (q * cDef I ε δ j i l)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4.2 hC.le) (sq_nonneg q)
  calc cDef I ε δ j i t * cDef I ε δ j t l ≤ q ^ 2 * (Cpart I ε δ j * (q * cDef I ε δ j i l)) :=
        s1.trans (s2.trans s3)
    _ = q ^ 3 * Cpart I ε δ j * cDef I ε δ j i l := by ring

end Cellcounting.Analysis
