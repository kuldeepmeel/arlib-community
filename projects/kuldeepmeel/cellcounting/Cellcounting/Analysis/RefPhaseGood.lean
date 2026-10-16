import Cellcounting.Analysis.RefExperiment
import Cellcounting.Analysis.RestartCoupling
import Cellcounting.Analysis.ObserveAccurate
import Cellcounting.Model.Prior

/-!
# One phase of the reference experiment (`prop:annealing`, per-phase step)

The conditional heart of `prop:annealing` (`algorithm.tex:278-371`): fix a
past on which no phase has aborted and the stored multipliers
`w^(0), …, w^(j)` are good at their own parameters.  Then phase `j` of the
reference experiment fails with probability at most `2/[100(H+1)] = 1/[50(H+1)]`.
Success (`phaseOK`) means: no abort; the stored multipliers of earlier stages are
untouched; the new collection `w^(j+1)` (if `j + 1 < H`) is good at `j + 1`; and
the new ratio estimate `R̂_j` is positive with
`|log(R̂_j / (C(j+1)/C(j)))| ≤ 4η`.

In the paper this combines the cap bound `eq:alg-cap-probability` (trace mixing
and warm return cost, `lem:trace`), the empirical bound
`eq:alg-empirical-probability` (`lem:time-average` from the endpoint domination
`≤ 2μ_j ≤ 10p²π`), and the update calculation of `algorithm.tex:345-363`.

Here the two probability bounds are `restart_coupling` (a coupling of the capped
restart with a virtual endpoint of law `≤ 2μ_j`, off an event of probability
`1/[100(H+1)]`) and `observe_accurate` (failure of `obsAccurate` from that endpoint
law, probability `1/[100(H+1)]`); `refPhase_obs_ok` is the deterministic update
calculation on `obsAccurate`, using `C(j) = Σ_A f_j` (`transMass_eq_Cpart`) and the
adjacent-parameter bounds (`fWeight_adjacent`).
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal

/-- INTERNAL: success of reference phase `j` from `st` to `st'`.
TEXLINE: sections/algorithm.tex:345-371 -/
def phaseOK (I : Instance) (ε δ : ℚ) (j : ℕ) (st st' : RefRunState) : Prop :=
  st'.aborted = false ∧
    (∀ a ≤ j, st'.ws a = st.ws a) ∧
    (j + 1 < HParam I ε δ → goodMult I ε δ (j + 1) (st'.ws (j + 1))) ∧
    ∃ R : ℝ, 0 < R ∧ st'.prod = st.prod * R ∧
      |Real.log (R / (Cpart I ε δ (j + 1) / Cpart I ε δ j))| ≤ 4 * (ηParam I ε δ : ℝ)

/-- INTERNAL: two empirical means each within relative error `η` of positive targets
`a, b` have ratio within the factors `(1-η)/(1+η)` and `(1+η)/(1-η)` of `a/b`.
TEXLINE: sections/algorithm.tex:347-352 -/
theorem phase_ratio_bounds {η a b e f : ℝ} (hη0 : 0 ≤ η) (hη : η < 1) (ha : 0 < a)
    (hb : 0 < b) (he : |e - a| ≤ η * a) (hf : |f - b| ≤ η * b) :
    0 < e ∧ 0 < f ∧ (1 - η) / (1 + η) * (a / b) ≤ e / f ∧
      e / f ≤ (1 + η) / (1 - η) * (a / b) := by
  obtain ⟨he1, he2⟩ := abs_le.1 he
  obtain ⟨hf1, hf2⟩ := abs_le.1 hf
  have h1 : 0 < 1 - η := by linarith
  have hepos : 0 < e := by nlinarith
  have hfpos : 0 < f := by nlinarith
  refine ⟨hepos, hfpos, ?_, ?_⟩
  · rw [div_mul_div_comm]
    exact div_le_div₀ hepos.le (by nlinarith) hfpos (by nlinarith)
  · rw [div_mul_div_comm]
    exact div_le_div₀ (by positivity) (by nlinarith) (by positivity) (by nlinarith)

/-- INTERNAL: a factor between `(1-η)/(1+η)` and its reciprocal has log at most `4η`
in absolute value (`η ≤ 1/2`).
TEXLINE: sections/algorithm.tex:362-368 -/
theorem phase_log_le {η x : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (hx : (1 - η) / (1 + η) ≤ x) (hx' : x ≤ (1 + η) / (1 - η)) :
    |Real.log x| ≤ 4 * η := by
  have h1 : 0 < 1 - η := by linarith
  have h2 : 0 < 1 + η := by linarith
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hkey : (1 + η) / (1 - η) - 1 ≤ 4 * η := by
    rw [div_sub_one h1.ne', div_le_iff₀ h1]; nlinarith
  have hinv : x⁻¹ ≤ (1 + η) / (1 - η) := by
    rw [inv_le_comm₀ hxpos (by positivity), inv_div]; exact hx
  rw [abs_le]
  constructor
  · have := Real.one_sub_inv_le_log_of_pos hxpos; linarith
  · have := Real.log_le_sub_one_of_pos hxpos; linarith


/-- INTERNAL: an estimate within a factor two of `C(j)/c_il(j)` is good at `j + 1`, given
the adjacent-parameter bounds on `C` and `c_il`.
TEXLINE: sections/algorithm.tex:352-357 -/
theorem phase_good_of_adj {C0 C1 c0 c1 W : ℝ} (hC1 : 0 < C1) (hc0 : 0 < c0) (hc1 : 0 < c1)
    (hCa : C1 ≤ C0) (hCb : C0 ≤ 2 * C1) (hca : c1 ≤ c0) (hcb : c0 ≤ 2 * c1)
    (hlo : 1 / 2 * (C0 / c0) ≤ W) (hhi : W ≤ 2 * (C0 / c0)) :
    C1 / (4 * c1) ≤ W ∧ W ≤ 4 * C1 / c1 := by
  constructor
  · refine le_trans ?_ hlo
    rw [div_le_iff₀ (by positivity), show 1 / 2 * (C0 / c0) * (4 * c1) = 2 * C0 * c1 / c0 by
      field_simp; ring, le_div_iff₀ hc0]
    nlinarith
  · refine le_trans hhi ?_
    rw [le_div_iff₀ hc1, show 2 * (C0 / c0) * c1 = 2 * C0 * c1 / c0 by ring, div_le_iff₀ hc0]
    nlinarith

/-- INTERNAL: `f_j(S) > 0` (the free box is nonempty and every term is positive). -/
theorem refPhase_fWeight_pos (I : Instance) (ε δ : ℚ) (j : ℕ) (S : Finset ℕ) :
    0 < fWeight I ε δ j S := by
  unfold fWeight
  refine mul_pos ?_ (Finset.prod_pos fun s _ => by positivity)
  exact Finset.sum_pos (fun z _ => by positivity) ⟨fun _ => 0, by simp [freeBox]⟩

/-- INTERNAL: `C(j) > 0` (a local copy of `Cpart_pos`, which lives in a module that
imports this one). -/
theorem refPhase_Cpart_pos (I : Instance) (ε δ : ℚ) (j : ℕ) : 0 < Cpart I ε δ j :=
  Finset.sum_pos (fun _ _ => Finset.sum_pos (fun _ _ => by positivity)
    ⟨fun _ => 0, by simp [freeBox]⟩) ⟨fun _ => 0, by simp [smallBox]⟩

open Classical in
/-- INTERNAL: `C(j+1) ≤ C(j) ≤ 2 C(j+1)`, summing `fWeight_adjacent` over transversals.
TEXLINE: sections/algorithm.tex:35-42 -/
theorem refPhase_Cpart_adj (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (hfeas : feasible I)
    (j : ℕ) : Cpart I ε δ (j + 1) ≤ Cpart I ε δ j ∧ Cpart I ε δ j ≤ 2 * Cpart I ε δ (j + 1) := by
  rw [← transMass_eq_Cpart, ← transMass_eq_Cpart]
  unfold transMass
  have hS : ∀ S ∈ transStates I ε δ, S ∈ refStates I ε δ := fun S hS =>
    (Finset.mem_filter.1 hS).1
  constructor
  · exact Finset.sum_le_sum fun S hS' => (fWeight_adjacent I ε δ hε hfeas j S (hS S hS')).2
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun S hS' => ?_
    have := (fWeight_adjacent I ε δ hε hfeas j S (hS S hS')).1
    linarith

open Classical in
/-- INTERNAL: `c_il(j+1) ≤ c_il(j) ≤ 2 c_il(j+1)`, summing `fWeight_adjacent` over `A_il`.
TEXLINE: sections/algorithm.tex:35-42 -/
theorem refPhase_cDef_adj (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (hfeas : feasible I)
    (j i l : ℕ) : cDef I ε δ (j + 1) i l ≤ cDef I ε δ j i l ∧
      cDef I ε δ j i l ≤ 2 * cDef I ε δ (j + 1) i l := by
  unfold cDef
  constructor
  · exact Finset.sum_le_sum fun S hS' =>
      (fWeight_adjacent I ε δ hε hfeas j S (Finset.mem_filter.1 hS').1).2
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun S hS' => ?_
    have := (fWeight_adjacent I ε δ hε hfeas j S (Finset.mem_filter.1 hS').1).1
    linarith

/-- INTERNAL: a state of type `A_il` has distinct labels `i, l < p`. -/
theorem kind_defect_spec (I : Instance) (ε δ : ℚ) (S : Finset ℕ) (i l : ℕ)
    (h : kind I ε δ S = .defect i l) : i < pSmall I ε δ ∧ l < pSmall I ε δ ∧ i ≠ l := by
  unfold kind at h
  dsimp only at h
  split_ifs at h with h1 h2 h3
  obtain ⟨e, he⟩ := Finset.card_eq_one.1 h3.1
  obtain ⟨f, hf⟩ := Finset.card_eq_one.1 h3.2
  rw [he, hf] at h
  simp only [Finset.sup_singleton, id, Program.Kind.defect.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hem : e ∈ (Finset.range (pSmall I ε δ)).filter fun i => 2 * i ∉ S ∧ 2 * i + 1 ∉ S := by
    rw [he]; exact Finset.mem_singleton_self _
  have hfm : f ∈ (Finset.range (pSmall I ε δ)).filter fun i => 2 * i ∈ S ∧ 2 * i + 1 ∈ S := by
    rw [hf]; exact Finset.mem_singleton_self _
  simp only [Finset.mem_filter, Finset.mem_range] at hem hfm
  refine ⟨hem.1, hfm.1, fun hef => ?_⟩
  subst hef
  exact hem.2.1 hfm.2.1

/-- INTERNAL: every defect class `A_il` (`i ≠ l < p`) is nonempty in the paired ground set.
TEXLINE: sections/signatures.tex:13-41 -/
theorem exists_defect_state (I : Instance) (ε δ : ℚ) (i l : ℕ) (hi : i < pSmall I ε δ)
    (hl : l < pSmall I ε δ) (hil : i ≠ l) :
    ∃ S ∈ refStates I ε δ, kind I ε δ S = .defect i l := by
  set p := pSmall I ε δ
  refine ⟨insert (2 * l + 1) (((Finset.range p).erase i).image (2 * ·)), ?_, ?_⟩
  · simp only [refStates, Finset.mem_powerset]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_erase, Finset.mem_range] at hx
    rw [Finset.mem_range]
    rcases hx with rfl | ⟨a, ⟨-, ha⟩, rfl⟩ <;> omega
  · have m2 : ∀ k, 2 * k ∈ insert (2 * l + 1) (((Finset.range p).erase i).image (2 * ·)) ↔
        k ≠ i ∧ k < p := by
      intro k
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_erase, Finset.mem_range]
      constructor
      · rintro (h | ⟨a, ⟨ha1, ha2⟩, ha⟩)
        · omega
        · obtain rfl : a = k := by omega
          exact ⟨ha1, ha2⟩
      · rintro ⟨h1, h2⟩; exact Or.inr ⟨k, ⟨h1, h2⟩, rfl⟩
    have m21 : ∀ k, 2 * k + 1 ∈ insert (2 * l + 1) (((Finset.range p).erase i).image (2 * ·)) ↔
        k = l := by
      intro k
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_erase, Finset.mem_range]
      constructor
      · rintro (h | ⟨a, -, ha⟩) <;> omega
      · rintro rfl; exact Or.inl rfl
    have hE : (Finset.range p).filter (fun k => 2 * k ∉
        insert (2 * l + 1) (((Finset.range p).erase i).image (2 * ·)) ∧
        2 * k + 1 ∉ insert (2 * l + 1) (((Finset.range p).erase i).image (2 * ·))) = {i} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, m2, m21, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2, h3⟩; by_contra hk; exact h2 ⟨hk, h1⟩
      · rintro rfl; exact ⟨hi, fun h => h.1 rfl, hil⟩
    have hF : (Finset.range p).filter (fun k => 2 * k ∈
        insert (2 * l + 1) (((Finset.range p).erase i).image (2 * ·)) ∧
        2 * k + 1 ∈ insert (2 * l + 1) (((Finset.range p).erase i).image (2 * ·))) = {l} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, m2, m21, Finset.mem_singleton]
      constructor
      · rintro ⟨-, -, h⟩; exact h
      · rintro rfl; exact ⟨hl, ⟨Ne.symm hil, hl⟩, rfl⟩
    unfold kind
    dsimp only
    rw [hE, hF]
    simp

open Classical in
/-- INTERNAL: `c_il(j) > 0` for distinct labels `i, l < p`. -/
theorem refPhase_cDef_pos (I : Instance) (ε δ : ℚ) (j i l : ℕ) (hi : i < pSmall I ε δ)
    (hl : l < pSmall I ε δ) (hil : i ≠ l) : 0 < cDef I ε δ j i l := by
  obtain ⟨S, hS, hk⟩ := exists_defect_state I ε δ i l hi hl hil
  unfold cDef
  exact lt_of_lt_of_le (refPhase_fWeight_pos I ε δ j S)
    (Finset.single_le_sum (f := fun S => fWeight I ε δ j S)
      (fun S _ => (refPhase_fWeight_pos I ε δ j S).le) (Finset.mem_filter.2 ⟨hS, hk⟩))

/-- INTERNAL: with good multipliers the total mass `Λ` is at least the transversal mass `C(j)`.
TEXLINE: sections/transport.tex:36-47 -/
theorem refPhase_lamTot (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ j w) : Cpart I ε δ j ≤ refLamTot I ε δ j w := by
  rw [← transMass_eq_Cpart]
  unfold transMass refLamTot
  have hsub : transStates I ε δ ⊆ chainStates I ε δ := by
    intro S hS
    simp only [transStates, chainStates, Finset.mem_filter] at hS ⊢
    exact ⟨hS.1, by rw [hS.2]; simp⟩
  have heq : ∀ S ∈ transStates I ε δ, fWeight I ε δ j S = refLam I ε δ S j w := by
    intro S hS
    simp only [transStates, Finset.mem_filter] at hS
    unfold refLam; rw [hS.2]
  rw [Finset.sum_congr rfl heq]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun S _ _ => ?_
  unfold refLam
  split
  · rename_i i l hk
    obtain ⟨hi, hl, hil⟩ := kind_defect_spec I ε δ S i l hk
    refine mul_nonneg (refPhase_fWeight_pos I ε δ j S).le (le_trans ?_ (hgood i hi l hl hil).1)
    exact div_nonneg (refPhase_Cpart_pos I ε δ j).le (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun S _ => (refPhase_fWeight_pos I ε δ j S).le))
  · exact (refPhase_fWeight_pos I ε δ j S).le

/-- INTERNAL: `0 ≤ η ≤ 1/3` (indeed `η = ε/(200(H+1)) < 1/200`). -/
theorem ηParam_le_third (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (hε1 : ε < 1) :
    0 ≤ (ηParam I ε δ : ℝ) ∧ (ηParam I ε δ : ℝ) ≤ 1 / 3 := by
  have hpos : (0 : ℚ) < ((200 * (HParam I ε δ + 1) : ℕ) : ℚ) := by positivity
  have h1 : 0 ≤ ηParam I ε δ := div_nonneg hε.le hpos.le
  have h2 : ηParam I ε δ ≤ 1 / 3 := by
    unfold ηParam
    rw [div_le_iff₀ hpos]
    push_cast
    nlinarith
  refine ⟨by exact_mod_cast h1, ?_⟩
  have := (Rat.cast_le (K := ℝ)).2 h2
  simpa using this

/-- INTERNAL: empirical success makes the phase succeed: on `obsAccurate` every type count
is positive, the update `w^(j+1)` is good at `j + 1`, and the ratio estimate `R̂_j` is
positive with `|log(R̂_j / (C(j+1)/C(j)))| ≤ 4η`.
TEXLINE: sections/algorithm.tex:345-371 -/
theorem refPhase_obs_ok (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (hε1 : ε < 1)
    (hfeas : feasible I) (j : ℕ) (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) (o : RefObs)
    (hacc : obsAccurate I ε δ j w o) :
    (0 < o.n0 ∧ ∀ i < pSmall I ε δ, ∀ l < pSmall I ε δ, i ≠ l → 0 < o.nT i l) ∧
      goodMult I ε δ (j + 1) (refUpdateW (pSmall I ε δ) w o) ∧
      0 < (o.sumG / (NavParam I ε δ : ℝ)) / ((o.n0 : ℝ) / (NavParam I ε δ : ℝ)) ∧
      |Real.log ((o.sumG / (NavParam I ε δ : ℝ)) / ((o.n0 : ℝ) / (NavParam I ε δ : ℝ)) /
          (Cpart I ε δ (j + 1) / Cpart I ε δ j))| ≤ 4 * (ηParam I ε δ : ℝ) := by
  obtain ⟨hη0, hη3⟩ := ηParam_le_third I ε δ hε hε1
  have hC0 := refPhase_Cpart_pos I ε δ j
  have hC1 := refPhase_Cpart_pos I ε δ (j + 1)
  have hΛ : 0 < refLamTot I ε δ j w := lt_of_lt_of_le hC0 (refPhase_lamTot I ε δ j w hgood)
  obtain ⟨h0, hT, hG⟩ := hacc
  rw [transMass_eq_Cpart] at h0 hG
  have hW : ∀ i < pSmall I ε δ, ∀ l < pSmall I ε δ, i ≠ l →
      ((refUpdateW (pSmall I ε δ) w o i l : ℚ) : ℝ) = (w i l : ℝ) * o.n0 / o.nT i l := by
    intro i hi l hl hil
    simp only [refUpdateW, hi, hl, hil, ne_eq, not_false_eq_true, and_self, if_true]
    push_cast; rfl
  unfold goodMult
  generalize (ηParam I ε δ : ℝ) = η at *
  generalize (NavParam I ε δ : ℝ) = N at *
  generalize refLamTot I ε δ j w = Λ at *
  obtain ⟨hGpos, hn0pos, hRlo, hRhi⟩ := phase_ratio_bounds hη0 (by linarith)
    (div_pos hC1 hΛ) (div_pos hC0 hΛ) hG h0
  have hNpos : N ≠ 0 := by
    intro h; rw [h, div_zero] at hn0pos; exact lt_irrefl _ hn0pos
  have hn0 : 0 < o.n0 := by
    rcases Nat.eq_zero_or_pos o.n0 with h | h
    · rw [h] at hn0pos; simp at hn0pos
    · exact h
  have hk1 : 1 / 2 ≤ (1 - η) / (1 + η) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hk2 : (1 + η) / (1 - η) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hpair : ∀ i < pSmall I ε δ, ∀ l < pSmall I ε δ, i ≠ l →
      0 < o.nT i l ∧ (1 / 2) * (Cpart I ε δ j / cDef I ε δ j i l) ≤
        (w i l : ℝ) * ((o.n0 : ℝ) / N) / ((o.nT i l : ℝ) / N) ∧
        (w i l : ℝ) * ((o.n0 : ℝ) / N) / ((o.nT i l : ℝ) / N) ≤
          2 * (Cpart I ε δ j / cDef I ε δ j i l) := by
    intro i hi l hl hil
    have hc := refPhase_cDef_pos I ε δ j i l hi hl hil
    have hw : 0 < (w i l : ℝ) :=
      lt_of_lt_of_le (div_pos hC0 (mul_pos (by norm_num) hc)) (hgood i hi l hl hil).1
    obtain ⟨-, hnTpos, hlo, hhi⟩ := phase_ratio_bounds hη0 (by linarith)
      (div_pos hC0 hΛ) (div_pos (mul_pos hw hc) hΛ) h0 (hT i hi l hl hil)
    have hab : Cpart I ε δ j / Λ / ((w i l : ℝ) * cDef I ε δ j i l / Λ) =
        Cpart I ε δ j / cDef I ε δ j i l / (w i l : ℝ) := by
      field_simp
    rw [hab] at hlo hhi
    refine ⟨?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos (o.nT i l) with h | h
      · rw [h] at hnTpos; simp at hnTpos
      · exact h
    · rw [mul_div_assoc]
      have := mul_le_mul_of_nonneg_left hlo hw.le
      have e : (w i l : ℝ) * ((1 - η) / (1 + η) * (Cpart I ε δ j / cDef I ε δ j i l /
          (w i l : ℝ))) = (1 - η) / (1 + η) * (Cpart I ε δ j / cDef I ε δ j i l) := by
        field_simp
      rw [e] at this
      exact le_trans (mul_le_mul_of_nonneg_right hk1 (div_pos hC0 hc).le) this
    · rw [mul_div_assoc]
      have := mul_le_mul_of_nonneg_left hhi hw.le
      have e : (w i l : ℝ) * ((1 + η) / (1 - η) * (Cpart I ε δ j / cDef I ε δ j i l /
          (w i l : ℝ))) = (1 + η) / (1 - η) * (Cpart I ε δ j / cDef I ε δ j i l) := by
        field_simp
      rw [e] at this
      exact le_trans this (mul_le_mul_of_nonneg_right hk2 (div_pos hC0 hc).le)
  refine ⟨⟨hn0, fun i hi l hl hil => (hpair i hi l hl hil).1⟩, ?_, div_pos hGpos hn0pos, ?_⟩
  · intro i hi l hl hil
    obtain ⟨hnT, hlo, hhi⟩ := hpair i hi l hl hil
    have hc0 := refPhase_cDef_pos I ε δ j i l hi hl hil
    have hc1 := refPhase_cDef_pos I ε δ (j + 1) i l hi hl hil
    obtain ⟨hCa, hCb⟩ := refPhase_Cpart_adj I ε δ hε hfeas j
    obtain ⟨hca, hcb⟩ := refPhase_cDef_adj I ε δ hε hfeas j i l
    rw [hW i hi l hl hil, show (w i l : ℝ) * o.n0 / o.nT i l =
        (w i l : ℝ) * ((o.n0 : ℝ) / N) / ((o.nT i l : ℝ) / N) by field_simp]
    exact phase_good_of_adj hC1 hc0 hc1 hCa hCb hca hcb hlo hhi
  · have hq : (Cpart I ε δ (j + 1) / Λ) / (Cpart I ε δ j / Λ) =
        Cpart I ε δ (j + 1) / Cpart I ε δ j := by
      field_simp
    rw [hq] at hRlo hRhi
    have hqpos : 0 < Cpart I ε δ (j + 1) / Cpart I ε δ j := div_pos hC1 hC0
    exact phase_log_le hη0 (by linarith) ((le_div_iff₀ hqpos).2 hRlo)
      ((div_le_iff₀ hqpos).2 hRhi)

/-- **One reference phase** (`prop:annealing`, the conditional step): from a
non-aborted state whose stored multipliers `w^(0..j)` are good, phase `j` fails
with probability at most `2/[100(H+1)]`.
PAPER: sections/algorithm.tex:278-371 -/
theorem ref_phase_good (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (st : RefRunState) (hab : st.aborted = false)
    (hgood : ∀ a ≤ j, goodMult I ε δ a (st.ws a)) :
    (refPhase I ε δ j st).toOuterMeasure {st' | ¬ phaseOK I ε δ j st st'} ≤
      1 / (50 * ((HParam I ε δ : ENNReal) + 1)) := by
  obtain ⟨κ, hκ1, hκ2, hκ3⟩ :=
    restart_coupling hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj st.ws hgood
  have hobs := observe_accurate hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj (st.ws j)
    (hgood j le_rfl) (κ.map Prod.snd) hκ2
  set B : Set RefRunState := {st' | ¬ phaseOK I ε δ j st st'} with hB
  set E : Set (Restart × Finset ℕ) := {q | q.1.aborted = true ∨ q.1.S ≠ q.2} with hE
  set Bo : Set RefObs := {o | ¬ obsAccurate I ε δ j (st.ws j) o} with hBo
  -- the observation-and-update stage of the phase
  set g : RefObs → PMF RefRunState := fun o =>
    if 0 < o.n0 ∧ ∀ i < pSmall I ε δ, ∀ l < pSmall I ε δ, i ≠ l → 0 < o.nT i l then
        let R := (o.sumG / (NavParam I ε δ : ℝ)) / ((o.n0 : ℝ) / (NavParam I ε δ : ℝ))
        if j + 1 < HParam I ε δ then
          pure ⟨Function.update st.ws (j + 1) (refUpdateW (pSmall I ε δ) (st.ws j) o),
            st.prod * R, false⟩
        else pure ⟨st.ws, st.prod * R, false⟩
      else pure { st with aborted := true } with hg
  set F : Restart → PMF RefRunState := fun rs =>
    if rs.aborted then pure { st with aborted := true } else
      (refObserve I ε δ j (st.ws j) rs.S).bind g with hF
  have hphase : refPhase I ε δ j st = κ.bind (F ∘ Prod.fst) := by
    rw [← PMF.bind_map, hκ1, PMF.bind_bind]
    simp only [refPhase, hab]
    rfl
  have hgok : ∀ o, obsAccurate I ε δ j (st.ws j) o → (g o).toOuterMeasure B = 0 := by
    intro o hacc
    obtain ⟨hcond, hgw, hRpos, hRlog⟩ :=
      refPhase_obs_ok I ε δ hε hε1 hfeas j (st.ws j) (hgood j le_rfl) o hacc
    simp only [hg, if_pos hcond]
    by_cases hjH : j + 1 < HParam I ε δ
    · rw [if_pos hjH]
      change (PMF.pure _).toOuterMeasure B = 0
      rw [PMF.toOuterMeasure_pure_apply, if_neg]
      simp only [hB, Set.mem_setOf_eq, not_not]
      refine ⟨rfl, fun a ha => Function.update_of_ne (by omega) _ _, fun _ => ?_, _, hRpos,
        rfl, hRlog⟩
      simpa only [Function.update_self] using hgw
    · rw [if_neg hjH]
      change (PMF.pure _).toOuterMeasure B = 0
      rw [PMF.toOuterMeasure_pure_apply, if_neg]
      simp only [hB, Set.mem_setOf_eq, not_not]
      exact ⟨rfl, fun a ha => rfl, fun h => absurd h hjH, _, hRpos, rfl, hRlog⟩
  have hstep : ∀ q, κ q * (F q.1).toOuterMeasure B ≤
      E.indicator κ q + κ q * (refObserve I ε δ j (st.ws j) q.2).toOuterMeasure Bo := by
    intro q
    by_cases hq : q ∈ E
    · rw [Set.indicator_of_mem hq]
      calc κ q * (F q.1).toOuterMeasure B ≤ κ q * 1 := by
            gcongr
            calc (F q.1).toOuterMeasure B ≤ (F q.1).toOuterMeasure Set.univ :=
                  MeasureTheory.measure_mono (Set.subset_univ _)
              _ = 1 := (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)
        _ ≤ _ := by rw [mul_one]; exact le_self_add
    · rw [Set.indicator_of_notMem hq, zero_add]
      simp only [hE, Set.mem_setOf_eq, not_or, Bool.not_eq_true, not_not] at hq
      gcongr
      simp only [hF, hq.1, Bool.false_eq_true, if_false, hq.2]
      rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
      refine ENNReal.tsum_le_tsum fun o => ?_
      by_cases ho : o ∈ Bo
      · rw [Set.indicator_of_mem ho]
        calc _ ≤ (refObserve I ε δ j (st.ws j) q.2) o * 1 := by
              gcongr
              calc (g o).toOuterMeasure B ≤ (g o).toOuterMeasure Set.univ :=
                    MeasureTheory.measure_mono (Set.subset_univ _)
                _ = 1 := (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)
          _ = _ := mul_one _
      · rw [Set.indicator_of_notMem ho, hgok o (by simpa [hBo] using ho), mul_zero]
  rw [hphase, PMF.toOuterMeasure_bind_apply]
  calc ∑' q, κ q * (F q.1).toOuterMeasure B
      ≤ ∑' q, (E.indicator κ q +
          κ q * (refObserve I ε δ j (st.ws j) q.2).toOuterMeasure Bo) :=
        ENNReal.tsum_le_tsum hstep
    _ = κ.toOuterMeasure E + ((κ.map Prod.snd).bind (refObserve I ε δ j (st.ws j))).toOuterMeasure Bo := by
        rw [ENNReal.tsum_add, PMF.toOuterMeasure_apply, PMF.bind_map,
          PMF.toOuterMeasure_bind_apply]
        rfl
    _ ≤ 1 / (100 * ((HParam I ε δ : ℝ≥0∞) + 1)) + 1 / (100 * ((HParam I ε δ : ℝ≥0∞) + 1)) :=
        add_le_add hκ3 hobs
    _ = 1 / (50 * ((HParam I ε δ : ENNReal) + 1)) := by
        rw [ENNReal.div_add_div_same, show (100 : ℝ≥0∞) * ((HParam I ε δ : ℝ≥0∞) + 1) =
            2 * (50 * ((HParam I ε δ : ℝ≥0∞) + 1)) by rw [← mul_assoc]; norm_num,
          show (1 : ℝ≥0∞) + 1 = 2 * 1 by norm_num,
          ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r5 · proved · `ref_phase_good` from `restart_coupling`, `observe_accurate`, `refPhase_obs_ok`
-/
