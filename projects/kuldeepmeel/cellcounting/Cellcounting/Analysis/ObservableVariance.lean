import Cellcounting.Analysis.RefStationary
import Cellcounting.Analysis.TransversalVariance
import Cellcounting.Analysis.DefectMean
import Cellcounting.Analysis.RefEnergyDirichlet
import Cellcounting.Model.Prior

/-!
# Observable variance (`prop:observable-variance`, `transport.tex:532-571`)

For good multipliers and every real `g` on `X`,
`Var_π(𝓠 g) ≤ K_obs 𝓔(g)`: the variance under `π` of the projection `𝓠 g`
(`refQ`: transversal values kept, each defect type averaged) is controlled by the
energy `𝓔(g) = ⟨g, (I - P) g⟩_π` (`refEnergy`).  The proof follows the paper: bound
the variance by the squared deviation about `m = E_μ g`; on transversals this is
`(C/Λ) Var_μ g ≤ Var_μ g`; on each defect state `𝓠 g = ḡ_il` and
`(ḡ_il - m)² ≤ 2 (C_d / C) 𝔇(g) + 8 Var_μ g` (`defect_mean`); the defect states carry
`π`-mass at most one; then `C Var_μ g ≤ C_p 𝔇(g)` (`transversal_variance`), and
`𝔇(g)/C ≤ 10 p⁴ 𝓔(g)` from `refEnergy_eq_refDir` and `Λ ≤ 5 p² C`
(`td_refLamTot_le`).  The defect states are bounded state by state rather than grouped
by type.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: variance is at most the squared deviation about any constant, for weights
summing to one.
TEXLINE: sections/transport.tex:552-556 -/
theorem ov_var_le_dev {α : Type*} (s : Finset α) (π Q : α → ℝ)
    (hπ : ∑ x ∈ s, π x = 1) (c : ℝ) :
    ∑ x ∈ s, π x * (Q x - ∑ y ∈ s, π y * Q y) ^ 2 ≤ ∑ x ∈ s, π x * (Q x - c) ^ 2 := by
  set M := ∑ y ∈ s, π y * Q y with hM
  have h : ∀ x, π x * (Q x - c) ^ 2 = π x * (Q x - M) ^ 2 + (2 * (M - c)) * (π x * Q x)
      - (2 * (M - c) * M) * π x + (M - c) ^ 2 * π x := by intro x; ring
  rw [Finset.sum_congr rfl (fun x _ => h x), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← hM, hπ]
  nlinarith [sq_nonneg (M - c)]

open Classical in
/-- INTERNAL: on a defect type with nonzero multiplier, `𝓠 g` is the defect mean `ḡ_il`
(the multiplier is constant on the type, so the conditional `π`-mean is the `f_j`-mean).
TEXLINE: sections/transport.tex:508-512 -/
theorem ov_refQ_defect (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ j w) (g : Finset ℕ → ℝ) (S : Finset ℕ) (i l : ℕ)
    (hk : kind I ε δ S = .defect i l) (hw : (w i l : ℝ) ≠ 0) :
    refQ I ε δ j w g S = refDefMean I ε δ j i l g := by
  have hΛ : 0 < refLamTot I ε δ j w :=
    lt_of_lt_of_le (td_Cpart_pos I ε δ j) (td_Cpart_le_refLamTot I ε δ j w hgood)
  have hset : (chainStates I ε δ).filter (fun S' => kind I ε δ S' = .defect i l) =
      (refStates I ε δ).filter (fun S' => kind I ε δ S' = .defect i l) := by
    unfold chainStates
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun S' _ => ?_
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨by rw [h]; simp, h⟩
  have hpi : ∀ S' ∈ (refStates I ε δ).filter (fun S' => kind I ε δ S' = .defect i l),
      refPi I ε δ j w S' = (w i l : ℝ) / refLamTot I ε δ j w * fWeight I ε δ j S' := by
    intro S' hS'
    have hX : S' ∈ chainStates I ε δ := by rw [← hset] at hS'; exact (Finset.mem_filter.1 hS').1
    have hk' := (Finset.mem_filter.1 hS').2
    unfold refPi
    rw [if_pos hX, td_refLam_eq, hk']
    ring
  unfold refQ
  rw [hk]
  simp only
  rw [hset, Finset.sum_congr rfl (fun S' hS' => by rw [hpi S' hS']),
    Finset.sum_congr rfl hpi, ← Finset.mul_sum]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, mul_div_mul_left _ _ (div_ne_zero hw hΛ.ne')]
  rfl

/-- **Observable variance** (`prop:observable-variance`): for good multipliers,
`Var_π(𝓠 g) ≤ K_obs 𝓔(g)` for every real `g`.
PAPER: sections/transport.tex:532-541 -/
theorem observable_variance (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) (g : Finset ℕ → ℝ) :
    ∑ S ∈ chainStates I ε δ, refPi I ε δ j w S *
        (refQ I ε δ j w g S -
          ∑ S' ∈ chainStates I ε δ, refPi I ε δ j w S' * refQ I ε δ j w g S') ^ 2 ≤
      (KobsParam I ε δ : ℝ) * refEnergy I ε δ j w g := by
  classical
  set X := chainStates I ε δ with hX
  set p : ℝ := (pSmall I ε δ : ℝ) with hpdef
  set C := Cpart I ε δ j with hCdef
  set Λ := refLamTot I ε δ j w with hΛdef
  set m := refMuMean I ε δ j g with hmdef
  set V := refMuVar I ε δ j g with hVdef
  set D := refDir I ε δ j w g with hDdef
  set Cp : ℝ := (CpParam I ε δ : ℝ) with hCpdef
  set Cd : ℝ := (CdParam I ε δ : ℝ) with hCddef
  have hC : 0 < C := td_Cpart_pos I ε δ j
  have hCΛ : C ≤ Λ := td_Cpart_le_refLamTot I ε δ j w hgood
  have hΛ : 0 < Λ := lt_of_lt_of_le hC hCΛ
  have hp1 : (1 : ℝ) ≤ p := by
    rw [hpdef]; exact_mod_cast Nat.one_le_iff_ne_zero.2 hp
  have hπ0 : ∀ S, 0 ≤ refPi I ε δ j w S := td_refPi_nonneg I ε δ j w hgood
  -- `π` is a probability vector on `X`
  have hπsum : ∑ S ∈ X, refPi I ε δ j w S = 1 := by
    rw [Finset.sum_congr rfl (fun S hS => by unfold refPi; rw [if_pos hS]),
      ← Finset.sum_div]
    exact div_self hΛ.ne'
  have hV : 0 ≤ V := by
    refine Finset.sum_nonneg fun S _ => mul_nonneg ?_ (sq_nonneg _)
    unfold refMu
    split_ifs
    exact div_nonneg (td_fWeight_pos I ε δ j S).le (by rw [transMass_eq_Cpart]; exact hC.le)
  have hD : 0 ≤ D := td_refDir_nonneg I ε δ j w hgood g
  have hCd : 0 ≤ Cd := Nat.cast_nonneg _
  have hVle : V ≤ Cp * D / C := by
    rw [le_div_iff₀ hC]
    have := transversal_variance hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj w hgood g
    linarith
  -- the bound on one defect state
  set B := 2 * (Cd / C * D) + 8 * V with hBdef
  have hB : 0 ≤ B := add_nonneg (mul_nonneg (by norm_num) (mul_nonneg (div_nonneg hCd hC.le) hD))
    (mul_nonneg (by norm_num) hV)
  have hdef : ∀ S ∈ X.filter (fun S => ¬ kind I ε δ S = .transversal),
      refPi I ε δ j w S * (refQ I ε δ j w g S - m) ^ 2 ≤ refPi I ε δ j w S * B := by
    intro S hS
    obtain ⟨hSX, hnt⟩ := Finset.mem_filter.1 hS
    have hno : kind I ε δ S ≠ .outside := (Finset.mem_filter.1 hSX).2
    cases hk : kind I ε δ S with
    | transversal => exact absurd hk hnt
    | outside => exact absurd hk hno
    | defect i l =>
      obtain ⟨hi, hl, hil⟩ := kind_defect_lt I ε δ S i l hk
      by_cases hw : (w i l : ℝ) = 0
      · have : refPi I ε δ j w S = 0 := by
          unfold refPi
          rw [if_pos hSX, td_refLam_eq, hk]
          simp [hw]
        rw [this]; simp
      · refine mul_le_mul_of_nonneg_left ?_ (hπ0 S)
        rw [ov_refQ_defect I ε δ j w hgood g S i l hk hw]
        obtain ⟨g', h1, h2⟩ :=
          defect_mean hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj w hgood g i l hi hl hil
        have : (refDefMean I ε δ j i l g - m) ^ 2 ≤
            2 * (refDefMean I ε δ j i l g - g') ^ 2 + 2 * (g' - m) ^ 2 := by
          nlinarith [sq_nonneg (refDefMean I ε δ j i l g - g' - (g' - m))]
        rw [hBdef]
        linarith
  -- the transversal part is `(C/Λ) Var_μ g`
  have htrans : ∑ S ∈ X.filter (fun S => kind I ε δ S = .transversal),
      refPi I ε δ j w S * (refQ I ε δ j w g S - m) ^ 2 = C / Λ * V := by
    rw [hX, td_chainStates_filter_trans, hVdef, refMuVar, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hk : kind I ε δ S = .transversal := (Finset.mem_filter.1 hS).2
    have hSX : S ∈ chainStates I ε δ :=
      Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hS).1, by rw [hk]; simp⟩
    have hQ : refQ I ε δ j w g S = g S := by unfold refQ; rw [hk]
    unfold refPi refMu
    rw [if_pos hSX, if_pos hS, hQ, td_refLam_eq, hk, transMass_eq_Cpart, ← hΛdef, ← hCdef,
      ← hmdef]
    field_simp
  have hnontrans : ∑ S ∈ X.filter (fun S => ¬ kind I ε δ S = .transversal),
      refPi I ε δ j w S ≤ 1 := by
    rw [← hπsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun S _ _ => hπ0 S
  have hDC : D / C ≤ 10 * p ^ 4 * refEnergy I ε δ j w g := by
    rw [refEnergy_eq_refDir I ε δ hp j w hgood g, ← hDdef, ← hΛdef, ← hpdef,
      div_le_iff₀ hC]
    have hΛle : Λ ≤ 5 * p ^ 2 * C := td_refLamTot_le I ε δ hp j w hgood
    have hp0 : 0 < p := lt_of_lt_of_le one_pos hp1
    have : 10 * p ^ 4 * (D / (2 * p ^ 2 * Λ)) * C = 5 * p ^ 2 * C * D / Λ := by
      field_simp; ring
    rw [this, le_div_iff₀ hΛ]
    nlinarith [mul_le_mul_of_nonneg_left hΛle hD]
  calc _ ≤ ∑ S ∈ X, refPi I ε δ j w S * (refQ I ε δ j w g S - m) ^ 2 :=
        ov_var_le_dev X _ _ hπsum m
    _ = C / Λ * V + ∑ S ∈ X.filter (fun S => ¬ kind I ε δ S = .transversal),
          refPi I ε δ j w S * (refQ I ε δ j w g S - m) ^ 2 := by
        rw [← htrans, Finset.sum_filter_add_sum_filter_not]
    _ ≤ V + (∑ S ∈ X.filter (fun S => ¬ kind I ε δ S = .transversal),
          refPi I ε δ j w S) * B := by
        rw [Finset.sum_mul]
        have h1 : C / Λ * V ≤ V := by
          have : C / Λ ≤ 1 := (div_le_one hΛ).2 hCΛ
          nlinarith
        linarith [Finset.sum_le_sum hdef]
    _ ≤ V + B := by nlinarith
    _ ≤ (9 * Cp + 2 * Cd) * (D / C) := by
        rw [hBdef]
        have : Cp * D / C = Cp * (D / C) := by ring
        have h2 : Cd / C * D = Cd * (D / C) := by ring
        rw [this] at hVle
        rw [h2]
        linarith
    _ ≤ (9 * Cp + 2 * Cd) * (10 * p ^ 4 * refEnergy I ε δ j w g) :=
        mul_le_mul_of_nonneg_left hDC (add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
          (mul_nonneg (by norm_num) hCd))
    _ = (KobsParam I ε δ : ℝ) * refEnergy I ε δ j w g := by
        rw [KobsParam]; push_cast; ring

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r8 · proved · `observable_variance` from `transversal_variance`, `defect_mean`,
  `refEnergy_eq_refDir`, `td_refLamTot_le`; local helpers `ov_var_le_dev`, `ov_refQ_defect`
-/
