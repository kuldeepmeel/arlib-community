import Cellcounting.Analysis.RefChainLaw
import Cellcounting.Analysis.FWeightAdjacent
import Cellcounting.Analysis.TransMassEqCpart
import Cellcounting.Analysis.TimeAverage
import Cellcounting.Model.Prior

/-!
# Empirical accuracy of one observation trajectory (`eq:alg-empirical-probability`)

`prop:annealing`, the observation half (`algorithm.tex:313-337`).  Let the
multipliers `w` be good at `j` and let the starting law `ν` satisfy `ν ≤ 2 μ_j`,
hence `ν ≤ 10 p² π` on the full state space (`π(A) ≥ 1/(5p²)`,
`eq:type-mass-bounds`).  The observables (type indicators and `G_j`) are fixed by
the projection `Q`, take values in `[0, 1]`, and have stationary means at least
`1/(20p²)`.  `lem:time-average` bounds each empirical mean's mean squared error by
`20p² K_obs / N_av`; Markov's inequality and a union bound over the
`p(p-1) + 2 ≤ 2p²` observables give failure probability at most
`16000 p⁸ K_obs / (N_av η²) ≤ 1/[100(H+1)]`.
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal


/-- INTERNAL: `loop` commutes with a map that intertwines the step kernels.
TEXLINE: sections/algorithm.tex:226-233 -/
theorem oa_loop_map {β γ : Type} (f : ℕ → β → PMF β) (g : ℕ → γ → PMF γ) (φ : β → γ)
    (h : ∀ i b, (f i b).map φ = g i (φ b)) (k : ℕ) (b : β) :
    (loop f k b).map φ = loop g k (φ b) := by
  induction k with
  | zero => rw [loop_zero, loop_zero, PMF.pure_map]
  | succ k ih =>
    rw [loop_succ, loop_succ, PMF.map_bind, ← ih, PMF.bind_map]
    congr 1; funext x; exact h k x

/-- INTERNAL: observing a state does not move it.
TEXLINE: sections/algorithm.tex:150-156 -/
theorem oa_observeState_S (I : Instance) (ε δ : ℚ) (j : ℕ) (o : RefObs) :
    (refObserveState I ε δ j o).S = o.S := by
  unfold refObserveState; split <;> rfl

/-- INTERNAL: a tally of `refObserve` that adds `G(S')` at each observed state is the
running sum of `refTraj`.
TEXLINE: sections/algorithm.tex:226-233 -/
theorem oa_refObserve_map (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (G : Finset ℕ → ℝ) (T : RefObs → ℝ)
    (hT : ∀ o S', T (refObserveState I ε δ j { o with S := S' }) = T o + G S')
    (hT0 : ∀ S0, T ⟨S0, 0, fun _ _ => 0, 0⟩ = 0) (S0 : Finset ℕ) :
    (refObserve I ε δ j w S0).map (fun o => (o.S, T o)) =
      refTraj I ε δ j w G (NavParam I ε δ) S0 := by
  have hSeq : ∀ (o : RefObs) (S' : Finset ℕ),
      (refObserveState I ε δ j { o with S := S' }).S = S' := by
    intro o S'
    unfold refObserveState
    cases kind I ε δ S' with
    | transversal => rfl
    | defect i l => rfl
    | outside => rfl
  unfold refObserve refTraj
  have hstep : ∀ (i : ℕ) (o : RefObs),
      ((refStep I ε δ j w o.S).map fun S' => refObserveState I ε δ j { o with S := S' }).map
          (fun o => (o.S, T o)) =
        (refStep I ε δ j w (o.S, T o).1).map fun S' => (S', (o.S, T o).2 + G S') := by
    intro i o
    rw [PMF.map_comp]
    congr 1
    funext S'
    simp only [Function.comp]
    rw [hSeq o S', hT o S']
  have := oa_loop_map
    (fun _ (o : RefObs) =>
      (refStep I ε δ j w o.S).map fun S' => refObserveState I ε δ j { o with S := S' })
    (fun _ (x : Finset ℕ × ℝ) => (refStep I ε δ j w x.1).map fun S' => (S', x.2 + G S'))
    (fun o => (o.S, T o)) hstep (NavParam I ε δ - 1)
    (refObserveState I ε δ j ⟨S0, 0, fun _ _ => 0, 0⟩)
  rw [this]
  congr 1
  show ((refObserveState I ε δ j ⟨S0, 0, fun _ _ => 0, 0⟩).S,
      T (refObserveState I ε δ j ⟨S0, 0, fun _ _ => 0, 0⟩)) = (S0, G S0)
  have hS0 : (refObserveState I ε δ j ⟨S0, 0, fun _ _ => 0, 0⟩).S = S0 := by
    have := hSeq ⟨S0, 0, fun _ _ => 0, 0⟩ S0
    simpa using this
  rw [hS0]
  congr 1
  have := hT ⟨S0, 0, fun _ _ => 0, 0⟩ S0
  simp only [hT0] at this
  simpa using this

open Classical in
/-- INTERNAL: the type of a defect state names two distinct labels below `p`.
TEXLINE: sections/signatures.tex:13-41 -/
theorem oa_kind_defect (I : Instance) (ε δ : ℚ) (S : Finset ℕ) (i l : ℕ)
    (h : kind I ε δ S = .defect i l) : i < pSmall I ε δ ∧ l < pSmall I ε δ ∧ i ≠ l := by
  simp only [kind] at h
  split_ifs at h with h1 h2 h3
  obtain ⟨x, hxE⟩ := Finset.card_eq_one.mp h3.1
  obtain ⟨y, hyF⟩ := Finset.card_eq_one.mp h3.2
  rw [hxE, Finset.sup_singleton] at h
  rw [hyF, Finset.sup_singleton] at h
  injection h with hi hl
  subst hi; subst hl
  have hxE' : x ∈ (Finset.range (pSmall I ε δ)).filter
      fun k => 2 * k ∉ S ∧ 2 * k + 1 ∉ S := hxE ▸ Finset.mem_singleton_self x
  have hyF' : y ∈ (Finset.range (pSmall I ε δ)).filter
      fun k => 2 * k ∈ S ∧ 2 * k + 1 ∈ S := hyF ▸ Finset.mem_singleton_self y
  obtain ⟨hxrange, hxcond⟩ := Finset.mem_filter.mp hxE'
  obtain ⟨hyrange, hycond⟩ := Finset.mem_filter.mp hyF'
  refine ⟨Finset.mem_range.mp hxrange, Finset.mem_range.mp hyrange, ?_⟩
  rintro rfl
  exact hxcond.1 hycond.1

/-- INTERNAL: `f_j(S) > 0` (the free box is nonempty and every term is positive); a
local copy of `Cellcounting.Analysis.refPhase_fWeight_pos`, which lives in a module
that imports this one. -/
theorem oa_fWeight_pos (I : Instance) (ε δ : ℚ) (j : ℕ) (S : Finset ℕ) :
    0 < fWeight I ε δ j S := by
  unfold fWeight
  refine mul_pos ?_ (Finset.prod_pos fun s _ => by positivity)
  exact Finset.sum_pos (fun z _ => by positivity) ⟨fun _ => 0, by simp [freeBox]⟩

/-- INTERNAL: `C(j) > 0`; a local copy of `Cellcounting.Analysis.refPhase_Cpart_pos`,
which lives in a module that imports this one. -/
theorem oa_Cpart_pos (I : Instance) (ε δ : ℚ) (j : ℕ) : 0 < Cpart I ε δ j :=
  Finset.sum_pos (fun _ _ => Finset.sum_pos (fun _ _ => by positivity)
    ⟨fun _ => 0, by simp [freeBox]⟩) ⟨fun _ => 0, by simp [smallBox]⟩

/-- INTERNAL: good multipliers are nonnegative, so `λ ≥ 0`.
TEXLINE: sections/transport.tex:36-54 -/
theorem oa_refLam_nonneg (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ j w) (S : Finset ℕ) : 0 ≤ refLam I ε δ S j w := by
  unfold refLam
  split
  · rename_i i l hk
    obtain ⟨hi, hl, hil⟩ := oa_kind_defect I ε δ S i l hk
    refine mul_nonneg (oa_fWeight_pos I ε δ j S).le (le_trans ?_ (hgood i hi l hl hil).1)
    exact div_nonneg (oa_Cpart_pos I ε δ j).le (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun S _ => (oa_fWeight_pos I ε δ j S).le))
  · exact (oa_fWeight_pos I ε δ j S).le

/-- INTERNAL: the transversal mass is part of `Λ`, and `Λ ≤ 5 p² C`
(`eq:type-mass-bounds`: each defect type carries multiplied mass at most `4C`).
TEXLINE: sections/transport.tex:55-66 -/
theorem oa_lamTot_bounds (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (j : ℕ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) :
    transMass I ε δ j ≤ refLamTot I ε δ j w ∧
      refLamTot I ε δ j w ≤ 5 * (pSmall I ε δ : ℝ) ^ 2 * transMass I ε δ j := by
  classical
  set p := pSmall I ε δ with hpdef
  have hplt : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp
  constructor
  · unfold transMass refLamTot
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
    exact oa_refLam_nonneg I ε δ j w hgood S
  · set t : Finset Program.Kind :=
      insert Program.Kind.transversal
        ((Finset.range p ×ˢ Finset.range p).image (fun pr => Program.Kind.defect pr.1 pr.2))
      with htdef
    have hmaps : ∀ S ∈ chainStates I ε δ, kind I ε δ S ∈ t := by
      intro S hS
      simp only [chainStates, Finset.mem_filter] at hS
      cases hk : kind I ε δ S with
      | transversal => rw [htdef]; exact Finset.mem_insert_self _ _
      | defect i l =>
        have hb := oa_kind_defect I ε δ S i l hk
        rw [htdef]
        refine Finset.mem_insert_of_mem ?_
        simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range]
        exact ⟨(i, l), ⟨hb.1, hb.2.1⟩, rfl⟩
      | outside => exact absurd hk hS.2
    have hfiber : ∑ k ∈ t, ∑ S ∈ (chainStates I ε δ).filter (fun S => kind I ε δ S = k),
        refLam I ε δ S j w = refLamTot I ε δ j w := by
      unfold refLamTot
      exact Finset.sum_fiberwise_of_maps_to hmaps _
    rw [← hfiber]
    have hnotmem : Program.Kind.transversal ∉
        (Finset.range p ×ˢ Finset.range p).image (fun pr => Program.Kind.defect pr.1 pr.2) := by
      simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range]
      rintro ⟨⟨i, l⟩, -, h⟩
      exact absurd h (by simp)
    rw [htdef, Finset.sum_insert hnotmem]
    have htrans : (chainStates I ε δ).filter (fun S => kind I ε δ S = Program.Kind.transversal) =
        transStates I ε δ := by
      unfold chainStates transStates
      rw [Finset.filter_filter]
      congr 1
      ext S
      constructor
      · rintro ⟨-, h2⟩; exact h2
      · intro h2; exact ⟨by rw [h2]; simp, h2⟩
    have htransval : ∑ S ∈ (chainStates I ε δ).filter
        (fun S => kind I ε δ S = Program.Kind.transversal), refLam I ε δ S j w =
        transMass I ε δ j := by
      rw [htrans]
      unfold transMass
      refine Finset.sum_congr rfl fun S hS => ?_
      simp only [transStates, Finset.mem_filter] at hS
      unfold refLam
      rw [hS.2]
    rw [htransval]
    have hinj : ∀ pr1 ∈ Finset.range p ×ˢ Finset.range p, ∀ pr2 ∈ Finset.range p ×ˢ Finset.range p,
        Program.Kind.defect pr1.1 pr1.2 = Program.Kind.defect pr2.1 pr2.2 → pr1 = pr2 := by
      rintro ⟨i1, l1⟩ - ⟨i2, l2⟩ - h
      simp only [Program.Kind.defect.injEq] at h
      simp [h.1, h.2]
    rw [Finset.sum_image hinj]
    have hterm : ∀ pr ∈ Finset.range p ×ˢ Finset.range p,
        ∑ S ∈ (chainStates I ε δ).filter (fun S => kind I ε δ S = Program.Kind.defect pr.1 pr.2),
          refLam I ε δ S j w ≤ 4 * transMass I ε δ j := by
      rintro ⟨i, l⟩ hpr
      simp only [Finset.mem_product, Finset.mem_range] at hpr
      by_cases hil : i = l
      · have hempty : (chainStates I ε δ).filter
            (fun S => kind I ε δ S = Program.Kind.defect i l) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro S _ hk
          exact (oa_kind_defect I ε δ S i l hk).2.2 hil
        rw [hempty]
        simp only [Finset.sum_empty]
        have := oa_Cpart_pos I ε δ j
        rw [← transMass_eq_Cpart] at this
        linarith
      · have hfilt : (chainStates I ε δ).filter
            (fun S => kind I ε δ S = Program.Kind.defect i l) =
            (refStates I ε δ).filter (fun S => kind I ε δ S = Program.Kind.defect i l) := by
          unfold chainStates
          rw [Finset.filter_filter]
          congr 1
          ext S
          constructor
          · rintro ⟨-, h2⟩; exact h2
          · intro h2; exact ⟨by rw [h2]; simp, h2⟩
        have hval : ∑ S ∈ (chainStates I ε δ).filter
            (fun S => kind I ε δ S = Program.Kind.defect i l), refLam I ε δ S j w =
            (w i l : ℝ) * cDef I ε δ j i l := by
          rw [hfilt]
          unfold cDef
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun S hS => ?_
          simp only [Finset.mem_filter] at hS
          unfold refLam
          rw [hS.2]
          ring
        rw [hval, transMass_eq_Cpart]
        have hcDef0 : 0 ≤ cDef I ε δ j i l := by
          unfold cDef; exact Finset.sum_nonneg fun S _ => (oa_fWeight_pos I ε δ j S).le
        rcases eq_or_lt_of_le hcDef0 with h0 | h0
        · rw [← h0, mul_zero]
          have := oa_Cpart_pos I ε δ j
          linarith
        · exact (le_div_iff₀ h0).mp (hgood i hpr.1 l hpr.2 hil).2
    have hsum_le : ∑ pr ∈ Finset.range p ×ˢ Finset.range p,
          ∑ S ∈ (chainStates I ε δ).filter (fun S => kind I ε δ S = Program.Kind.defect pr.1 pr.2),
            refLam I ε δ S j w ≤ 4 * (p : ℝ) ^ 2 * transMass I ε δ j := by
      calc ∑ pr ∈ Finset.range p ×ˢ Finset.range p,
            ∑ S ∈ (chainStates I ε δ).filter
                (fun S => kind I ε δ S = Program.Kind.defect pr.1 pr.2),
              refLam I ε δ S j w
          ≤ ∑ _pr ∈ Finset.range p ×ˢ Finset.range p, 4 * transMass I ε δ j :=
            Finset.sum_le_sum hterm
        _ = 4 * (p : ℝ) ^ 2 * transMass I ε δ j := by
            rw [Finset.sum_const, Finset.card_product, Finset.card_range]
            ring
    have htm0 : 0 ≤ transMass I ε δ j := by
      rw [transMass_eq_Cpart]; exact (oa_Cpart_pos I ε δ j).le
    have hp1 : (1 : ℝ) ≤ (p : ℝ) ^ 2 := by
      have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hplt
      nlinarith
    nlinarith [hsum_le]

/-- INTERNAL: the type-mass lower bound in the form the union bound needs: a positive
stationary mean among `p_0`, `p_il`, `u` is at least `1/(20p²)`.
TEXLINE: sections/algorithm.tex:318-323 -/
theorem oa_mean_ge (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (j : ℕ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : M ≤ 4 * transMass I ε δ j) (hMC : 0 < M → transMass I ε δ j ≤ 4 * M) :
    0 < M / refLamTot I ε δ j w →
      1 / (20 * (pSmall I ε δ : ℝ) ^ 2) ≤ M / refLamTot I ε δ j w := by
  intro hpos
  set Λ := refLamTot I ε δ j w with hΛdef
  have hMpos : 0 < M := by
    rcases hM0.eq_or_lt with h0 | h0
    · exfalso; rw [← h0] at hpos; simp at hpos
    · exact h0
  have hΛpos : 0 < Λ := by
    by_contra hΛ
    have hΛ' : Λ ≤ 0 := not_lt.mp hΛ
    have : M / Λ ≤ 0 := div_nonpos_of_nonneg_of_nonpos hMpos.le hΛ'
    linarith
  have htm := hMC hMpos
  have hub := (oa_lamTot_bounds I ε δ hp j w hgood).2
  rw [← hΛdef] at hub
  have hple : Λ ≤ 20 * (pSmall I ε δ : ℝ) ^ 2 * M := by
    calc Λ ≤ 5 * (pSmall I ε δ : ℝ) ^ 2 * transMass I ε δ j := hub
      _ ≤ 5 * (pSmall I ε δ : ℝ) ^ 2 * (4 * M) := by
          have hp2 : (0 : ℝ) ≤ 5 * (pSmall I ε δ : ℝ) ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_left htm hp2
      _ = 20 * (pSmall I ε δ : ℝ) ^ 2 * M := by ring
  have hp2pos : (0 : ℝ) < 20 * (pSmall I ε δ : ℝ) ^ 2 := by
    have : (pSmall I ε δ : ℝ) ≠ 0 := by exact_mod_cast hp
    positivity
  rw [div_le_div_iff₀ hp2pos hΛpos]
  linarith

/-- INTERNAL: `Var_π G ≤ E_π G` for an observable with values in `[0, 1]` on `X`.
TEXLINE: sections/algorithm.tex:318-329 -/
theorem oa_var_le_mean (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ j w) (G : Finset ℕ → ℝ)
    (hG : ∀ S ∈ chainStates I ε δ, 0 ≤ G S ∧ G S ≤ 1) :
    refPiVar I ε δ j w G ≤ refPiMean I ε δ j w G := by
  classical
  by_cases hΛ0 : refLamTot I ε δ j w = 0
  · have hpi0 : ∀ S ∈ chainStates I ε δ, refPi I ε δ j w S = 0 := by
      intro S hS
      unfold refPi
      rw [if_pos hS, hΛ0, div_zero]
    unfold refPiVar refPiMean
    rw [Finset.sum_eq_zero (fun S hS => by rw [hpi0 S hS]; ring)]
    rw [Finset.sum_eq_zero (fun S hS => by rw [hpi0 S hS]; ring)]
  · have hΛnonneg : 0 ≤ refLamTot I ε δ j w := by
      unfold refLamTot
      exact Finset.sum_nonneg fun S _ => oa_refLam_nonneg I ε δ j w hgood S
    have hΛpos : 0 < refLamTot I ε δ j w := lt_of_le_of_ne hΛnonneg (Ne.symm hΛ0)
    have hpi_eq : ∀ S ∈ chainStates I ε δ,
        refPi I ε δ j w S = refLam I ε δ S j w / refLamTot I ε δ j w := by
      intro S hS; unfold refPi; rw [if_pos hS]
    set A := ∑ S ∈ chainStates I ε δ, refLam I ε δ S j w * G S with hAdef
    set B := ∑ S ∈ chainStates I ε δ, refLam I ε δ S j w * (G S) ^ 2 with hBdef
    have hΛeq : (∑ S ∈ chainStates I ε δ, refLam I ε δ S j w) = refLamTot I ε δ j w := rfl
    have hterm1 : ∀ S ∈ chainStates I ε δ,
        refPi I ε δ j w S * G S = refLam I ε δ S j w * G S / refLamTot I ε δ j w := by
      intro S hS; rw [hpi_eq S hS, div_mul_eq_mul_div]
    have hmeaneq : refPiMean I ε δ j w G = A / refLamTot I ε δ j w := by
      unfold refPiMean
      rw [Finset.sum_congr rfl hterm1, ← Finset.sum_div]
    have hBleA : B ≤ A := by
      apply Finset.sum_le_sum
      intro S hS
      have hL := oa_refLam_nonneg I ε δ j w hgood S
      have hG1 := (hG S hS).1
      have hG2 := (hG S hS).2
      have hsq : G S ^ 2 ≤ G S := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq hL]
    have hA0 : 0 ≤ A := by
      apply Finset.sum_nonneg
      intro S hS
      exact mul_nonneg (oa_refLam_nonneg I ε δ j w hgood S) (hG S hS).1
    have hCeq : (∑ S ∈ chainStates I ε δ,
        refLam I ε δ S j w * (G S - A / refLamTot I ε δ j w) ^ 2) =
        B - A ^ 2 / refLamTot I ε δ j w := by
      have expand : ∀ S ∈ chainStates I ε δ,
          refLam I ε δ S j w * (G S - A / refLamTot I ε δ j w) ^ 2 =
            (refLam I ε δ S j w * (G S) ^ 2 -
                2 * (A / refLamTot I ε δ j w) * (refLam I ε δ S j w * G S)) +
              (A / refLamTot I ε δ j w) ^ 2 * refLam I ε δ S j w := by
        intro S hS; ring
      rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← hAdef, ← hBdef, hΛeq]
      field_simp
      ring
    have hterm2 : ∀ S ∈ chainStates I ε δ,
        refPi I ε δ j w S * (G S - refPiMean I ε δ j w G) ^ 2 =
          refLam I ε δ S j w * (G S - A / refLamTot I ε δ j w) ^ 2 / refLamTot I ε δ j w := by
      intro S hS
      rw [hpi_eq S hS, hmeaneq, div_mul_eq_mul_div]
    have hvareq : refPiVar I ε δ j w G =
        (∑ S ∈ chainStates I ε δ,
          refLam I ε δ S j w * (G S - A / refLamTot I ε δ j w) ^ 2) / refLamTot I ε δ j w := by
      unfold refPiVar
      rw [Finset.sum_congr rfl hterm2, ← Finset.sum_div]
    rw [hvareq, hCeq, hmeaneq]
    have hstep : B - A ^ 2 / refLamTot I ε δ j w ≤ B := by
      have : 0 ≤ A ^ 2 / refLamTot I ε δ j w := div_nonneg (sq_nonneg A) hΛnonneg
      linarith
    exact div_le_div_of_nonneg_right (le_trans hstep hBleA) hΛnonneg

/-- INTERNAL: Markov's inequality for a squared deviation, `t ≥ 0` allowed.
TEXLINE: sections/algorithm.tex:332-340 -/
theorem oa_markov_sq {α : Type} (μ : PMF α) (f : α → ℝ) (c t : ℝ) :
    μ.toOuterMeasure {a | ¬ |f a - c| ≤ t} ≤
      pexp μ (fun a => ENNReal.ofReal ((f a - c) ^ 2)) * (ENNReal.ofReal (t ^ 2))⁻¹ := by
  -- DISPROVED: Cellcounting.Analysis.oa_markov_sq_false
  -- REPAIR: (ht : 0 ≤ t)
  sorry

/-- INTERNAL: `oa_markov_sq` repaired with the sign hypothesis `0 ≤ t` its proof
actually needs (see `Cellcounting.Analysis.oa_markov_sq_false`): without it, a
threshold `t < 0` makes the bad event the whole space while the right side can be
`0`. Used in place of `oa_markov_sq` below.
TEXLINE: sections/algorithm.tex:332-340 -/
theorem oa_markov_sq_nonneg {α : Type} (μ : PMF α) (f : α → ℝ) (c t : ℝ) (ht : 0 ≤ t) :
    μ.toOuterMeasure {a | ¬ |f a - c| ≤ t} ≤
      pexp μ (fun a => ENNReal.ofReal ((f a - c) ^ 2)) * (ENNReal.ofReal (t ^ 2))⁻¹ := by
  rw [outer_eq_pexp]
  have hpt : ∀ a, ({a | ¬ |f a - c| ≤ t}.indicator 1) a ≤
      ENNReal.ofReal ((f a - c) ^ 2) * (ENNReal.ofReal (t ^ 2))⁻¹ := by
    intro a
    by_cases ha : a ∈ {a | ¬ |f a - c| ≤ t}
    · rw [Set.indicator_of_mem ha]
      simp only [Set.mem_setOf_eq, not_le] at ha
      have h1 : t ^ 2 ≤ (f a - c) ^ 2 := by nlinarith [abs_nonneg (f a - c), sq_abs (f a - c)]
      have hne0 : ENNReal.ofReal ((f a - c) ^ 2) ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        nlinarith [abs_nonneg (f a - c), sq_abs (f a - c)]
      rw [Pi.one_apply, ← div_eq_mul_inv,
        ENNReal.le_div_iff_mul_le (Or.inr hne0) (Or.inl ENNReal.ofReal_ne_top), one_mul]
      exact ENNReal.ofReal_le_ofReal h1
    · rw [Set.indicator_of_notMem ha]; exact zero_le
  calc pexp μ _ ≤ pexp μ (fun a => ENNReal.ofReal ((f a - c) ^ 2) * (ENNReal.ofReal (t ^ 2))⁻¹) :=
        pexp_mono μ hpt
    _ = pexp μ (fun a => ENNReal.ofReal ((f a - c) ^ 2)) * (ENNReal.ofReal (t ^ 2))⁻¹ := by
        rw [pexp, pexp, ← ENNReal.tsum_mul_right]; congr 1; funext a; ring

/-- INTERNAL: `π ≥ 0` pointwise (zero off `X`, a nonneg ratio of nonneg `λ`-masses on `X`). -/
theorem oa_refPi_nonneg (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ j w) (S : Finset ℕ) : 0 ≤ refPi I ε δ j w S := by
  unfold refPi
  split
  · exact div_nonneg (oa_refLam_nonneg I ε δ j w hgood S)
      (Finset.sum_nonneg fun S _ => oa_refLam_nonneg I ε δ j w hgood S)
  · exact le_refl 0

/-- INTERNAL: `Var_π G ≥ 0`, a sum of nonneg `π`-weighted squares. -/
theorem oa_refPiVar_nonneg (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ j w) (G : Finset ℕ → ℝ) :
    0 ≤ refPiVar I ε δ j w G := by
  unfold refPiVar
  exact Finset.sum_nonneg fun S _ => mul_nonneg (oa_refPi_nonneg I ε δ j w hgood S) (sq_nonneg _)

/-- INTERNAL: `E_π G ≥ 0` for `G ≥ 0` on `X`. -/
theorem oa_refPiMean_nonneg (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ j w) (G : Finset ℕ → ℝ)
    (hG : ∀ S ∈ chainStates I ε δ, 0 ≤ G S ∧ G S ≤ 1) :
    0 ≤ refPiMean I ε δ j w G := by
  unfold refPiMean
  exact Finset.sum_nonneg fun S hS =>
    mul_nonneg (oa_refPi_nonneg I ε δ j w hgood S) (hG S hS).1

/-- INTERNAL: `μ_j ≤ 5p² π` pointwise (`C(j) ≤ Λ ≤ 5p² C(j)`, `oa_lamTot_bounds`). -/
theorem oa_mu_le_pi (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (j : ℕ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) (S : Finset ℕ) :
    refMu I ε δ j S ≤ 5 * (pSmall I ε δ : ℝ) ^ 2 * refPi I ε δ j w S := by
  unfold refMu
  split
  · rename_i hS
    have hsub : S ∈ chainStates I ε δ := by
      simp only [transStates, chainStates, Finset.mem_filter] at hS ⊢
      exact ⟨hS.1, by rw [hS.2]; simp⟩
    have hrefPi : refPi I ε δ j w S = fWeight I ε δ j S / refLamTot I ε δ j w := by
      unfold refPi
      rw [if_pos hsub]
      congr 1
      simp only [transStates, Finset.mem_filter] at hS
      unfold refLam
      rw [hS.2]
    rw [hrefPi]
    have htm_pos : 0 < transMass I ε δ j := by
      rw [transMass_eq_Cpart]; exact oa_Cpart_pos I ε δ j
    have hlam_bounds := oa_lamTot_bounds I ε δ hp j w hgood
    have hlamtot_pos : 0 < refLamTot I ε δ j w := lt_of_lt_of_le htm_pos hlam_bounds.1
    rw [mul_div_assoc', div_le_div_iff₀ htm_pos hlamtot_pos]
    have hfw0 : 0 ≤ fWeight I ε δ j S := (oa_fWeight_pos I ε δ j S).le
    calc fWeight I ε δ j S * refLamTot I ε δ j w ≤
          fWeight I ε δ j S * (5 * (pSmall I ε δ : ℝ) ^ 2 * transMass I ε δ j) :=
          mul_le_mul_of_nonneg_left hlam_bounds.2 hfw0
      _ = 5 * (pSmall I ε δ : ℝ) ^ 2 * fWeight I ε δ j S * transMass I ε δ j := by ring
  · exact mul_nonneg (by positivity) (oa_refPi_nonneg I ε δ j w hgood S)


/-- INTERNAL: one observable of one observation trajectory (`eq:alg-empirical-probability`
before the union bound): from `ν ≤ 10 p² π`, an observable `G` fixed by `Q` with values
in `[0, 1]` on `X` and stationary mean `m` (zero or at least `1/(20p²)`) has
relative error above `η` with probability at most `400 p⁴ K_obs / (N_av η²)`.
TEXLINE: sections/algorithm.tex:323-340 -/
theorem oa_obs_fail_le (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) (G : Finset ℕ → ℝ)
    (hQ : ∀ S S' i l, kind I ε δ S = .defect i l → kind I ε δ S' = .defect i l → G S = G S')
    (hG : ∀ S ∈ chainStates I ε δ, 0 ≤ G S ∧ G S ≤ 1)
    (hmean : 0 < refPiMean I ε δ j w G →
      1 / (20 * (pSmall I ε δ : ℝ) ^ 2) ≤ refPiMean I ε δ j w G)
    (ν : PMF (Finset ℕ))
    (hν : ∀ S, ν S ≤ ENNReal.ofReal (10 * (pSmall I ε δ : ℝ) ^ 2 * refPi I ε δ j w S)) :
    (ν.bind (refTraj I ε δ j w G (NavParam I ε δ))).toOuterMeasure
        {x | ¬ |x.2 / NavParam I ε δ - refPiMean I ε δ j w G| ≤
          (ηParam I ε δ : ℝ) * refPiMean I ε δ j w G} ≤
      ENNReal.ofReal (400 * (pSmall I ε δ : ℝ) ^ 4 * KobsParam I ε δ /
        (NavParam I ε δ * (ηParam I ε δ : ℝ) ^ 2)) := by
  set p := (pSmall I ε δ : ℝ) with hpdef
  set mean := refPiMean I ε δ j w G with hmeandef
  set N := (NavParam I ε δ : ℝ) with hNdef
  set η := (ηParam I ε δ : ℝ) with hηdef
  have hvarmean : refPiVar I ε δ j w G ≤ mean := oa_var_le_mean I ε δ j w hgood G hG
  have hvar0 : 0 ≤ refPiVar I ε δ j w G := oa_refPiVar_nonneg I ε δ j w hgood G
  have hηParampos : 0 < ηParam I ε δ := by
    unfold ηParam
    refine div_pos hε ?_
    have h200 : 0 < 200 * (HParam I ε δ + 1) := by omega
    exact_mod_cast h200
  have hηpos : 0 < η := by rw [hηdef]; exact_mod_cast hηParampos
  have hNav1 : 1 ≤ NavParam I ε δ := by
    rw [NavParam, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Nat.ceil_pos]
    have hp1 : 1 ≤ pSmall I ε δ := Nat.one_le_iff_ne_zero.mpr hp
    have hCd : 1 ≤ CdParam I ε δ := by unfold CdParam; omega
    have hKobs1 : 1 ≤ KobsParam I ε δ := by
      unfold KobsParam
      have hp4 : 1 ≤ pSmall I ε δ ^ 4 := Nat.one_le_pow _ _ hp1
      have hCd' : 1 ≤ 9 * CpParam I ε δ + 2 * CdParam I ε δ := by omega
      calc (1:ℕ) = 1 * 1 := by ring
        _ ≤ 10 * pSmall I ε δ ^ 4 * (9 * CpParam I ε δ + 2 * CdParam I ε δ) := by
            gcongr
            omega
    have hnum_pos : (0 : ℚ) <
        ((100000000 * pSmall I ε δ ^ 8 * KobsParam I ε δ * (HParam I ε δ + 1) : ℕ) : ℚ) := by
      have : 1 ≤ 100000000 * pSmall I ε δ ^ 8 * KobsParam I ε δ * (HParam I ε δ + 1) := by
        have hp8 : 1 ≤ pSmall I ε δ ^ 8 := Nat.one_le_pow _ _ hp1
        have hH1 : 1 ≤ HParam I ε δ + 1 := by omega
        calc (1:ℕ) = 1 * 1 * 1 * 1 := by ring
          _ ≤ 100000000 * pSmall I ε δ ^ 8 * KobsParam I ε δ * (HParam I ε δ + 1) := by
              gcongr
              omega
      exact_mod_cast this
    exact div_pos hnum_pos (pow_pos hηParampos 2)
  have hNpos : (0:ℝ) < N := by rw [hNdef]; exact_mod_cast hNav1
  have hp0 : 0 ≤ p := by rw [hpdef]; exact_mod_cast Nat.zero_le _
  have hKobs0 : (0:ℝ) ≤ (KobsParam I ε δ : ℝ) := by exact_mod_cast Nat.zero_le _
  have hmean0 : 0 ≤ mean := oa_refPiMean_nonneg I ε δ j w hgood G hG
  have hvar_le : refPiVar I ε δ j w G ≤ 20 * p ^ 2 * mean ^ 2 := by
    rcases hmean0.eq_or_lt with h0 | h0
    · rw [← h0]; simp; linarith [hvarmean, h0]
    · have hme := hmean h0
      have h20p2 : (0:ℝ) < 20 * p ^ 2 := by
        have : p ≠ 0 := by rw [hpdef]; exact_mod_cast hp
        positivity
      have : mean ≤ 20 * p ^ 2 * mean ^ 2 := by
        have hstep : 1 ≤ 20 * p ^ 2 * mean := by
          have := (div_le_iff₀ h20p2).mp hme
          linarith [this]
        nlinarith [h0.le]
      linarith [hvarmean]
  have htavg := time_average hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj w hgood G hQ
    (10 * p ^ 2) ν hν (NavParam I ε δ) hNav1
  have hmarkov := oa_markov_sq_nonneg (ν.bind (refTraj I ε δ j w G (NavParam I ε δ)))
    (fun x => x.2 / N) mean (η * mean) (mul_nonneg hηpos.le hmean0)
  refine hmarkov.trans ?_
  have htavg' : pexp (ν.bind (refTraj I ε δ j w G (NavParam I ε δ)))
      (fun a => ENNReal.ofReal ((a.2 / N - mean) ^ 2)) ≤
      ENNReal.ofReal (20 * p ^ 2 * (KobsParam I ε δ : ℝ) * refPiVar I ε δ j w G / N) := by
    have heq : (2 * (10 * p ^ 2) * (KobsParam I ε δ : ℝ) * refPiVar I ε δ j w G /
        (NavParam I ε δ : ℝ)) =
        (20 * p ^ 2 * (KobsParam I ε δ : ℝ) * refPiVar I ε δ j w G / N) := by
      rw [hNdef]; ring
    rw [heq, ← hmeandef, ← hNdef] at htavg
    exact htavg
  refine le_trans (mul_le_mul_left htavg' _) ?_
  rcases hmean0.eq_or_lt with h0 | h0
  · have hvar0' : refPiVar I ε δ j w G = 0 := le_antisymm (by rw [← h0] at hvarmean; linarith) hvar0
    rw [hvar0', ← h0]
    simp
  · have hηm2pos : (0:ℝ) < (η * mean) ^ 2 := pow_pos (mul_pos hηpos h0) 2
    have hfrac_nonneg : (0:ℝ) ≤ 20 * p ^ 2 * (KobsParam I ε δ : ℝ) * refPiVar I ε δ j w G / N :=
      div_nonneg (mul_nonneg (mul_nonneg (by positivity) hKobs0) hvar0) hNpos.le
    rw [← ENNReal.ofReal_inv_of_pos hηm2pos, ← ENNReal.ofReal_mul hfrac_nonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    have hp2nonneg : (0:ℝ) ≤ p ^ 2 := sq_nonneg p
    have hNη2pos : (0:ℝ) < N * η ^ 2 := mul_pos hNpos (by positivity)
    rw [← div_eq_mul_inv, div_div,
      div_le_div_iff₀ (mul_pos hNpos hηm2pos) hNη2pos]
    have key : 20 * p ^ 2 * (KobsParam I ε δ : ℝ) * refPiVar I ε δ j w G * η ^ 2 ≤
        400 * p ^ 4 * (KobsParam I ε δ : ℝ) * ((η * mean) ^ 2) := by
      have hmul : refPiVar I ε δ j w G * η ^ 2 ≤ (20 * p ^ 2 * mean ^ 2) * η ^ 2 :=
        mul_le_mul_of_nonneg_right hvar_le (sq_nonneg η)
      calc 20 * p ^ 2 * (KobsParam I ε δ : ℝ) * refPiVar I ε δ j w G * η ^ 2
          = 20 * p ^ 2 * (KobsParam I ε δ : ℝ) * (refPiVar I ε δ j w G * η ^ 2) := by ring
        _ ≤ 20 * p ^ 2 * (KobsParam I ε δ : ℝ) * ((20 * p ^ 2 * mean ^ 2) * η ^ 2) := by
            have h0' : (0:ℝ) ≤ 20 * p ^ 2 * (KobsParam I ε δ : ℝ) :=
              mul_nonneg (by positivity) hKobs0
            exact mul_le_mul_of_nonneg_left hmul h0'
        _ = 400 * p ^ 4 * (KobsParam I ε δ : ℝ) * ((η * mean) ^ 2) := by ring
    calc 20 * p ^ 2 * (KobsParam I ε δ : ℝ) * refPiVar I ε δ j w G * (N * η ^ 2)
        = (20 * p ^ 2 * (KobsParam I ε δ : ℝ) * refPiVar I ε δ j w G * η ^ 2) * N := by ring
      _ ≤ (400 * p ^ 4 * (KobsParam I ε δ : ℝ) * ((η * mean) ^ 2)) * N := by
          exact mul_le_mul_of_nonneg_right key hNpos.le
      _ = 400 * p ^ 4 * (KobsParam I ε δ : ℝ) * (N * (η * mean) ^ 2) := by ring

/-- INTERNAL: one observable of the implemented observation trajectory, parametrized
over the tally `T` it accumulates and the target mean `M/Λ` it compares to: the
`oa_obs_fail_le` bound, transported from `refTraj` to `refObserve` via
`oa_refObserve_map`, and from `2 μ_j`-domination to `10 p² π`-domination via
`oa_mu_le_pi`. Used for `n0`, each `n_{il}`, and `sumG` in `observe_accurate`. -/
theorem oa_single_fail (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w)
    (G : Finset ℕ → ℝ) (T : RefObs → ℝ)
    (hT : ∀ o S', T (refObserveState I ε δ j { o with S := S' }) = T o + G S')
    (hT0 : ∀ S0, T ⟨S0, 0, fun _ _ => 0, 0⟩ = 0)
    (hQ : ∀ S S' i l, kind I ε δ S = .defect i l → kind I ε δ S' = .defect i l → G S = G S')
    (hG : ∀ S ∈ chainStates I ε δ, 0 ≤ G S ∧ G S ≤ 1)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : M ≤ 4 * transMass I ε δ j)
    (hMC : 0 < M → transMass I ε δ j ≤ 4 * M)
    (hMeq : refPiMean I ε δ j w G = M / refLamTot I ε δ j w)
    (ν : PMF (Finset ℕ)) (hν : ∀ S, ν S ≤ 2 * ENNReal.ofReal (refMu I ε δ j S)) :
    (ν.bind (refObserve I ε δ j w)).toOuterMeasure
        {o | ¬ |T o / NavParam I ε δ - M / refLamTot I ε δ j w| ≤
          (ηParam I ε δ : ℝ) * (M / refLamTot I ε δ j w)} ≤
      ENNReal.ofReal (400 * (pSmall I ε δ : ℝ) ^ 4 * KobsParam I ε δ /
        (NavParam I ε δ * (ηParam I ε δ : ℝ) ^ 2)) := by
  have hmean : 0 < refPiMean I ε δ j w G → 1 / (20 * (pSmall I ε δ : ℝ) ^ 2) ≤
      refPiMean I ε δ j w G := by
    rw [hMeq]; exact oa_mean_ge I ε δ hp j w hgood M hM0 hM hMC
  have hνpi : ∀ S, ν S ≤ ENNReal.ofReal (10 * (pSmall I ε δ : ℝ) ^ 2 * refPi I ε δ j w S) := by
    intro S
    refine le_trans (hν S) ?_
    rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := oa_mu_le_pi I ε δ hp j w hgood S
    linarith
  have hfail := oa_obs_fail_le hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj w hgood G hQ hG
    hmean ν hνpi
  set ψ : RefObs → Finset ℕ × ℝ := fun o => (o.S, T o) with hψdef
  have hmapeq : (ν.bind (refObserve I ε δ j w)).map ψ =
      ν.bind (refTraj I ε δ j w G (NavParam I ε δ)) := by
    rw [PMF.map_bind]
    congr 1
    funext S0
    exact oa_refObserve_map I ε δ j w G T hT hT0 S0
  have hset : {o : RefObs | ¬ |T o / NavParam I ε δ - refPiMean I ε δ j w G| ≤
      (ηParam I ε δ : ℝ) * refPiMean I ε δ j w G} =
      ψ ⁻¹' {x : Finset ℕ × ℝ | ¬ |x.2 / NavParam I ε δ - refPiMean I ε δ j w G| ≤
        (ηParam I ε δ : ℝ) * refPiMean I ε δ j w G} := rfl
  have hswap : (ν.bind (refObserve I ε δ j w)).toOuterMeasure
      {o | ¬ |T o / NavParam I ε δ - M / refLamTot I ε δ j w| ≤
        (ηParam I ε δ : ℝ) * (M / refLamTot I ε δ j w)} =
      (ν.bind (refTraj I ε δ j w G (NavParam I ε δ))).toOuterMeasure
        {x : Finset ℕ × ℝ | ¬ |x.2 / NavParam I ε δ - refPiMean I ε δ j w G| ≤
          (ηParam I ε δ : ℝ) * refPiMean I ε δ j w G} := by
    rw [← hMeq, hset, ← hmapeq, PMF.toOuterMeasure_map_apply]
  rw [hswap]
  exact hfail

/-- INTERNAL: `h_j(x, y) > 0` (the free box is nonempty and every term is positive). -/
theorem oa_hWeight_pos (I : Instance) (ε δ : ℚ) (j : ℕ) (x y : ℕ → ℕ) :
    0 < hWeight I ε δ j x y := by
  unfold hWeight
  exact Finset.sum_pos (fun z _ => by positivity) ⟨fun _ => 0, by simp [freeBox]⟩

open Classical in
/-- INTERNAL: the type-0 indicator, observed as `n0` (`eq:alg-observable-identities`). -/
noncomputable def obsG0 (I : Instance) (ε δ : ℚ) (S : Finset ℕ) : ℝ :=
  if kind I ε δ S = Program.Kind.transversal then 1 else 0

open Classical in
/-- INTERNAL: `G_j`, observed as `sumG` only at transversals (`algorithm.tex:150-156`). -/
noncomputable def obsGC (I : Instance) (ε δ : ℚ) (j : ℕ) (S : Finset ℕ) : ℝ :=
  if kind I ε δ S = Program.Kind.transversal then
    hWeight I ε δ (j + 1) (profile I ε δ S).1 (profile I ε δ S).2 /
      hWeight I ε δ j (profile I ε δ S).1 (profile I ε δ S).2
  else 0

open Classical in
/-- INTERNAL: the type-`(i, l)` indicator, observed as `n_{il}`. -/
noncomputable def obsGil (I : Instance) (ε δ : ℚ) (i l : ℕ) (S : Finset ℕ) : ℝ :=
  if kind I ε δ S = Program.Kind.defect i l then 1 else 0

/-- INTERNAL: the implemented tally of `n0` telescopes the type-0 indicator. -/
theorem oa_obsG0_hT (I : Instance) (ε δ : ℚ) (j : ℕ) (o : RefObs) (S' : Finset ℕ) :
    ((refObserveState I ε δ j { o with S := S' }).n0 : ℝ) =
      (o.n0 : ℝ) + obsG0 I ε δ S' := by
  classical
  unfold refObserveState obsG0
  cases kind I ε δ S' with
  | transversal => simp
  | defect i l => simp
  | outside => simp

/-- INTERNAL: `refPiMean` of the type-0 indicator is `C(j)/Λ`. -/
theorem oa_obsG0_mean (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ) :
    refPiMean I ε δ j w (obsG0 I ε δ) = transMass I ε δ j / refLamTot I ε δ j w := by
  classical
  unfold refPiMean
  have hswap : ∀ S, refPi I ε δ j w S * obsG0 I ε δ S =
      if kind I ε δ S = Program.Kind.transversal then refPi I ε δ j w S else 0 := by
    intro S; unfold obsG0; split <;> ring
  rw [Finset.sum_congr rfl fun S _ => hswap S, ← Finset.sum_filter]
  have htrans : (chainStates I ε δ).filter
      (fun S => kind I ε δ S = Program.Kind.transversal) = transStates I ε δ := by
    unfold chainStates transStates
    rw [Finset.filter_filter]
    congr 1
    ext S
    constructor
    · rintro ⟨-, h2⟩; exact h2
    · intro h2; exact ⟨by rw [h2]; simp, h2⟩
  rw [htrans]
  unfold transMass
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun S hS => ?_
  simp only [transStates, Finset.mem_filter] at hS
  unfold refPi
  have hsub : S ∈ chainStates I ε δ := by
    simp only [transStates, chainStates, Finset.mem_filter]
    exact ⟨hS.1, by rw [hS.2]; simp⟩
  rw [if_pos hsub]
  congr 1
  unfold refLam
  rw [hS.2]

/-- INTERNAL: the implemented tally of `sumG` telescopes `G_j`. -/
theorem oa_obsGC_hT (I : Instance) (ε δ : ℚ) (j : ℕ) (o : RefObs) (S' : Finset ℕ) :
    (refObserveState I ε δ j { o with S := S' }).sumG = o.sumG + obsGC I ε δ j S' := by
  classical
  unfold refObserveState obsGC
  cases kind I ε δ S' with
  | transversal => simp
  | defect i l => simp
  | outside => simp

/-- INTERNAL: `G_j ∈ [0, 1]` (`eq:alg-adjacent`, `hWeight_adjacent`). -/
theorem oa_obsGC_range (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (hfeas : feasible I) (j : ℕ)
    (S : Finset ℕ) : 0 ≤ obsGC I ε δ j S ∧ obsGC I ε δ j S ≤ 1 := by
  classical
  unfold obsGC
  split
  · have hxy := profile_le_smallB I ε δ S
    have hadj := hWeight_adjacent I ε δ hε hfeas j (profile I ε δ S).1 (profile I ε δ S).2 hxy
    have hpos := oa_hWeight_pos I ε δ j (profile I ε δ S).1 (profile I ε δ S).2
    have hpos1 := oa_hWeight_pos I ε δ (j + 1) (profile I ε δ S).1 (profile I ε δ S).2
    exact ⟨div_nonneg hpos1.le hpos.le, (div_le_one hpos).2 hadj.2⟩
  · norm_num

/-- INTERNAL: `refPiMean` of `G_j` is `C(j + 1)/Λ`. -/
theorem oa_obsGC_mean (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ) :
    refPiMean I ε δ j w (obsGC I ε δ j) = transMass I ε δ (j + 1) / refLamTot I ε δ j w := by
  classical
  unfold refPiMean
  have htrans : (chainStates I ε δ).filter
      (fun S => kind I ε δ S = Program.Kind.transversal) = transStates I ε δ := by
    unfold chainStates transStates
    rw [Finset.filter_filter]
    congr 1
    ext S
    constructor
    · rintro ⟨-, h2⟩; exact h2
    · intro h2; exact ⟨by rw [h2]; simp, h2⟩
  have hswap : ∀ S ∈ chainStates I ε δ, refPi I ε δ j w S * obsGC I ε δ j S =
      if kind I ε δ S = Program.Kind.transversal then
        fWeight I ε δ (j + 1) S / refLamTot I ε δ j w
      else 0 := by
    intro S hS
    have hrefPi : refPi I ε δ j w S = refLam I ε δ S j w / refLamTot I ε δ j w := by
      unfold refPi; rw [if_pos hS]
    unfold obsGC
    split
    · rename_i hk
      rw [hrefPi]
      have hrl : refLam I ε δ S j w = fWeight I ε δ j S := by unfold refLam; rw [hk]
      rw [hrl]
      have hpos := oa_hWeight_pos I ε δ j (profile I ε δ S).1 (profile I ε δ S).2
      have hfwj : fWeight I ε δ j S =
          hWeight I ε δ j (profile I ε δ S).1 (profile I ε δ S).2 *
            ∏ s ∈ Finset.range (nSmall I ε δ),
              (((profile I ε δ S).1 s).factorial : ℝ) * (((profile I ε δ S).2 s).factorial : ℝ) /
                ((smallB I ε δ s).factorial : ℝ) := rfl
      have hfwj1 : fWeight I ε δ (j + 1) S =
          hWeight I ε δ (j + 1) (profile I ε δ S).1 (profile I ε δ S).2 *
            ∏ s ∈ Finset.range (nSmall I ε δ),
              (((profile I ε δ S).1 s).factorial : ℝ) * (((profile I ε δ S).2 s).factorial : ℝ) /
                ((smallB I ε δ s).factorial : ℝ) := rfl
      rw [hfwj1, hfwj]
      field_simp
    · ring
  rw [Finset.sum_congr rfl hswap, ← Finset.sum_filter, htrans]
  unfold transMass
  rw [Finset.sum_div]

/-- INTERNAL: the implemented tally of `n_{il}` telescopes the type-`(i, l)` indicator. -/
theorem oa_obsGil_hT (I : Instance) (ε δ : ℚ) (j : ℕ) (i l : ℕ) (o : RefObs) (S' : Finset ℕ) :
    ((refObserveState I ε δ j { o with S := S' }).nT i l : ℝ) =
      (o.nT i l : ℝ) + obsGil I ε δ i l S' := by
  classical
  unfold refObserveState obsGil
  cases hk : kind I ε δ S' with
  | transversal => simp
  | defect i' l' =>
    by_cases hil : i' = i ∧ l' = l
    · obtain ⟨rfl, rfl⟩ := hil
      simp
    · have hne : ¬ (Program.Kind.defect i' l' = Program.Kind.defect i l) := by
        simp only [Program.Kind.defect.injEq]; tauto
      have hne' : ¬ (i = i' ∧ l = l') := by tauto
      simp [hne, hne']
  | outside => simp

/-- INTERNAL: `G_{il}` is constant on each defect type (trivially, from `kind`). -/
theorem oa_obsGil_hQ (I : Instance) (ε δ : ℚ) (i l : ℕ) (S S' : Finset ℕ) (i' l' : ℕ)
    (h1 : kind I ε δ S = Program.Kind.defect i' l')
    (h2 : kind I ε δ S' = Program.Kind.defect i' l') :
    obsGil I ε δ i l S = obsGil I ε δ i l S' := by
  classical
  unfold obsGil; rw [h1, h2]

/-- INTERNAL: `w_{il} c_{il}(j)` satisfies the bounds `oa_mean_ge` and `oa_single_fail` need. -/
theorem oa_obsGil_M (I : Instance) (ε δ : ℚ) (j i l : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ j w) (hi : i < pSmall I ε δ) (hl : l < pSmall I ε δ) (hil : i ≠ l) :
    0 ≤ (w i l : ℝ) * cDef I ε δ j i l ∧
      (w i l : ℝ) * cDef I ε δ j i l ≤ 4 * transMass I ε δ j ∧
      (0 < (w i l : ℝ) * cDef I ε δ j i l →
        transMass I ε δ j ≤ 4 * ((w i l : ℝ) * cDef I ε δ j i l)) := by
  have hcDef0 : (0 : ℝ) ≤ cDef I ε δ j i l := by
    unfold cDef; exact Finset.sum_nonneg fun S _ => (oa_fWeight_pos I ε δ j S).le
  have htm0 : (0 : ℝ) ≤ transMass I ε δ j := by
    rw [transMass_eq_Cpart]; exact (oa_Cpart_pos I ε δ j).le
  rcases eq_or_lt_of_le hcDef0 with h0 | h0
  · refine ⟨by rw [← h0]; simp, by rw [← h0]; simp; linarith, ?_⟩
    rw [← h0]; simp
  · have hwil0 : (0 : ℝ) ≤ (w i l : ℝ) := by
      have hb := (hgood i hi l hl hil).1
      have hcpart0 : (0 : ℝ) ≤ Cpart I ε δ j := (oa_Cpart_pos I ε δ j).le
      calc (0 : ℝ) ≤ Cpart I ε δ j / (4 * cDef I ε δ j i l) := by positivity
        _ ≤ (w i l : ℝ) := hb
    refine ⟨mul_nonneg hwil0 hcDef0, ?_, ?_⟩
    · have := (le_div_iff₀ h0).mp (hgood i hi l hl hil).2
      rw [transMass_eq_Cpart]; linarith
    · intro _
      have := (hgood i hi l hl hil).1
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * cDef I ε δ j i l)] at this
      rw [transMass_eq_Cpart]; linarith

/-- INTERNAL: `refPiMean` of `G_{il}` is `w_{il} c_{il}(j)/Λ`. -/
theorem oa_obsGil_mean (I : Instance) (ε δ : ℚ) (j i l : ℕ) (w : ℕ → ℕ → ℚ) :
    refPiMean I ε δ j w (obsGil I ε δ i l) =
      (w i l : ℝ) * cDef I ε δ j i l / refLamTot I ε δ j w := by
  classical
  unfold refPiMean
  have hswap : ∀ S ∈ chainStates I ε δ, refPi I ε δ j w S * obsGil I ε δ i l S =
      if kind I ε δ S = Program.Kind.defect i l then
        (w i l : ℝ) * fWeight I ε δ j S / refLamTot I ε δ j w
      else 0 := by
    intro S hS
    have hrefPi : refPi I ε δ j w S = refLam I ε δ S j w / refLamTot I ε δ j w := by
      unfold refPi; rw [if_pos hS]
    unfold obsGil
    split
    · rename_i hk
      rw [hrefPi]
      have hrl : refLam I ε δ S j w = fWeight I ε δ j S * (w i l : ℝ) := by
        unfold refLam; rw [hk]
      rw [hrl]; ring
    · ring
  rw [Finset.sum_congr rfl hswap, ← Finset.sum_filter]
  have hfilt : (chainStates I ε δ).filter (fun S => kind I ε δ S = Program.Kind.defect i l) =
      (refStates I ε δ).filter (fun S => kind I ε δ S = Program.Kind.defect i l) := by
    unfold chainStates
    rw [Finset.filter_filter]
    congr 1
    ext S
    constructor
    · rintro ⟨-, h2⟩; exact h2
    · intro h2; exact ⟨by rw [h2]; simp, h2⟩
  rw [hfilt]
  unfold cDef
  rw [Finset.mul_sum, Finset.sum_div]

/-- INTERNAL: `C(j + 1) ≤ C(j) ≤ 2 C(j + 1)` (`eq:alg-adjacent`, summing `fWeight_adjacent`
over transversals); a local copy of `Cellcounting.Analysis.refPhase_Cpart_adj`'s transMass
form, which lives in a module that imports this one. -/
theorem oa_transMass_adjacent (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (hfeas : feasible I)
    (j : ℕ) : transMass I ε δ (j + 1) ≤ transMass I ε δ j ∧
      transMass I ε δ j ≤ 2 * transMass I ε δ (j + 1) := by
  classical
  unfold transMass
  have hS : ∀ S ∈ transStates I ε δ, S ∈ refStates I ε δ := fun S hS => (Finset.mem_filter.1 hS).1
  constructor
  · exact Finset.sum_le_sum fun S hS' => (fWeight_adjacent I ε δ hε hfeas j S (hS S hS')).2
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun S hS' => ?_
    have := (fWeight_adjacent I ε δ hε hfeas j S (hS S hS')).1
    linarith

/-- INTERNAL: the number of ordered pairs of distinct labels below `p` is `p(p - 1)`. -/
theorem oa_defectPairs_card (p : ℕ) :
    ((Finset.range p ×ˢ Finset.range p).filter (fun pr : ℕ × ℕ => pr.1 ≠ pr.2)).card =
      p * p - p := by
  have h1 : (Finset.range p ×ˢ Finset.range p).filter (fun pr : ℕ × ℕ => pr.1 ≠ pr.2) =
      (Finset.range p ×ˢ Finset.range p) \
        (Finset.range p ×ˢ Finset.range p).filter (fun pr : ℕ × ℕ => pr.1 = pr.2) := by
    rw [Finset.filter_not]
  rw [h1, Finset.card_sdiff]
  have hsub : (Finset.range p ×ˢ Finset.range p).filter (fun pr : ℕ × ℕ => pr.1 = pr.2) ⊆
      Finset.range p ×ˢ Finset.range p := Finset.filter_subset _ _
  rw [Finset.inter_eq_left.mpr hsub]
  have h2 : (Finset.range p ×ˢ Finset.range p).filter (fun pr : ℕ × ℕ => pr.1 = pr.2) =
      (Finset.range p).image (fun i => (i, i)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, rfl⟩
    · rintro ⟨i, hi, hiq⟩
      obtain rfl : i = a := (Prod.mk.injEq .. ▸ hiq).1
      obtain rfl : i = b := (Prod.mk.injEq .. ▸ hiq).2
      exact ⟨⟨hi, hi⟩, rfl⟩
  rw [h2, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.injEq .. ▸ h).1),
    Finset.card_range, Finset.card_product, Finset.card_range]

/-- INTERNAL: the numeric tail of the union bound, with `N_av`'s defining inequality
abstracted out: `(p² - p + 2) * 400 p⁴ K_obs/(N_av η²) ≤ 1/[100(H + 1)]`, given
`N_av η² ≥ 10⁸ p⁸ K_obs (H + 1)`, `p ≥ 1`, `K_obs ≥ 1`. -/
theorem oa_final_numeric_bound (p H Kobs Nav : ℕ) (η : ℝ) (hp1 : 1 ≤ p) (hKobs1 : 1 ≤ Kobs)
    (hNav : ((100000000 * p ^ 8 * Kobs * (H + 1) : ℕ) : ℝ) ≤ (Nav : ℝ) * η ^ 2) :
    ((p * p - p + 2 : ℕ) : ℝ) * (400 * (p : ℝ) ^ 4 * Kobs / ((Nav : ℝ) * η ^ 2)) ≤
      1 / (100 * ((H : ℝ) + 1)) := by
  have hNavη2pos : (0 : ℝ) < (Nav : ℝ) * η ^ 2 := by
    have h1 : (0 : ℝ) < ((100000000 * p ^ 8 * Kobs * (H + 1) : ℕ) : ℝ) := by
      have : 0 < 100000000 * p ^ 8 * Kobs * (H + 1) := by positivity
      exact_mod_cast this
    exact lt_of_lt_of_le h1 hNav
  rw [← mul_div_assoc, div_le_div_iff₀ hNavη2pos (by positivity : (0 : ℝ) < 100 * ((H : ℝ) + 1))]
  have hppnat : p ≤ p * p := Nat.le_mul_of_pos_left p hp1
  have hp2nat : p * p - p + 2 ≤ 2 * (p * p) := by omega
  have hp2 : ((p * p - p + 2 : ℕ) : ℝ) ≤ 2 * (p : ℝ) ^ 2 := by
    have h := (by exact_mod_cast hp2nat : ((p * p - p + 2 : ℕ) : ℝ) ≤ ((2 * (p * p) : ℕ) : ℝ))
    have heq2 : ((2 * (p * p) : ℕ) : ℝ) = 2 * (p : ℝ) ^ 2 := by push_cast; ring
    linarith [h, heq2]
  have hKobsR : (1 : ℝ) ≤ (Kobs : ℝ) := by exact_mod_cast hKobs1
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
  have hp6R : (1 : ℝ) ≤ (p : ℝ) ^ 6 := one_le_pow₀ hpR
  have hp2R : (1 : ℝ) ≤ (p : ℝ) ^ 2 := one_le_pow₀ hpR
  have hp8ge6 : (p : ℝ) ^ 6 ≤ (p : ℝ) ^ 8 := by
    have heq : (p : ℝ) ^ 8 = (p : ℝ) ^ 6 * (p : ℝ) ^ 2 := by ring
    rw [heq]; nlinarith [hp6R, hp2R]
  have step1 : ((p * p - p + 2 : ℕ) : ℝ) * (400 * (p : ℝ) ^ 4 * Kobs) * (100 * ((H : ℝ) + 1)) ≤
      2 * (p : ℝ) ^ 2 * (400 * (p : ℝ) ^ 4 * Kobs) * (100 * ((H : ℝ) + 1)) := by
    have hfac0 : (0 : ℝ) ≤ 400 * (p : ℝ) ^ 4 * Kobs * (100 * ((H : ℝ) + 1)) := by positivity
    nlinarith [hp2, hfac0]
  calc ((p * p - p + 2 : ℕ) : ℝ) * (400 * (p : ℝ) ^ 4 * Kobs) * (100 * ((H : ℝ) + 1))
      ≤ 2 * (p : ℝ) ^ 2 * (400 * (p : ℝ) ^ 4 * Kobs) * (100 * ((H : ℝ) + 1)) := step1
    _ = 80000 * (p : ℝ) ^ 6 * Kobs * ((H : ℝ) + 1) := by ring
    _ ≤ 100000000 * (p : ℝ) ^ 8 * Kobs * ((H : ℝ) + 1) := by
        have hfac1 : (0 : ℝ) ≤ Kobs * ((H : ℝ) + 1) := by positivity
        nlinarith [hp8ge6, hfac1]
    _ = ((100000000 * p ^ 8 * Kobs * (H + 1) : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (Nav : ℝ) * η ^ 2 := hNav
    _ = 1 * ((Nav : ℝ) * η ^ 2) := by ring

/-- **Empirical accuracy** (`eq:alg-empirical-probability`): from a starting law
dominated by `2 μ_j`, the `N_av` observations of `P_{j, w}` with good multipliers
`w` fail `obsAccurate` with probability at most `1/[100(H+1)]`.
PAPER: sections/algorithm.tex:313-337 -/
theorem observe_accurate (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) (ν : PMF (Finset ℕ))
    (hν : ∀ S, ν S ≤ 2 * ENNReal.ofReal (refMu I ε δ j S)) :
    (ν.bind (refObserve I ε δ j w)).toOuterMeasure {o | ¬ obsAccurate I ε δ j w o} ≤
      1 / (100 * ((HParam I ε δ : ℝ≥0∞) + 1)) := by
  classical
  set p := pSmall I ε δ with hpdef
  set bound : ℝ≥0∞ := ENNReal.ofReal (400 * (p : ℝ) ^ 4 * KobsParam I ε δ /
    (NavParam I ε δ * (ηParam I ε δ : ℝ) ^ 2)) with hbounddef
  set defectPairs : Finset (ℕ × ℕ) :=
    (Finset.range p ×ˢ Finset.range p).filter (fun pr => pr.1 ≠ pr.2) with hdpdef
  have htm0 : (0 : ℝ) ≤ transMass I ε δ j := by
    rw [transMass_eq_Cpart]; exact (oa_Cpart_pos I ε δ j).le
  have htm0' : (0 : ℝ) ≤ transMass I ε δ (j + 1) := by
    rw [transMass_eq_Cpart]; exact (oa_Cpart_pos I ε δ (j+1)).le
  have hadj := oa_transMass_adjacent I ε δ hε hfeas j
  have hfail0 := oa_single_fail hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj w hgood
    (obsG0 I ε δ) (fun o => (o.n0 : ℝ))
    (oa_obsG0_hT I ε δ j) (fun _ => by norm_num)
    (fun S S' i l h1 h2 => by unfold obsG0; rw [h1, h2])
    (fun S _ => by unfold obsG0; split <;> norm_num)
    (transMass I ε δ j) htm0 (by linarith) (fun _ => by linarith)
    (oa_obsG0_mean I ε δ j w) ν hν
  have hfailC := oa_single_fail hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj w hgood
    (obsGC I ε δ j) (fun o => o.sumG)
    (oa_obsGC_hT I ε δ j) (fun _ => rfl)
    (fun S S' i l h1 h2 => by unfold obsGC; simp [h1, h2])
    (fun S _ => oa_obsGC_range I ε δ hε hfeas j S)
    (transMass I ε δ (j + 1)) htm0' (by linarith [hadj.1]) (fun _ => by linarith [hadj.2])
    (oa_obsGC_mean I ε δ j w) ν hν
  have hfailIl : ∀ pr ∈ defectPairs,
      (ν.bind (refObserve I ε δ j w)).toOuterMeasure
        {o | ¬ |(o.nT pr.1 pr.2 : ℝ) / NavParam I ε δ -
            (w pr.1 pr.2 : ℝ) * cDef I ε δ j pr.1 pr.2 / refLamTot I ε δ j w| ≤
          (ηParam I ε δ : ℝ) * ((w pr.1 pr.2 : ℝ) * cDef I ε δ j pr.1 pr.2 /
            refLamTot I ε δ j w)} ≤ bound := by
    rintro ⟨i, l⟩ hpr
    simp only [hdpdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hpr
    obtain ⟨⟨hi, hl⟩, hil⟩ := hpr
    have hMfacts := oa_obsGil_M I ε δ j i l w hgood hi hl hil
    exact oa_single_fail hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj w hgood
      (obsGil I ε δ i l) (fun o => (o.nT i l : ℝ))
      (oa_obsGil_hT I ε δ j i l) (fun _ => by norm_num)
      (oa_obsGil_hQ I ε δ i l)
      (fun S _ => by unfold obsGil; split <;> norm_num)
      ((w i l : ℝ) * cDef I ε δ j i l) hMfacts.1 hMfacts.2.1 hMfacts.2.2
      (oa_obsGil_mean I ε δ j i l w) ν hν
  have hsub : {o | ¬ obsAccurate I ε δ j w o} ⊆
      ({o | ¬ |(o.n0 : ℝ) / NavParam I ε δ - transMass I ε δ j / refLamTot I ε δ j w| ≤
          (ηParam I ε δ : ℝ) * (transMass I ε δ j / refLamTot I ε δ j w)} ∪
        ⋃ pr ∈ defectPairs, {o | ¬ |(o.nT pr.1 pr.2 : ℝ) / NavParam I ε δ -
            (w pr.1 pr.2 : ℝ) * cDef I ε δ j pr.1 pr.2 / refLamTot I ε δ j w| ≤
          (ηParam I ε δ : ℝ) * ((w pr.1 pr.2 : ℝ) * cDef I ε δ j pr.1 pr.2 /
            refLamTot I ε δ j w)}) ∪
        {o | ¬ |o.sumG / NavParam I ε δ - transMass I ε δ (j + 1) / refLamTot I ε δ j w| ≤
          (ηParam I ε δ : ℝ) * (transMass I ε δ (j + 1) / refLamTot I ε δ j w)} := by
    intro o ho
    simp only [Set.mem_setOf_eq] at ho
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion]
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨hA, hBi⟩, hC⟩ := hcon
    apply ho
    unfold obsAccurate
    refine ⟨hA, ?_, hC⟩
    intro i hi l hl hil
    refine hBi ⟨i, l⟩ ?_
    simp only [hdpdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨hi, hl⟩, hil⟩
  have hunion : (ν.bind (refObserve I ε δ j w)).toOuterMeasure {o | ¬ obsAccurate I ε δ j w o} ≤
      bound + defectPairs.card * bound + bound := by
    refine le_trans (MeasureTheory.OuterMeasureClass.measure_mono _ hsub) ?_
    refine le_trans (MeasureTheory.measure_union_le _ _) ?_
    refine add_le_add ?_ (hfailC.trans_eq (by rw [hbounddef]))
    refine le_trans (MeasureTheory.measure_union_le _ _) ?_
    refine add_le_add (hfail0.trans_eq (by rw [hbounddef])) ?_
    refine le_trans (MeasureTheory.measure_biUnion_finset_le defectPairs _) ?_
    calc ∑ pr ∈ defectPairs, (ν.bind (refObserve I ε δ j w)).toOuterMeasure
          {o | ¬ |(o.nT pr.1 pr.2 : ℝ) / NavParam I ε δ -
              (w pr.1 pr.2 : ℝ) * cDef I ε δ j pr.1 pr.2 / refLamTot I ε δ j w| ≤
            (ηParam I ε δ : ℝ) * ((w pr.1 pr.2 : ℝ) * cDef I ε δ j pr.1 pr.2 /
              refLamTot I ε δ j w)}
        ≤ ∑ _pr ∈ defectPairs, bound := Finset.sum_le_sum hfailIl
      _ = defectPairs.card * bound := by rw [Finset.sum_const, nsmul_eq_mul]
  refine hunion.trans ?_
  have hcard : defectPairs.card = p * p - p := by rw [hdpdef]; exact oa_defectPairs_card p
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp
  have hsum_eq : bound + (defectPairs.card : ℝ≥0∞) * bound + bound =
      ((defectPairs.card + 2 : ℕ) : ℝ≥0∞) * bound := by
    push_cast; ring
  rw [hsum_eq]
  have hKobs1 : 1 ≤ KobsParam I ε δ := by
    unfold KobsParam
    have hCd : 1 ≤ CdParam I ε δ := by unfold CdParam; omega
    have hp4 : 1 ≤ p ^ 4 := Nat.one_le_pow _ _ hp1
    have hCd' : 1 ≤ 9 * CpParam I ε δ + 2 * CdParam I ε δ := by omega
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ 10 * p ^ 4 * (9 * CpParam I ε δ + 2 * CdParam I ε δ) := by gcongr <;> omega
  have hNavη2 : ((100000000 * p ^ 8 * KobsParam I ε δ * (HParam I ε δ + 1) : ℕ) : ℝ) ≤
      (NavParam I ε δ : ℝ) * (ηParam I ε δ : ℝ) ^ 2 := by
    have hηpos : (0 : ℚ) < ηParam I ε δ := by
      unfold ηParam
      refine div_pos hε ?_
      have h200 : 0 < 200 * (HParam I ε δ + 1) := by omega
      exact_mod_cast h200
    have hηsq0 : (0 : ℚ) < ηParam I ε δ ^ 2 := by positivity
    have hle := Nat.le_ceil (((100000000 * pSmall I ε δ ^ 8 * KobsParam I ε δ *
      (HParam I ε δ + 1) : ℕ) : ℚ) / ηParam I ε δ ^ 2)
    rw [div_le_iff₀ hηsq0] at hle
    rw [NavParam, ← hpdef]
    exact_mod_cast hle
  have hfinal := oa_final_numeric_bound p (HParam I ε δ) (KobsParam I ε δ) (NavParam I ε δ)
    (ηParam I ε δ : ℝ) hp1 hKobs1 hNavη2
  rw [← hcard] at hfinal
  have hcast : ((defectPairs.card + 2 : ℕ) : ℝ≥0∞) =
      ENNReal.ofReal ((defectPairs.card + 2 : ℕ) : ℝ) := (ENNReal.ofReal_natCast _).symm
  have hstep1 : ((defectPairs.card + 2 : ℕ) : ℝ≥0∞) * bound =
      ENNReal.ofReal (((defectPairs.card + 2 : ℕ) : ℝ) *
        (400 * (p : ℝ) ^ 4 * KobsParam I ε δ / (NavParam I ε δ * (ηParam I ε δ : ℝ) ^ 2))) := by
    rw [hbounddef, hcast, ← ENNReal.ofReal_mul (by positivity)]
  have hstep2 : ENNReal.ofReal (((defectPairs.card + 2 : ℕ) : ℝ) *
      (400 * (p : ℝ) ^ 4 * KobsParam I ε δ / (NavParam I ε δ * (ηParam I ε δ : ℝ) ^ 2))) ≤
      ENNReal.ofReal (1 / (100 * ((HParam I ε δ : ℝ) + 1))) := ENNReal.ofReal_le_ofReal hfinal
  have hH0 : (0 : ℝ) ≤ (HParam I ε δ : ℝ) := by exact_mod_cast Nat.zero_le _
  have hstep3 : ENNReal.ofReal (1 / (100 * ((HParam I ε δ : ℝ) + 1))) =
      1 / (100 * ((HParam I ε δ : ℝ≥0∞) + 1)) := by
    rw [one_div, one_div, ENNReal.ofReal_inv_of_pos (by linarith),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add hH0 (by norm_num),
      ENNReal.ofReal_natCast, ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  rw [hstep1]
  exact hstep2.trans_eq hstep3

end Cellcounting.Analysis
