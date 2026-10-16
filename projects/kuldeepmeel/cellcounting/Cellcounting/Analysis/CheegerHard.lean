import Arlib.MarkovChains.Techniques.Conductance
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Cheeger's inequality, hard direction

`Cellcounting.Analysis.spectralGap_of_cut`: a finite chain `P`, reversible for `μ`, all of
whose cuts of stationary mass at most `1/2` satisfy `κ π(A) ≤ Q(A, Aᶜ)`, has
spectral gap at least `κ²/2` in Arlib's Poincaré sense (`SpectralGapAtLeast`).

This is the argument of `evaluation.tex:299-312`, step for step.
* `coarea_cut`: for `a ≥ 0` supported on mass `≤ 1/2`,
  `κ E_π a ≤ Σ_{v,w} π(v)P(v,w)(a(v) - a(w))⁺`. This is integration over the superlevel
  sets `{a > s}`, written as Lebesgue integrals of interval indicators.
* `cheeger_nonneg`: with `a = g²`, the AM-GM inequality in place of Cauchy–Schwarz gives
  `κ²/2 · E_π g² ≤ ℰ_P(g)` for `g ≥ 0` supported on mass `≤ 1/2`.
* `spectralGap_of_cut`: apply that to the positive and negative parts about a median
  (`exists_median`). Their energies add to at most `ℰ_P(f)`, by `parts_sq_le`.

Arlib (`Arlib.MarkovChains.Techniques.Conductance`) has only the easy direction.
-/

namespace Cellcounting.Analysis

open Arlib.Probability Arlib.MarkovChains MeasureTheory Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- INTERNAL: `∫ 1_{[a,b)} = (b - a)⁺`. -/
theorem integral_Ico_one (a b : ℝ) :
    ∫ s, (Set.Ico a b).indicator (1 : ℝ → ℝ) s = max (b - a) 0 := by
  rw [integral_indicator_one measurableSet_Ico, Measure.real, Real.volume_Ico,
    ENNReal.toReal_ofReal']

/-- INTERNAL: the indicator of a bounded interval is integrable. -/
theorem integrable_Ico_one (a b : ℝ) : Integrable ((Set.Ico a b).indicator (1 : ℝ → ℝ)) := by
  rw [integrable_indicator_iff measurableSet_Ico]
  exact integrableOn_const (by simp [Real.volume_Ico])

/-- **Co-area step** of the hard Cheeger bound: integrate the cut bound over the
superlevel sets of `a`.
PAPER: sections/evaluation.tex:299-306 ("integration over superlevel sets of `g²`") -/
theorem coarea_cut {μ : FinDist Ω} {P : FinChain Ω} {κ : ℝ}
    (hcut : ∀ A : Finset Ω, Pr μ A ≤ 1 / 2 → κ * Pr μ A ≤ cut μ P A)
    (a : Ω → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hsupp : Pr μ (univ.filter fun x => a x ≠ 0) ≤ 1 / 2) :
    κ * ∑ x, μ x * a x ≤ ∑ x, ∑ y, μ x * P x y * max (a x - a y) 0 := by
  have hL : ∑ x, μ x * a x = ∫ s, ∑ x, μ x * (Set.Ico 0 (a x)).indicator (1 : ℝ → ℝ) s := by
    rw [integral_finsetSum _ fun x _ => (integrable_Ico_one _ _).const_mul _]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_const_mul, integral_Ico_one, sub_zero, max_eq_left (ha x)]
  have hR : ∑ x, ∑ y, μ x * P x y * max (a x - a y) 0 =
      ∫ s, ∑ x, ∑ y, μ x * P x y * (Set.Ico (a y) (a x)).indicator (1 : ℝ → ℝ) s := by
    rw [integral_finsetSum _ fun x _ =>
      integrable_finsetSum _ fun y _ => (integrable_Ico_one _ _).const_mul _]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_finsetSum _ fun y _ => (integrable_Ico_one _ _).const_mul _]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [integral_const_mul, integral_Ico_one]
  rw [hL, hR, ← integral_const_mul]
  refine integral_mono ((integrable_finsetSum _ fun x _ =>
      (integrable_Ico_one _ _).const_mul _).const_mul _)
    (integrable_finsetSum _ fun x _ =>
      integrable_finsetSum _ fun y _ => (integrable_Ico_one _ _).const_mul _) fun s => ?_
  dsimp only
  by_cases hs : s < 0
  · have : ∑ x, μ x * (Set.Ico 0 (a x)).indicator (1 : ℝ → ℝ) s = 0 :=
      Finset.sum_eq_zero fun x _ => by
        rw [Set.indicator_of_notMem (by simp [Set.mem_Ico]; intro h; linarith), mul_zero]
    rw [this, mul_zero]
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (mul_nonneg (μ.coe_nonneg x) (P.coe_nonneg x y))
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  push Not at hs
  set A : Finset Ω := univ.filter fun x => s < a x with hA
  have hPr : Pr μ A ≤ 1 / 2 := by
    refine le_trans (Pr_mono μ fun x hx => ?_) hsupp
    simp only [hA, mem_filter, mem_univ, true_and] at hx ⊢
    intro h; rw [h] at hx; linarith
  have hL' : ∑ x, μ x * (Set.Ico 0 (a x)).indicator (1 : ℝ → ℝ) s = Pr μ A := by
    rw [Pr_apply, hA, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : s < a x
    · rw [Set.indicator_of_mem (by simp [Set.mem_Ico]; exact ⟨hs, h⟩), if_pos h]; simp
    · rw [Set.indicator_of_notMem (by simp [Set.mem_Ico]; intro _; exact not_lt.1 h), if_neg h,
        mul_zero]
  have hR' : ∑ x, ∑ y, μ x * P x y * (Set.Ico (a y) (a x)).indicator (1 : ℝ → ℝ) s =
      cut μ P A := by
    rw [cut_apply, flow_apply, hA, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : s < a x
    · rw [if_pos h, Finset.compl_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases h' : s < a y
      · rw [Set.indicator_of_notMem (by simp [Set.mem_Ico]; intro h''; linarith)]
        simp [h']
      · rw [Set.indicator_of_mem (by simp [Set.mem_Ico]; exact ⟨not_lt.1 h', h⟩)]
        simp [h']
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [Set.indicator_of_notMem (by simp [Set.mem_Ico]; intro _; exact not_lt.1 h), mul_zero]
  rw [hL', hR']
  exact hcut A hPr


/-- **Cheeger for a function supported on mass `≤ 1/2`**: `κ²/2 · E_π g² ≤ ℰ_P(g)`.
PAPER: sections/evaluation.tex:299-308 -/
theorem cheeger_nonneg {μ : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P) {κ : ℝ}
    (hκ : 0 < κ) (hcut : ∀ A : Finset Ω, Pr μ A ≤ 1 / 2 → κ * Pr μ A ≤ cut μ P A)
    (g : Ω → ℝ) (hg : ∀ x, 0 ≤ g x)
    (hsupp : Pr μ (univ.filter fun x => g x ≠ 0) ≤ 1 / 2) :
    κ ^ 2 / 2 * ip μ g g ≤ dirichlet μ P g g := by
  have hst := hrev.stationary
  set a : Ω → ℝ := fun x => g x ^ 2 with ha
  have hco := coarea_cut hcut a (fun x => sq_nonneg _) (by
    refine le_trans (le_of_eq ?_) hsupp
    congr 1; ext x; simp [ha])
  have hip : ip μ g g = ∑ x, μ x * a x := by
    rw [ip_apply]; exact Finset.sum_congr rfl fun x _ => by simp [ha]; ring
  set w : Ω → Ω → ℝ := fun x y => μ x * P x y with hw
  have hw0 : ∀ x y, 0 ≤ w x y := fun x y => mul_nonneg (μ.coe_nonneg x) (P.coe_nonneg x y)
  -- symmetry of the positive parts
  have hsym : ∑ x, ∑ y, w x y * max (a x - a y) 0 = ∑ x, ∑ y, w x y * max (a y - a x) 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [hw]; rw [hrev y x]
  have h2X : 2 * ∑ x, ∑ y, w x y * max (a x - a y) 0 =
      ∑ x, ∑ y, w x y * |a x - a y| := by
    conv_lhs => rw [two_mul]; arg 2; rw [hsym]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← mul_add]; congr 1
    rcases le_total (a y) (a x) with h | h
    · rw [max_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonneg (by linarith)]
      ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos (by linarith)]
      ring
  -- AM-GM on each pair
  have hpt : ∀ x y, |a x - a y| ≤ (g x - g y) ^ 2 / κ + κ * (g x + g y) ^ 2 / 4 := by
    intro x y
    have hfac : |a x - a y| = |g x - g y| * (g x + g y) := by
      simp only [ha]
      rw [show g x ^ 2 - g y ^ 2 = (g x - g y) * (g x + g y) by ring, abs_mul,
        abs_of_nonneg (add_nonneg (hg x) (hg y))]
    rw [hfac]
    have key : 0 ≤ (|g x - g y| / κ - (g x + g y) / 2) ^ 2 * κ := mul_nonneg (sq_nonneg _) hκ.le
    have hsq : |g x - g y| ^ 2 = (g x - g y) ^ 2 := sq_abs _
    have : (|g x - g y| / κ - (g x + g y) / 2) ^ 2 * κ =
        (g x - g y) ^ 2 / κ + κ * (g x + g y) ^ 2 / 4 - |g x - g y| * (g x + g y) := by
      rw [← hsq]; field_simp; ring
    linarith
  have hE : ∑ x, ∑ y, w x y * (g x - g y) ^ 2 = 2 * dirichlet μ P g g := by
    rw [dirichlet_self_eq_pair hst]; simp only [hw]; ring
  have hplus : ∑ x, ∑ y, w x y * (g x + g y) ^ 2 ≤ 4 * ip μ g g := by
    have h1 : ∀ x y, w x y * (g x + g y) ^ 2 ≤ 2 * (w x y * g x ^ 2) + 2 * (w x y * g y ^ 2) :=
      fun x y => by nlinarith [hw0 x y, sq_nonneg (g x - g y)]
    have hA : ∑ x, ∑ y, w x y * g x ^ 2 = ip μ g g := by
      rw [ip_apply]; refine Finset.sum_congr rfl fun x _ => ?_
      simp only [hw]
      rw [show ∑ y, μ x * P x y * g x ^ 2 = μ x * g x ^ 2 * ∑ y, P x y by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring, P.sum_coe x]; ring
    have hB : ∑ x, ∑ y, w x y * g y ^ 2 = ip μ g g := by
      rw [Finset.sum_comm, ip_apply]; refine Finset.sum_congr rfl fun y _ => ?_
      simp only [hw]
      rw [show ∑ x, μ x * P x y * g y ^ 2 = (∑ x, μ x * P x y) * g y ^ 2 by
        rw [Finset.sum_mul], hst y]; ring
    calc ∑ x, ∑ y, w x y * (g x + g y) ^ 2
        ≤ ∑ x, ∑ y, (2 * (w x y * g x ^ 2) + 2 * (w x y * g y ^ 2)) :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => h1 x y
      _ = 4 * ip μ g g := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hA, hB]; ring
  have hbound : ∑ x, ∑ y, w x y * |a x - a y| ≤
      2 * dirichlet μ P g g / κ + κ * ip μ g g := by
    calc ∑ x, ∑ y, w x y * |a x - a y|
        ≤ ∑ x, ∑ y, (w x y * (g x - g y) ^ 2 / κ + κ / 4 * (w x y * (g x + g y) ^ 2)) :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => by
            have := mul_le_mul_of_nonneg_left (hpt x y) (hw0 x y)
            calc w x y * |a x - a y| ≤ w x y * ((g x - g y) ^ 2 / κ + κ * (g x + g y) ^ 2 / 4) :=
                  this
              _ = _ := by ring
      _ = (∑ x, ∑ y, w x y * (g x - g y) ^ 2) / κ +
            κ / 4 * ∑ x, ∑ y, w x y * (g x + g y) ^ 2 := by
          simp only [Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
      _ ≤ 2 * dirichlet μ P g g / κ + κ / 4 * (4 * ip μ g g) := by
          rw [hE]; gcongr
      _ = _ := by ring
  have hX : κ * ip μ g g ≤ ∑ x, ∑ y, w x y * max (a x - a y) 0 := by rw [hip]; exact hco
  have : 2 * κ * ip μ g g ≤ 2 * dirichlet μ P g g / κ + κ * ip μ g g := by linarith
  have h3 : κ * ip μ g g ≤ 2 * dirichlet μ P g g / κ := by linarith
  rw [le_div_iff₀ hκ] at h3
  nlinarith


omit [DecidableEq Ω] in
/-- INTERNAL: a median of `f` under a finite law.
TEXLINE: sections/evaluation.tex:309-311 -/
theorem exists_median (μ : FinDist Ω) (f : Ω → ℝ) :
    ∃ m : ℝ, Pr μ (univ.filter fun x => m < f x) ≤ 1 / 2 ∧
      Pr μ (univ.filter fun x => f x < m) ≤ 1 / 2 := by
  have hne : (univ : Finset Ω).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := μ.sum_coe; rw [h, Finset.sum_empty] at this; norm_num at this
  have hcompl : ∀ p : Ω → Prop, [DecidablePred p] →
      Pr μ (univ.filter p) + Pr μ (univ.filter fun x => ¬ p x) = 1 := by
    intro p _
    rw [Pr_apply, Pr_apply, Finset.sum_filter_add_sum_filter_not, μ.sum_coe]
  obtain ⟨xM, -, hxM⟩ := Finset.exists_max_image univ f hne
  set S : Finset Ω := univ.filter fun x => 1 / 2 ≤ Pr μ (univ.filter fun y => f y ≤ f x)
  have hS : S.Nonempty := ⟨xM, by
    simp only [S, mem_filter, mem_univ, true_and]
    rw [show (univ.filter fun y => f y ≤ f xM) = univ from
      Finset.filter_true_of_mem fun y _ => hxM y (mem_univ y), Pr_apply, μ.sum_coe]
    norm_num⟩
  obtain ⟨x0, hx0S, hx0⟩ := Finset.exists_min_image S f hS
  refine ⟨f x0, ?_, ?_⟩
  · have h1 := hcompl (fun y => f y ≤ f x0)
    simp only [S, mem_filter, mem_univ, true_and] at hx0S
    have : (univ.filter fun x => f x0 < f x) = univ.filter fun x => ¬ f x ≤ f x0 := by
      ext x; simp
    rw [this]; linarith
  · by_contra hlt
    push Not at hlt
    set B : Finset Ω := univ.filter fun x => f x < f x0
    have hB : B.Nonempty := by
      by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h] at hlt; simp at hlt; linarith
    obtain ⟨x1, hx1B, hx1⟩ := Finset.exists_max_image B f hB
    have hx1lt : f x1 < f x0 := by simpa [B] using hx1B
    have hEq : (univ.filter fun y => f y ≤ f x1) = B := by
      ext y; simp only [B, mem_filter, mem_univ, true_and]
      constructor
      · intro h; linarith
      · intro h; exact hx1 y (by simpa [B] using h)
    have hx1S : x1 ∈ S := by
      simp only [S, mem_filter, mem_univ, true_and]; rw [hEq]; linarith
    linarith [hx0 x1 hx1S]

/-- INTERNAL: splitting into positive and negative parts does not increase the energy
of an edge. -/
theorem parts_sq_le (u v : ℝ) :
    (max u 0 - max v 0) ^ 2 + (max (-u) 0 - max (-v) 0) ^ 2 ≤ (u - v) ^ 2 := by
  rcases le_total 0 u with h | h <;> rcases le_total 0 v with h' | h'
  · rw [max_eq_left h, max_eq_left h', max_eq_right (by linarith), max_eq_right (by linarith)]
    nlinarith
  · rw [max_eq_left h, max_eq_right h', max_eq_right (by linarith), max_eq_left (by linarith)]
    nlinarith
  · rw [max_eq_right h, max_eq_left h', max_eq_left (by linarith), max_eq_right (by linarith)]
    nlinarith
  · rw [max_eq_right h, max_eq_right h', max_eq_left (by linarith), max_eq_left (by linarith)]
    nlinarith

/-- **Cheeger's inequality, hard direction**: a cut bound `κ` gives inverse spectral gap at
most `2/κ²`.
PAPER: sections/evaluation.tex:299-312 -/
theorem spectralGap_of_cut {μ : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P) {κ : ℝ}
    (hκ : 0 ≤ κ) (hcut : ∀ A : Finset Ω, Pr μ A ≤ 1 / 2 → κ * Pr μ A ≤ cut μ P A) :
    SpectralGapAtLeast μ P (κ ^ 2 / 2) := by
  have hst := hrev.stationary
  rcases hκ.eq_or_lt with h0 | hκ
  · subst h0; simpa using spectralGapAtLeast_zero hst
  intro f
  obtain ⟨m, hm1, hm2⟩ := exists_median μ f
  set gp : Ω → ℝ := fun x => max (f x - m) 0
  set gm : Ω → ℝ := fun x => max (m - f x) 0
  have hp := cheeger_nonneg hrev hκ hcut gp (fun x => le_max_right _ _) (by
    refine le_trans (le_of_eq ?_) hm1; congr 1; ext x
    simp only [gp, mem_filter, mem_univ, true_and]
    constructor
    · intro h; by_contra h'; push Not at h'; exact h (max_eq_right (by linarith))
    · intro h; rw [max_eq_left (by linarith)]; linarith)
  have hm := cheeger_nonneg hrev hκ hcut gm (fun x => le_max_right _ _) (by
    refine le_trans (le_of_eq ?_) hm2; congr 1; ext x
    simp only [gm, mem_filter, mem_univ, true_and]
    constructor
    · intro h; by_contra h'; push Not at h'; exact h (max_eq_right (by linarith))
    · intro h; rw [max_eq_left (by linarith)]; linarith)
  have hvar : Var μ f ≤ ip μ gp gp + ip μ gm gm := by
    rw [← Var_sub_const μ f m]
    refine le_trans (Var_le_ip_self μ _) (le_of_eq ?_)
    rw [ip_apply, ip_apply, ip_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [gp, gm]
    rcases le_total m (f x) with h | h
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  have hdir : dirichlet μ P gp gp + dirichlet μ P gm gm ≤ dirichlet μ P f f := by
    rw [dirichlet_self_eq_pair hst, dirichlet_self_eq_pair hst, dirichlet_self_eq_pair hst,
      ← mul_add, ← Finset.sum_add_distrib]
    gcongr with x _
    rw [← Finset.sum_add_distrib]
    gcongr with y _
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (μ.coe_nonneg x) (P.coe_nonneg x y))
    have := parts_sq_le (f x - m) (f y - m)
    simp only [gp, gm]
    rw [show m - f x = -(f x - m) by ring, show m - f y = -(f y - m) by ring,
      show f x - f y = (f x - m) - (f y - m) by ring]
    exact this
  have hκ2 : 0 ≤ κ ^ 2 / 2 := by positivity
  calc κ ^ 2 / 2 * Var μ f ≤ κ ^ 2 / 2 * (ip μ gp gp + ip μ gm gm) :=
        mul_le_mul_of_nonneg_left hvar hκ2
    _ ≤ dirichlet μ P gp gp + dirichlet μ P gm gm := by rw [mul_add]; linarith
    _ ≤ _ := hdir

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `spectralGap_of_cut` and its steps, no `sorry`
-/
