import Cellcounting.Analysis.PmfClose

/-!
# Real-valued expectations under finitely supported laws

`rpexp μ f = Σ' a, μ(a) f(a)` for a real (possibly signed) `f`.  For a law with
finite support this is a finite sum, so it is linear, monotone on the support,
commutes with `pure`, `map` and `bind` (when every kernel used has finite support),
and agrees with `pexp` on nonnegative functions (`pexp_ofReal_eq`).  This is what the
second-moment computation of `lem:time-average` needs: the autocovariance expansion
has cross terms of both signs, which `ℝ≥0∞`-valued `pexp` cannot express.
-/

namespace Cellcounting.Analysis

open scoped ENNReal

variable {α β : Type*}

/-- INTERNAL: the real expectation of `f` under `μ`. -/
noncomputable def rpexp (μ : PMF α) (f : α → ℝ) : ℝ := ∑' a, (μ a).toReal * f a

/-- INTERNAL: under a finitely supported law the expectation is a finite sum over any
finset containing the support. -/
theorem rpexp_eq_sum (μ : PMF α) (F : Finset α) (hF : ∀ a ∈ μ.support, a ∈ F) (f : α → ℝ) :
    rpexp μ f = ∑ a ∈ F, (μ a).toReal * f a := by
  unfold rpexp
  refine tsum_eq_sum fun a ha => ?_
  have : μ a = 0 := by
    by_contra h; exact ha (hF a ((PMF.mem_support_iff μ a).2 h))
  simp [this]

/-- INTERNAL: the probabilities of a finite support sum to one. -/
theorem sum_toReal_eq_one (μ : PMF α) (F : Finset α) (hF : ∀ a ∈ μ.support, a ∈ F) :
    ∑ a ∈ F, (μ a).toReal = 1 := by
  rw [← ENNReal.toReal_sum fun a _ => PMF.apply_ne_top μ a]
  have : ∑ a ∈ F, μ a = ∑' a, μ a := by
    refine (tsum_eq_sum fun a ha => ?_).symm
    by_contra h; exact ha (hF a ((PMF.mem_support_iff μ a).2 h))
  rw [this, PMF.tsum_coe]; rfl

theorem rpexp_congr (μ : PMF α) {f g : α → ℝ} (h : ∀ a ∈ μ.support, f a = g a) :
    rpexp μ f = rpexp μ g := by
  unfold rpexp
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ μ.support
  · rw [h a ha]
  · rw [PMF.mem_support_iff, not_not] at ha; simp [ha]

theorem rpexp_add (μ : PMF α) (hμ : μ.support.Finite) (f g : α → ℝ) :
    rpexp μ (fun a => f a + g a) = rpexp μ f + rpexp μ g := by
  have hF : ∀ a ∈ μ.support, a ∈ hμ.toFinset := fun a ha => hμ.mem_toFinset.2 ha
  rw [rpexp_eq_sum μ _ hF, rpexp_eq_sum μ _ hF, rpexp_eq_sum μ _ hF, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem rpexp_const_mul (μ : PMF α) (hμ : μ.support.Finite) (c : ℝ) (f : α → ℝ) :
    rpexp μ (fun a => c * f a) = c * rpexp μ f := by
  have hF : ∀ a ∈ μ.support, a ∈ hμ.toFinset := fun a ha => hμ.mem_toFinset.2 ha
  rw [rpexp_eq_sum μ _ hF, rpexp_eq_sum μ _ hF, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem rpexp_const (μ : PMF α) (hμ : μ.support.Finite) (c : ℝ) :
    rpexp μ (fun _ => c) = c := by
  have hF : ∀ a ∈ μ.support, a ∈ hμ.toFinset := fun a ha => hμ.mem_toFinset.2 ha
  rw [rpexp_eq_sum μ _ hF, ← Finset.sum_mul, sum_toReal_eq_one μ _ hF, one_mul]

theorem rpexp_mono (μ : PMF α) (hμ : μ.support.Finite) {f g : α → ℝ}
    (h : ∀ a ∈ μ.support, f a ≤ g a) : rpexp μ f ≤ rpexp μ g := by
  have hF : ∀ a ∈ μ.support, a ∈ hμ.toFinset := fun a ha => hμ.mem_toFinset.2 ha
  rw [rpexp_eq_sum μ _ hF, rpexp_eq_sum μ _ hF]
  refine Finset.sum_le_sum fun a ha => ?_
  exact mul_le_mul_of_nonneg_left (h a (hμ.mem_toFinset.1 ha)) ENNReal.toReal_nonneg

theorem rpexp_pure (a : α) (f : α → ℝ) : rpexp (PMF.pure a) f = f a := by
  rw [rpexp_eq_sum (PMF.pure a) {a} (fun b hb => by simpa using hb)]
  simp

theorem rpexp_bind (μ : PMF α) (K : α → PMF β) (hμ : μ.support.Finite)
    (hK : ∀ a ∈ μ.support, (K a).support.Finite) (f : β → ℝ) :
    rpexp (μ.bind K) f = rpexp μ fun a => rpexp (K a) f := by
  have hB : (μ.bind K).support.Finite := by
    rw [PMF.support_bind]; exact hμ.biUnion hK
  have hF : ∀ a ∈ μ.support, a ∈ hμ.toFinset := fun a ha => hμ.mem_toFinset.2 ha
  have hFB : ∀ b ∈ (μ.bind K).support, b ∈ hB.toFinset := fun b hb => hB.mem_toFinset.2 hb
  rw [rpexp_eq_sum _ _ hFB, rpexp_eq_sum μ _ hF]
  have hpt : ∀ b, ((μ.bind K) b).toReal = ∑ a ∈ hμ.toFinset, (μ a).toReal * (K a b).toReal := by
    intro b
    rw [PMF.bind_apply, tsum_eq_sum (s := hμ.toFinset) fun a ha => ?_]
    · rw [ENNReal.toReal_sum fun a _ =>
        ENNReal.mul_ne_top (PMF.apply_ne_top μ a) (PMF.apply_ne_top (K a) b)]
      exact Finset.sum_congr rfl fun a _ => ENNReal.toReal_mul
    · have : μ a = 0 := by
        by_contra h; exact ha (hF a ((PMF.mem_support_iff μ a).2 h))
      simp [this]
  simp_rw [hpt, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' : a ∈ μ.support := hμ.mem_toFinset.1 ha
  have hKF : ∀ b ∈ (K a).support, b ∈ hB.toFinset := fun b hb => by
    refine hB.mem_toFinset.2 ?_
    rw [PMF.mem_support_bind_iff]; exact ⟨a, ha', hb⟩
  rw [rpexp_eq_sum (K a) _ hKF, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem rpexp_map (μ : PMF α) (hμ : μ.support.Finite) (g : α → β) (f : β → ℝ) :
    rpexp (μ.map g) f = rpexp μ (fun a => f (g a)) := by
  rw [← PMF.bind_pure_comp, rpexp_bind μ _ hμ (fun a _ => by simp)]
  simp [rpexp_pure]

/-- INTERNAL: on nonnegative functions `pexp` is the real expectation. -/
theorem pexp_ofReal_eq (μ : PMF α) (hμ : μ.support.Finite) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    pexp μ (fun a => ENNReal.ofReal (f a)) = ENNReal.ofReal (rpexp μ f) := by
  have hF : ∀ a ∈ μ.support, a ∈ hμ.toFinset := fun a ha => hμ.mem_toFinset.2 ha
  rw [rpexp_eq_sum μ _ hF, ENNReal.ofReal_sum_of_nonneg fun a _ =>
    mul_nonneg ENNReal.toReal_nonneg (hf a)]
  unfold pexp
  rw [tsum_eq_sum (s := hμ.toFinset) fun a ha => ?_]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top μ a)]
  · have : μ a = 0 := by
      by_contra h; exact ha (hF a ((PMF.mem_support_iff μ a).2 h))
    simp [this]

end Cellcounting.Analysis
