import Cellcounting.Interface.Pseudocode

/-!
# Closeness of finite-bit laws to their ideal counterparts

The coupling arguments of `evaluation.tex:373-388` replace each bin draw and
each offset draw by an exact draw from its ideal law, at a total-variation cost
per draw.  Here that is phrased without explicit couplings:
`PClose μ ν ζ` says every `[0, 1]`-valued expectation under `μ` exceeds the one
under `ν` by at most `ζ` (one-sided total variation; `PClose.symm` gives the
other side).  It composes along `bind`, `map` and `Pseudocode.loop`, adding the
per-step costs, and transfers to event probabilities (`PClose.outer_le`).
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal

/-- INTERNAL: the expectation of `f` under `μ`. -/
noncomputable def pexp {α : Type*} (μ : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ := ∑' a, μ a * f a

/-- INTERNAL: one-sided total-variation closeness of two laws. -/
def PClose {α : Type*} (μ ν : PMF α) (ζ : ℝ≥0∞) : Prop :=
  ∀ f : α → ℝ≥0∞, (∀ a, f a ≤ 1) → pexp μ f ≤ pexp ν f + ζ

section
variable {α β : Type*}

/-- INTERNAL: expectations of functions bounded by one are at most one. -/
theorem pexp_le_one (μ : PMF α) (f : α → ℝ≥0∞) (hf : ∀ a, f a ≤ 1) : pexp μ f ≤ 1 := by
  calc pexp μ f ≤ ∑' a, μ a * 1 := ENNReal.tsum_le_tsum fun a => by gcongr; exact hf a
    _ = 1 := by simp [μ.tsum_coe]

/-- INTERNAL: expectations are monotone. -/
theorem pexp_mono (μ : PMF α) {f g : α → ℝ≥0∞} (h : ∀ a, f a ≤ g a) : pexp μ f ≤ pexp μ g :=
  ENNReal.tsum_le_tsum fun a => by gcongr; exact h a

/-- INTERNAL: expectations are monotone, comparing only on the support. -/
theorem pexp_mono_support (μ : PMF α) {f g : α → ℝ≥0∞} (h : ∀ a ∈ μ.support, f a ≤ g a) :
    pexp μ f ≤ pexp μ g := by
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ μ.support
  · gcongr; exact h a ha
  · rw [PMF.mem_support_iff, not_not] at ha
    simp [ha]

/-- INTERNAL: adding a constant. -/
theorem pexp_add_const (μ : PMF α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    pexp μ (fun a => f a + c) = pexp μ f + c := by
  simp only [pexp, mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

/-- INTERNAL: expectation under a `bind`. -/
theorem pexp_bind (μ : PMF α) (K : α → PMF β) (f : β → ℝ≥0∞) :
    pexp (μ.bind K) f = pexp μ fun a => pexp (K a) f := by
  simp only [pexp, PMF.bind_apply]
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

/-- INTERNAL: expectation under `pure`. -/
theorem pexp_pure (a : α) (f : α → ℝ≥0∞) : pexp (PMF.pure a) f = f a := by
  simp only [pexp, PMF.pure_apply]
  rw [tsum_eq_single a (fun b hb => by simp [hb])]
  simp

/-- INTERNAL: expectation under `map`. -/
theorem pexp_map (μ : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    pexp (μ.map g) f = pexp μ (f ∘ g) := by
  rw [← PMF.bind_pure_comp, pexp_bind]
  simp [pexp_pure]; rfl

/-- INTERNAL: event probability as an expectation. -/
theorem outer_eq_pexp (μ : PMF α) (s : Set α) :
    μ.toOuterMeasure s = pexp μ (s.indicator 1) := by
  rw [PMF.toOuterMeasure_apply, pexp]
  congr 1; funext a
  by_cases h : a ∈ s <;> simp [h]

theorem PClose.refl (μ : PMF α) (ζ : ℝ≥0∞) : PClose μ μ ζ :=
  fun _ _ => le_add_right le_rfl

theorem PClose.mono {μ ν : PMF α} {ζ ζ' : ℝ≥0∞} (h : PClose μ ν ζ) (hζ : ζ ≤ ζ') :
    PClose μ ν ζ' :=
  fun f hf => (h f hf).trans (by gcongr)

theorem PClose.trans {μ ν ρ : PMF α} {ζ ζ' : ℝ≥0∞} (h : PClose μ ν ζ) (h' : PClose ν ρ ζ') :
    PClose μ ρ (ζ + ζ') :=
  fun f hf => (h f hf).trans (by
    calc pexp ν f + ζ ≤ pexp ρ f + ζ' + ζ := by gcongr; exact h' f hf
      _ = pexp ρ f + (ζ + ζ') := by ring)

/-- INTERNAL: closeness composes along `bind`; the kernels need only be close
on the support of the first law. -/
theorem PClose.bind {μ μ' : PMF α} {K K' : α → PMF β} {a b : ℝ≥0∞} (h : PClose μ μ' a)
    (hK : ∀ x ∈ μ.support, PClose (K x) (K' x) b) :
    PClose (μ.bind K) (μ'.bind K') (a + b) := by
  intro f hf
  rw [pexp_bind, pexp_bind]
  calc pexp μ (fun x => pexp (K x) f) ≤ pexp μ (fun x => pexp (K' x) f + b) :=
        pexp_mono_support μ fun x hx => hK x hx f hf
    _ = pexp μ (fun x => pexp (K' x) f) + b := pexp_add_const _ _ _
    _ ≤ pexp μ' (fun x => pexp (K' x) f) + a + b := by
        gcongr; exact h _ fun x => pexp_le_one _ _ hf
    _ = _ := by rw [add_assoc]

theorem PClose.map {μ ν : PMF α} {ζ : ℝ≥0∞} (h : PClose μ ν ζ) (g : α → β) :
    PClose (μ.map g) (ν.map g) ζ := by
  intro f hf
  rw [pexp_map, pexp_map]
  exact h _ fun a => hf (g a)

/-- INTERNAL: closeness transfers to event probabilities. -/
theorem PClose.outer_le {μ ν : PMF α} {ζ : ℝ≥0∞} (h : PClose μ ν ζ) (s : Set α) :
    μ.toOuterMeasure s ≤ ν.toOuterMeasure s + ζ := by
  rw [outer_eq_pexp, outer_eq_pexp]
  exact h _ fun a => by by_cases ha : a ∈ s <;> simp [ha]

/-- INTERNAL: one-sided closeness is symmetric for probability laws. -/
theorem PClose.symm {μ ν : PMF α} {ζ : ℝ≥0∞} (h : PClose μ ν ζ) : PClose ν μ ζ := by
  intro f hf
  have hc : ∀ a, 1 - f a ≤ 1 := fun a => tsub_le_self
  have hsplit : ∀ ρ : PMF α, pexp ρ f + pexp ρ (fun a => 1 - f a) = 1 := by
    intro ρ
    rw [pexp, pexp, ← ENNReal.tsum_add]
    simp_rw [← mul_add]
    simp_rw [add_tsub_cancel_of_le (hf _), mul_one]
    exact ρ.tsum_coe
  have h1 := h _ hc
  have hfin : pexp ν (fun a => 1 - f a) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (pexp_le_one _ _ hc)
  have key : pexp ν f + pexp ν (fun a => 1 - f a) ≤
      (pexp μ f + ζ) + pexp ν (fun a => 1 - f a) := by
    rw [hsplit ν]
    calc (1 : ℝ≥0∞) = pexp μ f + pexp μ (fun a => 1 - f a) := (hsplit μ).symm
      _ ≤ pexp μ f + (pexp ν (fun a => 1 - f a) + ζ) := by gcongr
      _ = _ := by ring
  exact (ENNReal.add_le_add_iff_right hfin).1 key

/-- INTERNAL: closeness from a pointwise excess whose total is at most `ζ`. -/
theorem PClose.of_pointwise {μ ν : PMF α} (g : α → ℝ≥0∞) (hg : ∀ a, μ a ≤ ν a + g a)
    {ζ : ℝ≥0∞} (hζ : ∑' a, g a ≤ ζ) : PClose μ ν ζ := by
  intro f hf
  calc pexp μ f ≤ ∑' a, (ν a * f a + g a) := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        calc μ a * f a ≤ (ν a + g a) * f a := by gcongr; exact hg a
          _ = ν a * f a + g a * f a := add_mul _ _ _
          _ ≤ ν a * f a + g a := by gcongr; exact mul_le_of_le_one_right' (hf a)
    _ = pexp ν f + ∑' a, g a := ENNReal.tsum_add
    _ ≤ pexp ν f + ζ := by gcongr

end

/-- INTERNAL: one more iteration of `loop`. -/
theorem loop_succ {β : Type} (f : ℕ → β → PMF β) (k : ℕ) (b : β) :
    loop f (k + 1) b = (loop f k b).bind (f k) := by
  simp only [loop, List.range_succ, List.foldlM_append, List.foldlM_cons, List.foldlM_nil]
  change (List.foldlM (fun b i => f i b) b (List.range k)).bind
      (fun x => (f k x).bind PMF.pure) = _
  simp [PMF.bind_pure]

@[simp] theorem loop_zero {β : Type} (f : ℕ → β → PMF β) (b : β) : loop f 0 b = PMF.pure b := rfl

/-- INTERNAL: closeness composes along `loop`, adding the per-step costs. -/
theorem PClose.loop {β : Type} {f g : ℕ → β → PMF β} {ζ : ℕ → ℝ≥0∞}
    (h : ∀ i x, PClose (f i x) (g i x) (ζ i)) (k : ℕ) (b : β) :
    PClose (Pseudocode.loop f k b) (Pseudocode.loop g k b) (∑ i ∈ Finset.range k, ζ i) := by
  induction k with
  | zero => simpa using PClose.refl (PMF.pure b) 0
  | succ k ih =>
    rw [loop_succ, loop_succ, Finset.sum_range_succ]
    exact ih.bind fun x _ => h k x

end Cellcounting.Analysis
