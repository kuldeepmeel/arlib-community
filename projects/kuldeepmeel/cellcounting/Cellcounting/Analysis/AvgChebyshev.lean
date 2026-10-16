import Cellcounting.Analysis.PmfClose

/-!
# Chebyshev's inequality for an average of independent draws

`evaluation.tex:398-406`: an average of `N` independent draws of a `[0, c]`-valued
observable with mean `m > 0` has relative error more than `σ` with probability at
most `Var/(N σ² m²) ≤ c/(N σ² m)`, since `Var ≤ E X² ≤ c m`.

The averages of `Pseudocode` are sums accumulated by `loop` and then divided by
`N`; `sumLoop ν N` is that accumulated sum.  Everything is computed with
`ENNReal`-valued expectations: the first two moments of the sum satisfy
`E S_N = N m₁` and `E S_N² = N m₂ + N(N-1) m₁²`, and the identity
`(s - M)² + 2 M s = s² + M²` for `s ≥ 0` gives `E (S_N - N m)² ≤ N m₂` without
signed sums.  Markov's inequality then finishes (`avg_chebyshev`).
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal

/-- INTERNAL: the sum of `N` independent draws from `ν`, as `loop` accumulates it. -/
noncomputable def sumLoop (ν : PMF ℚ) (N : ℕ) : PMF ℚ :=
  loop (fun _ s => ν.map (s + ·)) N 0

theorem sumLoop_succ (ν : PMF ℚ) (N : ℕ) :
    sumLoop ν (N + 1) = (sumLoop ν N).bind fun s => ν.map (s + ·) :=
  loop_succ _ _ _

/-- INTERNAL: expectations agree when the functions agree on the support. -/
theorem pexp_congr_support {α : Type*} (μ : PMF α) {f g : α → ℝ≥0∞}
    (h : ∀ a ∈ μ.support, f a = g a) : pexp μ f = pexp μ g :=
  le_antisymm (pexp_mono_support μ fun a ha => (h a ha).le)
    (pexp_mono_support μ fun a ha => (h a ha).ge)

theorem pexp_add {α : Type*} (μ : PMF α) (f g : α → ℝ≥0∞) :
    pexp μ (fun a => f a + g a) = pexp μ f + pexp μ g := by
  simp only [pexp, mul_add]; exact ENNReal.tsum_add

theorem pexp_const_mul {α : Type*} (μ : PMF α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    pexp μ (fun a => c * f a) = c * pexp μ f := by
  simp only [pexp]
  rw [← ENNReal.tsum_mul_left]; congr 1; funext a; ring

theorem pexp_const {α : Type*} (μ : PMF α) (c : ℝ≥0∞) : pexp μ (fun _ => c) = c := by
  simpa using pexp_add_const μ (fun _ => 0) c |>.trans (by simp [pexp])

section
variable (ν : PMF ℚ) (c : ℝ) (hsupp : ∀ x ∈ ν.support, 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ c)
include hsupp

theorem sumLoop_nonneg (N : ℕ) : ∀ s ∈ (sumLoop ν N).support, 0 ≤ (s : ℝ) := by
  induction N with
  | zero => intro s hs; simp [sumLoop, PMF.support_pure] at hs; simp [hs]
  | succ N ih =>
    intro s hs
    rw [sumLoop_succ, PMF.mem_support_bind_iff] at hs
    obtain ⟨s0, hs0, hs⟩ := hs
    rw [PMF.support_map] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    push_cast
    exact add_nonneg (ih s0 hs0) (hsupp x hx).1

/-- INTERNAL: the first moment of the sum. -/
theorem sumLoop_m1 (N : ℕ) :
    pexp (sumLoop ν N) (fun s => ENNReal.ofReal s) =
      N * pexp ν (fun x => ENNReal.ofReal x) := by
  induction N with
  | zero => simp [sumLoop, pexp_pure]
  | succ N ih =>
    rw [sumLoop_succ, pexp_bind]
    have : ∀ s ∈ (sumLoop ν N).support,
        pexp (ν.map (s + ·)) (fun s => ENNReal.ofReal s) =
          ENNReal.ofReal s + pexp ν (fun x => ENNReal.ofReal x) := by
      intro s hs
      rw [pexp_map, add_comm (ENNReal.ofReal _), ← pexp_add_const]
      apply pexp_congr_support
      intro x hx
      simp only [Function.comp, Rat.cast_add]
      rw [add_comm (s : ℝ)]
      exact ENNReal.ofReal_add (hsupp x hx).1 (sumLoop_nonneg ν c hsupp N s hs)
    rw [pexp_congr_support _ this, pexp_add_const, ih]
    push_cast; ring

/-- INTERNAL: the second moment of the sum. -/
theorem sumLoop_m2 (N : ℕ) :
    pexp (sumLoop ν N) (fun s => ENNReal.ofReal ((s : ℝ) ^ 2)) =
      N * pexp ν (fun x => ENNReal.ofReal ((x : ℝ) ^ 2)) +
        (N * (N - 1 : ℕ) : ℝ≥0∞) * pexp ν (fun x => ENNReal.ofReal x) ^ 2 := by
  induction N with
  | zero => simp [sumLoop, pexp_pure]
  | succ N ih =>
    rw [sumLoop_succ, pexp_bind]
    set m1 := pexp ν (fun x => ENNReal.ofReal x)
    set m2 := pexp ν (fun x => ENNReal.ofReal ((x : ℝ) ^ 2))
    have : ∀ s ∈ (sumLoop ν N).support,
        pexp (ν.map (s + ·)) (fun s => ENNReal.ofReal ((s : ℝ) ^ 2)) =
          ENNReal.ofReal ((s : ℝ) ^ 2) + 2 * m1 * ENNReal.ofReal s + m2 := by
      intro s hs
      have hs0 := sumLoop_nonneg ν c hsupp N s hs
      rw [pexp_map]
      have h1 : ∀ x ∈ ν.support, ((fun s : ℚ => ENNReal.ofReal ((s : ℝ) ^ 2)) ∘ (s + ·)) x =
          ((2 * ENNReal.ofReal s) * ENNReal.ofReal x + ENNReal.ofReal ((s : ℝ) ^ 2)) +
            ENNReal.ofReal ((x : ℝ) ^ 2) := by
        intro x hx
        have hx0 := (hsupp x hx).1
        simp only [Function.comp, Rat.cast_add]
        rw [show ((s : ℝ) + x) ^ 2 = (2 * s * x + (s : ℝ) ^ 2) + (x : ℝ) ^ 2 by ring,
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity)]
        simp
      rw [pexp_congr_support _ h1, pexp_add, pexp_add_const, pexp_const_mul]
      ring
    rw [pexp_congr_support _ this, pexp_add_const, pexp_add, pexp_const_mul, ih,
      sumLoop_m1 ν c hsupp N]
    rcases N with _ | N
    · simp
    · push_cast
      ring

/-- INTERNAL: the second moment of one draw is at most `c` times its mean. -/
theorem m2_le (hc : 0 ≤ c) :
    pexp ν (fun x => ENNReal.ofReal ((x : ℝ) ^ 2)) ≤
      ENNReal.ofReal c * pexp ν (fun x => ENNReal.ofReal x) := by
  rw [← pexp_const_mul]
  apply pexp_mono_support
  intro x hx
  obtain ⟨h0, h1⟩ := hsupp x hx
  rw [← ENNReal.ofReal_mul hc]
  apply ENNReal.ofReal_le_ofReal
  nlinarith

/-- **Chebyshev for an average** (`evaluation.tex:398-406`): an average of `N`
independent `[0, c]`-valued draws with mean `m > 0` leaves `[(1-σ)m, (1+σ)m]` with
probability at most `c/(N σ² m)`.
TEXLINE: sections/evaluation.tex:398-406 -/
theorem avg_chebyshev (hc : 0 ≤ c) (m : ℝ) (hm : pexp ν (fun x => ENNReal.ofReal x) =
      ENNReal.ofReal m) (hm0 : 0 < m) (N : ℕ) (hN : 0 < N) (σ : ℝ) (hσ : 0 < σ) :
    ((sumLoop ν N).map (· / (N : ℚ))).toOuterMeasure
        {a | ¬ ((1 - σ) * m ≤ (a : ℝ) ∧ (a : ℝ) ≤ (1 + σ) * m)} ≤
      ENNReal.ofReal (c / (N * σ ^ 2 * m)) := by
  set μ := sumLoop ν N
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set M : ℝ := N * m with hM
  have hM0 : 0 ≤ M := by positivity
  set g : ℚ → ℝ≥0∞ := fun s => ENNReal.ofReal (((s : ℝ) - M) ^ 2)
  -- `E g ≤ N c m`
  have hid : pexp μ g + ENNReal.ofReal (2 * M) * pexp μ (fun s => ENNReal.ofReal s) =
      pexp μ (fun s => ENNReal.ofReal ((s : ℝ) ^ 2)) + ENNReal.ofReal (M ^ 2) := by
    rw [← pexp_const_mul, ← pexp_add, ← pexp_add_const]
    apply pexp_congr_support
    intro s hs
    have hs0 := sumLoop_nonneg ν c hsupp N s hs
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
      (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  rw [sumLoop_m1 ν c hsupp N, sumLoop_m2 ν c hsupp N, hm] at hid
  have hm2 := m2_le ν c hsupp hc
  rw [hm] at hm2
  have hEg : pexp μ g ≤ N * (ENNReal.ofReal c * ENNReal.ofReal m) := by
    have key : pexp μ g + ENNReal.ofReal (2 * M) * (N * ENNReal.ofReal m) ≤
        N * (ENNReal.ofReal c * ENNReal.ofReal m) + ENNReal.ofReal (2 * M) * (N * ENNReal.ofReal m) := by
      rw [hid]
      have e1 : ((N * (N - 1 : ℕ) : ℝ≥0∞)) * ENNReal.ofReal m ^ 2 + ENNReal.ofReal (M ^ 2) ≤
          ENNReal.ofReal (2 * M) * (N * ENNReal.ofReal m) := by
        rw [show ((N : ℝ≥0∞)) = ENNReal.ofReal N by simp,
          show (((N - 1 : ℕ) : ℝ≥0∞)) = ENNReal.ofReal ((N - 1 : ℕ) : ℝ) by simp,
          ← ENNReal.ofReal_pow hm0.le, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have : ((N - 1 : ℕ) : ℝ) = N - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [this, hM]; nlinarith [sq_nonneg (m : ℝ)]
      calc N * pexp ν (fun x => ENNReal.ofReal ((x : ℝ) ^ 2)) +
            ((N * (N - 1 : ℕ) : ℝ≥0∞)) * ENNReal.ofReal m ^ 2 + ENNReal.ofReal (M ^ 2)
          = N * pexp ν (fun x => ENNReal.ofReal ((x : ℝ) ^ 2)) +
            (((N * (N - 1 : ℕ) : ℝ≥0∞)) * ENNReal.ofReal m ^ 2 + ENNReal.ofReal (M ^ 2)) := by ring
        _ ≤ _ := by gcongr
    have hfin : ENNReal.ofReal (2 * M) * (N * ENNReal.ofReal m) ≠ ⊤ := by
      apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
    exact (ENNReal.add_le_add_iff_right hfin).1 key
  -- Markov
  set t : ℝ := (N * σ * m) ^ 2
  have ht : 0 < t := by positivity
  rw [PMF.toOuterMeasure_map_apply, outer_eq_pexp]
  have hpt : ∀ s, (((· / (N : ℚ)) ⁻¹' {a : ℚ | ¬((1 - σ) * m ≤ (a : ℝ) ∧ (a : ℝ) ≤ (1 + σ) * m)}).indicator
      (1 : ℚ → ℝ≥0∞)) s ≤ g s * (ENNReal.ofReal t)⁻¹ := by
    intro s
    by_cases hs : s ∈ ((· / (N : ℚ)) ⁻¹' {a : ℚ | ¬((1 - σ) * m ≤ (a : ℝ) ∧ (a : ℝ) ≤ (1 + σ) * m)})
    · rw [Set.indicator_of_mem hs]
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Rat.cast_div, Rat.cast_natCast] at hs
      have hfar : t ≤ ((s : ℝ) - M) ^ 2 := by
        have : N * σ * m ≤ |(s : ℝ) - M| := by
          by_contra hlt
          push_neg at hlt
          rw [abs_lt] at hlt
          apply hs
          constructor
          · rw [le_div_iff₀ hNr]; nlinarith
          · rw [div_le_iff₀ hNr]; nlinarith
        have h0 : 0 ≤ N * σ * m := by positivity
        calc t = (N * σ * m) ^ 2 := rfl
          _ ≤ |(s : ℝ) - M| ^ 2 := pow_le_pow_left₀ h0 this 2
          _ = _ := sq_abs _
      rw [Pi.one_apply, ← div_eq_mul_inv,
        ENNReal.le_div_iff_mul_le (Or.inl (by simp [ht])) (Or.inl ENNReal.ofReal_ne_top), one_mul]
      exact ENNReal.ofReal_le_ofReal hfar
    · rw [Set.indicator_of_notMem hs]; exact zero_le
  calc pexp μ _ ≤ pexp μ (fun s => g s * (ENNReal.ofReal t)⁻¹) := pexp_mono μ hpt
    _ = pexp μ g * (ENNReal.ofReal t)⁻¹ := by
        rw [pexp, pexp, ← ENNReal.tsum_mul_right]; congr 1; funext s; ring
    _ ≤ N * (ENNReal.ofReal c * ENNReal.ofReal m) * (ENNReal.ofReal t)⁻¹ := by gcongr
    _ = ENNReal.ofReal (c / (N * σ ^ 2 * m)) := by
        rw [show ((N : ℝ≥0∞)) = ENNReal.ofReal N by simp, ← ENNReal.ofReal_mul hc,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_inv_of_pos ht,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring

end

end Cellcounting.Analysis
