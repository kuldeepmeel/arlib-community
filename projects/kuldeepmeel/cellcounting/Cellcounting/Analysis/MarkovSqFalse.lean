import Cellcounting.Analysis.PmfClose

/-!
# `oa_markov_sq` is false without `0 ≤ t`

`Cellcounting.Analysis.oa_markov_sq` (in `ObserveAccurate.lean`) states a one-sided
Markov bound for a squared deviation with no sign hypothesis on the threshold `t`.
When `t < 0`, the event `{a | ¬ |f a - c| ≤ t}` is the whole space (since `|f a - c|
≥ 0 > t` always), so its probability is `1`; but the right side can be `0`, e.g. when
`f` is a.e. equal to `c` on the support of `μ`. The statement as written is false.
-/

namespace Cellcounting.Analysis

open scoped ENNReal

/-- **DISPROVED**: `oa_markov_sq` as stated, with `μ = PMF.pure 0`, `f = id`, `c = 0`,
`t = -1`: the left side is `1` and the right side is `0`. -/
theorem oa_markov_sq_false :
    ¬ ∀ {α : Type} (μ : PMF α) (f : α → ℝ) (c t : ℝ),
      μ.toOuterMeasure {a | ¬ |f a - c| ≤ t} ≤
        pexp μ (fun a => ENNReal.ofReal ((f a - c) ^ 2)) * (ENNReal.ofReal (t ^ 2))⁻¹ := by
  intro h
  have key := h (PMF.pure (0 : ℝ)) id 0 (-1)
  simp only [id] at key
  have hset : {a : ℝ | ¬ |a - 0| ≤ (-1 : ℝ)} = Set.univ := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    nlinarith [abs_nonneg (a - 0)]
  rw [hset] at key
  have h1 : (PMF.pure (0 : ℝ)).toOuterMeasure Set.univ = 1 := by
    simp [PMF.toOuterMeasure_apply]
  rw [h1] at key
  have h2 : pexp (PMF.pure (0 : ℝ)) (fun a => ENNReal.ofReal ((a - 0 : ℝ) ^ 2)) = 0 := by
    rw [pexp_pure]; norm_num
  rw [h2] at key
  simp at key

end Cellcounting.Analysis
