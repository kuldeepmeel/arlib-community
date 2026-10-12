import Esa22Copy.Meta.ModelClosure
import Mathlib.Data.Real.ENatENNReal
import Esa22Copy.Model.Prior
import Esa22Copy.Model.Run
import Esa22Copy.Interface.Encoding
import Esa22Copy.Interface.Pseudocode
import Esa22Copy.Interface.ProgramModel
import Esa22Copy.Analysis.FailBound
import Esa22Copy.Analysis.NonfailLeRelaxed
import Esa22Copy.Analysis.RelaxedErrorBound

/-!
# Accuracy of the F0-Estimator (`thm:main`, first clause)

`correct_proof`: with probability `≥ 1 - δ`, Algorithm 1 outputs a number in
`[(1-ε)F0, (1+ε)F0]` (esa22-final.tex:502; proof 513-524).

The assembly follows the paper.  `output_bridge` rewrites the program's output
law as `Pseudocode.answer`.  The error event `{o | ¬ Accurate}` contains `⊥`, so
`Pr[Error] ≤ Pr[Fail] + Pr[Error ∩ ¬Fail]` (`answer_error_le`), where the
second term is bounded by the relaxed Algorithm 2's error through the pointwise
domination `answer_some_le_relaxedAnswer` (claim `claim:errfail`).  Then
`Pr[Fail] ≤ δ/8` (`answer_none_le`, claim `lm:fail`) and
`Pr[Error₂] ≤ δ/2` (`relaxedAnswer_error_le`, claim `lm:error-fail`), and
`δ/8 + δ/2 ≤ δ` closes the complement bound.
-/

namespace Esa22Copy.Analysis

open Esa22Copy.Interface.Pseudocode

/-- INTERNAL: the error event `{o | ¬ Accurate}` of Algorithm 1 is covered by `⊥`
and the numeric errors; this is `Pr[Error] ≤ Pr[Fail] + Pr[Error ∩ ¬Fail]` with
the second term already bounded by Algorithm 2's error (claim `claim:errfail`).
TEXLINE: esa22-final.tex:513-524 -/
theorem answer_error_le {α : Type} [DecidableEq α] [Fintype α] (ε δ : ℝ) (s : List α) :
    (answer ε δ s).toOuterMeasure {o | ¬ Accurate ε (F0 s) o} ≤
      answer ε δ s none +
        (relaxedAnswer ε δ s).toOuterMeasure {c | ¬ Accurate ε (F0 s) (some c)} := by
  set B : Set ℕ := {c | ¬ Accurate ε (F0 s) (some c)}
  have hsub : {o | ¬ Accurate ε (F0 s) o} ⊆ {none} ∪ some '' B := by
    intro o ho
    cases o with
    | none => exact Or.inl rfl
    | some c => exact Or.inr ⟨c, ho, rfl⟩
  refine (MeasureTheory.measure_mono hsub).trans ((MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ ?_))
  · rw [PMF.toOuterMeasure_apply_singleton]
  · rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    refine le_of_eq_of_le ((Option.some_injective ℕ).tsum_eq ?_).symm ?_
    · intro o ho
      cases o with
      | none =>
        exfalso; apply ho
        exact Set.indicator_of_notMem (by rintro ⟨c, -, hc⟩; cases hc) _
      | some c => exact ⟨c, rfl⟩
    · refine ENNReal.tsum_le_tsum fun c => ?_
      by_cases hc : c ∈ B
      · rw [Set.indicator_of_mem (Set.mem_image_of_mem _ hc), Set.indicator_of_mem hc]
        exact answer_some_le_relaxedAnswer ε δ s c
      · rw [Set.indicator_of_notMem, Set.indicator_of_notMem hc]
        rintro ⟨c', hc', h⟩
        exact hc (Option.some_injective ℕ h ▸ hc')

end Esa22Copy.Analysis

section
open scoped ENNReal

/-- Proof-side owner for `Esa22Copy.esa22copy_correct`; its statement is fixed by the proof charter.

PAPER: esa22-final.tex:502 (accuracy clause; proof 513-524) -/
theorem Esa22Copy.Analysis.correct_proof (hprior : Prior) {n : ℕ} (s : List (Fin n)) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) : ENNReal.ofReal (1 - δ) ≤ (Esa22Copy.output ε δ s).toOuterMeasure {o | Esa22Copy.Accurate ε (Esa22Copy.F0 s) o} := by
  rw [(output_bridge ε δ s).1]
  set μ := Esa22Copy.Interface.Pseudocode.answer ε δ s
  set A : Set (Option ℕ) := {o | Esa22Copy.Accurate ε (Esa22Copy.F0 s) o}
  -- `Pr[Error] ≤ Pr[Fail] + Pr[Error₂] ≤ δ/8 + δ/2 ≤ δ`
  have herr : μ.toOuterMeasure Aᶜ ≤ ENNReal.ofReal δ := by
    refine (Esa22Copy.Analysis.answer_error_le ε δ s).trans ?_
    refine (add_le_add (Esa22Copy.Analysis.answer_none_le ε δ s hε0 hε1 hδ0 hδ1)
      (Esa22Copy.Analysis.relaxedAnswer_error_le ε δ s hε0 hε1 hδ0 hδ1)).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- complement rule: `Pr[A] = 1 - Pr[Aᶜ]`
  have hsum : μ.toOuterMeasure A + μ.toOuterMeasure Aᶜ = 1 := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
    simp only [Set.indicator_self_add_compl_apply]
    exact μ.tsum_coe
  have hne : μ.toOuterMeasure Aᶜ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top herr
  rw [ENNReal.eq_sub_of_add_eq hne hsum, ENNReal.ofReal_sub _ hδ0.le, ENNReal.ofReal_one]
  exact tsub_le_tsub_left herr 1

end

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · closed · all children proved (`relaxed_domination` replaces the coupling of tex:684; Chernoff from arlib); only `output_bridge` upstream remained `sorry` in its published olean
* r1 · assembled · `correct_proof` closed from `answer_none_le` (proved), `answer_some_le_relaxedAnswer` (proved), `relaxedAnswer_error_le` (open, handed off)
-/
