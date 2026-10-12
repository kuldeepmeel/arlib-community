import Esa22Copy.Interface.Pseudocode
import Esa22Copy.Interface.ProgramModel
import Esa22Copy.Analysis.AccuracyProof
import Esa22Copy.Analysis.SpaceProof
import Esa22Copy.Analysis.SpaceBitsProof
import Esa22Copy.Analysis.TimeProof

/-!
# The proof-side root

This module is created when `Interface/` is finished.  A successful
correctness reduction writes the pseudocode-side capstone here; until then the
decomposition may build its direct proof underneath `Analysis/`.

`Esa22Copy.Analysis.main_of_parts` assembles the four claims of `thm:main`
(accuracy, exact space, asymptotic space, expected time) into the capstone's
conjunction.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Esa22Copy

/-- Assembly of `thm:main` (esa22-final.tex:501-503): the four claims —
accuracy, exact space, asymptotic space, expected time — packaged as one
conjunction.  The surface theorem feeds in its four component theorems, so each
remains reached by the capstone. -/
theorem Analysis.main_of_parts
    (hcorrect : ∀ {n : ℕ} (s : List (Fin n)) (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        ENNReal.ofReal (1 - δ) ≤ (output ε δ s).toOuterMeasure {o | Accurate ε (F0 s) o})
    (hspace : ∀ {n : ℕ} (s : List (Fin n)) (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        Arlib.Computation.worstSpace Arlib.Computation.Cell.roster 0 (run ε δ s)
          ≤ (thresh ε δ s.length : ℕ∞))
    (hbigO : ∃ C : ℝ, ∀ (n : ℕ) (s : List (Fin n)) (ε δ : ℝ),
      0 < ε → ε < 1 → 0 < δ → δ < 1 → 2 ≤ n → 2 ≤ s.length →
        (Arlib.Computation.worstSpace Arlib.Computation.Cell.roster 0 (run ε δ s) : ℝ≥0∞)
            * (bitsPerItem n : ℝ≥0∞)
          ≤ ENNReal.ofReal (C * (1 / ε ^ 2) * Real.logb 2 n
              * (Real.logb 2 s.length + Real.logb 2 (1 / δ))))
    (htime : ∃ C : ℕ, ∀ (n : ℕ) (s : List (Fin n)) (ε δ : ℝ),
      0 < ε → ε < 1 → 0 < δ → δ < 1 →
        expectedSteps Esa22Copy.Model.Operations.rate (run ε δ s)
          ≤ (C : ℝ≥0∞) * ((s.length : ℝ≥0∞) + 1)) :
    (∀ (n : ℕ) (s : List (Fin n)) (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        ENNReal.ofReal (1 - δ) ≤ (output ε δ s).toOuterMeasure {o | Accurate ε (F0 s) o}) ∧
    (∀ (n : ℕ) (s : List (Fin n)) (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        Arlib.Computation.worstSpace Arlib.Computation.Cell.roster 0 (run ε δ s)
          ≤ (thresh ε δ s.length : ℕ∞)) ∧
    (∃ C : ℝ, ∀ (n : ℕ) (s : List (Fin n)) (ε δ : ℝ),
      0 < ε → ε < 1 → 0 < δ → δ < 1 → 2 ≤ n → 2 ≤ s.length →
        (Arlib.Computation.worstSpace Arlib.Computation.Cell.roster 0 (run ε δ s) : ℝ≥0∞)
            * (bitsPerItem n : ℝ≥0∞)
          ≤ ENNReal.ofReal (C * (1 / ε ^ 2) * Real.logb 2 n
              * (Real.logb 2 s.length + Real.logb 2 (1 / δ)))) ∧
    (∃ C : ℕ, ∀ (n : ℕ) (s : List (Fin n)) (ε δ : ℝ),
      0 < ε → ε < 1 → 0 < δ → δ < 1 →
        expectedSteps Esa22Copy.Model.Operations.rate (run ε δ s)
          ≤ (C : ℝ≥0∞) * ((s.length : ℝ≥0∞) + 1)) :=
  ⟨fun _ s ε δ hε0 hε1 hδ0 hδ1 => hcorrect s ε δ hε0 hε1 hδ0 hδ1,
   fun _ s ε δ hε0 hε1 hδ0 hδ1 => hspace s ε δ hε0 hε1 hδ0 hδ1,
   hbigO,
   htime⟩

end Esa22Copy
