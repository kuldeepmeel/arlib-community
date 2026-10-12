import Esa22Copy.Analysis.RelaxedAlgorithm

/-!
# Algorithm 1 off `⊥` is dominated by Algorithm 2

The coupling step of claim `claim:errfail` (esa22-final.tex:545-562): Algorithm 1
behaves exactly as the relaxed Algorithm 2 until it outputs `⊥`.  As laws, this
is a pointwise domination: for every final state `x`, the probability that
Algorithm 1 ends (not at `⊥`) in `x` is at most the probability that Algorithm 2
ends in `x`.  Hence `Pr[Error ∩ ¬Fail] ≤ Pr[Error₂]` for any error event.
-/

set_option autoImplicit false

namespace Esa22Copy.Analysis

open Esa22Copy.Interface (Snapshot)
open Esa22Copy.Interface.Pseudocode

variable {α : Type} [DecidableEq α] [Fintype α]

/-- INTERNAL: after `⊥`, Algorithm 1's loop stays at `⊥`. -/
theorem loop_none (thr w : ℕ) (s : List α) :
    loop thr w s (none : Option (Snapshot α)) = PMF.pure none := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    show (step thr w none a).bind (loop thr w s) = _
    simp [step, ih]

omit [DecidableEq α] [Fintype α] in
/-- INTERNAL: an indicator of `some y = some z` is at most that of `y = z`. -/
theorem ite_some_le {β : Type} (y z : β) (r : ENNReal) {_ : Decidable (some y = some z)}
    {_ : Decidable (y = z)} : (if some y = some z then r else 0) ≤ if y = z then r else 0 := by
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (Option.some_injective _ h1) h2
  · exact bot_le
  · exact le_rfl

/-- INTERNAL: one iteration of Algorithm 1 landing on `some y` is at most one
iteration of Algorithm 2 landing on `y`.
TEXLINE: esa22-final.tex:552 -/
theorem step_some_le_relaxedStep (thr w : ℕ) (st y : Snapshot α) (a : α) :
    step thr w (some st) a (some y) ≤ relaxedStep thr w st a y := by
  simp only [step, relaxedStep, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun X => mul_le_mul' le_rfl ?_
  split_ifs
  · simp only [PMF.map_apply]
    refine ENNReal.tsum_le_tsum fun Y => ?_
    by_cases hY : full thr Y = true
    · simp [hY]
    · rw [if_neg hY]
      exact ite_some_le _ _ _
  · simp only [PMF.pure_apply]
    exact ite_some_le _ _ _

/-- **Claim `claim:errfail`, the coupling** (esa22-final.tex:552-557): from any
state, the probability that Algorithm 1 ends in `some x` is at most the
probability that Algorithm 2 ends in `x`.

PAPER: esa22-final.tex:552-557 -/
theorem loop_some_le_relaxedLoop (thr w : ℕ) (s : List α) (st x : Snapshot α) :
    loop thr w s (some st) (some x) ≤ relaxedLoop thr w s st x := by
  induction s generalizing st with
  | nil => exact ite_some_le _ _ _
  | cons a s ih =>
    show ((step thr w (some st) a).bind (loop thr w s)) (some x) ≤
      ((relaxedStep thr w st a).bind (relaxedLoop thr w s)) x
    rw [PMF.bind_apply, PMF.bind_apply]
    refine le_of_eq_of_le ((Option.some_injective (Snapshot α)).tsum_eq ?_).symm ?_
    rotate_left
    · exact ENNReal.tsum_le_tsum fun y =>
        mul_le_mul' (step_some_le_relaxedStep thr w st y a) (ih y)
    · intro o ho
      cases o with
      | none => simp [loop_none, PMF.pure_apply] at ho
      | some y => exact ⟨y, rfl⟩

/-- **`Pr[Error ∩ ¬Fail] ≤ Pr[Error₂]`, pointwise** (esa22-final.tex:557): the
probability that Algorithm 1 outputs the number `c` is at most the probability
that Algorithm 2 outputs `c`.

PAPER: esa22-final.tex:552-557 -/
theorem answer_some_le_relaxedAnswer (ε δ : ℝ) (s : List α) (c : ℕ) :
    answer ε δ s (some c) ≤ relaxedAnswer ε δ s c := by
  simp only [answer, relaxedAnswer, PMF.map_apply]
  refine le_of_eq_of_le ((Option.some_injective (Snapshot α)).tsum_eq ?_).symm ?_
  rotate_left
  · refine ENNReal.tsum_le_tsum fun x => ?_
    split_ifs with h1 h2 h2
    · exact loop_some_le_relaxedLoop _ _ _ _ _
    · exact absurd (Option.some_injective ℕ h1) h2
    · exact bot_le
    · exact le_rfl
  · intro o ho
    cases o with
    | none => simp [report] at ho
    | some y => exact ⟨y, rfl⟩

end Esa22Copy.Analysis
