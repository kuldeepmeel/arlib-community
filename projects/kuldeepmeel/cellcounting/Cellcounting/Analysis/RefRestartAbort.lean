import Cellcounting.Analysis.RefExperiment
import Cellcounting.Analysis.RefRestartUsedLe
import Cellcounting.Model.Prior

/-!
# The capped restart rarely aborts (`eq:alg-cap-probability`)

`prop:annealing`, the cap bound (`algorithm.tex:298-311`).  Fix stored multipliers
`w^(1..j)` good at their own parameters.  The capped reference restart of phase `j`,
started from the `μ₀` draw, aborts with probability at most `1/[100(H+1)]`.

In the paper: the capped restart aborts only when the virtual (uncapped) restart
uses more than `B_ret` transitions.  Its expected cost is at most `20 p² H τ`
(warm return cost of `lem:trace`, with the warm-start bound `≤ 4μ_a` in every stage
and `π(A) ≥ 1/(5p²)` from `eq:type-mass-bounds`), and Markov's inequality with
`B_ret = 2000 p² (H+1)² τ` gives `H/[100(H+1)²] ≤ 1/[100(H+1)]`.  For `j = 0` the
restart is finished from the start and never aborts.

Here the Markov step is taken on the capped counter itself: an aborted restart has used
exactly `B_ret` transitions (`refRestart_aborted_used`), so
`B_ret · P(abort) ≤ E[used] ≤ 20 p² j τ` (`refRestart_used_le`, the warm-return-cost
expectation bound, in its own file), and `20 p² j τ · 100 (H + 1) ≤ B_ret`.
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal

/-- INTERNAL: one capped restart iteration keeps `used ≤ B_ret`, and an abort happens
only with `used = B_ret`.
TEXLINE: sections/algorithm.tex:214-225 -/
theorem refRestartStep_inv (I : Instance) (ε δ : ℚ) (ws : ℕ → ℕ → ℕ → ℚ) (j : ℕ)
    (st : Restart)
    (hst : st.used ≤ BretParam I ε δ ∧ (st.aborted = true → st.used = BretParam I ε δ))
    (r : Restart) (hr : r ∈ (refRestartStep I ε δ ws j st).support) :
    r.used ≤ BretParam I ε δ ∧ (r.aborted = true → r.used = BretParam I ε δ) := by
  unfold refRestartStep at hr
  split_ifs at hr with h1 h2 h3 h4
  · rw [(PMF.mem_support_pure_iff _ _).1 hr]; exact hst
  · rw [(PMF.mem_support_pure_iff _ _).1 hr]; exact hst
  · rw [(PMF.mem_support_pure_iff _ _).1 hr]
    exact ⟨hst.1, fun _ => le_antisymm hst.1 h3⟩
  all_goals
    obtain ⟨S', -, hr⟩ := (PMF.mem_support_bind_iff _ _ _).1 hr
    have h3' : st.used + 1 ≤ BretParam I ε δ := Nat.lt_of_not_le h3
    split at hr <;>
      · rw [(PMF.mem_support_pure_iff _ _).1 hr]
        exact ⟨h3', fun h => by simp at h⟩

/-- INTERNAL: an aborted capped restart has used exactly `B_ret` transitions.
TEXLINE: sections/algorithm.tex:214-225 -/
theorem refRestart_aborted_used (I : Instance) (ε δ : ℚ) (ws : ℕ → ℕ → ℕ → ℚ) (j : ℕ)
    (S0 : Finset ℕ) (r : Restart) (hr : r ∈ (refRestart I ε δ ws j S0).support)
    (ha : r.aborted = true) : r.used = BretParam I ε δ := by
  suffices h : ∀ k, ∀ r ∈ (loop (fun _ st => refRestartStep I ε δ ws j st) k
      ⟨S0, 1, 0, 0, decide (j = 0), false⟩).support,
      r.used ≤ BretParam I ε δ ∧ (r.aborted = true → r.used = BretParam I ε δ) from
    (h _ r hr).2 ha
  intro k
  induction k with
  | zero =>
    intro r hr
    rw [loop_zero, PMF.support_pure, Set.mem_singleton_iff] at hr
    subst hr; simp
  | succ k ih =>
    intro r hr
    rw [loop_succ] at hr
    obtain ⟨st, hst, hr⟩ := (PMF.mem_support_bind_iff _ _ _).1 hr
    exact refRestartStep_inv I ε δ ws j st (ih st hst) r hr

/-- INTERNAL: `τ > 0` once `p > 0` (`C_d ≥ 8`).
TEXLINE: sections/algorithm.tex:20-40 -/
theorem τParam_pos_of_p (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) :
    0 < τParam I ε δ := by
  have hp' : 0 < pSmall I ε δ := Nat.pos_of_ne_zero hp
  unfold τParam KobsParam CdParam
  positivity

/-- **The capped restart rarely aborts** (`eq:alg-cap-probability`): with good stored
multipliers `w^(0..j)`, the capped reference restart of phase `j` from the `μ₀` draw
aborts with probability at most `1/[100(H+1)]`.
PAPER: sections/algorithm.tex:298-311 -/
theorem refRestart_abort_le (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (ws : ℕ → ℕ → ℕ → ℚ) (hgood : ∀ a ≤ j, goodMult I ε δ a (ws a)) :
    ((refMu0 I ε δ).bind (refRestart I ε δ ws j)).toOuterMeasure {r | r.aborted = true} ≤
      1 / (100 * ((HParam I ε δ : ℝ≥0∞) + 1)) := by
  have hused := refRestart_used_le hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj ws hgood
  set μ := (refMu0 I ε δ).bind (refRestart I ε δ ws j) with hμ
  set B := BretParam I ε δ with hB
  -- Markov's inequality: an aborted restart has used exactly `B_ret` transitions.
  have hM : (B : ℝ≥0∞) * μ.toOuterMeasure {r | r.aborted = true} ≤
      pexp μ (fun r => (r.used : ℝ≥0∞)) := by
    rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun r => ?_
    by_cases ha : r.aborted = true
    · rw [Set.indicator_of_mem (show r ∈ {r : Restart | r.aborted = true} from ha)]
      by_cases hr : r ∈ μ.support
      · obtain ⟨S0, -, hr⟩ := (PMF.mem_support_bind_iff _ _ _).1 hr
        show (B : ℝ≥0∞) * μ r ≤ μ r * (r.used : ℝ≥0∞)
        rw [refRestart_aborted_used I ε δ ws j S0 r hr ha, mul_comm]
      · rw [PMF.mem_support_iff, not_not] at hr
        simp [hr]
    · rw [Set.indicator_of_notMem (show r ∉ {r : Restart | r.aborted = true} from ha)]
      simp
  -- The arithmetic of `eq:alg-cap-probability`: `20 p² j τ · 100 (H + 1) ≤ B_ret`.
  have hp' : 0 < pSmall I ε δ := Nat.pos_of_ne_zero hp
  have hτ := τParam_pos_of_p I ε δ hp
  have hnat : 20 * pSmall I ε δ ^ 2 * j * τParam I ε δ * (100 * (HParam I ε δ + 1)) ≤ B := by
    rw [hB, BretParam]
    have hj1 : j ≤ HParam I ε δ + 1 := by omega
    calc 20 * pSmall I ε δ ^ 2 * j * τParam I ε δ * (100 * (HParam I ε δ + 1))
        = 2000 * pSmall I ε δ ^ 2 * j * (HParam I ε δ + 1) * τParam I ε δ := by ring
      _ ≤ 2000 * pSmall I ε δ ^ 2 * (HParam I ε δ + 1) * (HParam I ε δ + 1) *
          τParam I ε δ := by gcongr
      _ = _ := by ring
  have hcast : 20 * (pSmall I ε δ : ℝ≥0∞) ^ 2 * (j : ℝ≥0∞) * (τParam I ε δ : ℝ≥0∞) *
      (100 * ((HParam I ε δ : ℝ≥0∞) + 1)) ≤ (B : ℝ≥0∞) := by exact_mod_cast hnat
  have hB0 : (B : ℝ≥0∞) ≠ 0 := by
    refine Nat.cast_ne_zero.2 (Nat.pos_iff_ne_zero.1 ?_)
    rw [hB, BretParam]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos hp' 2))
      (pow_pos (Nat.succ_pos _) 2)) hτ
  have hD0 : (100 * ((HParam I ε δ : ℝ≥0∞) + 1)) ≠ 0 :=
    mul_ne_zero (by norm_num) (add_ne_zero.2 (Or.inr one_ne_zero))
  have hDt : (100 * ((HParam I ε δ : ℝ≥0∞) + 1)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top _, ENNReal.one_ne_top⟩)
  rw [ENNReal.le_div_iff_mul_le (Or.inl hD0) (Or.inl hDt)]
  rw [← ENNReal.mul_le_mul_iff_right hB0 (ENNReal.natCast_ne_top B), mul_one, ← mul_assoc]
  calc (B : ℝ≥0∞) * μ.toOuterMeasure {r | r.aborted = true} *
        (100 * ((HParam I ε δ : ℝ≥0∞) + 1))
      ≤ 20 * (pSmall I ε δ : ℝ≥0∞) ^ 2 * (j : ℝ≥0∞) * (τParam I ε δ : ℝ≥0∞) *
          (100 * ((HParam I ε δ : ℝ≥0∞) + 1)) :=
        mul_le_mul_left (hM.trans hused) _
    _ ≤ B := hcast

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · reduced · Markov on `used`; expectation bound `refRestart_used_le` in `RefRestartUsedLe.lean`
-/
