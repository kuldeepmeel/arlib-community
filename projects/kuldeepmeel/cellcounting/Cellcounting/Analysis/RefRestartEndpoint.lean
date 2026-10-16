import Cellcounting.Analysis.RefChainLaw
import Cellcounting.Analysis.PmfClose
import Cellcounting.Analysis.StageEndpoint
import Cellcounting.Analysis.RefMu0Law
import Cellcounting.Model.Prior

/-!
# The endpoint of a non-aborted capped restart is close to `μ_j`

`prop:annealing`, the endpoint half (`algorithm.tex:283-296`, `312-313`).  Fix stored
multipliers `w^(1..j)` good at their own parameters.  The capped reference restart of
phase `j`, started from the `μ₀` draw, ends without abort at `S` with probability at
most `(3/2) μ_j(S)`.

In the paper: a non-aborted capped restart follows the virtual (uncapped) restart, so
this sub-law is at most the virtual endpoint law.  For `j = 0` that law is the `μ₀`
draw, which is `μ_0` (`lem:initialization`).  For `j ≥ 1` the endpoint is that of `τ`
trace steps of `P_{j, w^(j)}` from a transversal; by `eq:trace-relative-mixing`
(`lem:trace`) and `eq:alg-minimum-mass` its pointwise relative error is at most
`2^M exp(-τ/K_obs) = 2^M exp(-2(M+5)) ≤ e^{-10}`, `M = H + p + K`.  The paper only
records that this is `< 1` (endpoint `≤ 2μ_j`); the constant `3/2` used here is what the
same computation gives, and is what lets `restart_coupling` redraw the second
coordinate after an abort.
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal

/-- INTERNAL: a `loop` whose step ignores the index, unrolled at its first iteration. -/
theorem loop_const_succ {β : Type} (g : β → PMF β) (k : ℕ) (b : β) :
    loop (fun _ => g) (k + 1) b = (g b).bind (loop (fun _ => g) k) := by
  induction k generalizing b with
  | zero => rw [loop_succ, loop_zero, PMF.pure_bind]; exact (PMF.bind_pure _).symm
  | succ k ih =>
    rw [loop_succ, ih, PMF.bind_bind]
    congr 1; funext x; rw [loop_succ]

/-- INTERNAL: a fixed point of the step is a fixed point of the `loop`. -/
theorem loop_const_fixed {β : Type} (g : β → PMF β) (b : β) (hb : g b = PMF.pure b) (k : ℕ) :
    loop (fun _ => g) k b = PMF.pure b := by
  induction k with
  | zero => rfl
  | succ k ih => rw [loop_const_succ, hb, PMF.pure_bind, ih]

/-- INTERNAL: an event bound holding from every point of the support passes through `bind`. -/
theorem toOuterMeasure_bind_le {α β : Type} (p : PMF α) (f : α → PMF β) (s : Set β)
    (c : ℝ≥0∞) (h : ∀ a ∈ p.support, (f a).toOuterMeasure s ≤ c) :
    (p.bind f).toOuterMeasure s ≤ c := by
  rw [PMF.toOuterMeasure_bind_apply]
  calc ∑' a, p a * (f a).toOuterMeasure s ≤ ∑' a, p a * c := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        by_cases ha : a ∈ p.support
        · gcongr; exact h a ha
        · rw [PMF.mem_support_iff, not_not] at ha; simp [ha]
    _ = c := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- INTERNAL: `nthWith` always returns an element of the paired ground set `{0, …, 2p-1}`.
TEXLINE: sections/transport.tex:60-69 -/
theorem nthWith_lt (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (S : Finset ℕ) (v : Bool)
    (t : ℕ) : nthWith I ε δ S v t < 2 * pSmall I ε δ := by
  unfold nthWith
  rw [List.getD_eq_getElem?_getD]
  cases h : ((List.range (2 * pSmall I ε δ)).filter fun e => decide (e ∈ S) == v)[t]? with
  | none => simp; omega
  | some e =>
    simp only [Option.getD_some]
    have := List.mem_of_getElem? h
    exact List.mem_range.1 (List.mem_filter.1 this).1

/-- INTERNAL: one exact transition keeps the state inside the paired ground set.
TEXLINE: sections/transport.tex:60-69 -/
theorem refStep_subset (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (a : ℕ)
    (w : ℕ → ℕ → ℚ) (S : Finset ℕ) (hS : S ⊆ Finset.range (2 * pSmall I ε δ))
    (S' : Finset ℕ) (h : S' ∈ (refStep I ε δ a w S).support) :
    S' ⊆ Finset.range (2 * pSmall I ε δ) := by
  have hT : ∀ u1 u2, insert (nthWith I ε δ S false u2) (S.erase (nthWith I ε δ S true u1)) ⊆
      Finset.range (2 * pSmall I ε δ) := by
    intro u1 u2
    refine Finset.insert_subset (Finset.mem_range.2 (nthWith_lt I ε δ hp _ _ _)) ?_
    exact (Finset.erase_subset _ _).trans hS
  unfold refStep at h
  erw [PMF.mem_support_bind_iff] at h
  obtain ⟨hold, -, h⟩ := h
  cases hold
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    erw [PMF.mem_support_bind_iff] at h
    obtain ⟨u1, -, h⟩ := h
    erw [PMF.mem_support_bind_iff] at h
    obtain ⟨u2, -, h⟩ := h
    split at h
    · rw [(PMF.mem_support_pure_iff _ _).1 h]; exact hS
    · erw [PMF.mem_support_bind_iff] at h
      obtain ⟨ok, -, h⟩ := h
      rw [(PMF.mem_support_pure_iff _ _).1 h]
      split_ifs
      · exact hT _ _
      · exact hS
  · simp only [↓reduceIte] at h
    rw [(PMF.mem_support_pure_iff _ _).1 h]; exact hS


/-- INTERNAL: inside the last stage `j`, the capped restart is dominated by the uncapped trace
stage: ending non-aborted at `y` within `n` more iterations is at most as likely as completing
the `τ` trace steps at `y` within `n` underlying transitions of `stageStep`.  The invariant
`B_ret + 1 ≤ used + n` (with `used ≤ B_ret`) says the loop cannot stop with an unfinished,
non-aborted restart.
TEXLINE: sections/algorithm.tex:292-296, 337-341 -/
theorem restart_stage_sim (I : Instance) (ε δ : ℚ) (ws : ℕ → ℕ → ℕ → ℚ) (j : ℕ)
    (y : Finset ℕ) : ∀ (n : ℕ) (st : Restart), st.stage = j → st.finished = false →
      st.aborted = false → st.hits < τParam I ε δ → st.used ≤ BretParam I ε δ →
      BretParam I ε δ + 1 ≤ st.used + n →
      (loop (fun _ st => refRestartStep I ε δ ws j st) n st).toOuterMeasure
          {r | r.aborted = false ∧ r.S = y} ≤
        loop (fun _ => stageStep I ε δ j (ws j)) n (st.hits, st.S) (τParam I ε δ, y) := by
  intro n
  induction n with
  | zero => intro st _ _ _ _ hu hn; omega
  | succ n ih =>
    intro st hs hf ha hh hu hn
    rw [loop_const_succ (fun st => refRestartStep I ε δ ws j st)]
    by_cases hB : BretParam I ε δ ≤ st.used
    · have hstep : refRestartStep I ε δ ws j st = PMF.pure { st with aborted := true } := by
        simp [refRestartStep, hf, ha, hB]; rfl
      rw [hstep, PMF.pure_bind, loop_const_fixed _ _ (by simp [refRestartStep]; rfl),
        PMF.toOuterMeasure_pure_apply]
      simp
    · have hstep : refRestartStep I ε δ ws j st = (refStep I ε δ j (ws j) st.S).bind fun S' =>
          match kind I ε δ S' with
          | .transversal =>
            if st.hits + 1 = τParam I ε δ then
              PMF.pure ⟨S', st.stage + 1, 0, st.used + 1, decide (st.stage = j), false⟩
            else PMF.pure ⟨S', st.stage, st.hits + 1, st.used + 1, false, false⟩
          | _ => PMF.pure ⟨S', st.stage, st.hits, st.used + 1, false, false⟩ := by
        simp only [refRestartStep, hf, ha, hB, hs, Bool.false_eq_true, if_false]; rfl
      have hstage : stageStep I ε δ j (ws j) (st.hits, st.S) = (refStep I ε δ j (ws j) st.S).map
          fun S' => match kind I ε δ S' with
            | .transversal => (st.hits + 1, S')
            | _ => (st.hits, S') := by
        simp only [stageStep, if_neg (not_le.2 hh)]; rfl
      rw [hstep, PMF.bind_bind, PMF.toOuterMeasure_bind_apply, loop_const_succ, hstage,
        PMF.bind_map, PMF.bind_apply]
      refine ENNReal.tsum_le_tsum fun S' => ?_
      gcongr
      rcases hk : kind I ε δ S' with _ | ⟨i, l⟩ | _
      · simp only [Function.comp, hk]
        by_cases hτ : st.hits + 1 = τParam I ε δ
        · simp only [hτ, if_true, PMF.pure_bind]
          rw [loop_const_fixed (fun st => refRestartStep I ε δ ws j st) _
              (by simp [refRestartStep, hs]; rfl),
            loop_const_fixed _ _ (by simp [stageStep]),
            PMF.toOuterMeasure_pure_apply, PMF.pure_apply]
          by_cases hy : S' = y <;> simp [hy]
        · simp only [hτ, if_false, PMF.pure_bind]
          exact ih ⟨S', st.stage, st.hits + 1, st.used + 1, false, false⟩ hs rfl rfl
            (show st.hits + 1 < τParam I ε δ by omega) (show st.used + 1 ≤ _ by omega)
            (show _ ≤ st.used + 1 + n by omega)
      · simp only [Function.comp, hk, PMF.pure_bind]
        exact ih ⟨S', st.stage, st.hits, st.used + 1, false, false⟩ hs rfl rfl hh
          (show st.used + 1 ≤ _ by omega) (show _ ≤ st.used + 1 + n by omega)
      · simp only [Function.comp, hk, PMF.pure_bind]
        exact ih ⟨S', st.stage, st.hits, st.used + 1, false, false⟩ hs rfl rfl hh
          (show st.used + 1 ≤ _ by omega) (show _ ≤ st.used + 1 + n by omega)


/-- INTERNAL: from any unfinished, non-aborted state of a stage before `j` inside the paired
ground set, ending non-aborted at `y` is bounded by any bound `c` on the stage-`j` trace endpoint
from a transversal: stage `j` is entered at a transversal with no completed trace steps.
TEXLINE: sections/algorithm.tex:285-296 -/
theorem restart_early_le (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0)
    (ws : ℕ → ℕ → ℕ → ℚ) (j : ℕ) (y : Finset ℕ) (c : ℝ≥0∞) (hτ : 0 < τParam I ε δ)
    (hstage : ∀ x ∈ transStates I ε δ, ∀ N : ℕ,
      loop (fun _ => stageStep I ε δ j (ws j)) N (0, x) (τParam I ε δ, y) ≤ c) :
    ∀ (n : ℕ) (st : Restart), st.stage < j → st.finished = false →
      st.aborted = false → st.used ≤ BretParam I ε δ →
      BretParam I ε δ + 1 ≤ st.used + n → st.S ⊆ Finset.range (2 * pSmall I ε δ) →
      (loop (fun _ st => refRestartStep I ε δ ws j st) n st).toOuterMeasure
          {r | r.aborted = false ∧ r.S = y} ≤ c := by
  intro n
  induction n with
  | zero => intro st _ _ _ hu hn; omega
  | succ n ih =>
    intro st hs hf ha hu hn hS
    rw [loop_const_succ (fun st => refRestartStep I ε δ ws j st)]
    by_cases hB : BretParam I ε δ ≤ st.used
    · have hstep : refRestartStep I ε δ ws j st = PMF.pure { st with aborted := true } := by
        simp [refRestartStep, hf, ha, hB]; rfl
      rw [hstep, PMF.pure_bind, loop_const_fixed _ _ (by simp [refRestartStep]; rfl),
        PMF.toOuterMeasure_pure_apply]
      simp
    · have hstep : refRestartStep I ε δ ws j st =
          (refStep I ε δ st.stage (ws st.stage) st.S).bind fun S' =>
          match kind I ε δ S' with
          | .transversal =>
            if st.hits + 1 = τParam I ε δ then
              PMF.pure ⟨S', st.stage + 1, 0, st.used + 1, decide (st.stage = j), false⟩
            else PMF.pure ⟨S', st.stage, st.hits + 1, st.used + 1, false, false⟩
          | _ => PMF.pure ⟨S', st.stage, st.hits, st.used + 1, false, false⟩ := by
        simp only [refRestartStep, hf, ha, hB, Bool.false_eq_true, if_false]; rfl
      rw [hstep, PMF.bind_bind]
      refine toOuterMeasure_bind_le _ _ _ _ fun S' hS' => ?_
      have hS'r := refStep_subset I ε δ hp _ _ _ hS S' hS'
      rcases hk : kind I ε δ S' with _ | ⟨i, l⟩ | _
      · by_cases hτ' : st.hits + 1 = τParam I ε δ
        · simp only [hτ', if_true, PMF.pure_bind]
          have hdec : decide (st.stage = j) = false := by simp; omega
          rw [hdec]
          by_cases hsj : st.stage + 1 = j
          · refine (restart_stage_sim I ε δ ws j y n
              ⟨S', st.stage + 1, 0, st.used + 1, false, false⟩ hsj rfl rfl hτ
              (show st.used + 1 ≤ _ by omega) (show _ ≤ st.used + 1 + n by omega)).trans ?_
            refine hstage S' ?_ n
            simp only [transStates, Finset.mem_filter, refStates, Finset.mem_powerset]
            exact ⟨hS'r, hk⟩
          · exact ih ⟨S', st.stage + 1, 0, st.used + 1, false, false⟩
              (show st.stage + 1 < j by omega) rfl rfl (show st.used + 1 ≤ _ by omega)
              (show _ ≤ st.used + 1 + n by omega) hS'r
        · simp only [hτ', if_false, PMF.pure_bind]
          exact ih ⟨S', st.stage, st.hits + 1, st.used + 1, false, false⟩ hs rfl rfl
            (show st.used + 1 ≤ _ by omega) (show _ ≤ st.used + 1 + n by omega) hS'r
      · simp only [PMF.pure_bind]
        exact ih ⟨S', st.stage, st.hits, st.used + 1, false, false⟩ hs rfl rfl
          (show st.used + 1 ≤ _ by omega) (show _ ≤ st.used + 1 + n by omega) hS'r
      · simp only [PMF.pure_bind]
        exact ih ⟨S', st.stage, st.hits, st.used + 1, false, false⟩ hs rfl rfl
          (show st.used + 1 ≤ _ by omega) (show _ ≤ st.used + 1 + n by omega) hS'r


/-- INTERNAL: the non-aborted endpoint sub-law of the capped restart of phase `j` from the
`μ₀` draw is at most `(3/2) μ_j` (the paper's virtual-endpoint bound `≤ 2μ_j`, with the
constant its own relative-error computation gives).
TEXLINE: sections/algorithm.tex:283-296 -/
theorem refRestart_endpoint_le (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (ws : ℕ → ℕ → ℕ → ℚ) (hgood : ∀ a ≤ j, goodMult I ε δ a (ws a)) (S : Finset ℕ) :
    ((refMu0 I ε δ).bind (refRestart I ε δ ws j)).toOuterMeasure
        {r | r.aborted = false ∧ r.S = S} ≤
      3 / 2 * ENNReal.ofReal (refMu I ε δ j S) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · -- `j = 0`: the restart is finished from the start; the endpoint is the `μ₀` draw.
    have hfix : ∀ S0, refRestart I ε δ ws 0 S0 = PMF.pure ⟨S0, 1, 0, 0, true, false⟩ := by
      intro S0
      exact loop_const_fixed (fun st => refRestartStep I ε δ ws 0 st) _
        (by simp [refRestartStep]; rfl) _
    rw [PMF.toOuterMeasure_bind_apply]
    simp only [hfix, PMF.toOuterMeasure_pure_apply, Set.mem_setOf_eq, true_and]
    rw [tsum_eq_single S (fun S0 h => by simp [h])]
    simp only [if_true, mul_one, refMu0_apply]
    refine le_mul_of_one_le_left (by positivity) ?_
    rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
    norm_num
  · have hτ : 0 < τParam I ε δ := by
      have hp' : 0 < pSmall I ε δ := Nat.pos_of_ne_zero hp
      unfold τParam KobsParam CdParam
      positivity
    have hstage : ∀ x ∈ transStates I ε δ, ∀ N : ℕ,
        loop (fun _ => stageStep I ε δ j (ws j)) N (0, x) (τParam I ε δ, S) ≤
          3 / 2 * ENNReal.ofReal (refMu I ε δ j S) := fun x hx N =>
      stage_endpoint_le hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj (ws j)
        (hgood j le_rfl) x hx N S
    refine toOuterMeasure_bind_le _ _ _ _ fun S0 hS0 => ?_
    -- The `μ₀` draw is a transversal.
    have hS0t : S0 ∈ transStates I ε δ := by
      by_contra h
      rw [PMF.mem_support_iff, refMu0_apply, refMu, if_neg h, ENNReal.ofReal_zero] at hS0
      exact hS0 rfl
    have hS0r : S0 ⊆ Finset.range (2 * pSmall I ε δ) := by
      have := hS0t
      simp only [transStates, Finset.mem_filter, refStates, Finset.mem_powerset] at this
      exact this.1
    have hdec : decide (j = 0) = false := by simp; omega
    unfold refRestart
    rw [hdec]
    rcases Nat.lt_or_ge 1 j with h1 | h1
    · exact restart_early_le I ε δ hp ws j S _ hτ hstage _ _ h1 rfl rfl (Nat.zero_le _)
        (by omega) hS0r
    · have hj1 : 1 = j := by omega
      have h0 := restart_stage_sim I ε δ ws j S (BretParam I ε δ + 1) ⟨S0, 1, 0, 0, false, false⟩
        hj1 rfl rfl hτ (Nat.zero_le _)
        (show BretParam I ε δ + 1 ≤ 0 + (BretParam I ε δ + 1) by omega)
      have h2 := hstage S0 hS0t (BretParam I ε δ + 1)
      dsimp only at h0
      exact le_trans h0 h2


end Cellcounting.Analysis
