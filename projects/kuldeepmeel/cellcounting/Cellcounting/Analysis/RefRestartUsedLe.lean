import Cellcounting.Analysis.RefChainLaw
import Cellcounting.Analysis.PmfClose
import Cellcounting.Model.Prior
import Cellcounting.Analysis.LevelReturnCost
import Cellcounting.Analysis.RefRestartEndpoint
import Cellcounting.Analysis.RefStepReversible
import Cellcounting.Analysis.TransportDirichlet
import Cellcounting.Analysis.FWeightAdjacent

/-!
# Expected transition count of the capped restart (warm return cost)

`prop:annealing`, the expected-cost half of the cap bound (`algorithm.tex:298-305`).
Fix stored multipliers `w^(1..j)` good at their own parameters.  The capped reference
restart of phase `j`, started from the `μ₀` draw, uses on average at most `20 p² j τ`
underlying transitions (its `used` counter).

In the paper: the capped counter is at most the virtual (uncapped) restart cost.  That
restart runs `τ` trace steps of `P_{a, w^(a)}` in each stage `a = 1..j`.  At every
deterministic trace index of stage `a` the law is at most `4 μ_a` (entry law `μ_0 ≤ 2μ_1`
at `a = 1`; at later stages the previous endpoint `≤ 2μ_{a-1} ≤ 4μ_a` by
`eq:trace-relative-mixing` and `eq:alg-minimum-mass`; trace stationarity keeps the bound
within a stage).  For good multipliers `π(A) ≥ 1/(5p²)`, so by the warm return cost
`eq:trace-return-cost` of `lem:trace` each trace step costs at most `4 · 5p² = 20p²`
transitions in expectation.  For `j = 0` the restart is finished from the start and
`used = 0`.

Here the virtual restart is the *level process* of `LevelReturnCost.lean`: levels
`ℓ = (a-1)τ + hits` count completed trace steps, the kernel at level `ℓ` is that of stage
`⌊ℓ/τ⌋ + 1`, and the level rises on landing in a transversal.

* `rru_restart_le` — the capped `E[used]` is at most the expected time the level process
  spends below the frozen level `jτ` (`ru_loop_dom` through the projection `rruPsi`).
* `rru_ent_stage` — the cumulative entrance law at the start of stage `k + 1` is at most
  `(3/2) μ_k` (`stage_endpoint_le` through `ru_conv`, with total entrance mass `≤ 1`).
* `rru_mu_le_pi` — `(3/2) μ_k ≤ 20 p² π_{k+1}|_A` (`eq:alg-adjacent`, `Λ ≤ 5 p² C`).
* `rru_level` — each level then costs at most `20 p²` (`ru_level`: Kac's bound and trace
  sub-invariance under the stationary `π`), so `E[used] ≤ jτ · 20 p²`.

The paper's constant `4 · 5p²` becomes `3 · 5p² ≤ 20p²` here, since the stage endpoint
bound available is `(3/2) μ_a` rather than `2 μ_a`.
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal

/-- INTERNAL: the indicator that a restart state is still running (neither finished nor
aborted); exactly then an iteration takes one transition.
TEXLINE: sections/algorithm.tex:214-225 -/
def rruAct (st : Restart) : ℝ≥0∞ := if st.finished = false ∧ st.aborted = false then 1 else 0

/-- INTERNAL: the expectation of a constant. -/
theorem rru_pexp_const {α : Type} (μ : PMF α) (c : ℝ≥0∞) : pexp μ (fun _ => c) = c := by
  simp [pexp, ENNReal.tsum_mul_right]

/-- INTERNAL: one capped iteration raises `used` by at most the running indicator.
TEXLINE: sections/algorithm.tex:214-225 -/
theorem rru_step_used (I : Instance) (ε δ : ℚ) (ws : ℕ → ℕ → ℕ → ℚ) (j : ℕ) (st : Restart) :
    pexp (refRestartStep I ε δ ws j st) (fun r => (r.used : ℝ≥0∞)) ≤ st.used + rruAct st := by
  have hp : ∀ r : Restart, pexp (pure r : PMF Restart) (fun r => (r.used : ℝ≥0∞)) = r.used :=
    fun r => pexp_pure r _
  unfold refRestartStep
  by_cases h1 : st.finished = true
  · rw [if_pos h1, hp]; exact le_self_add
  by_cases h2 : st.aborted = true
  · rw [if_neg h1, if_pos h2, hp]; exact le_self_add
  have hA : rruAct st = 1 := by simp [rruAct] at h1 h2 ⊢; exact ⟨h1, h2⟩
  rw [if_neg h1, if_neg h2, hA]
  split_ifs with h3
  · rw [hp]; exact le_self_add
  all_goals
    erw [pexp_bind]
    calc _ ≤ pexp (refStep I ε δ st.stage (ws st.stage) st.S) (fun _ => (st.used : ℝ≥0∞) + 1) := by
          refine pexp_mono _ fun S' => ?_
          repeat' split
          all_goals simp [hp]
      _ = _ := rru_pexp_const _ _

/-- INTERNAL: `E[used]` after `N` iterations is at most the expected number of running
iterations.
TEXLINE: sections/algorithm.tex:214-225 -/
theorem rru_loop_used (I : Instance) (ε δ : ℚ) (ws : ℕ → ℕ → ℕ → ℚ) (j : ℕ) (b : Restart)
    (N : ℕ) :
    pexp (loop (fun _ st => refRestartStep I ε δ ws j st) N b) (fun r => (r.used : ℝ≥0∞)) ≤
      b.used + ∑ n ∈ Finset.range N,
        pexp (loop (fun _ st => refRestartStep I ε δ ws j st) n b) rruAct := by
  induction N with
  | zero => simp [pexp_pure]
  | succ N ih =>
    rw [loop_succ, pexp_bind, Finset.sum_range_succ, ← add_assoc]
    calc _ ≤ pexp (loop (fun _ st => refRestartStep I ε δ ws j st) N b)
          (fun st => (st.used : ℝ≥0∞) + rruAct st) := pexp_mono _ fun st => rru_step_used I ε δ ws j st
      _ = pexp (loop (fun _ st => refRestartStep I ε δ ws j st) N b) (fun r => (r.used : ℝ≥0∞)) +
            pexp (loop (fun _ st => refRestartStep I ε δ ws j st) N b) rruAct := by
          simp only [pexp, mul_add]
          rw [ENNReal.tsum_add]
      _ ≤ _ := by gcongr

/-- INTERNAL: the level of a restart state in the uncapped level process: `(a-1)τ + hits`
while running, the frozen level `jτ` once finished or aborted.
TEXLINE: sections/algorithm.tex:298-303 -/
def rruPsi (τ j : ℕ) (st : Restart) : ℕ × Finset ℕ :=
  if st.finished = false ∧ st.aborted = false then ((st.stage - 1) * τ + st.hits, st.S)
  else (j * τ, st.S)

/-- INTERNAL: the support invariant of the capped restart: states inside the paired ground
set, stage at least `1`, and while running, stage at most `j` with fewer than `τ` hits.
TEXLINE: sections/algorithm.tex:214-225 -/
noncomputable def rruInv (I : Instance) (ε δ : ℚ) (j : ℕ) (st : Restart) : Prop :=
  st.S ⊆ Finset.range (2 * pSmall I ε δ) ∧ 1 ≤ st.stage ∧
    (st.finished = false ∧ st.aborted = false → st.stage ≤ j ∧ st.hits < τParam I ε δ)

/-- INTERNAL: the kernel of the level process at level `ℓ`: `P_{a, w^(a)}` with
`a = ⌊ℓ/τ⌋ + 1`, the stage that level belongs to.
TEXLINE: sections/algorithm.tex:298-303 -/
noncomputable def rruP (I : Instance) (ε δ : ℚ) (ws : ℕ → ℕ → ℕ → ℚ) (ℓ : ℕ) :
    Finset ℕ → PMF (Finset ℕ) :=
  refStep I ε δ (ℓ / τParam I ε δ + 1) (ws (ℓ / τParam I ε δ + 1))

/-- INTERNAL: inside the paired ground set, being a transversal is `kind = transversal`. -/
theorem rru_mem_trans_iff (I : Instance) (ε δ : ℚ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range (2 * pSmall I ε δ)) :
    S ∈ transStates I ε δ ↔ kind I ε δ S = .transversal := by
  simp [transStates, refStates, Finset.mem_filter, Finset.mem_powerset, hS]


/-- INTERNAL: the restart state after one uncapped transition to `S'`.
TEXLINE: sections/algorithm.tex:214-225 -/
noncomputable def rruNext (I : Instance) (ε δ : ℚ) (j : ℕ) (st : Restart) (S' : Finset ℕ) : Restart :=
  match kind I ε δ S' with
  | .transversal =>
    if st.hits + 1 = τParam I ε δ then ⟨S', st.stage + 1, 0, st.used + 1, decide (st.stage = j), false⟩
    else ⟨S', st.stage, st.hits + 1, st.used + 1, false, false⟩
  | _ => ⟨S', st.stage, st.hits, st.used + 1, false, false⟩

/-- INTERNAL: an uncapped running iteration is one exact transition followed by `rruNext`. -/
theorem rru_step_eq (I : Instance) (ε δ : ℚ) (ws : ℕ → ℕ → ℕ → ℚ) (j : ℕ) (st : Restart)
    (hf : st.finished = false) (ha : st.aborted = false) (hB : ¬ BretParam I ε δ ≤ st.used) :
    refRestartStep I ε δ ws j st =
      (refStep I ε δ st.stage (ws st.stage) st.S).map (rruNext I ε δ j st) := by
  rw [refRestartStep, if_neg (by simp [hf]), if_neg (by simp [ha]), if_neg hB, PMF.map]
  show PMF.bind _ _ = _
  congr 1; funext S'
  unfold rruNext
  rcases hk : kind I ε δ S' with _ | ⟨i, l⟩ | _ <;>
    by_cases hτ : st.hits + 1 = τParam I ε δ <;> simp [hk, hτ] <;> rfl

/-- INTERNAL: `map` only sees a function on the support. -/
theorem rru_map_congr {α β : Type} (μ : PMF α) (f g : α → β) (h : ∀ a ∈ μ.support, f a = g a) :
    μ.map f = μ.map g := by
  ext c
  simp only [PMF.map_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ μ.support
  · rw [h a ha]
  · rw [PMF.mem_support_iff, not_not] at ha; simp [ha]


/-- INTERNAL: a running iteration at the cap only sets the abort flag. -/
theorem rru_step_capped (I : Instance) (ε δ : ℚ) (ws : ℕ → ℕ → ℕ → ℚ) (j : ℕ) (st : Restart)
    (hf : st.finished = false) (ha : st.aborted = false) (hB : BretParam I ε δ ≤ st.used) :
    refRestartStep I ε δ ws j st = PMF.pure { st with aborted := true } := by
  simp [refRestartStep, hf, ha, hB]; rfl

/-- INTERNAL: one capped iteration preserves `rruInv`. -/
theorem rru_inv_step (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (ws : ℕ → ℕ → ℕ → ℚ)
    (j : ℕ) (hτ : 0 < τParam I ε δ) (st : Restart) (hst : rruInv I ε δ j st) (r : Restart)
    (hr : r ∈ (refRestartStep I ε δ ws j st).support) : rruInv I ε δ j r := by
  by_cases hf : st.finished = true
  · rw [refRestartStep, if_pos hf] at hr
    rw [(PMF.mem_support_pure_iff _ _).1 hr]; exact hst
  by_cases ha : st.aborted = true
  · rw [refRestartStep, if_neg hf, if_pos ha] at hr
    rw [(PMF.mem_support_pure_iff _ _).1 hr]; exact hst
  simp only [Bool.not_eq_true] at hf ha
  by_cases hB : BretParam I ε δ ≤ st.used
  · rw [rru_step_capped I ε δ ws j st hf ha hB] at hr
    rw [(PMF.mem_support_pure_iff _ _).1 hr]
    exact ⟨hst.1, hst.2.1, fun h => by simp at h⟩
  · rw [rru_step_eq I ε δ ws j st hf ha hB, PMF.support_map] at hr
    obtain ⟨S', hS', rfl⟩ := hr
    have hsub := refStep_subset I ε δ hp _ _ _ hst.1 S' hS'
    obtain ⟨-, hlo, hact⟩ := hst
    obtain ⟨hsj, hh⟩ := hact ⟨hf, ha⟩
    unfold rruNext
    rcases hk : kind I ε δ S' with _ | ⟨i, l⟩ | _ <;>
      by_cases hτ' : st.hits + 1 = τParam I ε δ <;> simp [rruInv, hτ', hsub] <;> omega

/-- INTERNAL: monadic `pure` in `PMF` is `PMF.pure`. -/
theorem rru_pure {α : Type} (a : α) : (pure a : PMF α) = PMF.pure a := rfl

/-- INTERNAL: one capped iteration, seen through `rruPsi`, is dominated below level `jτ`
by one step of the level process (the capped restart follows the virtual one).
TEXLINE: sections/algorithm.tex:298-303 -/
theorem rru_dom_step (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (ws : ℕ → ℕ → ℕ → ℚ)
    (j : ℕ) (hτ : 0 < τParam I ε δ) (st : Restart) (hst : rruInv I ε δ j st)
    (c : ℕ × Finset ℕ) (hc : c.1 < j * τParam I ε δ) :
    (refRestartStep I ε δ ws j st).map (rruPsi (τParam I ε δ) j) c ≤
      if (rruPsi (τParam I ε δ) j st).1 < j * τParam I ε δ then
        ruLvStep (rruP I ε δ ws) (j * τParam I ε δ) (· ∈ transStates I ε δ)
          (rruPsi (τParam I ε δ) j st) c
      else 0 := by
  have hne : ∀ S, c ≠ (j * τParam I ε δ, S) := fun S h => by rw [h] at hc; simp at hc
  by_cases hf : st.finished = true
  · rw [refRestartStep, if_pos hf, rru_pure, PMF.pure_map, PMF.pure_apply]
    have : rruPsi (τParam I ε δ) j st = (j * τParam I ε δ, st.S) := by simp [rruPsi, hf]
    rw [this, if_neg (hne _)]; exact bot_le
  by_cases ha : st.aborted = true
  · rw [refRestartStep, if_neg hf, if_pos ha, rru_pure, PMF.pure_map, PMF.pure_apply]
    have : rruPsi (τParam I ε δ) j st = (j * τParam I ε δ, st.S) := by simp [rruPsi, ha]
    rw [this, if_neg (hne _)]; exact bot_le
  simp only [Bool.not_eq_true] at hf ha
  by_cases hB : BretParam I ε δ ≤ st.used
  · rw [rru_step_capped I ε δ ws j st hf ha hB, PMF.pure_map, PMF.pure_apply]
    have : rruPsi (τParam I ε δ) j { st with aborted := true } = (j * τParam I ε δ, st.S) := by
      simp [rruPsi]
    rw [this, if_neg (hne _)]; exact bot_le
  obtain ⟨hsub, hlo, hact⟩ := hst
  obtain ⟨hsj, hh⟩ := hact ⟨hf, ha⟩
  have hψ : rruPsi (τParam I ε δ) j st =
      ((st.stage - 1) * τParam I ε δ + st.hits, st.S) := by simp [rruPsi, hf, ha]
  have hlt : (st.stage - 1) * τParam I ε δ + st.hits < j * τParam I ε δ := by
    have h1 : (st.stage - 1) * τParam I ε δ + st.hits < (st.stage - 1) * τParam I ε δ +
        τParam I ε δ := by omega
    have h2 : (st.stage - 1) * τParam I ε δ + τParam I ε δ = st.stage * τParam I ε δ := by
      conv_rhs => rw [show st.stage = (st.stage - 1) + 1 by omega]
      ring
    have h3 := Nat.mul_le_mul_right (τParam I ε δ) hsj
    omega
  have hdiv : ((st.stage - 1) * τParam I ε δ + st.hits) / τParam I ε δ + 1 = st.stage := by
    rw [mul_comm, Nat.mul_add_div hτ, Nat.div_eq_of_lt hh]; omega
  rw [hψ, if_pos hlt, rru_step_eq I ε δ ws j st hf ha hB, PMF.map_comp, ruLvStep,
    if_neg (not_le.2 hlt)]
  refine le_of_eq ?_
  dsimp only
  rw [rruP, hdiv]
  congr 1
  refine rru_map_congr _ _ _ fun S' hS' => ?_
  have hsub' := refStep_subset I ε δ hp _ _ _ hsub S' hS'
  have hA := rru_mem_trans_iff I ε δ S' hsub'
  simp only [Function.comp]
  unfold rruNext
  rcases hk : kind I ε δ S' with _ | ⟨i, l⟩ | _
  · rw [if_pos (hA.2 hk)]
    by_cases hτ' : st.hits + 1 = τParam I ε δ
    · by_cases hsj' : st.stage = j
      · simp [hτ', hsj', rruPsi]
        rw [add_assoc, hτ']
        conv_lhs => rw [show j = (j - 1) + 1 by omega]
        ring
      · simp [hτ', hsj', rruPsi]
        rw [add_assoc, hτ']
        conv_lhs => rw [show st.stage = (st.stage - 1) + 1 by omega]
        ring
    · simp [hτ', rruPsi]; ring
  · have hn : S' ∉ transStates I ε δ := fun h => by rw [hA.1 h] at hk; cases hk
    simp [rruPsi, hn]
  · have hn : S' ∉ transStates I ε δ := fun h => by rw [hA.1 h] at hk; cases hk
    simp [rruPsi, hn]


/-- INTERNAL: a running restart state sits below the frozen level `jτ`. -/
theorem rru_psi_lt (I : Instance) (ε δ : ℚ) (j : ℕ) (st : Restart) (hst : rruInv I ε δ j st)
    (hf : st.finished = false) (ha : st.aborted = false) :
    (rruPsi (τParam I ε δ) j st).1 < j * τParam I ε δ := by
  obtain ⟨-, hlo, hact⟩ := hst
  obtain ⟨hsj, hh⟩ := hact ⟨hf, ha⟩
  simp only [rruPsi, hf, ha, and_self, if_true]
  have h2 : (st.stage - 1) * τParam I ε δ + τParam I ε δ = st.stage * τParam I ε δ := by
    conv_rhs => rw [show st.stage = (st.stage - 1) + 1 by omega]
    ring
  have h3 := Nat.mul_le_mul_right (τParam I ε δ) hsj
  omega

/-- INTERNAL: `rru_restart_le` from an arbitrary invariant starting state at level `0`. -/
theorem rru_restart_le_aux (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0)
    (ws : ℕ → ℕ → ℕ → ℚ) (j : ℕ) (hτ : 0 < τParam I ε δ) (S0 : Finset ℕ) (b0 : Restart)
    (hInv0 : rruInv I ε δ j b0) (hψ0 : rruPsi (τParam I ε δ) j b0 = (0, S0))
    (hu : b0.used = 0) (N : ℕ) :
    pexp (loop (fun _ st => refRestartStep I ε δ ws j st) N b0) (fun r => (r.used : ℝ≥0∞)) ≤
      ∑ n ∈ Finset.range N,
        pexp (loop (fun _ => ruLvStep (rruP I ε δ ws) (j * τParam I ε δ) (· ∈ transStates I ε δ))
          n (0, S0)) (fun c => if c.1 < j * τParam I ε δ then 1 else 0) := by
  refine (rru_loop_used I ε δ ws j b0 _).trans ?_
  rw [hu, Nat.cast_zero, zero_add]
  refine Finset.sum_le_sum fun n _ => ?_
  have hsupp := ru_loop_support (fun st => refRestartStep I ε δ ws j st) (rruInv I ε δ j)
    (fun b hb r hr => rru_inv_step I ε δ hp ws j hτ b hb r hr) n b0 hInv0
  calc pexp (loop (fun _ st => refRestartStep I ε δ ws j st) n b0) rruAct
      ≤ pexp (loop (fun _ st => refRestartStep I ε δ ws j st) n b0)
          ((fun c : ℕ × Finset ℕ => if c.1 < j * τParam I ε δ then (1 : ℝ≥0∞) else 0) ∘
            rruPsi (τParam I ε δ) j) := by
        refine pexp_mono_support _ fun st hst => ?_
        have hI : rruInv I ε δ j st := hsupp st hst
        rw [Function.comp_apply]
        by_cases h1 : st.finished = false ∧ st.aborted = false
        · rw [rruAct, if_pos h1, if_pos (rru_psi_lt I ε δ j st hI h1.1 h1.2)]
        · rw [rruAct, if_neg h1]; exact bot_le
    _ = pexp ((loop (fun _ st => refRestartStep I ε δ ws j st) n b0).map
          (rruPsi (τParam I ε δ) j))
          (fun c : ℕ × Finset ℕ => if c.1 < j * τParam I ε δ then (1 : ℝ≥0∞) else 0) :=
        (pexp_map _ _ _).symm
    _ ≤ _ := by
        rw [← hψ0]
        refine ENNReal.tsum_le_tsum fun c => ?_
        by_cases hc : c.1 < j * τParam I ε δ
        · simp only [hc, if_true, mul_one]
          exact ru_loop_dom (fun st => refRestartStep I ε δ ws j st) _ (rruPsi (τParam I ε δ) j)
            (fun c : ℕ × Finset ℕ => c.1 < j * τParam I ε δ) (rruInv I ε δ j)
            (fun b hb r hr => rru_inv_step I ε δ hp ws j hτ b hb r hr)
            (fun b hb c hc => rru_dom_step I ε δ hp ws j hτ b hb c hc) n b0 hInv0 c hc
        · simp [hc]

/-- INTERNAL: **capped cost ≤ virtual cost**: the expected transition count of the capped
restart from `S0` is at most the expected time the uncapped level process from `(0, S0)`
spends below level `jτ`.
TEXLINE: sections/algorithm.tex:298-311 -/
theorem rru_restart_le (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (ws : ℕ → ℕ → ℕ → ℚ)
    (j : ℕ) (hj : 1 ≤ j) (hτ : 0 < τParam I ε δ) (S0 : Finset ℕ)
    (hS0 : S0 ⊆ Finset.range (2 * pSmall I ε δ)) :
    pexp (refRestart I ε δ ws j S0) (fun r => (r.used : ℝ≥0∞)) ≤
      ∑ n ∈ Finset.range (BretParam I ε δ + 1),
        pexp (loop (fun _ => ruLvStep (rruP I ε δ ws) (j * τParam I ε δ) (· ∈ transStates I ε δ))
          n (0, S0)) (fun c => if c.1 < j * τParam I ε δ then 1 else 0) := by
  have hInv0 : rruInv I ε δ j ⟨S0, 1, 0, 0, decide (j = 0), false⟩ :=
    ⟨hS0, le_rfl, fun _ => ⟨hj, hτ⟩⟩
  have hψ0 : rruPsi (τParam I ε δ) j ⟨S0, 1, 0, 0, decide (j = 0), false⟩ = (0, S0) := by
    have : decide (j = 0) = false := by simp; omega
    simp [rruPsi, this]
  exact rru_restart_le_aux I ε δ hp ws j hτ S0 _ hInv0 hψ0 rfl _


open Classical in
/-- INTERNAL: one exact transition from a state of `X` stays in `X` (a local copy of
`ta_refStep_support`, whose module is still being edited).
TEXLINE: sections/transport.tex:60-69 -/
theorem rru_refStep_support (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (a : ℕ)
    (w : ℕ → ℕ → ℚ) (S : Finset ℕ) (hS : S ∈ chainStates I ε δ)
    (S' : Finset ℕ) (h : S' ∈ (refStep I ε δ a w S).support) : S' ∈ chainStates I ε δ := by
  have hT : ∀ u1 u2, insert (nthWith I ε δ S false u2) (S.erase (nthWith I ε δ S true u1)) ∈
      refStates I ε δ := by
    intro u1 u2
    unfold refStates
    rw [Finset.mem_powerset]
    refine Finset.insert_subset (Finset.mem_range.2 (nthWith_lt I ε δ hp _ _ _)) ?_
    exact (Finset.erase_subset _ _).trans
      (Finset.mem_powerset.1 (Finset.mem_filter.1 hS).1)
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
    · rename_i hk
      erw [PMF.mem_support_bind_iff] at h
      obtain ⟨ok, -, h⟩ := h
      rw [(PMF.mem_support_pure_iff _ _).1 h]
      split_ifs
      · exact Finset.mem_filter.2 ⟨hT _ _, hk⟩
      · exact hS
  · simp only [↓reduceIte] at h
    rw [(PMF.mem_support_pure_iff _ _).1 h]; exact hS

/-- INTERNAL: `Λ > 0` for good multipliers. -/
theorem rru_lamTot_pos (I : Instance) (ε δ : ℚ) (a : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ a w) : 0 < refLamTot I ε δ a w :=
  (td_Cpart_pos I ε δ a).trans_le (td_Cpart_le_refLamTot I ε δ a w hgood)

/-- INTERNAL: transversals belong to the chain state space `X`. -/
theorem rru_trans_chain (I : Instance) (ε δ : ℚ) (S : Finset ℕ) (hS : S ∈ transStates I ε δ) :
    S ∈ chainStates I ε δ := by
  simp only [transStates, chainStates, Finset.mem_filter] at hS ⊢
  exact ⟨hS.1, by rw [hS.2]; simp⟩

/-- INTERNAL: `π` is stationary for `P_{a, w}` (sub-measure form `π P ≤ π`), from
reversibility and row sums.
TEXLINE: sections/transport.tex:78-84 -/
theorem rru_stationary (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (a : ℕ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ a w) (y : Finset ℕ) :
    ruAct (refStep I ε δ a w) (fun x => ENNReal.ofReal (refPi I ε δ a w x)) y ≤
      ENNReal.ofReal (refPi I ε δ a w y) := by
  unfold ruAct
  simp only []
  have hoff : ∀ x ∉ chainStates I ε δ, ENNReal.ofReal (refPi I ε δ a w x) = 0 := by
    intro x hx; simp [refPi, hx]
  rw [tsum_eq_sum (s := chainStates I ε δ) fun x hx => by rw [hoff x hx, zero_mul]]
  by_cases hy : y ∈ chainStates I ε δ
  · have hrev : ∀ x ∈ chainStates I ε δ, ENNReal.ofReal (refPi I ε δ a w x) * refStep I ε δ a w x y =
        ENNReal.ofReal (refPi I ε δ a w y) * refStep I ε δ a w y x := by
      intro x hx
      have h := refStep_reversible I ε δ hp a w hgood x y hx hy
      unfold refPk at h
      rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top (refStep I ε δ a w x) y),
        ← ENNReal.ofReal_toReal (PMF.apply_ne_top (refStep I ε δ a w y) x),
        ← ENNReal.ofReal_mul (td_refPi_nonneg I ε δ a w hgood x),
        ← ENNReal.ofReal_mul (td_refPi_nonneg I ε δ a w hgood y), h]
    rw [Finset.sum_congr rfl hrev, ← Finset.mul_sum]
    have hrow : ∑ x ∈ chainStates I ε δ, refStep I ε δ a w y x = 1 := by
      rw [← PMF.tsum_coe (refStep I ε δ a w y)]
      refine (tsum_eq_sum fun x hx => ?_).symm
      by_contra h
      exact hx (rru_refStep_support I ε δ hp a w y hy x ((PMF.mem_support_iff _ _).2 h))
    rw [hrow, mul_one]
  · refine le_of_eq_of_le (Finset.sum_eq_zero fun x hx => ?_) bot_le
    have : refStep I ε δ a w x y = 0 := by
      by_contra h
      exact hy (rru_refStep_support I ε δ hp a w x hx y ((PMF.mem_support_iff _ _).2 h))
    rw [this, mul_zero]

/-- INTERNAL: `π` has total mass `1`. -/
theorem rru_mass (I : Instance) (ε δ : ℚ) (a : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ a w) :
    ruMass (fun x => ENNReal.ofReal (refPi I ε δ a w x)) = 1 := by
  unfold ruMass
  have hoff : ∀ x ∉ chainStates I ε δ, ENNReal.ofReal (refPi I ε δ a w x) = 0 := by
    intro x hx; simp [refPi, hx]
  rw [tsum_eq_sum (s := chainStates I ε δ) hoff,
    ← ENNReal.ofReal_sum_of_nonneg fun x _ => td_refPi_nonneg I ε δ a w hgood x]
  have : ∑ x ∈ chainStates I ε δ, refPi I ε δ a w x = 1 := by
    unfold refPi
    rw [Finset.sum_congr rfl fun S hS => if_pos hS, ← Finset.sum_div]
    exact div_self (rru_lamTot_pos I ε δ a w hgood).ne'
  rw [this, ENNReal.ofReal_one]


open Classical in
/-- INTERNAL: `(3/2) μ_k ≤ 3 μ_{k+1} ≤ 15 p² π_{k+1}|_A ≤ 20 p² π_{k+1}|_A` for good
`w^(k+1)` (`eq:alg-adjacent`, and `π(A) ≥ 1/(5p²)` from `Λ ≤ 5p² C`).
TEXLINE: sections/algorithm.tex:292-301 -/
theorem rru_mu_le_pi (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (hfeas : feasible I)
    (hp : pSmall I ε δ ≠ 0) (k : ℕ) (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ (k + 1) w)
    (y : Finset ℕ) :
    3 / 2 * ENNReal.ofReal (refMu I ε δ k y) ≤
      20 * (pSmall I ε δ : ℝ≥0∞) ^ 2 *
        ruRes (· ∈ transStates I ε δ) (fun x => ENNReal.ofReal (refPi I ε δ (k + 1) w x)) y := by
  unfold ruRes
  by_cases hy : y ∈ transStates I ε δ
  · simp only [hy, if_true]
    have hyR : y ∈ refStates I ε δ := (Finset.mem_filter.1 hy).1
    have hk : kind I ε δ y = .transversal := (Finset.mem_filter.1 hy).2
    have hadj := fWeight_adjacent I ε δ hε hfeas k y hyR
    have hC : Cpart I ε δ (k + 1) ≤ Cpart I ε δ k := by
      rw [← transMass_eq_Cpart, ← transMass_eq_Cpart]
      exact Finset.sum_le_sum fun S hS' =>
        (fWeight_adjacent I ε δ hε hfeas k S (Finset.mem_filter.1 hS').1).2
    have hC1 := td_Cpart_pos I ε δ (k + 1)
    have hΛ := rru_lamTot_pos I ε δ (k + 1) w hgood
    have hΛle := td_refLamTot_le I ε δ hp (k + 1) w hgood
    have hf1 := td_fWeight_pos I ε δ (k + 1) y
    have hf0 := td_fWeight_pos I ε δ k y
    have hmu : refMu I ε δ k y = fWeight I ε δ k y / Cpart I ε δ k := by
      rw [refMu, if_pos hy, transMass_eq_Cpart]
    have hpi : refPi I ε δ (k + 1) w y = fWeight I ε δ (k + 1) y / refLamTot I ε δ (k + 1) w := by
      rw [refPi, if_pos (rru_trans_chain I ε δ y hy), td_refLam_eq, hk]
    have hreal : 3 / 2 * refMu I ε δ k y ≤
        20 * (pSmall I ε δ : ℝ) ^ 2 * refPi I ε δ (k + 1) w y := by
      rw [hmu, hpi]
      have hp2 : (0 : ℝ) < (pSmall I ε δ : ℝ) ^ 2 := by
        have : (0 : ℝ) < pSmall I ε δ := Nat.cast_pos.2 (Nat.pos_of_ne_zero hp)
        positivity
      have e1 : fWeight I ε δ k y / Cpart I ε δ k ≤
          2 * fWeight I ε δ (k + 1) y / Cpart I ε δ (k + 1) := by
        rw [div_le_div_iff₀ (td_Cpart_pos I ε δ k) hC1]
        nlinarith [hadj.1]
      have e2 : 2 * fWeight I ε δ (k + 1) y / Cpart I ε δ (k + 1) ≤
          10 * (pSmall I ε δ : ℝ) ^ 2 * (fWeight I ε δ (k + 1) y / refLamTot I ε δ (k + 1) w) := by
        rw [mul_div_assoc', div_le_div_iff₀ hC1 hΛ]
        nlinarith
      have e3 : 0 ≤ (pSmall I ε δ : ℝ) ^ 2 *
          (fWeight I ε δ (k + 1) y / refLamTot I ε δ (k + 1) w) := by positivity
      nlinarith
    have hpi0 : 0 ≤ refPi I ε δ (k + 1) w y := td_refPi_nonneg I ε δ (k + 1) w hgood y
    calc 3 / 2 * ENNReal.ofReal (refMu I ε δ k y)
        = ENNReal.ofReal (3 / 2 * refMu I ε δ k y) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; congr 1
          rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
      _ ≤ ENNReal.ofReal (20 * (pSmall I ε δ : ℝ) ^ 2 * refPi I ε δ (k + 1) w y) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_pow (Nat.cast_nonneg _)]
          simp
  · simp [hy, refMu]


/-- INTERNAL: inside the paired ground set, the level process with a constant kernel is
`stageStep`. -/
theorem rru_lv_stage_eq (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (a : ℕ)
    (w : ℕ → ℕ → ℚ) (q : ℕ × Finset ℕ) (hq : q.2 ⊆ Finset.range (2 * pSmall I ε δ)) :
    ruLvStep (fun _ => refStep I ε δ a w) (τParam I ε δ) (· ∈ transStates I ε δ) q =
      stageStep I ε δ a w q := by
  unfold ruLvStep stageStep
  split_ifs with h
  · rfl
  · refine rru_map_congr _ _ _ fun S' hS' => ?_
    have hA := rru_mem_trans_iff I ε δ S' (refStep_subset I ε δ hp _ _ _ hq S' hS')
    rcases hk : kind I ε δ S' with _ | ⟨i, l⟩ | _
    · simp [hA.2 hk]
    · have hn : S' ∉ transStates I ε δ := fun h => by rw [hA.1 h] at hk; cases hk
      simp [hn]
    · have hn : S' ∉ transStates I ε δ := fun h => by rw [hA.1 h] at hk; cases hk
      simp [hn]

/-- INTERNAL: a `τ`-level run of `P_{a, w}` from a transversal ends at `y` with
probability at most `(3/2) μ_a(y)` (`stage_endpoint_le`).
TEXLINE: sections/algorithm.tex:285-291 -/
theorem rru_lv_stage_le (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (a : ℕ) (ha : a < HParam I ε δ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ a w) (x : Finset ℕ)
    (hx : x ∈ transStates I ε δ) (m : ℕ) (y : Finset ℕ) :
    ruLvLaw (fun _ => refStep I ε δ a w) (τParam I ε δ) (· ∈ transStates I ε δ)
        (PMF.pure (0, x)) m (τParam I ε δ, y) ≤
      3 / 2 * ENNReal.ofReal (refMu I ε δ a y) := by
  have hxR : x ⊆ Finset.range (2 * pSmall I ε δ) := by
    simp only [transStates, refStates] at hx
    classical exact Finset.mem_powerset.1 (Finset.mem_filter.1 hx).1
  rw [ruLvLaw, PMF.pure_bind]
  have hdom := ru_loop_dom (ruLvStep (fun _ => refStep I ε δ a w) (τParam I ε δ)
      (· ∈ transStates I ε δ)) (stageStep I ε δ a w) id (fun _ => True)
    (fun q => q.2 ⊆ Finset.range (2 * pSmall I ε δ))
    (fun q hq q' hq' => by
      rw [rru_lv_stage_eq I ε δ hp a w q hq] at hq'
      unfold stageStep at hq'
      split_ifs at hq'
      · rw [(PMF.mem_support_pure_iff _ _).1 hq']; exact hq
      · rw [PMF.support_map] at hq'
        obtain ⟨S', hS', rfl⟩ := hq'
        have := refStep_subset I ε δ hp _ _ _ hq S' hS'
        dsimp only
        split <;> exact this)
    (fun q hq c _ => by
      rw [PMF.map_id, rru_lv_stage_eq I ε δ hp a w q hq, if_pos trivial]; exact le_rfl)
    m (0, x) hxR (τParam I ε δ, y) trivial
  rw [PMF.map_id] at hdom
  exact hdom.trans (stage_endpoint_le hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp a ha w hgood
    x hx m y)


/-- INTERNAL: the initial law of the level process: the `μ₀` draw at level `0`.
TEXLINE: sections/algorithm.tex:292-296 -/
noncomputable def rruNu (I : Instance) (ε δ : ℚ) : PMF (ℕ × Finset ℕ) :=
  (refMu0 I ε δ).map fun S => (0, S)

/-- INTERNAL: the initial law lives on level `0`. -/
theorem rru_nu_off (I : Instance) (ε δ : ℚ) (ℓ : ℕ) (y : Finset ℕ) (h : ℓ ≠ 0) :
    rruNu I ε δ (ℓ, y) = 0 := by
  simp [rruNu, PMF.map_apply, h]

/-- INTERNAL: at level `0` the initial law is `μ₀`. -/
theorem rru_nu_zero (I : Instance) (ε δ : ℚ) (y : Finset ℕ) :
    rruNu I ε δ (0, y) = refMu0 I ε δ y := by
  rw [rruNu, PMF.map_apply, tsum_eq_single y]
  · simp
  · intro b hb; simp [Ne.symm hb]

/-- INTERNAL: the levels `kτ, …, kτ + τ - 1` use the kernel of stage `k + 1`. -/
theorem rru_P_eq (I : Instance) (ε δ : ℚ) (ws : ℕ → ℕ → ℕ → ℚ) (hτ : 0 < τParam I ε δ)
    (k h : ℕ) (hh : h < τParam I ε δ) :
    rruP I ε δ ws (k * τParam I ε δ + h) = refStep I ε δ (k + 1) (ws (k + 1)) := by
  have : (k * τParam I ε δ + h) / τParam I ε δ = k := by
    rw [mul_comm, Nat.mul_add_div hτ, Nat.div_eq_of_lt hh, add_zero]
  rw [rruP, this]

/-- INTERNAL: the level process enters a level only at transversals. -/
theorem rru_ent_off (I : Instance) (ε δ : ℚ) (ws : ℕ → ℕ → ℕ → ℚ) (L i b : ℕ) (x : Finset ℕ)
    (hx : x ∉ transStates I ε δ) :
    ruEnt (rruP I ε δ ws) L (· ∈ transStates I ε δ) (rruNu I ε δ) i b x = 0 := by
  cases i with
  | zero =>
    show rruNu I ε δ (b, x) = 0
    by_cases hb : b = 0
    · subst hb; rw [rru_nu_zero, refMu0_apply]; simp [refMu, hx]
    · exact rru_nu_off I ε δ b x hb
  | succ i => simp [ruEnt, hx]

/-- INTERNAL: the entrance law at level `0` is the initial law. -/
theorem rru_ent_zero (I : Instance) (ε δ : ℚ) (ws : ℕ → ℕ → ℕ → ℚ) (L N : ℕ) (y : Finset ℕ) :
    ∑ i ∈ Finset.range N, ruEnt (rruP I ε δ ws) L (· ∈ transStates I ε δ) (rruNu I ε δ) i 0 y ≤
      rruNu I ε δ (0, y) := by
  rcases N with _ | N
  · simp
  · rw [Finset.sum_range_succ']
    have : ∀ i ∈ Finset.range N,
        ruEnt (rruP I ε δ ws) L (· ∈ transStates I ε δ) (rruNu I ε δ) (i + 1) 0 y = 0 :=
      fun i _ => by simp [ruEnt]
    rw [Finset.sum_eq_zero this, zero_add]
    exact le_rfl

/-- INTERNAL: one level of a law has mass at most `1`. -/
theorem rru_tsum_snd_le {β : Type} (μ : PMF (ℕ × β)) (ℓ : ℕ) : ∑' y, μ (ℓ, y) ≤ 1 := by
  calc ∑' y, μ (ℓ, y) ≤ ∑' q, μ q :=
        ENNReal.tsum_comp_le_tsum_of_injective (f := fun y : β => (ℓ, y))
          (fun a b h => by simpa using h) (fun q => μ q)
    _ = 1 := PMF.tsum_coe μ

/-- INTERNAL: exchange of sums in `ℝ≥0∞`. -/
theorem rru_swap_tsum {ι β γ : Type} (s : Finset ι) (e : ι → β → ℝ≥0∞) (g : ι → β → γ → ℝ≥0∞) :
    ∑' y, ∑ i ∈ s, ∑' x, e i x * g i x y = ∑ i ∈ s, ∑' x, e i x * ∑' y, g i x y := by
  rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun x => ENNReal.tsum_mul_left


/-- INTERNAL: `ru_conv` at the stage boundary `(k+1)τ`.
TEXLINE: sections/algorithm.tex:292-296 -/
theorem rru_conv (I : Instance) (ε δ : ℚ) (ws : ℕ → ℕ → ℕ → ℚ) (j : ℕ)
    (hτ : 0 < τParam I ε δ) (k : ℕ) (hk : k + 1 ≤ j) (n : ℕ) (y : Finset ℕ) :
    ∑ i ∈ Finset.range (n + 1), ruEnt (rruP I ε δ ws) (j * τParam I ε δ)
        (· ∈ transStates I ε δ) (rruNu I ε δ) i ((k + 1) * τParam I ε δ) y ≤
      ∑ i ∈ Finset.range (n + 1), ∑' x, ruEnt (rruP I ε δ ws) (j * τParam I ε δ)
        (· ∈ transStates I ε δ) (rruNu I ε δ) i (k * τParam I ε δ) x *
        ruLvLaw (fun _ => refStep I ε δ (k + 1) (ws (k + 1))) (τParam I ε δ)
          (· ∈ transStates I ε δ) (PMF.pure (0, x)) (n - i) (τParam I ε δ, y) := by
  have hb : (k + 1) * τParam I ε δ = k * τParam I ε δ + τParam I ε δ := by ring
  rw [hb]
  exact (ru_conv (P := rruP I ε δ ws) (L := j * τParam I ε δ) (A := (· ∈ transStates I ε δ))
    (rruNu I ε δ) (fun ℓ y h => rru_nu_off I ε δ ℓ y h) (k * τParam I ε δ) (τParam I ε δ) hτ
    (by rw [← hb]; exact Nat.mul_le_mul_right _ hk)
    (fun _ => refStep I ε δ (k + 1) (ws (k + 1)))
    (fun k' hk' => (rru_P_eq I ε δ ws hτ k k' hk').symm) n).2 y

/-- INTERNAL: the cumulative entrance law at each stage boundary has mass at most `1`. -/
theorem rru_ent_mass (I : Instance) (ε δ : ℚ) (ws : ℕ → ℕ → ℕ → ℚ) (j : ℕ)
    (hτ : 0 < τParam I ε δ) (k : ℕ) (hk : k ≤ j) (N : ℕ) :
    ∑ i ∈ Finset.range N, ∑' x, ruEnt (rruP I ε δ ws) (j * τParam I ε δ)
      (· ∈ transStates I ε δ) (rruNu I ε δ) i (k * τParam I ε δ) x ≤ 1 := by
  induction k with
  | zero =>
    rw [zero_mul, ← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
    calc _ ≤ ∑' x, rruNu I ε δ (0, x) := ENNReal.tsum_le_tsum fun x => rru_ent_zero I ε δ ws _ N x
      _ ≤ 1 := rru_tsum_snd_le _ 0
  | succ k ih =>
    rcases N with _ | n
    · simp
    rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
    calc _ ≤ ∑' y, ∑ i ∈ Finset.range (n + 1), ∑' x, ruEnt (rruP I ε δ ws) (j * τParam I ε δ)
            (· ∈ transStates I ε δ) (rruNu I ε δ) i (k * τParam I ε δ) x *
            ruLvLaw (fun _ => refStep I ε δ (k + 1) (ws (k + 1))) (τParam I ε δ)
              (· ∈ transStates I ε δ) (PMF.pure (0, x)) (n - i) (τParam I ε δ, y) :=
          ENNReal.tsum_le_tsum fun y => rru_conv I ε δ ws j hτ k hk n y
      _ = _ := rru_swap_tsum _ _ _
      _ ≤ ∑ i ∈ Finset.range (n + 1), ∑' x, ruEnt (rruP I ε δ ws) (j * τParam I ε δ)
            (· ∈ transStates I ε δ) (rruNu I ε δ) i (k * τParam I ε δ) x := by
          gcongr with i hi x
          exact (mul_le_of_le_one_right' (rru_tsum_snd_le _ _))
      _ ≤ 1 := ih (by omega)


/-- INTERNAL: the cumulative entrance law at the start `kτ` of stage `k + 1` is at most
`(3/2) μ_k` (`μ₀` itself for `k = 0`; the previous stage's endpoint otherwise).
TEXLINE: sections/algorithm.tex:292-296 -/
theorem rru_ent_stage (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (ws : ℕ → ℕ → ℕ → ℚ) (hgood : ∀ a ≤ j, goodMult I ε δ a (ws a))
    (hτ : 0 < τParam I ε δ) (k : ℕ) (hk : k < j) (N : ℕ) (y : Finset ℕ) :
    ∑ i ∈ Finset.range N, ruEnt (rruP I ε δ ws) (j * τParam I ε δ)
        (· ∈ transStates I ε δ) (rruNu I ε δ) i (k * τParam I ε δ) y ≤
      3 / 2 * ENNReal.ofReal (refMu I ε δ k y) := by
  rcases k with _ | k
  · rw [zero_mul]
    refine (rru_ent_zero I ε δ ws _ N y).trans ?_
    rw [rru_nu_zero, refMu0_apply]
    refine le_mul_of_one_le_left bot_le ?_
    rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
    norm_num
  rcases N with _ | n
  · simp
  refine (rru_conv I ε δ ws j hτ k hk.le n y).trans ?_
  calc _ ≤ ∑ i ∈ Finset.range (n + 1), ∑' x, ruEnt (rruP I ε δ ws) (j * τParam I ε δ)
          (· ∈ transStates I ε δ) (rruNu I ε δ) i (k * τParam I ε δ) x *
          (3 / 2 * ENNReal.ofReal (refMu I ε δ (k + 1) y)) := by
        refine Finset.sum_le_sum fun i _ => ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ transStates I ε δ
        · gcongr
          exact rru_lv_stage_le hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp
            (k + 1) (by omega) (ws (k + 1)) (hgood _ hk.le) x hx (n - i) y
        · rw [rru_ent_off I ε δ ws _ _ _ x hx, zero_mul, zero_mul]
    _ = (∑ i ∈ Finset.range (n + 1), ∑' x, ruEnt (rruP I ε δ ws) (j * τParam I ε δ)
          (· ∈ transStates I ε δ) (rruNu I ε δ) i (k * τParam I ε δ) x) *
          (3 / 2 * ENNReal.ofReal (refMu I ε δ (k + 1) y)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => ENNReal.tsum_mul_right
    _ ≤ 1 * (3 / 2 * ENNReal.ofReal (refMu I ε δ (k + 1) y)) := by
        gcongr
        exact rru_ent_mass I ε δ ws j hτ k (by omega) _
    _ = _ := one_mul _

/-- INTERNAL: per level of stage `k + 1`: the entrance law is at most `20 p² π|_A`, and
the expected time spent there at most `20 p²` (warm return cost, `ru_level`).
TEXLINE: sections/algorithm.tex:298-303 -/
theorem rru_level (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (ws : ℕ → ℕ → ℕ → ℚ) (hgood : ∀ a ≤ j, goodMult I ε δ a (ws a))
    (hτ : 0 < τParam I ε δ) (k : ℕ) (hk : k < j) (h : ℕ) (hh : h < τParam I ε δ) (N : ℕ) :
    (∀ y, ∑ i ∈ Finset.range N, ruEnt (rruP I ε δ ws) (j * τParam I ε δ)
        (· ∈ transStates I ε δ) (rruNu I ε δ) i (k * τParam I ε δ + h) y ≤
      20 * (pSmall I ε δ : ℝ≥0∞) ^ 2 * ruRes (· ∈ transStates I ε δ)
        (fun x => ENNReal.ofReal (refPi I ε δ (k + 1) (ws (k + 1)) x)) y) ∧
    ruMass (fun y => ∑ n ∈ Finset.range N, ruLvLaw (rruP I ε δ ws) (j * τParam I ε δ)
        (· ∈ transStates I ε δ) (rruNu I ε δ) n (k * τParam I ε δ + h, y)) ≤
      20 * (pSmall I ε δ : ℝ≥0∞) ^ 2 := by
  have hgk := hgood (k + 1) hk
  have hlvl : ∀ h' < τParam I ε δ, k * τParam I ε δ + h' < j * τParam I ε δ := by
    intro h' hh'
    have := Nat.mul_le_mul_right (τParam I ε δ) (show k + 1 ≤ j by omega)
    rw [add_mul, one_mul] at this
    omega
  have hstep : ∀ h' < τParam I ε δ,
      (∀ y, ∑ i ∈ Finset.range N, ruEnt (rruP I ε δ ws) (j * τParam I ε δ)
        (· ∈ transStates I ε δ) (rruNu I ε δ) i (k * τParam I ε δ + h') y ≤
      20 * (pSmall I ε δ : ℝ≥0∞) ^ 2 * ruRes (· ∈ transStates I ε δ)
        (fun x => ENNReal.ofReal (refPi I ε δ (k + 1) (ws (k + 1)) x)) y) →
      ruMass (fun y => ∑ n ∈ Finset.range N, ruLvLaw (rruP I ε δ ws) (j * τParam I ε δ)
        (· ∈ transStates I ε δ) (rruNu I ε δ) n (k * τParam I ε δ + h', y)) ≤
        20 * (pSmall I ε δ : ℝ≥0∞) ^ 2 * ruMass
          (fun x => ENNReal.ofReal (refPi I ε δ (k + 1) (ws (k + 1)) x)) ∧
      ∀ y, ∑ i ∈ Finset.range N, ruEnt (rruP I ε δ ws) (j * τParam I ε δ)
        (· ∈ transStates I ε δ) (rruNu I ε δ) i (k * τParam I ε δ + h' + 1) y ≤
      20 * (pSmall I ε δ : ℝ≥0∞) ^ 2 * ruRes (· ∈ transStates I ε δ)
        (fun x => ENNReal.ofReal (refPi I ε δ (k + 1) (ws (k + 1)) x)) y := by
    intro h' hh' hF
    refine ru_level (rruNu I ε δ) (fun ℓ y h => rru_nu_off I ε δ ℓ y h) (hlvl h' hh') _
      (fun y => ?_) _ N hF
    rw [rru_P_eq I ε δ ws hτ k h' hh']
    exact rru_stationary I ε δ hp (k + 1) (ws (k + 1)) hgk y
  have hent : ∀ h' < τParam I ε δ, ∀ y,
      ∑ i ∈ Finset.range N, ruEnt (rruP I ε δ ws) (j * τParam I ε δ)
        (· ∈ transStates I ε δ) (rruNu I ε δ) i (k * τParam I ε δ + h') y ≤
      20 * (pSmall I ε δ : ℝ≥0∞) ^ 2 * ruRes (· ∈ transStates I ε δ)
        (fun x => ENNReal.ofReal (refPi I ε δ (k + 1) (ws (k + 1)) x)) y := by
    intro h' hh'
    induction h' with
    | zero =>
      intro y
      rw [add_zero]
      exact (rru_ent_stage hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj ws hgood hτ k hk N y).trans
        (rru_mu_le_pi I ε δ hε hfeas hp k (ws (k + 1)) hgk y)
    | succ h' ih =>
      exact (hstep h' (by omega) (ih (by omega))).2
  refine ⟨hent h hh, ?_⟩
  refine ((hstep h hh (hent h hh)).1).trans ?_
  rw [rru_mass I ε δ (k + 1) (ws (k + 1)) hgk, mul_one]


/-- INTERNAL: the probability of being below level `L`, level by level. -/
theorem rru_pexp_level {β : Type} (μ : PMF (ℕ × β)) (L : ℕ) :
    pexp μ (fun c => if c.1 < L then 1 else 0) = ∑ ℓ ∈ Finset.range L, ∑' y, μ (ℓ, y) := by
  unfold pexp
  rw [ENNReal.tsum_prod', tsum_eq_sum (s := Finset.range L)]
  · refine Finset.sum_congr rfl fun ℓ hℓ => tsum_congr fun y => ?_
    simp only [if_pos (Finset.mem_range.1 hℓ), mul_one]
  · intro ℓ hℓ
    refine ENNReal.tsum_eq_zero.2 fun y => ?_
    have : ¬ ℓ < L := by simpa using hℓ
    simp only [this, if_false, mul_zero]

/-- INTERNAL: the level process spends expected time at most `jτ · 20 p²` below `jτ`.
TEXLINE: sections/algorithm.tex:298-303 -/
theorem rru_lv_sum (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (ws : ℕ → ℕ → ℕ → ℚ) (hgood : ∀ a ≤ j, goodMult I ε δ a (ws a))
    (hτ : 0 < τParam I ε δ) (N : ℕ) :
    ∑ n ∈ Finset.range N, pexp (ruLvLaw (rruP I ε δ ws) (j * τParam I ε δ)
        (· ∈ transStates I ε δ) (rruNu I ε δ) n)
        (fun c => if c.1 < j * τParam I ε δ then 1 else 0) ≤
      ((j * τParam I ε δ : ℕ) : ℝ≥0∞) * (20 * (pSmall I ε δ : ℝ≥0∞) ^ 2) := by
  simp_rw [rru_pexp_level]
  rw [Finset.sum_comm]
  calc _ = ∑ ℓ ∈ Finset.range (j * τParam I ε δ), ruMass (fun y => ∑ n ∈ Finset.range N,
          ruLvLaw (rruP I ε δ ws) (j * τParam I ε δ) (· ∈ transStates I ε δ)
            (rruNu I ε δ) n (ℓ, y)) :=
        Finset.sum_congr rfl fun ℓ _ => (ruMass_sum _ _).symm
    _ ≤ ∑ ℓ ∈ Finset.range (j * τParam I ε δ), 20 * (pSmall I ε δ : ℝ≥0∞) ^ 2 := by
        refine Finset.sum_le_sum fun ℓ hℓ => ?_
        have hℓ' := Finset.mem_range.1 hℓ
        have hk : ℓ / τParam I ε δ < j := (Nat.div_lt_iff_lt_mul hτ).2 hℓ'
        have hdec : ℓ = ℓ / τParam I ε δ * τParam I ε δ + ℓ % τParam I ε δ := by
          rw [mul_comm]; exact (Nat.div_add_mod ℓ _).symm
        rw [hdec]
        exact (rru_level hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj ws hgood hτ _ hk _
          (Nat.mod_lt _ hτ) N).2
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- INTERNAL: linearity of `pexp` over a finite sum. -/
theorem rru_pexp_sum {α : Type} (μ : PMF α) (s : Finset ℕ) (f : ℕ → α → ℝ≥0∞) :
    pexp μ (fun a => ∑ n ∈ s, f n a) = ∑ n ∈ s, pexp μ (f n) := by
  unfold pexp
  simp_rw [Finset.mul_sum]
  exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable

/-- **Expected cost of the capped restart** (`algorithm.tex:298-305`): with good stored
multipliers `w^(0..j)`, the capped reference restart of phase `j` from the `μ₀` draw uses
on average at most `20 p² j τ` underlying transitions (the paper bounds the uncapped
cost by `20 p² H τ`, stage by stage; `j ≤ H` stages are run).
PAPER: sections/algorithm.tex:298-305 -/
theorem refRestart_used_le (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (ws : ℕ → ℕ → ℕ → ℚ) (hgood : ∀ a ≤ j, goodMult I ε δ a (ws a)) :
    pexp ((refMu0 I ε δ).bind (refRestart I ε δ ws j)) (fun r => (r.used : ℝ≥0∞)) ≤
      20 * (pSmall I ε δ : ℝ≥0∞) ^ 2 * (j : ℝ≥0∞) * (τParam I ε δ : ℝ≥0∞) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have hfix : ∀ S0, refRestart I ε δ ws 0 S0 = PMF.pure ⟨S0, 1, 0, 0, true, false⟩ := by
      intro S0
      exact loop_const_fixed (fun st => refRestartStep I ε δ ws 0 st) _
        (by simp [refRestartStep]; rfl) _
    rw [pexp_bind]
    simp [hfix, pexp]
  have hτ : 0 < τParam I ε δ := by
    have hp' : 0 < pSmall I ε δ := Nat.pos_of_ne_zero hp
    unfold τParam KobsParam CdParam
    positivity
  rw [pexp_bind]
  calc _ ≤ pexp (refMu0 I ε δ) (fun S0 => ∑ n ∈ Finset.range (BretParam I ε δ + 1),
          pexp (loop (fun _ => ruLvStep (rruP I ε δ ws) (j * τParam I ε δ)
            (· ∈ transStates I ε δ)) n (0, S0))
            (fun c => if c.1 < j * τParam I ε δ then 1 else 0)) := by
        refine pexp_mono_support _ fun S0 hS0 => ?_
        have hS0t : S0 ∈ transStates I ε δ := by
          by_contra h
          rw [PMF.mem_support_iff, refMu0_apply, refMu, if_neg h, ENNReal.ofReal_zero] at hS0
          exact hS0 rfl
        have hS0r : S0 ⊆ Finset.range (2 * pSmall I ε δ) := by
          simp only [transStates, refStates] at hS0t
          classical exact Finset.mem_powerset.1 (Finset.mem_filter.1 hS0t).1
        exact rru_restart_le I ε δ hp ws j hj0 hτ S0 hS0r
    _ = ∑ n ∈ Finset.range (BretParam I ε δ + 1), pexp (ruLvLaw (rruP I ε δ ws)
          (j * τParam I ε δ) (· ∈ transStates I ε δ) (rruNu I ε δ) n)
          (fun c => if c.1 < j * τParam I ε δ then 1 else 0) := by
        rw [rru_pexp_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [ruLvLaw, pexp_bind, rruNu, pexp_map]
        rfl
    _ ≤ ((j * τParam I ε δ : ℕ) : ℝ≥0∞) * (20 * (pSmall I ε δ : ℝ≥0∞) ^ 2) :=
        rru_lv_sum hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj ws hgood hτ _
    _ = _ := by push_cast; ring

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · capped cost ≤ level-process occupation; warm return cost per level via `LevelReturnCost`
-/
