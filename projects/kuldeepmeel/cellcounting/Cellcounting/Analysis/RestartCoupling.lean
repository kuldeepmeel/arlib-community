import Cellcounting.Analysis.RefChainLaw
import Cellcounting.Analysis.FWeightAdjacent
import Cellcounting.Model.Prior
import Cellcounting.Analysis.RefRestartAbort
import Cellcounting.Analysis.RefRestartEndpoint

/-!
# The capped restart and its virtual uncapped counterpart (`eq:alg-cap-probability`)

`prop:annealing`, the restart half (`algorithm.tex:283-311`).  Fix stored
multipliers `w^(1..j)` good at their own parameters.  The *virtual* restart runs
the same `μ₀` draw and the same `τ` trace steps of `P_{a, w^(a)}` for
`a = 1..j`, without a transition cap.  Its endpoint law is at most `2 μ_j`
(`lem:trace`, relative mixing with `eq:alg-minimum-mass`; for `j = 0` the endpoint
is the `μ₀` draw itself), and its total cost exceeds `B_ret` with probability at
most `H/[100(H+1)²] ≤ 1/[100(H+1)]` (warm return cost of `lem:trace`,
`π(A) ≥ 1/(5p²)`, Markov's inequality).  Whenever the cost is at most `B_ret` the
capped restart `refRestart` does not abort and ends where the virtual one ends.

`restart_coupling` states this as a coupling `κ` of the capped restart (first
coordinate) with the virtual endpoint (second coordinate).
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal

/-- INTERNAL: a `PMF` gives every set outer measure at most one. -/
theorem toOuterMeasure_le_one_aux {α : Type*} (p : PMF α) (s : Set α) :
    p.toOuterMeasure s ≤ 1 := by
  rw [PMF.toOuterMeasure_apply, ← p.tsum_coe]
  exact ENNReal.tsum_le_tsum fun a => Set.indicator_le_self s p a

/-- INTERNAL: the coupling of `restart_coupling` from two bounds on a restart law `ρ`:
abort probability `e ≤ 1/100`, and non-aborted endpoint sub-law at most `(3/2) m`.  Keep the
restart as the first coordinate; the second is its endpoint when it does not abort, and an
independent draw from the non-aborted endpoint law when it does.  The second marginal is then
`P(¬abort, S) / P(¬abort) ≤ (3/2)(1 + 2e) m ≤ 2m`, and the two disagree only on abort.
TEXLINE: sections/algorithm.tex:316-321 -/
theorem restart_couple_of_bounds {ρ : PMF Restart} {m : Finset ℕ → ℝ≥0∞} {e : ℝ≥0∞}
    (he : e ≤ 1 / 100) (hA : ρ.toOuterMeasure {r | r.aborted = true} ≤ e)
    (hB : ∀ S, ρ.toOuterMeasure {r | r.aborted = false ∧ r.S = S} ≤ 3 / 2 * m S) :
    ∃ κ : PMF (Restart × Finset ℕ), κ.map Prod.fst = ρ ∧
      (∀ S, κ.map Prod.snd S ≤ 2 * m S) ∧
      κ.toOuterMeasure {q | q.1.aborted = true ∨ q.1.S ≠ q.2} ≤ e := by
  classical
  set A : Set Restart := {r | r.aborted = true} with hAdef
  set N : Set Restart := {r | r.aborted = false} with hNdef
  set a := ρ.toOuterMeasure A
  set n := ρ.toOuterMeasure N
  have hsum : a + n = 1 := by
    simp only [a, n, PMF.toOuterMeasure_apply]
    rw [← ENNReal.tsum_add, ← ρ.tsum_coe]
    refine tsum_congr fun r => ?_
    cases h : r.aborted <;> simp [A, N, Set.indicator, h]
  have hn : 2⁻¹ ≤ n := by
    by_contra hlt
    push Not at hlt
    have h100 : (1 / 100 : ℝ≥0∞) ≤ 2⁻¹ := by
      have h : ((1 / 100 : NNReal) : ℝ≥0∞) ≤ ((2⁻¹ : NNReal) : ℝ≥0∞) := by
        exact_mod_cast (by rw [← NNReal.coe_le_coe]; push_cast; norm_num :
          (1 / 100 : NNReal) ≤ 2⁻¹)
      simpa using h
    have h1 : a + n < 2⁻¹ + 2⁻¹ := ENNReal.add_lt_add_of_le_of_lt
      (ne_top_of_le_ne_top ENNReal.one_ne_top (toOuterMeasure_le_one_aux _ _))
      ((hA.trans he).trans h100) hlt
    rw [hsum, ENNReal.inv_two_add_inv_two] at h1
    exact lt_irrefl _ h1
  have hNne : ∃ r ∈ N, r ∈ ρ.support := by
    by_contra hne
    push Not at hne
    have : n = 0 := by
      simp only [n, PMF.toOuterMeasure_apply]
      refine ENNReal.tsum_eq_zero.2 fun r => ?_
      by_cases hr : r ∈ N
      · simp [Set.indicator_of_mem hr, (PMF.mem_support_iff _ _).not.1 (hne r hr) |> not_not.1]
      · simp [Set.indicator_of_notMem hr]
    rw [this] at hn
    norm_num at hn
  let ν : PMF (Finset ℕ) := (ρ.filter N hNne).map Restart.S
  let k : Restart → PMF (Restart × Finset ℕ) := fun r =>
    if r.aborted then ν.map (fun S => (r, S)) else PMF.pure (r, r.S)
  refine ⟨ρ.bind k, ?_, ?_, ?_⟩
  · rw [PMF.map_bind]
    conv_rhs => rw [← PMF.bind_pure ρ]
    congr 1
    funext r
    by_cases h : r.aborted
    · simp only [k, h, ↓reduceIte, PMF.map_comp, Function.comp_def]
      exact PMF.map_const ν r
    · simp [k, h, PMF.pure_map]
  · intro S0
    set X : Set Restart := {r | r.aborted = false ∧ r.S = S0} with hXdef
    set x := ρ.toOuterMeasure X
    have hν : ν S0 = x * n⁻¹ := by
      show ((ρ.filter N hNne).map Restart.S) S0 = ρ.toOuterMeasure X * (ρ.toOuterMeasure N)⁻¹
      rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
        PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply,
        ← ENNReal.tsum_mul_right]
      refine tsum_congr fun r => ?_
      by_cases h2 : r.S = S0
      · rw [Set.indicator_of_mem (show r ∈ Restart.S ⁻¹' {S0} from h2), PMF.filter_apply]
        by_cases h1 : r.aborted <;> simp [Set.indicator, X, N, h1, h2]
      · rw [Set.indicator_of_notMem (show r ∉ Restart.S ⁻¹' {S0} from h2)]
        simp [Set.indicator, X, h2]
    have hk : ∀ r, ρ r * ((k r).map Prod.snd) S0 = A.indicator ρ r * ν S0 + X.indicator ρ r := by
      intro r
      by_cases h1 : r.aborted
      · have hm : (ν.map (fun S => (r, S))).map Prod.snd = ν := by
          rw [PMF.map_comp]; exact PMF.map_id ν
        simp only [k, h1, ↓reduceIte, hm]
        simp [Set.indicator, A, X, h1]
      · by_cases h2 : r.S = S0
        · simp [k, h1, h2, Set.indicator, A, X, PMF.pure_map]
        · simp [k, h1, h2, Set.indicator, A, X, PMF.pure_map, PMF.pure_apply, Ne.symm h2]
    rw [PMF.map_bind, PMF.bind_apply, tsum_congr hk, ENNReal.tsum_add, ENNReal.tsum_mul_right,
      ← PMF.toOuterMeasure_apply, ← PMF.toOuterMeasure_apply, hν]
    have hinv : n⁻¹ ≤ 2 := ENNReal.inv_le_iff_inv_le.2 hn
    have hx : x ≤ 3 / 2 * m S0 := hB S0
    have hnum : (3 / 2 : ℝ≥0∞) * (1 / 100 * 2 + 1) ≤ 2 := by
      have h : ((3 / 2 * (1 / 100 * 2 + 1) : NNReal) : ℝ≥0∞) ≤ ((2 : NNReal) : ℝ≥0∞) := by
        exact_mod_cast (by rw [← NNReal.coe_le_coe]; push_cast; norm_num :
          (3 / 2 * (1 / 100 * 2 + 1) : NNReal) ≤ 2)
      simpa using h
    calc a * (x * n⁻¹) + x ≤ 1 / 100 * (x * 2) + x := by gcongr; exact hA.trans he
      _ = x * (1 / 100 * 2 + 1) := by ring
      _ ≤ (3 / 2 * m S0) * (1 / 100 * 2 + 1) := by gcongr
      _ = m S0 * (3 / 2 * (1 / 100 * 2 + 1)) := by ring
      _ ≤ m S0 * 2 := by gcongr
      _ = 2 * m S0 := by ring
  · rw [PMF.toOuterMeasure_bind_apply]
    refine le_trans ?_ hA
    show _ ≤ ρ.toOuterMeasure A
    rw [PMF.toOuterMeasure_apply]
    refine ENNReal.tsum_le_tsum fun r => ?_
    by_cases h : r.aborted
    · simp only [A, Set.indicator_of_mem (show r ∈ {r : Restart | r.aborted = true} from h)]
      exact mul_le_of_le_one_right' (toOuterMeasure_le_one_aux _ _)
    · simp [k, h, PMF.toOuterMeasure_pure_apply]
/-- **The capped restart agrees with a dominated virtual restart**
(`eq:alg-cap-probability` and the endpoint bound `≤ 2μ_j`): there is a coupling of
the capped reference restart of phase `j` with a virtual endpoint whose law is at
most `2 μ_j`, such that, except with probability `1/[100(H+1)]`, the capped
restart does not abort and ends at the virtual endpoint.
PAPER: sections/algorithm.tex:283-319 -/
theorem restart_coupling (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (ws : ℕ → ℕ → ℕ → ℚ) (hgood : ∀ a ≤ j, goodMult I ε δ a (ws a)) :
    ∃ κ : PMF (Restart × Finset ℕ),
      κ.map Prod.fst = (refMu0 I ε δ).bind (refRestart I ε δ ws j) ∧
      (∀ S, κ.map Prod.snd S ≤ 2 * ENNReal.ofReal (refMu I ε δ j S)) ∧
      κ.toOuterMeasure {q | q.1.aborted = true ∨ q.1.S ≠ q.2} ≤
        1 / (100 * ((HParam I ε δ : ℝ≥0∞) + 1)) := by
  refine restart_couple_of_bounds ?_
    (refRestart_abort_le hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj ws hgood)
    (refRestart_endpoint_le hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj ws hgood)
  refine ENNReal.div_le_div_left ?_ 1
  calc (100 : ℝ≥0∞) = 100 * 1 := (mul_one _).symm
    _ ≤ 100 * ((HParam I ε δ : ℝ≥0∞) + 1) := by gcongr; exact le_add_self

end Cellcounting.Analysis
