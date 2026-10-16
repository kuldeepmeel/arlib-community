import Cellcounting.Analysis.RefChainLaw
import Cellcounting.Analysis.RefStationary
import Cellcounting.Analysis.PmfClose
import Cellcounting.Analysis.RefStepReversible
import Cellcounting.Analysis.ObservableVariance
import Cellcounting.Analysis.LazyReversibleAutocov
import Cellcounting.Analysis.RealPexp
import Cellcounting.Model.Prior

/-!
# Time averages from a dominated initial law (`lem:time-average`)

`transport.tex:575-630`.  For good multipliers `w` at parameter `j`, the exact
Metropolis chain `P_{j, w}` (`refStep`) is reversible with stationary law
`π = λ / Λ` on `X` (`refPi`).  For an observable `G` fixed by the projection `Q`
(constant on each defect type `A_il`) and an initial law `ν ≤ U π`, the average of
`N ≥ 1` consecutive observations `G(S_0), …, G(S_{N-1})` has mean squared error
about `E_π G` at most `2 U K_obs Var_π(G) / N`.

`refTraj` is the law of the final state and the running sum `Σ_{t<N} G(S_t)`,
accumulated by `loop` exactly as `refObserve` accumulates its tallies.

Proof structure, following the paper:
* `ta_inner_refQ`, `ta_inner_sq_le`: since `𝓠 G = G`, `⟨G_c, g⟩_π² ≤ K_obs Var_π(G) 𝓔(g)`
  (Cauchy–Schwarz plus `observable_variance`);
* `lra_autocov_sum_le`, `lra_autocov_nonneg` (`LazyReversibleAutocov`): every partial
  sum of the autocovariances `c_t` is at most `K_obs Var_π(G)`, and each `c_t ≥ 0`;
* `taW`, `taE_le`: the stationary second moment `E_π[(Σ_{t<N} G_c(S_t))²]`, computed by
  first-step recursion, is at most `2 N K_obs Var_π(G)`;
* `ta_traj_link`: `refTraj`'s second moment is that recursion;
* the domination `ν ≤ U π` is applied to the starting state only, which is the paper's
  remark that only the initial factor of the path law changes.
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal

/-! ### The exact chain `P_{j, w}` on `X` -/

open Classical in
/-- INTERNAL: the type of a defect state names two distinct labels below `p`; a local
copy of `oa_kind_defect`, which lives in a module that imports this one.
TEXLINE: sections/signatures.tex:13-41 -/
theorem ta_kind_defect (I : Instance) (ε δ : ℚ) (S : Finset ℕ) (i l : ℕ)
    (h : kind I ε δ S = .defect i l) : i < pSmall I ε δ ∧ l < pSmall I ε δ ∧ i ≠ l := by
  simp only [kind] at h
  split_ifs at h with h1 h2 h3
  obtain ⟨x, hxE⟩ := Finset.card_eq_one.mp h3.1
  obtain ⟨y, hyF⟩ := Finset.card_eq_one.mp h3.2
  rw [hxE, Finset.sup_singleton] at h
  rw [hyF, Finset.sup_singleton] at h
  injection h with hi hl
  subst hi; subst hl
  have hxE' : x ∈ (Finset.range (pSmall I ε δ)).filter
      fun k => 2 * k ∉ S ∧ 2 * k + 1 ∉ S := hxE ▸ Finset.mem_singleton_self x
  have hyF' : y ∈ (Finset.range (pSmall I ε δ)).filter
      fun k => 2 * k ∈ S ∧ 2 * k + 1 ∈ S := hyF ▸ Finset.mem_singleton_self y
  obtain ⟨hxrange, hxcond⟩ := Finset.mem_filter.mp hxE'
  obtain ⟨hyrange, hycond⟩ := Finset.mem_filter.mp hyF'
  refine ⟨Finset.mem_range.mp hxrange, Finset.mem_range.mp hyrange, ?_⟩
  rintro rfl
  exact hxcond.1 hycond.1

/-- INTERNAL: `f_j(S) ≥ 0`. -/
theorem ta_fWeight_nonneg (I : Instance) (ε δ : ℚ) (j : ℕ) (S : Finset ℕ) :
    0 ≤ fWeight I ε δ j S := by
  unfold fWeight
  refine mul_nonneg ?_ (Finset.prod_nonneg fun s _ => by positivity)
  exact Finset.sum_nonneg fun z _ => by positivity

/-- INTERNAL: `C(j) ≥ 0`. -/
theorem ta_Cpart_nonneg (I : Instance) (ε δ : ℚ) (j : ℕ) : 0 ≤ Cpart I ε δ j :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- INTERNAL: good multipliers are nonnegative, so `λ ≥ 0`.
TEXLINE: sections/transport.tex:36-54 -/
theorem ta_refLam_nonneg (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ j w) (S : Finset ℕ) : 0 ≤ refLam I ε δ S j w := by
  unfold refLam
  split
  · rename_i i l hk
    obtain ⟨hi, hl, hil⟩ := ta_kind_defect I ε δ S i l hk
    refine mul_nonneg (ta_fWeight_nonneg I ε δ j S) (le_trans ?_ (hgood i hi l hl hil).1)
    exact div_nonneg (ta_Cpart_nonneg I ε δ j) (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun S _ => ta_fWeight_nonneg I ε δ j S))
  · exact ta_fWeight_nonneg I ε δ j S

/-- INTERNAL: `π ≥ 0`. -/
theorem ta_refPi_nonneg (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ j w) (S : Finset ℕ) : 0 ≤ refPi I ε δ j w S := by
  unfold refPi
  split
  · exact div_nonneg (ta_refLam_nonneg I ε δ j w hgood S)
      (Finset.sum_nonneg fun S _ => ta_refLam_nonneg I ε δ j w hgood S)
  · exact le_refl 0

/-- INTERNAL: `Σ_X π = 1` once `Λ ≠ 0`. -/
theorem ta_refPi_sum (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (h : refLamTot I ε δ j w ≠ 0) : ∑ S ∈ chainStates I ε δ, refPi I ε δ j w S = 1 := by
  unfold refPi
  rw [Finset.sum_congr rfl fun S hS => if_pos hS, ← Finset.sum_div]
  exact div_self h

/-- INTERNAL: `nthWith` returns an element of `{0, …, 2p-1}`; a local copy of
`nthWith_lt` (`RefRestartEndpoint`).
TEXLINE: sections/transport.tex:60-69 -/
theorem ta_nthWith_lt (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (S : Finset ℕ) (v : Bool)
    (t : ℕ) : nthWith I ε δ S v t < 2 * pSmall I ε δ := by
  unfold nthWith
  rw [List.getD_eq_getElem?_getD]
  cases h : ((List.range (2 * pSmall I ε δ)).filter fun e => decide (e ∈ S) == v)[t]? with
  | none => simp; omega
  | some e =>
    simp only [Option.getD_some]
    have := List.mem_of_getElem? h
    exact List.mem_range.1 (List.mem_filter.1 this).1

open Classical in
/-- INTERNAL: one exact transition from a state of `X` stays in `X`.
TEXLINE: sections/transport.tex:60-69 -/
theorem ta_refStep_support (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (a : ℕ)
    (w : ℕ → ℕ → ℚ) (S : Finset ℕ) (hS : S ∈ chainStates I ε δ)
    (S' : Finset ℕ) (h : S' ∈ (refStep I ε δ a w S).support) : S' ∈ chainStates I ε δ := by
  have hT : ∀ u1 u2, insert (nthWith I ε δ S false u2) (S.erase (nthWith I ε δ S true u1)) ∈
      refStates I ε δ := by
    intro u1 u2
    unfold refStates
    rw [Finset.mem_powerset]
    refine Finset.insert_subset (Finset.mem_range.2 (ta_nthWith_lt I ε δ hp _ _ _)) ?_
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

open Classical in
/-- INTERNAL: the rows of `P_{j, w}` on `X` sum to one.
TEXLINE: sections/transport.tex:60-69 -/
theorem ta_refPk_row (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (j : ℕ)
    (w : ℕ → ℕ → ℚ) (S : Finset ℕ) (hS : S ∈ chainStates I ε δ) :
    ∑ S' ∈ chainStates I ε δ, refPk I ε δ j w S S' = 1 := by
  have := sum_toReal_eq_one (refStep I ε δ j w S) (chainStates I ε δ)
    (ta_refStep_support I ε δ hp j w S hS)
  exact this

/-- INTERNAL: `P_{j, w}` is lazy: it holds on a fair bit, so `P(S, S) ≥ 1/2`.
TEXLINE: sections/transport.tex:60-69, 616-621 -/
theorem ta_refPk_lazy (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ) (S : Finset ℕ) :
    1 / 2 ≤ refPk I ε δ j w S S := by
  unfold refPk
  have hge : (1 / 2 : ℝ≥0∞) ≤ refStep I ε δ j w S S := by
    unfold refStep
    erw [PMF.bind_apply]
    refine le_trans ?_ (ENNReal.le_tsum true)
    simp [Arlib.Computation.ProbRAM.fair, PMF.bernoulli_apply]
    erw [PMF.pure_apply_self, mul_one]
  have := ENNReal.toReal_mono (PMF.apply_ne_top _ _) hge
  simpa using this

/-! ### Second moment of a trajectory sum, abstractly -/

section TaAbstract

open Finset
variable {α : Type*} (X : Finset α) (P : α → α → ℝ) (g : α → ℝ)

/-- INTERNAL: `taW k S d = E_S[(d + Σ_{t=1}^{k} g(S_t))²]` for the chain with kernel `P` on
`X`, written as a backward recursion over the first step.
TEXLINE: sections/transport.tex:621-626 -/
noncomputable def taW : ℕ → α → ℝ → ℝ
  | 0 => fun _ d => d ^ 2
  | k + 1 => fun S d => ∑ S' ∈ X, P S S' * taW k S' (d + g S')

/-- INTERNAL: `taH k = Σ_{t=1}^{k} P^t g`, the conditional mean of the future sum.
TEXLINE: sections/transport.tex:621-626 -/
noncomputable def taH (k : ℕ) (S : α) : ℝ := ∑ t ∈ range k, (lraOp X P)^[t + 1] g S

/-- INTERNAL: first-step recursion for `taH`. -/
theorem taH_succ (k : ℕ) (S : α) :
    taH X P g (k + 1) S = ∑ S' ∈ X, P S S' * (g S' + taH X P g k S') := by
  unfold taH
  rw [sum_range_succ']
  simp only [mul_add, sum_add_distrib, mul_sum]
  rw [sum_comm, add_comm]
  congr 1
  · refine sum_congr rfl fun t _ => ?_
    rw [Function.iterate_succ_apply' (lraOp X P) (t + 1)]
    simp only [lraOp]

/-- INTERNAL: `taW k S d` is a quadratic polynomial in the offset `d`. -/
theorem taW_split (hrow : ∀ S ∈ X, ∑ S' ∈ X, P S S' = 1) (k : ℕ) :
    ∀ S ∈ X, ∀ d, taW X P g k S d = d ^ 2 + 2 * d * taH X P g k S + taW X P g k S 0 := by
  induction k with
  | zero => intro S _ d; simp [taW, taH]
  | succ k ih =>
    intro S hS d
    simp only [taW]
    have e1 : ∑ S' ∈ X, P S S' * taW X P g k S' (d + g S') = ∑ S' ∈ X, P S S' *
        ((d + g S') ^ 2 + 2 * (d + g S') * taH X P g k S' + taW X P g k S' 0) :=
      sum_congr rfl fun S' hS' => by rw [ih S' hS']
    have e2 : ∑ S' ∈ X, P S S' * taW X P g k S' (0 + g S') = ∑ S' ∈ X, P S S' *
        ((0 + g S') ^ 2 + 2 * (0 + g S') * taH X P g k S' + taW X P g k S' 0) :=
      sum_congr rfl fun S' hS' => by rw [ih S' hS']
    rw [e1, e2, taH_succ]
    have hd : d ^ 2 = ∑ S' ∈ X, P S S' * d ^ 2 := by rw [← sum_mul, hrow S hS, one_mul]
    rw [hd, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun S' _ => by ring

variable {π : α → ℝ}

/-- INTERNAL: **stationary mean squared error of a sum**: if every autocovariance
`c_t = ⟨g, P^t g⟩_π` is nonnegative and every partial sum `Σ_{t<n} c_t` is at most `A`,
then `E_π[(Σ_{t=0}^{k} g(S_t))²] = Σ_{j ≤ k} (c_0 + 2 Σ_{1 ≤ t ≤ j} c_t) ≤ 2 (k + 1) A`.
TEXLINE: sections/transport.tex:621-626 -/
theorem taE_le (hrow : ∀ S ∈ X, ∑ S' ∈ X, P S S' = 1)
    (hrev : ∀ S ∈ X, ∀ S' ∈ X, π S * P S S' = π S' * P S' S)
    (hc0 : ∀ t, 0 ≤ lraInner X π g ((lraOp X P)^[t] g)) (A : ℝ)
    (hA : ∀ n, ∑ t ∈ range n, lraInner X π g ((lraOp X P)^[t] g) ≤ A) (k : ℕ) :
    ∑ S ∈ X, π S * taW X P g k S (g S) ≤ 2 * (k + 1) * A := by
  set c : ℕ → ℝ := fun t => lraInner X π g ((lraOp X P)^[t] g) with hc
  have hE : ∀ k, ∑ S ∈ X, π S * taW X P g k S (g S) =
      c 0 + 2 * ∑ t ∈ range k, c (t + 1) + ∑ S ∈ X, π S * taW X P g k S 0 := by
    intro k
    rw [sum_congr rfl fun S hS => by rw [taW_split X P g hrow k S hS (g S)]]
    simp only [mul_add, sum_add_distrib]
    congr 2
    · simp [hc, lraInner, sq, mul_assoc]
    · simp only [hc, lraInner, taH, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun t _ => sum_congr rfl fun S _ => by ring
  have hB : ∀ k, ∑ S ∈ X, π S * taW X P g (k + 1) S 0 = ∑ S ∈ X, π S * taW X P g k S (g S) := by
    intro k
    have := lra_stat hrev hrow (fun S' => taW X P g k S' (g S'))
    simp only [lraOp] at this
    rw [← this]
    simp [taW]
  have hA0 : 0 ≤ A := by simpa using hA 0
  have hB2 : ∀ k, c 0 + 2 * ∑ t ∈ range k, c (t + 1) ≤ 2 * A := by
    intro k
    have h1 := hA (k + 1)
    rw [sum_range_succ'] at h1
    have h2 := hc0 0
    have h3 : 0 ≤ ∑ t ∈ range k, c (t + 1) := sum_nonneg fun t _ => hc0 (t + 1)
    simp only [hc] at h2 h3 ⊢
    linarith
  induction k with
  | zero =>
    rw [hE]; simp [taW]
    have := hB2 0; simp at this; linarith
  | succ k ih =>
    rw [hE, hB]
    have := hB2 (k + 1)
    push_cast
    linarith

end TaAbstract

/-! ### The trajectory law -/

/-- INTERNAL: `N` consecutive observations of `P_{j, w}` from `S0` (the starting
state included): the law of the last state and of `Σ_{t<N} G(S_t)`.
TEXLINE: sections/transport.tex:579-586 -/
noncomputable def refTraj (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (G : Finset ℕ → ℝ) (N : ℕ) (S0 : Finset ℕ) : PMF (Finset ℕ × ℝ) :=
  loop (fun _ x => (refStep I ε δ j w x.1).map fun S' => (S', x.2 + G S')) (N - 1)
    (S0, G S0)

/-- INTERNAL: a `loop` whose step ignores the index, unrolled at its first iteration; a
local copy of `loop_const_succ` (`RefRestartEndpoint`, not imported here). -/
theorem ta_loop_const_succ {β : Type} (g : β → PMF β) (k : ℕ) (b : β) :
    loop (fun _ => g) (k + 1) b = (g b).bind (loop (fun _ => g) k) := by
  induction k generalizing b with
  | zero => rw [loop_succ, loop_zero, PMF.pure_bind]; exact (PMF.bind_pure _).symm
  | succ k ih =>
    rw [loop_succ, ih, PMF.bind_bind]
    congr 1; funext x; rw [loop_succ]

/-- INTERNAL: one step of `P_{j, w}` from a state of `X` has finite support. -/
theorem ta_refStep_finite (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (j : ℕ)
    (w : ℕ → ℕ → ℚ) (S : Finset ℕ) (hS : S ∈ chainStates I ε δ) :
    (refStep I ε δ j w S).support.Finite :=
  (chainStates I ε δ).finite_toSet.subset fun _ h => ta_refStep_support I ε δ hp j w S hS _ h

/-- INTERNAL: from a state of `X`, the observation loop has finite support and stays
in `X`. -/
theorem ta_loop_support (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (j : ℕ)
    (w : ℕ → ℕ → ℚ) (G : Finset ℕ → ℝ) (k : ℕ) :
    ∀ x : Finset ℕ × ℝ, x.1 ∈ chainStates I ε δ →
      (loop (fun _ x => (refStep I ε δ j w x.1).map fun S' => (S', x.2 + G S')) k x).support.Finite ∧
      ∀ y ∈ (loop (fun _ x => (refStep I ε δ j w x.1).map fun S' => (S', x.2 + G S')) k x).support,
        y.1 ∈ chainStates I ε δ := by
  induction k with
  | zero => intro x hx; simp [hx]
  | succ k ih =>
    intro x hx
    have hstep : ∀ y ∈ ((refStep I ε δ j w x.1).map fun S' => (S', x.2 + G S')).support,
        y.1 ∈ chainStates I ε δ := by
      intro y hy
      rw [PMF.support_map] at hy
      obtain ⟨S', hS', rfl⟩ := hy
      exact ta_refStep_support I ε δ hp j w x.1 hx S' hS'
    rw [ta_loop_const_succ]
    refine ⟨?_, fun y hy => ?_⟩
    · rw [PMF.support_bind]
      refine Set.Finite.biUnion ?_ fun y hy => (ih y (hstep y hy)).1
      rw [PMF.support_map]
      exact (ta_refStep_finite I ε δ hp j w x.1 hx).image _
    · rw [PMF.mem_support_bind_iff] at hy
      obtain ⟨z, hz, hy⟩ := hy
      exact (ih z (hstep z hz)).2 y hy

open Classical in
/-- INTERNAL: the second moment of the observation loop about any centre `c` is the
abstract recursion `taW` for the observable `G - m`, offset by `a - c + k m`.
TEXLINE: sections/transport.tex:621-626 -/
theorem ta_traj_link (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (j : ℕ)
    (w : ℕ → ℕ → ℚ) (G : Finset ℕ → ℝ) (m : ℝ) (k : ℕ) :
    ∀ S ∈ chainStates I ε δ, ∀ a c : ℝ,
      rpexp (loop (fun _ x => (refStep I ε δ j w x.1).map fun S' => (S', x.2 + G S')) k (S, a))
          (fun x => (x.2 - c) ^ 2) =
        taW (chainStates I ε δ) (refPk I ε δ j w) (fun S => G S - m) k S (a - c + k * m) := by
  induction k with
  | zero => intro S _ a c; simp [rpexp_pure, taW]
  | succ k ih =>
    intro S hS a c
    rw [ta_loop_const_succ, rpexp_bind _ _ (by
        rw [PMF.support_map]; exact (ta_refStep_finite I ε δ hp j w S hS).image _)
      (fun y hy => (ta_loop_support I ε δ hp j w G k y (by
        rw [PMF.support_map] at hy
        obtain ⟨S', hS', rfl⟩ := hy
        exact ta_refStep_support I ε δ hp j w S hS S' hS')).1),
      rpexp_map _ (ta_refStep_finite I ε δ hp j w S hS)]
    rw [rpexp_congr _ fun S' hS' => ih S' (ta_refStep_support I ε δ hp j w S hS S' hS') _ _,
      rpexp_eq_sum _ _ (ta_refStep_support I ε δ hp j w S hS)]
    simp only [taW, refPk]
    refine Finset.sum_congr rfl fun S' _ => ?_
    congr 2
    push_cast; ring

open Classical in
/-- INTERNAL: pairing with an observable fixed by `𝓠` (constant on each defect type)
does not see the difference between `g` and `𝓠 g`.
TEXLINE: sections/transport.tex:592-598 -/
theorem ta_inner_refQ (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ j w) (H : Finset ℕ → ℝ)
    (hH : ∀ S S' i l, kind I ε δ S = .defect i l → kind I ε δ S' = .defect i l → H S = H S')
    (g : Finset ℕ → ℝ) :
    ∑ S ∈ chainStates I ε δ, refPi I ε δ j w S * H S * refQ I ε δ j w g S =
      ∑ S ∈ chainStates I ε δ, refPi I ε δ j w S * H S * g S := by
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib,
    ← Finset.sum_fiberwise_of_maps_to (s := chainStates I ε δ)
      (t := (chainStates I ε δ).image (kind I ε δ)) (g := kind I ε δ)
      (fun S hS => Finset.mem_image_of_mem _ hS)]
  refine Finset.sum_eq_zero fun κ _ => ?_
  cases κ with
  | transversal =>
    refine Finset.sum_eq_zero fun S hS => ?_
    have hk := (Finset.mem_filter.1 hS).2
    simp [refQ, hk]
  | outside =>
    refine Finset.sum_eq_zero fun S hS => ?_
    have hk := (Finset.mem_filter.1 hS).2
    simp [refQ, hk]
  | defect i l =>
    set D := (chainStates I ε δ).filter fun S => kind I ε δ S = .defect i l with hD
    rcases D.eq_empty_or_nonempty with hD0 | ⟨S0, hS0⟩
    · rw [hD0]; simp
    set QD := (∑ S' ∈ D, refPi I ε δ j w S' * g S') / ∑ S' ∈ D, refPi I ε δ j w S' with hQD
    have hQS : ∀ S ∈ D, refQ I ε δ j w g S = QD := by
      intro S hS
      have hk := (Finset.mem_filter.1 hS).2
      simp only [refQ, hk, hQD, hD]
    have hHS : ∀ S ∈ D, H S = H S0 := fun S hS =>
      hH S S0 i l (Finset.mem_filter.1 hS).2 (Finset.mem_filter.1 hS0).2
    have : ∑ S ∈ D, (refPi I ε δ j w S * H S * refQ I ε δ j w g S -
        refPi I ε δ j w S * H S * g S) =
        H S0 * (QD * ∑ S ∈ D, refPi I ε δ j w S - ∑ S ∈ D, refPi I ε δ j w S * g S) := by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [hQS S hS, hHS S hS]; ring
    rw [this]
    by_cases hz : ∑ S ∈ D, refPi I ε δ j w S = 0
    · have h0 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun S _ => ta_refPi_nonneg I ε δ j w hgood S)).1 hz
      rw [hz, Finset.sum_eq_zero fun S hS => by rw [h0 S hS, zero_mul]]
      ring
    · rw [hQD, div_mul_cancel₀ _ hz, sub_self, mul_zero]

/-- INTERNAL: **the restricted observable inequality**: for `G` fixed by `𝓠`,
`⟨G_c, g⟩_π² ≤ K_obs Var_π(G) 𝓔(g)` for every `g`.
TEXLINE: sections/transport.tex:592-598 -/
theorem ta_inner_sq_le (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) (G : Finset ℕ → ℝ)
    (hQ : ∀ S S' i l, kind I ε δ S = .defect i l → kind I ε δ S' = .defect i l → G S = G S')
    (hsum : ∑ S ∈ chainStates I ε δ, refPi I ε δ j w S = 1) (g : Finset ℕ → ℝ) :
    lraInner (chainStates I ε δ) (refPi I ε δ j w)
        (fun S => G S - refPiMean I ε δ j w G) g ^ 2 ≤
      ((KobsParam I ε δ : ℝ) * refPiVar I ε δ j w G) *
        lraEnergy (chainStates I ε δ) (refPi I ε δ j w) (refPk I ε δ j w) g := by
  set X := chainStates I ε δ
  set π := refPi I ε δ j w
  set m := refPiMean I ε δ j w G
  set M := ∑ S' ∈ X, π S' * refQ I ε δ j w g S'
  have hc : ∑ S ∈ X, π S * (G S - m) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
    simp [m, refPiMean, π, X]
  have h1 : lraInner X π (fun S => G S - m) g =
      ∑ S ∈ X, π S * (G S - m) * (refQ I ε δ j w g S - M) := by
    unfold lraInner
    rw [← ta_inner_refQ I ε δ j w hgood (fun S => G S - m)
      (fun S S' i l h h' => by rw [hQ S S' i l h h']) g]
    have : ∀ S, π S * (G S - m) * (refQ I ε δ j w g S - M) =
        π S * (G S - m) * refQ I ε δ j w g S - π S * (G S - m) * M := fun S => by ring
    rw [Finset.sum_congr rfl fun S _ => this S, Finset.sum_sub_distrib, ← Finset.sum_mul, hc,
      zero_mul, sub_zero]
  rw [h1]
  have hπ : ∀ S, 0 ≤ π S := ta_refPi_nonneg I ε δ j w hgood
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul X
    (r := fun S => π S * (G S - m) * (refQ I ε δ j w g S - M))
    (f := fun S => π S * (G S - m) ^ 2) (g := fun S => π S * (refQ I ε δ j w g S - M) ^ 2)
    (fun S _ => mul_nonneg (hπ S) (sq_nonneg _)) (fun S _ => mul_nonneg (hπ S) (sq_nonneg _))
    (fun S _ => le_of_eq (by ring))
  have hov := observable_variance hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj w hgood g
  have hv : 0 ≤ refPiVar I ε δ j w G :=
    Finset.sum_nonneg fun S _ => mul_nonneg (hπ S) (sq_nonneg _)
  have hE : refEnergy I ε δ j w g = lraEnergy X π (refPk I ε δ j w) g := rfl
  refine hcs.trans ?_
  change refPiVar I ε δ j w G * ∑ S ∈ X, π S * (refQ I ε δ j w g S - M) ^ 2 ≤ _
  rw [← hE]
  calc refPiVar I ε δ j w G * ∑ S ∈ X, π S * (refQ I ε δ j w g S - M) ^ 2
      ≤ refPiVar I ε δ j w G * ((KobsParam I ε δ : ℝ) * refEnergy I ε δ j w g) :=
        mul_le_mul_of_nonneg_left hov hv
    _ = _ := by ring

/-- **Time averages from a dominated initial law** (`lem:time-average`): for good
multipliers, an observable `G` constant on each defect type (`Q G = G`), and an
initial law `ν ≤ U π`, the average of `N ≥ 1` consecutive observations satisfies
`E_ν[(N⁻¹ Σ_t G(S_t) - E_π G)²] ≤ 2 U K_obs Var_π(G) / N`.
PAPER: sections/transport.tex:575-630 -/
theorem time_average (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) (G : Finset ℕ → ℝ)
    (hQ : ∀ S S' i l, kind I ε δ S = .defect i l → kind I ε δ S' = .defect i l → G S = G S')
    (U : ℝ) (ν : PMF (Finset ℕ)) (hν : ∀ S, ν S ≤ ENNReal.ofReal (U * refPi I ε δ j w S))
    (N : ℕ) (hN : 1 ≤ N) :
    pexp (ν.bind (refTraj I ε δ j w G N))
        (fun x => ENNReal.ofReal ((x.2 / N - refPiMean I ε δ j w G) ^ 2)) ≤
      ENNReal.ofReal (2 * U * KobsParam I ε δ * refPiVar I ε δ j w G / N) := by
  set X := chainStates I ε δ with hXdef
  set π := refPi I ε δ j w with hπdef
  set m := refPiMean I ε δ j w G with hmdef
  set v := refPiVar I ε δ j w G with hvdef
  set Gc : Finset ℕ → ℝ := fun S => G S - m with hGc
  have hπ : ∀ S, 0 ≤ π S := ta_refPi_nonneg I ε δ j w hgood
  -- `ν` is a law, so `U π` is somewhere positive: `U > 0` and `Λ ≠ 0`
  obtain ⟨S0, hS0⟩ : ∃ S, 0 < U * π S := by
    by_contra h
    push Not at h
    have h0 : ∀ S, ν S = 0 := fun S => le_antisymm
      ((hν S).trans (by rw [ENNReal.ofReal_eq_zero.2 (h S)])) bot_le
    have := ν.tsum_coe
    simp [h0] at this
  have hU : 0 < U := by
    by_contra h; push Not at h; nlinarith [hπ S0, mul_nonpos_of_nonpos_of_nonneg h (hπ S0)]
  have hΛ : refLamTot I ε δ j w ≠ 0 := by
    intro h0
    have : π S0 = 0 := by simp only [hπdef, refPi, h0, div_zero, ite_self]
    rw [this, mul_zero] at hS0; exact lt_irrefl 0 hS0
  have hsum := ta_refPi_sum I ε δ j w hΛ
  have hνX : ∀ S, S ∉ X → ν S = 0 := by
    intro S hS
    refine le_antisymm ((hν S).trans ?_) bot_le
    simp [hπdef, refPi, ← hXdef, hS]
  -- the chain on `X`
  have hrow : ∀ S ∈ X, ∑ S' ∈ X, refPk I ε δ j w S S' = 1 := ta_refPk_row I ε δ hp j w
  have hrev : ∀ S ∈ X, ∀ S' ∈ X, π S * refPk I ε δ j w S S' = π S' * refPk I ε δ j w S' S :=
    fun S hS S' hS' => refStep_reversible I ε δ hp j w hgood S S' hS hS'
  have hP0 : ∀ S ∈ X, ∀ S' ∈ X, 0 ≤ refPk I ε δ j w S S' := fun _ _ _ _ => ENNReal.toReal_nonneg
  have hlazy : ∀ S ∈ X, 1 / 2 ≤ refPk I ε δ j w S S := fun S _ => ta_refPk_lazy I ε δ j w S
  have hv0 : 0 ≤ v := Finset.sum_nonneg fun S _ => mul_nonneg (hπ S) (sq_nonneg _)
  have hA0 : 0 ≤ (KobsParam I ε δ : ℝ) * v := mul_nonneg (Nat.cast_nonneg _) hv0
  have hA := lra_autocov_sum_le (fun S _ => hπ S) hP0 hrow hrev hlazy Gc _ hA0
    (ta_inner_sq_le hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj w hgood G hQ hsum)
  have hc0 := lra_autocov_nonneg (fun S _ => hπ S) hP0 hrow hrev hlazy Gc
  have hE := taE_le X (refPk I ε δ j w) Gc hrow hrev hc0 _ hA (N - 1)
  -- the stationary second moment from each starting state
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set F : Finset ℕ → ℝ := fun S =>
    rpexp (refTraj I ε δ j w G N S) (fun x => (x.2 / N - m) ^ 2) with hF
  have hfin : ∀ S ∈ X, (refTraj I ε δ j w G N S).support.Finite := fun S hS =>
    (ta_loop_support I ε δ hp j w G (N - 1) (S, G S) hS).1
  have hF0 : ∀ S ∈ X, 0 ≤ F S := by
    intro S hS
    have := rpexp_mono _ (hfin S hS) (f := fun _ => (0 : ℝ))
      (g := fun x => (x.2 / N - m) ^ 2) (fun x _ => sq_nonneg _)
    rwa [rpexp_const _ (hfin S hS)] at this
  have hFW : ∀ S ∈ X, F S = taW X (refPk I ε δ j w) Gc (N - 1) S (Gc S) / (N : ℝ) ^ 2 := by
    intro S hS
    have hpt : ∀ x : Finset ℕ × ℝ, (x.2 / N - m) ^ 2 = 1 / (N : ℝ) ^ 2 * (x.2 - N * m) ^ 2 := by
      intro x; field_simp
    simp only [hF, hpt]
    rw [rpexp_const_mul _ (hfin S hS), refTraj, ta_traj_link I ε δ hp j w G m (N - 1) S hS]
    have : G S - N * m + ((N - 1 : ℕ) : ℝ) * m = Gc S := by
      rw [Nat.cast_sub hN]; simp [hGc]; ring
    rw [this]; ring
  -- domination of the initial law
  rw [pexp_bind]
  have hpt : ∀ S ∈ X, pexp (refTraj I ε δ j w G N S)
      (fun x => ENNReal.ofReal ((x.2 / N - m) ^ 2)) = ENNReal.ofReal (F S) := fun S hS =>
    pexp_ofReal_eq _ (hfin S hS) _ fun _ => sq_nonneg _
  unfold pexp
  rw [tsum_eq_sum (s := X) fun S hS => by rw [hνX S hS, zero_mul]]
  calc ∑ S ∈ X, ν S * ∑' x, (refTraj I ε δ j w G N S) x * ENNReal.ofReal ((x.2 / N - m) ^ 2)
      ≤ ∑ S ∈ X, ENNReal.ofReal (U * π S * F S) := by
        refine Finset.sum_le_sum fun S hS => ?_
        have := hpt S hS
        unfold pexp at this
        rw [this, ENNReal.ofReal_mul (mul_nonneg hU.le (hπ S))]
        gcongr
        exact hν S
    _ = ENNReal.ofReal (∑ S ∈ X, U * π S * F S) :=
        (ENNReal.ofReal_sum_of_nonneg fun S hS =>
          mul_nonneg (mul_nonneg hU.le (hπ S)) (hF0 S hS)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Finset.sum_congr rfl fun S hS => by rw [hFW S hS]]
        have : ∑ S ∈ X, U * π S * (taW X (refPk I ε δ j w) Gc (N - 1) S (Gc S) / (N : ℝ) ^ 2) =
            U / (N : ℝ) ^ 2 * ∑ S ∈ X, π S * taW X (refPk I ε δ j w) Gc (N - 1) S (Gc S) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun S _ => by ring
        rw [this]
        have hN1 : ((N - 1 : ℕ) : ℝ) + 1 = N := by rw [Nat.cast_sub hN]; simp
        rw [hN1] at hE
        calc U / (N : ℝ) ^ 2 * ∑ S ∈ X, π S * taW X (refPk I ε δ j w) Gc (N - 1) S (Gc S)
            ≤ U / (N : ℝ) ^ 2 * (2 * N * ((KobsParam I ε δ : ℝ) * v)) :=
              mul_le_mul_of_nonneg_left hE (by positivity)
          _ = _ := by field_simp

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · proved · `time_average` via `ta_inner_sq_le` + `lra_autocov_sum_le` + `taE_le` + `ta_traj_link`
-/
