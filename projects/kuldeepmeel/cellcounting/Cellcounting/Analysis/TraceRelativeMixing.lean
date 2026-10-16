import Cellcounting.Analysis.StageStep
import Cellcounting.Analysis.TraceDomination
import Cellcounting.Analysis.LazyMixing
import Cellcounting.Analysis.TransversalVariance
import Cellcounting.Analysis.RefEnergyDirichlet
import Cellcounting.Analysis.RefStepReversible
import Cellcounting.Analysis.RealPexp
import Cellcounting.Model.Prior

/-!
# Relative mixing of the transversal trace (`lem:trace`, `eq:trace-relative-mixing`)

`transport.tex:647-760`.  For good multipliers the trace `P_tr` of `P_{a, w}` on the
transversals `A` (one trace step per strictly positive return to `A`) is stochastic,
reversible with stationary law `μ_a`, lazy, and satisfies the Poincaré inequality
`Var_μ ≤ K_obs 𝓔_tr` (from `prop:transversal-variance` through the harmonic-extension
identity `eq:trace-bilinear-identity` and `eq:energy`, using `2 p² C_p ≤ K_obs`).
`LazyRev.pow_le` (`LazyMixing.lean`) then gives, for even `s`,
`P_tr^s(x, y) ≤ μ(y) (1 + (1 - 1/K_obs)^s / m) ≤ μ(y) (1 + exp(-s/K_obs) / m)`.

Stated here at `s = τ` (which is even) on the stage process `stageStep`: completing the
`τ` trace steps from a transversal `x` at `y` within `N` underlying transitions is at most
`P_tr^τ(x, y)` (`trStage_loop_le`: truncation only removes mass), so for any lower bound
`m` on the transversal masses of `μ_a` it is at most `μ_a(y) (1 + exp(-τ/K_obs)/m)`.

Departures from the paper's proof: return to `A` from a transversal is derived from the
escape probability being harmonic with vanishing Dirichlet form (instead of a qualitative
irreducibility/geometric-tail argument), and the spectral decomposition is replaced by
the elementary `L²(μ)` contraction of `LazyMixing.lean`, which yields the one-sided bound
the dependents use.
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal

section Generic

variable {α : Type} [DecidableEq α] (P : α → PMF α) (A : α → Prop) [DecidablePred A]

/-- INTERNAL: the first `N` terms of the hitting law have total mass at most one.
TEXLINE: sections/transport.tex:665-674 -/
theorem trm_hit_partial_le (N : ℕ) :
    ∀ u, ∑ n ∈ Finset.range N, ∑' z, trHitN P A n u z ≤ 1 := by
  induction N with
  | zero => intro u; simp
  | succ N ih =>
    intro u
    rw [Finset.sum_range_succ']
    by_cases hu : A u
    · simp [trHitN, hu]
    · simp only [trHitN, hu, ite_false, tsum_zero, add_zero]
      calc ∑ n ∈ Finset.range N, ∑' z, ∑' v, P u v * trHitN P A n v z
          = ∑' v, P u v * ∑ n ∈ Finset.range N, ∑' z, trHitN P A n v z := by
            have e1 : ∀ n, ∑' z, ∑' v, P u v * trHitN P A n v z =
                ∑' v, P u v * ∑' z, trHitN P A n v z := fun n => by
              rw [ENNReal.tsum_comm]; exact tsum_congr fun v => ENNReal.tsum_mul_left
            simp_rw [e1, Finset.mul_sum]
            exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm
        _ ≤ ∑' v, P u v * 1 := ENNReal.tsum_le_tsum fun v => by gcongr; exact ih v
        _ = 1 := by simp

/-- INTERNAL: the hitting law of `A` is a sub-probability.
TEXLINE: sections/transport.tex:665-674 -/
theorem trm_hit_tsum_le (u : α) : ∑' z, trHit P A u z ≤ 1 := by
  unfold trHit
  rw [ENNReal.tsum_comm]
  exact ENNReal.tsum_le_of_sum_range_le fun N => trm_hit_partial_le P A N u

/-- INTERNAL: hitting probabilities are at most one. -/
theorem trm_hit_le (u z : α) : trHit P A u z ≤ 1 :=
  (ENNReal.le_tsum z).trans (trm_hit_tsum_le P A u)

/-- INTERNAL: trace-kernel entries are at most one. -/
theorem trm_ret_le (x z : α) : trRet P A x z ≤ 1 := by
  unfold trRet
  calc ∑' v, P x v * trHit P A v z ≤ ∑' v, P x v * 1 :=
        ENNReal.tsum_le_tsum fun v => by gcongr; exact trm_hit_le P A v z
    _ = 1 := by simp

end Generic

section Trace

variable (I : Instance) (ε δ : ℚ) (a : ℕ) (w : ℕ → ℕ → ℚ)

/-- INTERNAL: the transversal predicate `A` used by the trace kernel. -/
def trmA : Finset ℕ → Prop := fun S => kind I ε δ S = .transversal

/-- INTERNAL: classical decidability of the trace predicate. -/
noncomputable instance trmA_dec : DecidablePred (trmA I ε δ) := Classical.decPred _

/-- INTERNAL: `stageStep` is the trace stage `trStage` of `P_{a, w}` on the transversals.
TEXLINE: sections/algorithm.tex:214-225 -/
theorem trm_stageStep_eq :
    stageStep I ε δ a w = trStage (refStep I ε δ a w) (trmA I ε δ) (τParam I ε δ) := by
  funext q
  unfold stageStep trStage
  split_ifs with h
  · rfl
  · congr 1; funext S'
    cases hk : kind I ε δ S' <;> simp [trmA, hk]

/-- INTERNAL: `nthWith` lands in `{0, …, 2p-1}` (local copy of `nthWith_lt`, whose module
imports this one). -/
theorem trm_nthWith_lt (hp : pSmall I ε δ ≠ 0) (S : Finset ℕ) (v : Bool)
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
/-- INTERNAL: one exact transition from a state of `X` stays in `X` (local copy of
`ta_refStep_support`).
TEXLINE: sections/transport.tex:60-69 -/
theorem trm_refStep_support (hp : pSmall I ε δ ≠ 0) (S : Finset ℕ) (hS : S ∈ chainStates I ε δ)
    (S' : Finset ℕ) (h : S' ∈ (refStep I ε δ a w S).support) : S' ∈ chainStates I ε δ := by
  have hT : ∀ u1 u2, insert (nthWith I ε δ S false u2) (S.erase (nthWith I ε δ S true u1)) ∈
      refStates I ε δ := by
    intro u1 u2
    unfold refStates
    rw [Finset.mem_powerset]
    refine Finset.insert_subset (Finset.mem_range.2 (trm_nthWith_lt I ε δ hp _ _ _)) ?_
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

/-- INTERNAL: `P(S, S') = 0` for `S ∈ X`, `S' ∉ X`. -/
theorem trm_refStep_zero (hp : pSmall I ε δ ≠ 0) (S : Finset ℕ) (hS : S ∈ chainStates I ε δ)
    (S' : Finset ℕ) (h : S' ∉ chainStates I ε δ) : refStep I ε δ a w S S' = 0 := by
  by_contra h'
  exact h (trm_refStep_support I ε δ a w hp S hS S' ((PMF.mem_support_iff _ _).2 h'))

open Classical in
/-- INTERNAL: transversals lie in `X` and satisfy the trace predicate. -/
theorem trm_trans_sub {S : Finset ℕ} (hS : S ∈ transStates I ε δ) :
    S ∈ chainStates I ε δ ∧ trmA I ε δ S := by
  unfold transStates at hS
  rw [Finset.mem_filter] at hS
  refine ⟨Finset.mem_filter.2 ⟨hS.1, ?_⟩, hS.2⟩
  rw [hS.2]; simp

open Classical in
/-- INTERNAL: a state of `X` satisfying the trace predicate is a transversal. -/
theorem trm_mem_trans {S : Finset ℕ} (hS : S ∈ chainStates I ε δ) (hA : trmA I ε δ S) :
    S ∈ transStates I ε δ :=
  Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hS).1, hA⟩

/-- INTERNAL: from `X`, the chain can only first hit `A` at a transversal. -/
theorem trm_hitN_mem (hp : pSmall I ε δ ≠ 0) (n : ℕ) : ∀ u ∈ chainStates I ε δ, ∀ z,
    trHitN (refStep I ε δ a w) (trmA I ε δ) n u z ≠ 0 → z ∈ transStates I ε δ := by
  induction n with
  | zero =>
    intro u hu z h
    simp only [trHitN] at h
    split_ifs at h with h1 h2
    · subst h2; exact trm_mem_trans I ε δ hu h1
    · exact absurd rfl h
    · exact absurd rfl h
  | succ n ih =>
    intro u hu z h
    simp only [trHitN] at h
    split_ifs at h with h1
    · exact absurd rfl h
    · obtain ⟨v, hv⟩ : ∃ v, refStep I ε δ a w u v * trHitN (refStep I ε δ a w) (trmA I ε δ) n v z ≠ 0 := by
        by_contra hc; push Not at hc; exact h (ENNReal.tsum_eq_zero.2 hc)
      rw [mul_ne_zero_iff] at hv
      exact ih v (trm_refStep_support I ε δ a w hp u hu v ((PMF.mem_support_iff _ _).2 hv.1)) z hv.2

/-- INTERNAL: from `X`, the hitting law is carried by the transversals. -/
theorem trm_hit_mem (hp : pSmall I ε δ ≠ 0) (u : Finset ℕ) (hu : u ∈ chainStates I ε δ) (z : Finset ℕ)
    (h : trHit (refStep I ε δ a w) (trmA I ε δ) u z ≠ 0) : z ∈ transStates I ε δ := by
  obtain ⟨n, hn⟩ : ∃ n, trHitN (refStep I ε δ a w) (trmA I ε δ) n u z ≠ 0 := by
    by_contra hc; push Not at hc; exact h (ENNReal.tsum_eq_zero.2 hc)
  exact trm_hitN_mem I ε δ a w hp n u hu z hn

/-- INTERNAL: from `X`, the trace kernel is carried by the transversals. -/
theorem trm_ret_mem (hp : pSmall I ε δ ≠ 0) (x : Finset ℕ) (hx : x ∈ chainStates I ε δ) (z : Finset ℕ)
    (h : trRet (refStep I ε δ a w) (trmA I ε δ) x z ≠ 0) : z ∈ transStates I ε δ := by
  obtain ⟨v, hv⟩ : ∃ v, refStep I ε δ a w x v * trHit (refStep I ε δ a w) (trmA I ε δ) v z ≠ 0 := by
    by_contra hc; push Not at hc; exact h (ENNReal.tsum_eq_zero.2 hc)
  rw [mul_ne_zero_iff] at hv
  exact trm_hit_mem I ε δ a w hp v (trm_refStep_support I ε δ a w hp x hx v
    ((PMF.mem_support_iff _ _).2 hv.1)) z hv.2

/-- INTERNAL: the hitting law `P_u(S_{T_A} = z)` as a real number. -/
noncomputable def trmH (u z : Finset ℕ) : ℝ :=
  (trHit (refStep I ε δ a w) (trmA I ε δ) u z).toReal

/-- INTERNAL: the trace kernel `P_tr(x, z)` as a real number. -/
noncomputable def trmR (x z : Finset ℕ) : ℝ :=
  (trRet (refStep I ε δ a w) (trmA I ε δ) x z).toReal

/-- INTERNAL: the escape probability `1 - P_u(T_A < ∞)`. -/
noncomputable def trmE (u : Finset ℕ) : ℝ := 1 - ∑ z ∈ transStates I ε δ, trmH I ε δ a w u z

/-- INTERNAL: a one-step average from `S ∈ X` as a finite real sum over `X`. -/
theorem trm_tsum_toReal (hp : pSmall I ε δ ≠ 0) (x : Finset ℕ) (hx : x ∈ chainStates I ε δ)
    (F : Finset ℕ → ℝ≥0∞) (hF : ∀ v, F v ≠ ⊤) :
    (∑' v, refStep I ε δ a w x v * F v).toReal =
      ∑ v ∈ chainStates I ε δ, refPk I ε δ a w x v * (F v).toReal := by
  rw [tsum_eq_sum (s := chainStates I ε δ)
    (fun v hv => by rw [trm_refStep_zero I ε δ a w hp x hx v hv, zero_mul])]
  rw [ENNReal.toReal_sum (fun v _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (hF v))]
  exact Finset.sum_congr rfl fun v _ => by rw [ENNReal.toReal_mul]; rfl

/-- INTERNAL: hitting probabilities are finite. -/
theorem trm_hit_ne_top (u z : Finset ℕ) : trHit (refStep I ε δ a w) (trmA I ε δ) u z ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (trm_hit_le _ _ u z)

/-- INTERNAL: trace-kernel entries are finite. -/
theorem trm_ret_ne_top (x z : Finset ℕ) : trRet (refStep I ε δ a w) (trmA I ε δ) x z ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (trm_ret_le _ _ x z)

/-- INTERNAL: the hitting law is the identity on `A`.
TEXLINE: sections/transport.tex:686-692 -/
theorem trm_H_of_mem {u : Finset ℕ} (hu : trmA I ε δ u) (z : Finset ℕ) :
    trmH I ε δ a w u z = if u = z then 1 else 0 := by
  unfold trmH; rw [trHit_of_mem _ _ hu]; split_ifs <;> simp

/-- INTERNAL: the hitting law is `P`-harmonic off `A` (real form).
TEXLINE: sections/transport.tex:686-692 -/
theorem trm_H_of_not_mem (hp : pSmall I ε δ ≠ 0) {u : Finset ℕ} (huX : u ∈ chainStates I ε δ)
    (hu : ¬ trmA I ε δ u) (z : Finset ℕ) :
    trmH I ε δ a w u z = ∑ v ∈ chainStates I ε δ, refPk I ε δ a w u v * trmH I ε δ a w v z := by
  unfold trmH; rw [trHit_of_not_mem _ _ hu]
  exact trm_tsum_toReal I ε δ a w hp u huX _ fun v => trm_hit_ne_top I ε δ a w v z

/-- INTERNAL: `P_tr(x, z) = Σ_v P(x, v) P_v(S_{T_A} = z)` (real form).
TEXLINE: sections/transport.tex:640-646 -/
theorem trm_R_eq (hp : pSmall I ε δ ≠ 0) {x : Finset ℕ} (hx : x ∈ chainStates I ε δ)
    (z : Finset ℕ) :
    trmR I ε δ a w x z = ∑ v ∈ chainStates I ε δ, refPk I ε δ a w x v * trmH I ε δ a w v z := by
  unfold trmR trRet
  exact trm_tsum_toReal I ε δ a w hp x hx _ fun v => trm_hit_ne_top I ε δ a w v z

/-- INTERNAL: the rows of `P_{a, w}` on `X` sum to one. -/
theorem trm_row (hp : pSmall I ε δ ≠ 0) (S : Finset ℕ) (hS : S ∈ chainStates I ε δ) :
    ∑ S' ∈ chainStates I ε δ, refPk I ε δ a w S S' = 1 :=
  sum_toReal_eq_one (refStep I ε δ a w S) (chainStates I ε δ)
    (trm_refStep_support I ε δ a w hp S hS)

/-- INTERNAL: the escape probability vanishes on transversals. -/
theorem trm_E_of_trans {u : Finset ℕ} (hu : u ∈ transStates I ε δ) : trmE I ε δ a w u = 0 := by
  unfold trmE
  rw [Finset.sum_congr rfl fun z _ => trm_H_of_mem I ε δ a w (trm_trans_sub I ε δ hu).2 z,
    Finset.sum_ite_eq]
  simp [hu]

/-- INTERNAL: the escape probability is `P`-harmonic off `A`. -/
theorem trm_E_harm (hp : pSmall I ε δ ≠ 0) {u : Finset ℕ} (huX : u ∈ chainStates I ε δ)
    (hu : ¬ trmA I ε δ u) :
    trmE I ε δ a w u = ∑ v ∈ chainStates I ε δ, refPk I ε δ a w u v * trmE I ε δ a w v := by
  unfold trmE
  rw [Finset.sum_congr rfl fun z _ => trm_H_of_not_mem I ε δ a w hp huX hu z, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, mul_sub, mul_one, Finset.sum_sub_distrib, trm_row I ε δ a w hp u huX]

/-- INTERNAL: the Dirichlet form of a reversible stochastic real kernel on a finite set. -/
theorem trm_dirichlet {β : Type*} (X : Finset β) (π : β → ℝ) (P : β → β → ℝ)
    (hrev : ∀ u ∈ X, ∀ v ∈ X, π u * P u v = π v * P v u)
    (hrow : ∀ u ∈ X, ∑ v ∈ X, P u v = 1) (g : β → ℝ) :
    ∑ u ∈ X, π u * g u * (g u - ∑ v ∈ X, P u v * g v) =
      (∑ u ∈ X, ∑ v ∈ X, π u * P u v * (g u - g v) ^ 2) / 2 := by
  have A1 : ∑ u ∈ X, ∑ v ∈ X, π u * P u v * g u ^ 2 = ∑ u ∈ X, π u * g u ^ 2 := by
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [show π u * g u ^ 2 = π u * g u ^ 2 * ∑ v ∈ X, P u v by rw [hrow u hu, mul_one],
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have A2 : ∑ u ∈ X, ∑ v ∈ X, π u * P u v * g v ^ 2 = ∑ u ∈ X, π u * g u ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [show π v * g v ^ 2 = π v * g v ^ 2 * ∑ u ∈ X, P v u by rw [hrow v hv, mul_one],
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [hrev u hu v hv]; ring
  have hexp : ∑ u ∈ X, ∑ v ∈ X, π u * P u v * (g u - g v) ^ 2 =
      ∑ u ∈ X, ∑ v ∈ X, π u * P u v * g u ^ 2 - 2 * ∑ u ∈ X, ∑ v ∈ X, π u * g u * (P u v * g v) +
        ∑ u ∈ X, ∑ v ∈ X, π u * P u v * g v ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [hexp, A1, A2]
  have : ∑ u ∈ X, π u * g u * (g u - ∑ v ∈ X, P u v * g v) =
      ∑ u ∈ X, π u * g u ^ 2 - ∑ u ∈ X, ∑ v ∈ X, π u * g u * (P u v * g v) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => by rw [← Finset.mul_sum]; ring
  rw [this]; ring

/-- INTERNAL: `Λ > 0` for good multipliers. -/
theorem trm_refLamTot_pos (hgood : goodMult I ε δ a w) : 0 < refLamTot I ε δ a w :=
  lt_of_lt_of_le (td_Cpart_pos I ε δ a) (td_Cpart_le_refLamTot I ε δ a w hgood)

/-- INTERNAL: `π = f_a / Λ` on transversals. -/
theorem trm_refPi_trans {x : Finset ℕ} (hx : x ∈ transStates I ε δ) :
    refPi I ε δ a w x = fWeight I ε δ a x / refLamTot I ε δ a w := by
  have h := trm_trans_sub I ε δ hx
  unfold refPi
  rw [if_pos h.1, td_refLam_eq]
  have hk : kind I ε δ x = .transversal := h.2
  rw [hk]

/-- INTERNAL: `π > 0` on transversals. -/
theorem trm_refPi_pos (hgood : goodMult I ε δ a w) {x : Finset ℕ}
    (hx : x ∈ transStates I ε δ) : 0 < refPi I ε δ a w x := by
  rw [trm_refPi_trans I ε δ a w hx]
  exact div_pos (td_fWeight_pos I ε δ a x) (trm_refLamTot_pos I ε δ a w hgood)

/-- INTERNAL: one step from a transversal never reaches a state that escapes `A`: the
escape probability is harmonic, zero on `A`, hence constant along positive transitions
(its Dirichlet form vanishes).  This replaces the paper's "finite irreducibility"
remark for the return to `A`.
TEXLINE: sections/transport.tex:665-674 -/
theorem trm_E_zero (hp : pSmall I ε δ ≠ 0) (hgood : goodMult I ε δ a w) {x : Finset ℕ}
    (hx : x ∈ transStates I ε δ) (v : Finset ℕ) (hv : v ∈ chainStates I ε δ)
    (hxv : refPk I ε δ a w x v ≠ 0) : trmE I ε δ a w v = 0 := by
  set X := chainStates I ε δ
  have hrev : ∀ u ∈ X, ∀ v ∈ X, refPi I ε δ a w u * refPk I ε δ a w u v =
      refPi I ε δ a w v * refPk I ε δ a w v u :=
    fun u hu v hv => refStep_reversible I ε δ hp a w hgood u v hu hv
  have hD := trm_dirichlet X (refPi I ε δ a w) (refPk I ε δ a w) hrev
    (fun u hu => trm_row I ε δ a w hp u hu) (trmE I ε δ a w)
  have hL : ∑ u ∈ X, refPi I ε δ a w u * trmE I ε δ a w u *
      (trmE I ε δ a w u - ∑ v ∈ X, refPk I ε δ a w u v * trmE I ε δ a w v) = 0 := by
    refine Finset.sum_eq_zero fun u hu => ?_
    by_cases hA : trmA I ε δ u
    · rw [trm_E_of_trans I ε δ a w (trm_mem_trans I ε δ hu hA)]; ring
    · rw [← trm_E_harm I ε δ a w hp hu hA]; ring
  rw [hL] at hD
  have hnn : ∀ u ∈ X, ∀ v ∈ X, 0 ≤ refPi I ε δ a w u * refPk I ε δ a w u v *
      (trmE I ε δ a w u - trmE I ε δ a w v) ^ 2 := fun u _ v _ =>
    mul_nonneg (mul_nonneg (td_refPi_nonneg I ε δ a w hgood u) ENNReal.toReal_nonneg)
      (sq_nonneg _)
  have hsum : ∑ u ∈ X, ∑ v ∈ X, refPi I ε δ a w u * refPk I ε δ a w u v *
      (trmE I ε δ a w u - trmE I ε δ a w v) ^ 2 = 0 := by linarith
  have hxX := (trm_trans_sub I ε δ hx).1
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun u hu =>
    Finset.sum_nonneg (hnn u hu)).1 hsum x hxX
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (hnn x hxX)).1 h1 v hv
  have hπ := trm_refPi_pos I ε δ a w hgood hx
  have hP : 0 < refPk I ε δ a w x v := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hxv)
  rw [trm_E_of_trans I ε δ a w hx] at h2
  have : (0 - trmE I ε δ a w v) ^ 2 = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h (mul_pos hπ hP).ne'
    · exact h
  nlinarith [sq_nonneg (trmE I ε δ a w v)]

/-- INTERNAL: the trace kernel is stochastic on the transversals (return is certain).
TEXLINE: sections/transport.tex:665-674 -/
theorem trm_R_stoch (hp : pSmall I ε δ ≠ 0) (hgood : goodMult I ε δ a w) {x : Finset ℕ}
    (hx : x ∈ transStates I ε δ) : ∑ z ∈ transStates I ε δ, trmR I ε δ a w x z = 1 := by
  have hxX := (trm_trans_sub I ε δ hx).1
  rw [Finset.sum_congr rfl fun z _ => trm_R_eq I ε δ a w hp hxX z, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hE : ∀ v ∈ chainStates I ε δ, refPk I ε δ a w x v *
      ∑ z ∈ transStates I ε δ, trmH I ε δ a w v z = refPk I ε δ a w x v := by
    intro v hv
    by_cases h : refPk I ε δ a w x v = 0
    · rw [h, zero_mul]
    · have := trm_E_zero I ε δ a w hp hgood hx v hv h
      unfold trmE at this
      rw [show ∑ z ∈ transStates I ε δ, trmH I ε δ a w v z = 1 by linarith, mul_one]
  rw [Finset.sum_congr rfl hE, trm_row I ε δ a w hp x hxX]

/-- INTERNAL: `P_tr(x, x) ≥ P(x, x) ≥ 1/2`.
TEXLINE: sections/transport.tex:703 -/
theorem trm_R_lazy {x : Finset ℕ} (hx : x ∈ transStates I ε δ) :
    1 / 2 ≤ trmR I ε δ a w x x := by
  have hA := (trm_trans_sub I ε δ hx).2
  have hle : refStep I ε δ a w x x ≤ trRet (refStep I ε δ a w) (trmA I ε δ) x x := by
    unfold trRet
    refine le_trans ?_ (ENNReal.le_tsum x)
    rw [trHit_of_mem _ _ hA, if_pos rfl, mul_one]
  have h := ENNReal.toReal_mono (trm_ret_ne_top I ε δ a w x x) hle
  have hl : 1 / 2 ≤ (refStep I ε δ a w x x).toReal := by
    have hge : (1 / 2 : ℝ≥0∞) ≤ refStep I ε δ a w x x := by
      unfold refStep
      erw [PMF.bind_apply]
      refine le_trans ?_ (ENNReal.le_tsum true)
      simp [Arlib.Computation.ProbRAM.fair, PMF.bernoulli_apply]
      erw [PMF.pure_apply_self, mul_one]
    have := ENNReal.toReal_mono (PMF.apply_ne_top _ _) hge
    simpa using this
  unfold trmR; linarith

/-- INTERNAL: the form `⟨f, (I - P) g⟩_π` of a reversible real kernel is symmetric. -/
theorem trm_bilin_symm {β : Type*} (X : Finset β) (π : β → ℝ) (P : β → β → ℝ)
    (hrev : ∀ u ∈ X, ∀ v ∈ X, π u * P u v = π v * P v u) (f g : β → ℝ) :
    ∑ u ∈ X, π u * f u * (g u - ∑ v ∈ X, P u v * g v) =
      ∑ u ∈ X, π u * g u * (f u - ∑ v ∈ X, P u v * f v) := by
  have key : ∑ u ∈ X, π u * f u * ∑ v ∈ X, P u v * g v =
      ∑ u ∈ X, π u * g u * ∑ v ∈ X, P u v * f v := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun u hu => ?_
    have := hrev u hu v hv
    linear_combination (f u * g v) * this
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [key]
  congr 1
  exact Finset.sum_congr rfl fun u _ => by ring

/-- INTERNAL: `⟨ĥ_x, (I - P) ĥ_z⟩_π = π(x) (1_{x = z} - P_tr(x, z))` for the harmonic
extensions of point masses (`eq:trace-bilinear-identity`).
TEXLINE: sections/transport.tex:693-702 -/
theorem trm_bilin_H (hp : pSmall I ε δ ≠ 0) {x : Finset ℕ} (hx : x ∈ transStates I ε δ)
    (z : Finset ℕ) :
    ∑ u ∈ chainStates I ε δ, refPi I ε δ a w u * trmH I ε δ a w u x *
      (trmH I ε δ a w u z - ∑ v ∈ chainStates I ε δ, refPk I ε δ a w u v * trmH I ε δ a w v z) =
    refPi I ε δ a w x * ((if x = z then 1 else 0) - trmR I ε δ a w x z) := by
  have hxX := (trm_trans_sub I ε δ hx).1
  have hterm : ∀ u ∈ chainStates I ε δ, refPi I ε δ a w u * trmH I ε δ a w u x *
      (trmH I ε δ a w u z - ∑ v ∈ chainStates I ε δ, refPk I ε δ a w u v * trmH I ε δ a w v z) =
      if u = x then refPi I ε δ a w x * ((if x = z then 1 else 0) - trmR I ε δ a w x z)
      else 0 := by
    intro u hu
    by_cases hA : trmA I ε δ u
    · rw [← trm_R_eq I ε δ a w hp hu, trm_H_of_mem I ε δ a w hA, trm_H_of_mem I ε δ a w hA]
      by_cases hux : u = x
      · subst hux; simp
      · simp [hux]
    · rw [← trm_H_of_not_mem I ε δ a w hp hu hA, sub_self, mul_zero]
      have : u ≠ x := fun h => hA (h ▸ (trm_trans_sub I ε δ hx).2)
      simp [this]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ _ _, if_pos hxX]

/-- INTERNAL: `μ_a = (Λ / C) π` on transversals. -/
theorem trm_refMu_trans (hgood : goodMult I ε δ a w) {x : Finset ℕ}
    (hx : x ∈ transStates I ε δ) :
    refMu I ε δ a x = refPi I ε δ a w x * (refLamTot I ε δ a w / transMass I ε δ a) := by
  rw [trm_refPi_trans I ε δ a w hx, refMu, if_pos hx]
  have hΛ := (trm_refLamTot_pos I ε δ a w hgood).ne'
  have hC : transMass I ε δ a ≠ 0 := by rw [transMass_eq_Cpart]; exact (td_Cpart_pos I ε δ a).ne'
  field_simp

/-- INTERNAL: the trace kernel is reversible with respect to `μ_a`.
TEXLINE: sections/transport.tex:700-702 -/
theorem trm_R_rev (hp : pSmall I ε δ ≠ 0) (hgood : goodMult I ε δ a w) {x z : Finset ℕ}
    (hx : x ∈ transStates I ε δ) (hz : z ∈ transStates I ε δ) :
    refMu I ε δ a x * trmR I ε δ a w x z = refMu I ε δ a z * trmR I ε δ a w z x := by
  have hs := trm_bilin_symm (chainStates I ε δ) (refPi I ε δ a w) (refPk I ε δ a w)
    (fun u hu v hv => refStep_reversible I ε δ hp a w hgood u v hu hv)
    (fun u => trmH I ε δ a w u x) (fun u => trmH I ε δ a w u z)
  rw [trm_bilin_H I ε δ a w hp hx z, trm_bilin_H I ε δ a w hp hz x] at hs
  rw [trm_refMu_trans I ε δ a w hgood hx, trm_refMu_trans I ε δ a w hgood hz]
  by_cases hxz : x = z
  · subst hxz; ring
  · rw [if_neg hxz, if_neg (Ne.symm hxz)] at hs
    linear_combination (-(refLamTot I ε δ a w / transMass I ε δ a)) * hs

/-- INTERNAL: the harmonic extension `ĥ(u) = E_u h(S_{T_A})` of a function on `A`. -/
noncomputable def trmHat (h : Finset ℕ → ℝ) (u : Finset ℕ) : ℝ :=
  ∑ z ∈ transStates I ε δ, trmH I ε δ a w u z * h z

/-- INTERNAL: the harmonic extension agrees with `h` on `A`. -/
theorem trm_hat_trans (h : Finset ℕ → ℝ) {u : Finset ℕ} (hu : u ∈ transStates I ε δ) :
    trmHat I ε δ a w h u = h u := by
  unfold trmHat
  rw [Finset.sum_congr rfl fun z _ => by rw [trm_H_of_mem I ε δ a w (trm_trans_sub I ε δ hu).2 z]]
  simp [hu]

/-- INTERNAL: one step of `P` applied to a harmonic extension. -/
theorem trm_P_hat (h : Finset ℕ → ℝ) (u : Finset ℕ) :
    ∑ v ∈ chainStates I ε δ, refPk I ε δ a w u v * trmHat I ε δ a w h v =
      ∑ z ∈ transStates I ε δ,
        (∑ v ∈ chainStates I ε δ, refPk I ε δ a w u v * trmH I ε δ a w v z) * h z := by
  unfold trmHat
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- INTERNAL: the harmonic extension is `P`-harmonic off `A`. -/
theorem trm_hat_harm (hp : pSmall I ε δ ≠ 0) (h : Finset ℕ → ℝ) {u : Finset ℕ}
    (huX : u ∈ chainStates I ε δ) (hu : ¬ trmA I ε δ u) :
    ∑ v ∈ chainStates I ε δ, refPk I ε δ a w u v * trmHat I ε δ a w h v =
      trmHat I ε δ a w h u := by
  rw [trm_P_hat]; unfold trmHat
  exact Finset.sum_congr rfl fun z _ => by rw [← trm_H_of_not_mem I ε δ a w hp huX hu z]

/-- INTERNAL: on `A`, `P ĥ = P_tr h`. -/
theorem trm_hat_trace (hp : pSmall I ε δ ≠ 0) (h : Finset ℕ → ℝ) {x : Finset ℕ}
    (hx : x ∈ chainStates I ε δ) :
    ∑ v ∈ chainStates I ε δ, refPk I ε δ a w x v * trmHat I ε δ a w h v =
      ∑ z ∈ transStates I ε δ, trmR I ε δ a w x z * h z := by
  rw [trm_P_hat]
  exact Finset.sum_congr rfl fun z _ => by rw [← trm_R_eq I ε δ a w hp hx z]

/-- INTERNAL: `𝓔(ĥ) = (C/Λ) 𝓔_tr(h)` (`eq:trace-bilinear-identity` at `k = h`).
TEXLINE: sections/transport.tex:693-713 -/
theorem trm_energy_hat (hp : pSmall I ε δ ≠ 0) (hgood : goodMult I ε δ a w)
    (h : Finset ℕ → ℝ) :
    refEnergy I ε δ a w (trmHat I ε δ a w h) =
      transMass I ε δ a / refLamTot I ε δ a w *
        ∑ x ∈ transStates I ε δ, refMu I ε δ a x * h x *
          (h x - ∑ z ∈ transStates I ε δ, trmR I ε δ a w x z * h z) := by
  unfold refEnergy
  have hsub : transStates I ε δ ⊆ chainStates I ε δ := fun x hx => (trm_trans_sub I ε δ hx).1
  rw [← Finset.sum_subset hsub, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun x hx => ?_
    have hxX := hsub hx
    rw [trm_hat_trace I ε δ a w hp h hxX, trm_hat_trans I ε δ a w h hx,
      trm_refMu_trans I ε δ a w hgood hx]
    have hΛ := (trm_refLamTot_pos I ε δ a w hgood).ne'
    have hC : transMass I ε δ a ≠ 0 := by
      rw [transMass_eq_Cpart]; exact (td_Cpart_pos I ε δ a).ne'
    field_simp
  · intro u hu hnot
    have hA : ¬ trmA I ε δ u := fun hA => hnot (trm_mem_trans I ε δ hu hA)
    rw [trm_hat_harm I ε δ a w hp h hu hA, sub_self, mul_zero]

/-- INTERNAL: `2 p² C_p ≤ K_obs`.
TEXLINE: sections/transport.tex:720-722 -/
theorem trm_two_p_Cp_le (hp : pSmall I ε δ ≠ 0) :
    2 * pSmall I ε δ ^ 2 * CpParam I ε δ ≤ KobsParam I ε δ := by
  have h1 : 1 ≤ pSmall I ε δ := Nat.one_le_iff_ne_zero.2 hp
  have h2 : pSmall I ε δ ^ 2 ≤ pSmall I ε δ ^ 4 := Nat.pow_le_pow_right h1 (by norm_num)
  unfold KobsParam
  calc 2 * pSmall I ε δ ^ 2 * CpParam I ε δ ≤ 90 * pSmall I ε δ ^ 4 * CpParam I ε δ := by
        gcongr; omega
    _ ≤ _ := by nlinarith [Nat.zero_le (pSmall I ε δ ^ 4 * CdParam I ε δ)]

/-- INTERNAL: the arithmetic closing the trace Poincaré inequality. -/
theorem trm_alg (V E D C Λ p2 Cp K : ℝ) (hC : 0 < C) (hΛ : 0 < Λ) (hp2 : 0 < p2)
    (hed : C / Λ * E = D / (2 * p2 * Λ)) (htv : C * V ≤ Cp * D) (hD : 0 ≤ D)
    (hK : 2 * p2 * Cp ≤ K) : V ≤ K * E := by
  have hDE : D = 2 * p2 * C * E := by
    field_simp at hed; linarith
  have hE : 0 ≤ E := by
    rw [hDE] at hD
    by_contra hneg; push Not at hneg
    have : 2 * p2 * C * E < 0 := mul_neg_of_pos_of_neg (by positivity) hneg
    linarith
  rw [hDE] at htv
  have hV : V ≤ 2 * p2 * Cp * E := by
    have : C * V ≤ C * (2 * p2 * Cp * E) := by linarith
    exact le_of_mul_le_mul_left this hC
  exact hV.trans (mul_le_mul_of_nonneg_right hK hE)

/-- INTERNAL: the trace Poincaré inequality `Var_μ(h) ≤ K_obs 𝓔_tr(h)`, from
`prop:transversal-variance` through the harmonic extension and `eq:energy`.
TEXLINE: sections/transport.tex:708-722 -/
theorem trm_poincare (hprior : Prior) (hm : 0 < I.m) (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0)
    (ha : a < HParam I ε δ) (hgood : goodMult I ε δ a w) (h : Finset ℕ → ℝ) :
    ∑ x ∈ transStates I ε δ, refMu I ε δ a x *
        (h x - ∑ y ∈ transStates I ε δ, refMu I ε δ a y * h y) ^ 2 ≤
      (KobsParam I ε δ : ℝ) * ∑ x ∈ transStates I ε δ, refMu I ε δ a x * h x *
        (h x - ∑ y ∈ transStates I ε δ, trmR I ε δ a w x y * h y) := by
  have hvar : refMuVar I ε δ a (trmHat I ε δ a w h) = ∑ x ∈ transStates I ε δ, refMu I ε δ a x *
        (h x - ∑ y ∈ transStates I ε δ, refMu I ε δ a y * h y) ^ 2 := by
    unfold refMuVar refMuMean
    have hm' : ∑ S ∈ transStates I ε δ, refMu I ε δ a S * trmHat I ε δ a w h S =
        ∑ y ∈ transStates I ε δ, refMu I ε δ a y * h y :=
      Finset.sum_congr rfl fun y hy => by rw [trm_hat_trans I ε δ a w h hy]
    rw [hm']
    exact Finset.sum_congr rfl fun x hx => by rw [trm_hat_trans I ε δ a w h hx]
  have htv := transversal_variance hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp a ha w hgood
    (trmHat I ε δ a w h)
  have hed := refEnergy_eq_refDir I ε δ hp a w hgood (trmHat I ε δ a w h)
  rw [trm_energy_hat I ε δ a w hp hgood h] at hed
  rw [hvar, ← transMass_eq_Cpart] at htv
  have hC : 0 < transMass I ε δ a := by rw [transMass_eq_Cpart]; exact td_Cpart_pos I ε δ a
  have hp0 : (0 : ℝ) < (pSmall I ε δ : ℝ) ^ 2 := by
    have : (0 : ℝ) < pSmall I ε δ := by exact_mod_cast Nat.pos_of_ne_zero hp
    positivity
  have hK : (2 * (pSmall I ε δ : ℝ) ^ 2 * (CpParam I ε δ : ℝ)) ≤ (KobsParam I ε δ : ℝ) := by
    exact_mod_cast trm_two_p_Cp_le I ε δ hp
  exact trm_alg _ _ _ _ _ _ _ _ hC (trm_refLamTot_pos I ε δ a w hgood) hp0
    hed htv (td_refDir_nonneg I ε δ a w hgood _) hK

/-- INTERNAL: the trace kernel is a lazy reversible stochastic chain on `A` with law `μ_a`.
TEXLINE: sections/transport.tex:667-703 -/
theorem trm_lazyRev (hp : pSmall I ε δ ≠ 0) (hgood : goodMult I ε δ a w) :
    LazyRev (transStates I ε δ) (refMu I ε δ a) (trmR I ε δ a w) where
  μ_pos x hx := by
    rw [refMu, if_pos hx, transMass_eq_Cpart]
    exact div_pos (td_fWeight_pos I ε δ a x) (td_Cpart_pos I ε δ a)
  μ_sum := by
    have hC : transMass I ε δ a ≠ 0 := by
      rw [transMass_eq_Cpart]; exact (td_Cpart_pos I ε δ a).ne'
    rw [Finset.sum_congr rfl fun x hx => by rw [refMu, if_pos hx], ← Finset.sum_div]
    exact div_self hC
  r_nonneg _ _ _ _ := ENNReal.toReal_nonneg
  stoch x hx := trm_R_stoch I ε δ a w hp hgood hx
  rev x hx z hz := trm_R_rev I ε δ a w hp hgood hx hz
  lazy x hx := trm_R_lazy I ε δ a w hx

/-- INTERNAL: `P_tr^s(x, y)` is the `s`-th power of the real trace operator at `1_y`. -/
theorem trm_pow_eq (hp : pSmall I ε δ ≠ 0) (hgood : goodMult I ε δ a w) (y : Finset ℕ)
    (s : ℕ) : ∀ x ∈ transStates I ε δ,
    trRetPow (refStep I ε δ a w) (trmA I ε δ) s x y =
      ENNReal.ofReal ((kerOp (transStates I ε δ) (trmR I ε δ a w) ^ s)
        (fun z => if z = y then 1 else 0) x) := by
  have hC := trm_lazyRev I ε δ a w hp hgood
  induction s with
  | zero =>
    intro x _
    simp only [trRetPow, pow_zero, Module.End.one_apply]
    split_ifs <;> simp
  | succ s ih =>
    intro x hx
    have hxX := (trm_trans_sub I ε δ hx).1
    simp only [trRetPow]
    rw [tsum_eq_sum (s := transStates I ε δ) (fun z hz => by
      have : trRet (refStep I ε δ a w) (trmA I ε δ) x z = 0 := by
        by_contra h; exact hz (trm_ret_mem I ε δ a w hp x hxX z h)
      rw [this, zero_mul])]
    rw [kerOp_pow_succ, kerOp_apply, ENNReal.ofReal_sum_of_nonneg (fun z hz =>
      mul_nonneg (hC.r_nonneg x hx z hz) (hC.kerOp_pow_nonneg s _
        (fun u _ => by split_ifs <;> norm_num) z hz))]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [ih z hz, ENNReal.ofReal_mul (hC.r_nonneg x hx z hz), trmR,
      ENNReal.ofReal_toReal (trm_ret_ne_top I ε δ a w x z)]

/-- INTERNAL: powers of the trace operator vanish on targets outside `A`. -/
theorem trm_pow_out (y : Finset ℕ) (hy : y ∉ transStates I ε δ) (s : ℕ) :
    ∀ x ∈ transStates I ε δ, (kerOp (transStates I ε δ) (trmR I ε δ a w) ^ s)
      (fun z => if z = y then 1 else 0) x = 0 := by
  induction s with
  | zero =>
    intro x hx
    simp only [pow_zero, Module.End.one_apply]
    rw [if_neg (fun h : x = y => hy (h ▸ hx))]
  | succ s ih =>
    intro x hx
    rw [kerOp_pow_succ, kerOp_apply]
    exact Finset.sum_eq_zero fun z hz => by rw [ih z hz, mul_zero]

end Trace

/-- **Trace relative mixing** (`eq:trace-relative-mixing` of `lem:trace`, at `s = τ`, on the
`N`-transition truncation of the stage): from any transversal `x`, with `m ≤ μ_min`,
the stage completes its `τ` trace steps at `y` with probability at most
`μ_a(y) (1 + m⁻¹ exp(-τ/K_obs))`.
PAPER: sections/transport.tex:656-662 -/
theorem trace_relative_mixing (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (a : ℕ) (ha : a < HParam I ε δ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ a w) (m : ℝ) (hm0 : 0 < m)
    (hmin : ∀ z ∈ transStates I ε δ, m ≤ refMu I ε δ a z) (x : Finset ℕ)
    (hx : x ∈ transStates I ε δ) (N : ℕ) (y : Finset ℕ) :
    loop (fun _ => stageStep I ε δ a w) N (0, x) (τParam I ε δ, y) ≤
      ENNReal.ofReal (refMu I ε δ a y *
        (1 + Real.exp (-((τParam I ε δ : ℝ) / (KobsParam I ε δ : ℝ))) / m)) := by
  have hC := trm_lazyRev I ε δ a w hp hgood
  rw [trm_stageStep_eq]
  refine (trStage_loop_le _ _ (τParam I ε δ) (trm_trans_sub I ε δ hx).2 y N).trans ?_
  rw [trm_pow_eq I ε δ a w hp hgood y _ x hx]
  refine ENNReal.ofReal_le_ofReal ?_
  have hK1 : (1 : ℝ) ≤ KobsParam I ε δ := by
    have hp' : 0 < pSmall I ε δ := Nat.pos_of_ne_zero hp
    have : 0 < KobsParam I ε δ := by unfold KobsParam CdParam; positivity
    exact_mod_cast this
  by_cases hy : y ∈ transStates I ε δ
  · set K : ℝ := (KobsParam I ε δ : ℝ) with hKdef
    have hτ : τParam I ε δ =
        2 * (KobsParam I ε δ * (HParam I ε δ + pSmall I ε δ + KParam I ε δ + 5)) := by
      unfold τParam; ring
    have key := hC.pow_le K hK1 (trm_poincare I ε δ a w hprior hm hn hε hε1 hδ hδ1 hfeas hp ha
      hgood) m hm0 hmin
      (KobsParam I ε δ * (HParam I ε δ + pSmall I ε δ + KParam I ε δ + 5)) x y hx hy
    rw [← hτ] at key
    refine key.trans ?_
    have hμ : 0 ≤ refMu I ε δ a y := (hC.μ_pos y hy).le
    have h0 : 0 ≤ 1 - 1 / K := by
      rw [sub_nonneg, div_le_one (by linarith)]; exact hK1
    have hexp : (1 - 1 / K) ^ τParam I ε δ ≤ Real.exp (-((τParam I ε δ : ℝ) / K)) := by
      calc (1 - 1 / K) ^ τParam I ε δ ≤ (Real.exp (-(1 / K))) ^ τParam I ε δ :=
            pow_le_pow_left₀ h0 (Real.one_sub_le_exp_neg _) _
        _ = Real.exp (-((τParam I ε δ : ℝ) / K)) := by
            rw [← Real.exp_nat_mul]; ring_nf
    exact mul_le_mul_of_nonneg_left
      (add_le_add_right (div_le_div_of_nonneg_right hexp hm0.le) 1) hμ
  · rw [trm_pow_out I ε δ a w y hy _ x hx, refMu, if_neg hy, zero_mul]

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · trace kernel as `LazyRev` + Poincaré via harmonic extension, then `LazyRev.pow_le`
-/
