import Cellcounting.Analysis.PmfClose

/-!
# The trace kernel of a set, and the stage process it dominates

For a Markov kernel `P` on a type `α` and a set `A` (a decidable predicate), with the
conventions of `lem:trace` (`transport.tex:640-646`):

* `trHitN n u y` — the probability that the chain from `u` first lies in `A` at time `n`,
  and there at `y` (time `0` counts);
* `trHit u y = Σ_n trHitN n u y` — the hitting law of `A` from `u`, harmonic off `A`
  (`trHit_eq`);
* `trRet x y = Σ_v P(x, v) trHit(v, y)` — the trace kernel `P_tr`: the first strictly
  positive return to `A`, at `y`;
* `trRetPow s` — the `s`-fold power of `P_tr`.

Everything is in `ℝ≥0∞`, so no summability or a.s.-return assumption is needed here.

`trStage τ` runs the underlying chain counting completed trace steps (one per transition
landing in `A`, holding steps included) and freezes after `τ` of them.  From `x ∈ A`, the
probability that `N` transitions complete the `τ` trace steps at `y` is at most
`P_tr^τ(x, y)` (`trStage_loop_le`): truncation only removes mass.  The proof is a
superharmonic potential (`trStageV`), on which one step of `trStage` acts exactly.
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal

section TraceDomination

variable {α : Type} [DecidableEq α] (P : α → PMF α) (A : α → Prop) [DecidablePred A]

/-- INTERNAL: the probability of first lying in `A` at time `n`, at `y`.
TEXLINE: sections/transport.tex:640-646 -/
noncomputable def trHitN : ℕ → α → α → ℝ≥0∞
  | 0, u, y => if A u then (if u = y then 1 else 0) else 0
  | n + 1, u, y => if A u then 0 else ∑' v, P u v * trHitN n v y

/-- INTERNAL: the hitting law of `A` from `u` (the law of `S_{T_A}`, `T_A ≥ 0`).
TEXLINE: sections/transport.tex:686-692 -/
noncomputable def trHit (u y : α) : ℝ≥0∞ := ∑' n, trHitN P A n u y

/-- INTERNAL: the trace kernel `P_tr(x, y)`: the first strictly positive return to `A`
is at `y`.
TEXLINE: sections/transport.tex:640-646 -/
noncomputable def trRet (x y : α) : ℝ≥0∞ := ∑' v, P x v * trHit P A v y

/-- INTERNAL: the `s`-th power of the trace kernel.
TEXLINE: sections/transport.tex:656-662 -/
noncomputable def trRetPow : ℕ → α → α → ℝ≥0∞
  | 0, x, y => if x = y then 1 else 0
  | s + 1, x, y => ∑' z, trRet P A x z * trRetPow s z y

/-- INTERNAL: one underlying transition of a trace stage: count the transitions landing
in `A`, freeze after `τ` of them.
TEXLINE: sections/algorithm.tex:214-225 -/
noncomputable def trStage (τ : ℕ) (q : ℕ × α) : PMF (ℕ × α) :=
  if τ ≤ q.1 then PMF.pure q else
    (P q.2).map fun v => if A v then (q.1 + 1, v) else (q.1, v)

/-- INTERNAL: the hitting law is the identity on `A` and harmonic off `A`.
TEXLINE: sections/transport.tex:686-692 -/
theorem trHit_eq (u y : α) :
    trHit P A u y = if A u then (if u = y then 1 else 0) else ∑' v, P u v * trHit P A v y := by
  unfold trHit
  rw [tsum_eq_zero_add' ENNReal.summable]
  by_cases hu : A u
  · simp [trHitN, hu]
  · simp only [trHitN, hu, if_false, zero_add]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun v => ENNReal.tsum_mul_left

theorem trHit_of_mem {u : α} (hu : A u) (y : α) :
    trHit P A u y = if u = y then 1 else 0 := by
  rw [trHit_eq, if_pos hu]

theorem trHit_of_not_mem {u : α} (hu : ¬ A u) (y : α) :
    trHit P A u y = ∑' v, P u v * trHit P A v y := by
  rw [trHit_eq, if_neg hu]

/-- INTERNAL: `Σ_z trHit(u, z) F(z)` is `F(u)` on `A`. -/
theorem tsum_trHit_of_mem {u : α} (hu : A u) (F : α → ℝ≥0∞) :
    ∑' z, trHit P A u z * F z = F u := by
  simp_rw [trHit_of_mem P A hu]
  rw [tsum_eq_single u (fun z hz => by simp [Ne.symm hz])]
  simp

/-- INTERNAL: `Σ_z trHit(u, z) F(z)` is harmonic off `A`. -/
theorem tsum_trHit_of_not_mem {u : α} (hu : ¬ A u) (F : α → ℝ≥0∞) :
    ∑' z, trHit P A u z * F z = ∑' v, P u v * ∑' z, trHit P A v z * F z := by
  simp_rw [trHit_of_not_mem P A hu, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun v => ?_
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun z => by ring

/-- INTERNAL: one more trace step, written through the first underlying transition. -/
theorem trRetPow_succ_eq (s : ℕ) (x y : α) :
    trRetPow P A (s + 1) x y = ∑' v, P x v * ∑' z, trHit P A v z * trRetPow P A s z y := by
  simp only [trRetPow, trRet, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun v => ?_
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun z => by ring

/-- INTERNAL: `∑' q, (p.map g) q * F q = ∑' a, p a * F (g a)`. -/
theorem tsum_map_mul {β γ : Type} (p : PMF β) (g : β → γ) (F : γ → ℝ≥0∞) :
    ∑' q, (p.map g) q * F q = ∑' a, p a * F (g a) := by
  classical
  simp_rw [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single (g a) (fun q hq => by simp [hq])]
  simp

/-- INTERNAL: the potential of the stage process: from count `c < τ` at `u`, the trace
power still to run (through the hitting law when `u ∉ A`); after the stage, the indicator
of the target.
TEXLINE: sections/transport.tex:656-662 -/
noncomputable def trStageV (τ : ℕ) (y : α) (q : ℕ × α) : ℝ≥0∞ :=
  if q.1 < τ then
    (if A q.2 then trRetPow P A (τ - q.1) q.2 y
      else ∑' z, trHit P A q.2 z * trRetPow P A (τ - q.1 - 1) z y)
  else if q = (τ, y) then 1 else 0

/-- INTERNAL: one step of the stage process preserves the potential exactly. -/
theorem trStage_potential (τ : ℕ) (y : α) (q : ℕ × α) :
    ∑' q', trStage P A τ q q' * trStageV P A τ y q' = trStageV P A τ y q := by
  obtain ⟨c, u⟩ := q
  by_cases hc : τ ≤ c
  · simp only [trStage, hc, if_true]
    rw [tsum_eq_single (c, u) (fun q hq => by simp [PMF.pure_apply, hq])]
    simp
  · simp only [trStage, hc, if_false]
    rw [tsum_map_mul]
    set W : α → ℝ≥0∞ := fun v => ∑' z, trHit P A v z * trRetPow P A (τ - c - 1) z y with hW
    have hstep : ∀ v, trStageV P A τ y (if A v then (c + 1, v) else (c, v)) = W v := by
      intro v
      by_cases hv : A v
      · simp only [hv, if_true, trStageV, hW, tsum_trHit_of_mem P A hv]
        by_cases hc1 : c + 1 < τ
        · rw [if_pos hc1, show τ - (c + 1) = τ - c - 1 by omega]
        · rw [if_neg hc1, show τ - c - 1 = 0 by omega, show τ = c + 1 by omega]
          simp [trRetPow]
      · simp only [hv, if_false, trStageV, hW, show c < τ by omega, if_true]
    simp_rw [hstep]
    have hcτ : c < τ := by omega
    by_cases hu : A u
    · simp only [trStageV, hcτ, hu, if_true]
      rw [show τ - c = τ - c - 1 + 1 by omega, trRetPow_succ_eq]
    · simp only [trStageV, hcτ, hu, if_true, if_false, hW]
      rw [tsum_trHit_of_not_mem P A hu]

/-- INTERNAL: a `loop` whose step ignores the index, unrolled at its first iteration. -/
theorem trd_loop_const_succ {β : Type} (g : β → PMF β) (k : ℕ) (b : β) :
    loop (fun _ => g) (k + 1) b = (g b).bind (loop (fun _ => g) k) := by
  induction k generalizing b with
  | zero => rw [loop_succ, loop_zero, PMF.pure_bind]; exact (PMF.bind_pure _).symm
  | succ k ih =>
    rw [loop_succ, ih, PMF.bind_bind]
    congr 1; funext x; rw [loop_succ]

/-- INTERNAL: the stage process is dominated by its potential, for every number of
underlying transitions. -/
theorem trStage_loop_le_V (τ : ℕ) (y : α) (N : ℕ) (q : ℕ × α) :
    loop (fun _ => trStage P A τ) N q (τ, y) ≤ trStageV P A τ y q := by
  induction N generalizing q with
  | zero =>
    rw [loop_zero, PMF.pure_apply]
    split_ifs with h
    · subst h; simp [trStageV]
    · exact zero_le
  | succ N ih =>
    rw [trd_loop_const_succ, PMF.bind_apply, ← trStage_potential P A τ y q]
    exact ENNReal.tsum_le_tsum fun q' => by gcongr; exact ih q'

/-- INTERNAL: **truncated trace steps are dominated by the trace power**: from `x ∈ A`,
completing `τ` trace steps at `y` within `N` underlying transitions has probability at most
`P_tr^τ(x, y)`.
TEXLINE: sections/algorithm.tex:283-291 -/
theorem trStage_loop_le (τ : ℕ) {x : α} (hx : A x) (y : α) (N : ℕ) :
    loop (fun _ => trStage P A τ) N (0, x) (τ, y) ≤ trRetPow P A τ x y := by
  refine (trStage_loop_le_V P A τ y N (0, x)).trans (le_of_eq ?_)
  unfold trStageV
  rcases Nat.eq_zero_or_pos τ with hτ | hτ
  · subst hτ; simp [trRetPow]
  · simp [hτ, hx]

end TraceDomination

end Cellcounting.Analysis
