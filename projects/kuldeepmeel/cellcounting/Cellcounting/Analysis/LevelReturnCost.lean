import Cellcounting.Analysis.PmfClose

/-!
# Warm return costs of a level-counting chain (`lem:trace`, `eq:trace-return-cost`)

Elementary, sub-measure-valued (`α → ℝ≥0∞`) facts about a Markov kernel `K : α → PMF α`,
a target set `A`, and the *killed* operator `ruKil` (one step, mass landing in `A`
removed).  Iterating it from `π|_A` describes the excursions of the chain away from `A`.

* `ru_kac` — **Kac's bound**: if `π K ≤ π`, the expected return time to `A` from
  `π|_A` (truncated after `N` steps) has `π`-mass at most `π(Ω)`:
  `Σ_{m<N} |π|_A K_kill^m| ≤ |π|`.
* `ru_trace` — **sub-invariance of the trace**: the law of the first return point to `A`
  from `π|_A` is at most `π|_A`.
* `ru_occ` — the occupation measure of a process `u_{n+1} = K_kill u_n + e_{n+1}` is at
  most the killed Green operator applied to its total entrance measure.

Then the *level process* `ruLvStep`: a state `(ℓ, x)`; one step of the level-`ℓ` kernel
`P ℓ`, and the level goes up by one each time the chain lands in `A`; frozen at level `L`.
This is the uncapped restart of `algorithm.tex:214-225` (levels count completed trace
steps, `τ` per stage), and with `L = τ` the trace stage of `StageEndpoint.lean`.

* `ruLvLaw_succ_lt`, `ruLvLaw_succ_top` — the one-step recursions of its law by level.
* `ru_level` — per level: an entrance law `≤ c π|_A` (with `π` sub-stationary for that
  level's kernel) costs at most `c |π|` expected transitions, and the next level's
  entrance law is again `≤ c π|_A`.
* `ru_conv` — the entrance law at level `b + τ'` is the superposition, over the entrance
  times and points at level `b`, of independent `τ'`-level runs (the strong Markov
  property at those entrance times, in time-indexed form).
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal

section Kernel

variable {α : Type} (K : α → PMF α) (A : α → Prop) [DecidablePred A]

/-- INTERNAL: the action `ρ ↦ ρ K` of a kernel on a sub-measure.
TEXLINE: sections/transport.tex:647-700 -/
noncomputable def ruAct (ρ : α → ℝ≥0∞) : α → ℝ≥0∞ := fun y => ∑' x, ρ x * K x y

/-- INTERNAL: the killed step: one step of `K`, with the mass landing in `A` removed.
TEXLINE: sections/transport.tex:647-700 -/
noncomputable def ruKil (ρ : α → ℝ≥0∞) : α → ℝ≥0∞ := fun y => if A y then 0 else ruAct K ρ y

/-- INTERNAL: the hitting step: one step of `K`, keeping only the mass landing in `A`.
TEXLINE: sections/transport.tex:647-700 -/
noncomputable def ruHit (ρ : α → ℝ≥0∞) : α → ℝ≥0∞ := fun y => if A y then ruAct K ρ y else 0

/-- INTERNAL: the killed Green operator truncated after `N` steps, `Σ_{m<N} K_kill^m`.
TEXLINE: sections/transport.tex:647-700 -/
noncomputable def ruGreen (N : ℕ) (ρ : α → ℝ≥0∞) : α → ℝ≥0∞ :=
  fun y => ∑ m ∈ Finset.range N, (ruKil K A)^[m] ρ y

/-- INTERNAL: the total mass of a sub-measure. -/
noncomputable def ruMass (ρ : α → ℝ≥0∞) : ℝ≥0∞ := ∑' x, ρ x

/-- INTERNAL: the restriction `ρ|_A`. -/
noncomputable def ruRes (ρ : α → ℝ≥0∞) : α → ℝ≥0∞ := fun x => if A x then ρ x else 0

variable {K A}

theorem ruAct_mono {ρ ρ' : α → ℝ≥0∞} (h : ∀ x, ρ x ≤ ρ' x) (y : α) :
    ruAct K ρ y ≤ ruAct K ρ' y :=
  ENNReal.tsum_le_tsum fun x => mul_le_mul_left (h x) _

theorem ruAct_add (ρ ρ' : α → ℝ≥0∞) (y : α) :
    ruAct K (fun x => ρ x + ρ' x) y = ruAct K ρ y + ruAct K ρ' y := by
  simp only [ruAct, add_mul]
  exact ENNReal.tsum_add

theorem ruAct_smul (c : ℝ≥0∞) (ρ : α → ℝ≥0∞) (y : α) :
    ruAct K (fun x => c * ρ x) y = c * ruAct K ρ y := by
  simp only [ruAct, mul_assoc]
  exact ENNReal.tsum_mul_left

theorem ruAct_sum {ι : Type} (s : Finset ι) (ρ : ι → α → ℝ≥0∞) (y : α) :
    ruAct K (fun x => ∑ i ∈ s, ρ i x) y = ∑ i ∈ s, ruAct K (ρ i) y := by
  simp only [ruAct, Finset.sum_mul]
  exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable

theorem ruMass_act (ρ : α → ℝ≥0∞) : ruMass (ruAct K ρ) = ruMass ρ := by
  simp only [ruMass, ruAct]
  rw [ENNReal.tsum_comm]
  congr 1; funext x
  rw [ENNReal.tsum_mul_left, (K x).tsum_coe, mul_one]

theorem ruMass_mono {ρ ρ' : α → ℝ≥0∞} (h : ∀ x, ρ x ≤ ρ' x) : ruMass ρ ≤ ruMass ρ' :=
  ENNReal.tsum_le_tsum h

theorem ruMass_add (ρ ρ' : α → ℝ≥0∞) : ruMass (fun x => ρ x + ρ' x) = ruMass ρ + ruMass ρ' :=
  ENNReal.tsum_add

theorem ruMass_smul (c : ℝ≥0∞) (ρ : α → ℝ≥0∞) : ruMass (fun x => c * ρ x) = c * ruMass ρ :=
  ENNReal.tsum_mul_left

theorem ruMass_sum {ι : Type} (s : Finset ι) (ρ : ι → α → ℝ≥0∞) :
    ruMass (fun x => ∑ i ∈ s, ρ i x) = ∑ i ∈ s, ruMass (ρ i) :=
  Summable.tsum_finsetSum fun _ _ => ENNReal.summable

theorem ruKil_mono {ρ ρ' : α → ℝ≥0∞} (h : ∀ x, ρ x ≤ ρ' x) (y : α) :
    ruKil K A ρ y ≤ ruKil K A ρ' y := by
  unfold ruKil; split_ifs
  · exact le_rfl
  · exact ruAct_mono h y

theorem ruKil_add (ρ ρ' : α → ℝ≥0∞) (y : α) :
    ruKil K A (fun x => ρ x + ρ' x) y = ruKil K A ρ y + ruKil K A ρ' y := by
  unfold ruKil; split_ifs
  · simp
  · exact ruAct_add ρ ρ' y

theorem ruKil_smul (c : ℝ≥0∞) (ρ : α → ℝ≥0∞) (y : α) :
    ruKil K A (fun x => c * ρ x) y = c * ruKil K A ρ y := by
  unfold ruKil; split_ifs
  · simp
  · exact ruAct_smul c ρ y

theorem ruKil_sum {ι : Type} (s : Finset ι) (ρ : ι → α → ℝ≥0∞) (y : α) :
    ruKil K A (fun x => ∑ i ∈ s, ρ i x) y = ∑ i ∈ s, ruKil K A (ρ i) y := by
  unfold ruKil; split_ifs
  · simp
  · exact ruAct_sum s ρ y

theorem ruHit_mono {ρ ρ' : α → ℝ≥0∞} (h : ∀ x, ρ x ≤ ρ' x) (y : α) :
    ruHit K A ρ y ≤ ruHit K A ρ' y := by
  unfold ruHit; split_ifs
  · exact ruAct_mono h y
  · exact le_rfl

theorem ruHit_smul (c : ℝ≥0∞) (ρ : α → ℝ≥0∞) (y : α) :
    ruHit K A (fun x => c * ρ x) y = c * ruHit K A ρ y := by
  unfold ruHit; split_ifs
  · exact ruAct_smul c ρ y
  · simp

theorem ruHit_sum {ι : Type} (s : Finset ι) (ρ : ι → α → ℝ≥0∞) (y : α) :
    ruHit K A (fun x => ∑ i ∈ s, ρ i x) y = ∑ i ∈ s, ruHit K A (ρ i) y := by
  unfold ruHit; split_ifs
  · exact ruAct_sum s ρ y
  · simp

theorem ruKil_iter_mono (m : ℕ) {ρ ρ' : α → ℝ≥0∞} (h : ∀ x, ρ x ≤ ρ' x) (y : α) :
    (ruKil K A)^[m] ρ y ≤ (ruKil K A)^[m] ρ' y := by
  induction m generalizing y with
  | zero => exact h y
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact ruKil_mono ih y

theorem ruKil_iter_add (m : ℕ) (ρ ρ' : α → ℝ≥0∞) :
    (ruKil K A)^[m] (fun x => ρ x + ρ' x) =
      fun y => (ruKil K A)^[m] ρ y + (ruKil K A)^[m] ρ' y := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext y
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, ruKil_add]

theorem ruKil_iter_smul (m : ℕ) (c : ℝ≥0∞) (ρ : α → ℝ≥0∞) :
    (ruKil K A)^[m] (fun x => c * ρ x) = fun y => c * (ruKil K A)^[m] ρ y := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext y
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, ruKil_smul]

theorem ruGreen_mono (N : ℕ) {ρ ρ' : α → ℝ≥0∞} (h : ∀ x, ρ x ≤ ρ' x) (y : α) :
    ruGreen K A N ρ y ≤ ruGreen K A N ρ' y :=
  Finset.sum_le_sum fun m _ => ruKil_iter_mono m h y

theorem ruGreen_smul (N : ℕ) (c : ℝ≥0∞) (ρ : α → ℝ≥0∞) (y : α) :
    ruGreen K A N (fun x => c * ρ x) y = c * ruGreen K A N ρ y := by
  simp only [ruGreen, ruKil_iter_smul, Finset.mul_sum]

theorem ruGreen_succ (N : ℕ) (ρ : α → ℝ≥0∞) (y : α) :
    ruGreen K A (N + 1) ρ y = ρ y + ruKil K A (ruGreen K A N ρ) y := by
  show _ = ρ y + ruKil K A (fun x => ∑ m ∈ Finset.range N, (ruKil K A)^[m] ρ x) y
  simp only [ruGreen]
  rw [Finset.sum_range_succ', ruKil_sum]
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id]
  rw [add_comm]

/-- INTERNAL: **Kac's bound** for a sub-stationary `π`: the `N`-step truncated expected
return time to `A` from `π|_A` is at most the mass of `π`.
TEXLINE: sections/transport.tex:647-700 -/
theorem ru_kac (π : α → ℝ≥0∞) (hπ : ∀ y, ruAct K π y ≤ π y) (N : ℕ) :
    ruMass (ruGreen K A N (ruRes A π)) ≤ ruMass π := by
  set πB : α → ℝ≥0∞ := fun x => if A x then 0 else π x with hπB
  have hsplit : (fun x => ruRes A π x + πB x) = π := by
    funext x; simp only [ruRes, hπB]; split_ifs <;> simp
  -- one killed step from `π` lands below `π|_{Aᶜ}`
  have hkil : ∀ y, ruKil K A π y ≤ πB y := by
    intro y; simp only [ruKil, hπB]; split_ifs
    · exact le_rfl
    · exact hπ y
  have hstep : ∀ m y, (ruKil K A)^[m + 1] (ruRes A π) y + (ruKil K A)^[m + 1] πB y ≤
      (ruKil K A)^[m] πB y := by
    intro m y
    have := congrFun (ruKil_iter_add (K := K) (A := A) (m + 1) (ruRes A π) πB) y
    rw [← this, hsplit, Function.iterate_succ_apply]
    exact ruKil_iter_mono m hkil y
  have hclaim : ∀ M, ∑ m ∈ Finset.range (M + 1), ruMass ((ruKil K A)^[m] (ruRes A π)) +
      ruMass ((ruKil K A)^[M] πB) ≤ ruMass π := by
    intro M
    induction M with
    | zero =>
      rw [Finset.sum_range_one]
      show ruMass (ruRes A π) + ruMass πB ≤ ruMass π
      rw [← ruMass_add, hsplit]
    | succ M ih =>
      rw [Finset.sum_range_succ, add_assoc, ← ruMass_add]
      calc _ ≤ ∑ m ∈ Finset.range (M + 1), ruMass ((ruKil K A)^[m] (ruRes A π)) +
            ruMass ((ruKil K A)^[M] πB) := by
            gcongr
            exact ruMass_mono (hstep M)
        _ ≤ _ := ih
  rcases N with _ | M
  · simp [ruGreen, ruMass]
  · unfold ruGreen
    rw [ruMass_sum]
    exact le_trans le_self_add (hclaim M)

/-- INTERNAL: **sub-invariance of the trace law**: for a sub-stationary `π`, the law of
the first return point to `A` from `π|_A` (truncated after `N` steps) is at most `π|_A`.
TEXLINE: sections/transport.tex:647-700 -/
theorem ru_trace (π : α → ℝ≥0∞) (hπ : ∀ y, ruAct K π y ≤ π y) (N : ℕ) (y : α) :
    ruHit K A (ruGreen K A N (ruRes A π)) y ≤ ruRes A π y := by
  set πB : α → ℝ≥0∞ := fun x => if A x then 0 else π x with hπB
  have hsplit : (fun x => ruRes A π x + πB x) = π := by
    funext x; simp only [ruRes, hπB]; split_ifs <;> simp
  have hkil : ∀ y, ruKil K A π y ≤ πB y := by
    intro y; simp only [ruKil, hπB]; split_ifs
    · exact le_rfl
    · exact hπ y
  have hstep : ∀ m x, (ruKil K A)^[m + 1] (ruRes A π) x + (ruKil K A)^[m + 1] πB x ≤
      (ruKil K A)^[m] πB x := by
    intro m x
    have := congrFun (ruKil_iter_add (K := K) (A := A) (m + 1) (ruRes A π) πB) x
    rw [← this, hsplit, Function.iterate_succ_apply]
    exact ruKil_iter_mono m hkil x
  have hclaim : ∀ M, ∑ m ∈ Finset.range (M + 1), ruAct K ((ruKil K A)^[m] (ruRes A π)) y +
      ruAct K ((ruKil K A)^[M] πB) y ≤ ruAct K π y := by
    intro M
    induction M with
    | zero =>
      rw [Finset.sum_range_one]
      show ruAct K (ruRes A π) y + ruAct K πB y ≤ ruAct K π y
      rw [← ruAct_add, hsplit]
    | succ M ih =>
      rw [Finset.sum_range_succ, add_assoc, ← ruAct_add]
      calc _ ≤ ∑ m ∈ Finset.range (M + 1), ruAct K ((ruKil K A)^[m] (ruRes A π)) y +
            ruAct K ((ruKil K A)^[M] πB) y := by
            gcongr
            exact ruAct_mono (hstep M) y
        _ ≤ _ := ih
  unfold ruHit ruRes
  split_ifs with hA
  · unfold ruGreen
    rw [ruAct_sum]
    rcases N with _ | M
    · simp
    · exact le_trans le_self_add ((hclaim M).trans (hπ y))
  · exact le_rfl

/-- INTERNAL: the occupation measure of `u_{n+1} = K_kill u_n + e_{n+1}`, `u_0 = e_0`, up to
time `N` is at most the killed Green operator applied to the total entrance measure.
TEXLINE: sections/transport.tex:647-700 -/
theorem ru_occ (u e : ℕ → α → ℝ≥0∞) (h0 : ∀ y, u 0 y = e 0 y)
    (hs : ∀ n y, u (n + 1) y = ruKil K A (u n) y + e (n + 1) y) (N : ℕ) (y : α) :
    ∑ n ∈ Finset.range N, u n y ≤
      ruGreen K A N (fun x => ∑ n ∈ Finset.range N, e n x) y := by
  induction N generalizing y with
  | zero => simp [ruGreen]
  | succ N ih =>
    rw [Finset.sum_range_succ', ruGreen_succ]
    simp only [hs]
    rw [Finset.sum_add_distrib, ← ruKil_sum, h0]
    have hE : (∑ n ∈ Finset.range N, e (n + 1) y) + e 0 y =
        ∑ n ∈ Finset.range (N + 1), e n y := (Finset.sum_range_succ' (fun n => e n y) N).symm
    calc ruKil K A (fun x => ∑ i ∈ Finset.range N, u i x) y +
          ∑ n ∈ Finset.range N, e (n + 1) y + e 0 y
        = ∑ n ∈ Finset.range (N + 1), e n y +
            ruKil K A (fun x => ∑ i ∈ Finset.range N, u i x) y := by
          rw [← hE]; ring
      _ ≤ ∑ n ∈ Finset.range (N + 1), e n y +
            ruKil K A (ruGreen K A N fun x => ∑ n ∈ Finset.range (N + 1), e n x) y := by
          gcongr
          refine ruKil_mono (fun x => (ih x).trans (ruGreen_mono N (fun z => ?_) x)) y
          exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.le_succ N))

end Kernel

section Level

variable {α : Type} (P : ℕ → α → PMF α) (L : ℕ) (A : α → Prop) [DecidablePred A]

/-- INTERNAL: one step of the level process: from `(ℓ, x)` take a step of `P ℓ`, and go up
one level on landing in `A`; frozen once the level reaches `L`.
TEXLINE: sections/algorithm.tex:214-225 -/
noncomputable def ruLvStep (q : ℕ × α) : PMF (ℕ × α) :=
  if L ≤ q.1 then PMF.pure q else (P q.1 q.2).map fun y => (if A y then q.1 + 1 else q.1, y)

/-- INTERNAL: the law of the level process after `n` steps from the initial law `ν0`.
TEXLINE: sections/algorithm.tex:214-225 -/
noncomputable def ruLvLaw (ν0 : PMF (ℕ × α)) (n : ℕ) : PMF (ℕ × α) :=
  ν0.bind fun q => loop (fun _ => ruLvStep P L A) n q

/-- INTERNAL: the entrance sub-law at level `ℓ` at time `i`: the initial law at `i = 0`,
afterwards the mass arriving at level `ℓ` (from level `ℓ - 1`, landing in `A`) at time `i`.
TEXLINE: sections/algorithm.tex:214-225 -/
noncomputable def ruEnt (ν0 : PMF (ℕ × α)) : ℕ → ℕ → α → ℝ≥0∞
  | 0, ℓ, y => ν0 (ℓ, y)
  | i + 1, ℓ, y =>
    if A y ∧ ℓ ≠ 0 then ∑' x, ruLvLaw P L A ν0 i (ℓ - 1, x) * P (ℓ - 1) x y else 0

variable {P L A}

theorem ruLvLaw_zero (ν0 : PMF (ℕ × α)) : ruLvLaw P L A ν0 0 = ν0 := by
  simp only [ruLvLaw, loop_zero]
  exact PMF.bind_pure ν0

theorem ruLvLaw_succ (ν0 : PMF (ℕ × α)) (n : ℕ) :
    ruLvLaw P L A ν0 (n + 1) = (ruLvLaw P L A ν0 n).bind (ruLvStep P L A) := by
  simp only [ruLvLaw, loop_succ, PMF.bind_bind]

open Classical in
theorem ruLvStep_apply (q : ℕ × α) (ℓ : ℕ) (y : α) :
    ruLvStep P L A q (ℓ, y) = if L ≤ q.1 then (if (ℓ, y) = q then 1 else 0)
      else (if ℓ = (if A y then q.1 + 1 else q.1) then P q.1 q.2 y else 0) := by
  unfold ruLvStep
  by_cases h1 : L ≤ q.1
  · rw [if_pos h1, if_pos h1, PMF.pure_apply]
    congr
  · rw [if_neg h1, if_neg h1, PMF.map_apply, tsum_eq_single y]
    · simp
    · intro a ha
      simp [Ne.symm ha]

theorem ruLvStep_apply_lt (q : ℕ × α) {ℓ : ℕ} (hℓ : ℓ < L) (y : α) :
    ruLvStep P L A q (ℓ, y) =
      if q.1 < L ∧ ℓ = (if A y then q.1 + 1 else q.1) then P q.1 q.2 y else 0 := by
  rw [ruLvStep_apply]
  by_cases h1 : L ≤ q.1
  · have h2 : ¬ (q.1 < L ∧ ℓ = (if A y then q.1 + 1 else q.1)) := fun h => by omega
    rw [if_pos h1, if_neg h2]
    split_ifs with h3
    · rw [← h3] at h1
      exact absurd h1 (by simp only; omega)
    · rfl
  · rw [if_neg h1]
    by_cases h2 : ℓ = (if A y then q.1 + 1 else q.1)
    · rw [if_pos h2, if_pos ⟨by omega, h2⟩]
    · rw [if_neg h2, if_neg (fun h => h2 h.2)]

/-- INTERNAL: one step of the level law below the frozen level.
TEXLINE: sections/algorithm.tex:214-225 -/
theorem ruLvLaw_succ_lt (ν0 : PMF (ℕ × α)) (n : ℕ) {ℓ : ℕ} (hℓ : ℓ < L) (y : α) :
    ruLvLaw P L A ν0 (n + 1) (ℓ, y) =
      if A y then
        (if ℓ = 0 then 0 else ∑' x, ruLvLaw P L A ν0 n (ℓ - 1, x) * P (ℓ - 1) x y)
      else ∑' x, ruLvLaw P L A ν0 n (ℓ, x) * P ℓ x y := by
  rw [ruLvLaw_succ, PMF.bind_apply, ENNReal.tsum_prod']
  simp_rw [ruLvStep_apply_lt _ hℓ]
  by_cases hA : A y
  · simp only [hA, if_true]
    rcases ℓ with _ | m
    · simp
    · rw [if_neg (Nat.succ_ne_zero m), tsum_eq_single m]
      · congr 1; funext x
        rw [if_pos ⟨by omega, rfl⟩]; rfl
      · intro a ha
        refine ENNReal.tsum_eq_zero.2 fun x => ?_
        rw [if_neg (fun h => ha (by omega))]; simp
  · simp only [hA, if_false]
    rw [tsum_eq_single ℓ]
    · congr 1; funext x
      rw [if_pos ⟨hℓ, rfl⟩]
    · intro a ha
      refine ENNReal.tsum_eq_zero.2 fun x => ?_
      rw [if_neg (fun h => ha h.2.symm)]; simp

/-- INTERNAL: one step of the level law at the frozen level `L`.
TEXLINE: sections/algorithm.tex:214-225 -/
theorem ruLvLaw_succ_top (ν0 : PMF (ℕ × α)) (n : ℕ) (hL : 0 < L) (y : α) :
    ruLvLaw P L A ν0 (n + 1) (L, y) = ruLvLaw P L A ν0 n (L, y) +
      (if A y then ∑' x, ruLvLaw P L A ν0 n (L - 1, x) * P (L - 1) x y else 0) := by
  rw [ruLvLaw_succ, PMF.bind_apply, ENNReal.tsum_prod']
  simp_rw [ruLvStep_apply]
  rw [tsum_eq_sum (s := {L - 1, L})]
  · rw [Finset.sum_pair (show L - 1 ≠ L by omega), add_comm]
    congr 1
    · rw [tsum_eq_single y]
      · simp
      · intro b hb
        simp [Ne.symm hb]
    · have hL1 : ¬ (L ≤ L - 1) := by omega
      simp only [hL1, if_false]
      by_cases hA : A y
      · simp only [hA, if_true]
        congr 1; funext x
        rw [if_pos (show L = L - 1 + 1 by omega)]
      · simp only [hA, if_false]
        refine ENNReal.tsum_eq_zero.2 fun x => ?_
        rw [if_neg (show ¬ L = L - 1 by omega)]; simp
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
    refine ENNReal.tsum_eq_zero.2 fun x => ?_
    by_cases h1 : L ≤ a
    · rw [if_pos h1, if_neg (by simp; omega)]; simp
    · rw [if_neg h1, if_neg (by split_ifs <;> omega)]; simp

/-- INTERNAL: below the frozen level, the level law is the killed step of the previous one
plus the fresh entrance mass.
TEXLINE: sections/algorithm.tex:214-225 -/
theorem ruLv_split (ν0 : PMF (ℕ × α)) (n : ℕ) {ℓ : ℕ} (hℓ : ℓ < L) (y : α) :
    ruLvLaw P L A ν0 (n + 1) (ℓ, y) =
      ruKil (P ℓ) A (fun x => ruLvLaw P L A ν0 n (ℓ, x)) y + ruEnt P L A ν0 (n + 1) ℓ y := by
  rw [ruLvLaw_succ_lt ν0 n hℓ]
  simp only [ruKil, ruAct, ruEnt]
  by_cases hA : A y <;> by_cases hℓ0 : ℓ = 0 <;> simp [hA, hℓ0]

/-- INTERNAL: the total entrance law at level `ℓ + 1` is at most the hitting step of the
occupation measure of level `ℓ`.
TEXLINE: sections/algorithm.tex:214-225 -/
theorem ruEnt_succ_le (ν0 : PMF (ℕ × α)) (hν0 : ∀ ℓ y, ℓ ≠ 0 → ν0 (ℓ, y) = 0) (N ℓ : ℕ)
    (y : α) :
    ∑ i ∈ Finset.range N, ruEnt P L A ν0 i (ℓ + 1) y ≤
      ruHit (P ℓ) A (fun x => ∑ i ∈ Finset.range N, ruLvLaw P L A ν0 i (ℓ, x)) y := by
  rw [ruHit_sum]
  rcases N with _ | N
  · simp
  · rw [Finset.sum_range_succ']
    have h0 : ruEnt P L A ν0 0 (ℓ + 1) y = 0 := hν0 _ _ (Nat.succ_ne_zero ℓ)
    rw [h0, add_zero]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      (Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.le_succ N)))
    simp only [ruEnt, ruHit, ruAct, Nat.add_sub_cancel]
    by_cases hA : A y <;> simp [hA]

/-- INTERNAL: **one level of the level process** (`eq:trace-return-cost`): if the total
entrance law at level `ℓ < L` is at most `c π|_A` for a `π` sub-stationary under `P ℓ`,
the expected number of steps spent at level `ℓ` is at most `c |π|`, and the total entrance
law at level `ℓ + 1` is again at most `c π|_A`.
TEXLINE: sections/transport.tex:647-700 -/
theorem ru_level (ν0 : PMF (ℕ × α)) (hν0 : ∀ ℓ y, ℓ ≠ 0 → ν0 (ℓ, y) = 0) {ℓ : ℕ}
    (hℓ : ℓ < L) (π : α → ℝ≥0∞) (hπ : ∀ y, ruAct (P ℓ) π y ≤ π y) (c : ℝ≥0∞) (N : ℕ)
    (hF : ∀ y, ∑ i ∈ Finset.range N, ruEnt P L A ν0 i ℓ y ≤ c * ruRes A π y) :
    ruMass (fun y => ∑ n ∈ Finset.range N, ruLvLaw P L A ν0 n (ℓ, y)) ≤ c * ruMass π ∧
      ∀ y, ∑ i ∈ Finset.range N, ruEnt P L A ν0 i (ℓ + 1) y ≤ c * ruRes A π y := by
  have hocc := ru_occ (K := P ℓ) (A := A) (fun n y => ruLvLaw P L A ν0 n (ℓ, y))
    (fun n y => ruEnt P L A ν0 n ℓ y) (fun y => by simp [ruLvLaw_zero, ruEnt])
    (fun n y => ruLv_split ν0 n hℓ y) N
  have hU : ∀ y, ∑ n ∈ Finset.range N, ruLvLaw P L A ν0 n (ℓ, y) ≤
      c * ruGreen (P ℓ) A N (ruRes A π) y := fun y =>
    (hocc y).trans ((ruGreen_mono N hF y).trans (ruGreen_smul N c _ y).le)
  constructor
  · calc _ ≤ ruMass (fun y => c * ruGreen (P ℓ) A N (ruRes A π) y) := ruMass_mono hU
      _ = c * ruMass (ruGreen (P ℓ) A N (ruRes A π)) := ruMass_smul _ _
      _ ≤ c * ruMass π := mul_le_mul_right (ru_kac π hπ N) c
  · intro y
    calc _ ≤ _ := ruEnt_succ_le ν0 hν0 N ℓ y
      _ ≤ ruHit (P ℓ) A (fun x => c * ruGreen (P ℓ) A N (ruRes A π) x) y := ruHit_mono hU y
      _ = c * ruHit (P ℓ) A (ruGreen (P ℓ) A N (ruRes A π)) y := ruHit_smul _ _ _
      _ ≤ c * ruRes A π y := mul_le_mul_right (ru_trace π hπ N y) c

theorem ru_swap {ι β : Type} (s : Finset ι) (c : ι → β → ℝ≥0∞) (h : ι → β → α → ℝ≥0∞)
    (g : α → ℝ≥0∞) :
    ∑' x, (∑ i ∈ s, ∑' z, c i z * h i z x) * g x =
      ∑ i ∈ s, ∑' z, c i z * ∑' x, h i z x * g x := by
  simp_rw [Finset.sum_mul, ← ENNReal.tsum_mul_right]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun z => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun x => ?_
  ring

/-- INTERNAL: **superposition at the entrance to level `b`** (the strong Markov property
at the entrance times, in time-indexed form): while the level process is in the levels
`b, …, b + τ' - 1` driven by `P (b + k)`, its law is at most the superposition, over the
entrance times `i` and points `x` at level `b`, of a `τ'`-level process (kernels
`P' k = P (b + k)`, frozen at `τ'`) started at `(0, x)` and run `n - i` steps; and the
cumulative entrance law at level `b + τ'` is at most the frozen-level mass of the same
superposition.
TEXLINE: sections/algorithm.tex:283-296 -/
theorem ru_conv (ν0 : PMF (ℕ × α)) (hν0 : ∀ ℓ y, ℓ ≠ 0 → ν0 (ℓ, y) = 0) (b τ' : ℕ)
    (hτ' : 0 < τ') (hbL : b + τ' ≤ L) (P' : ℕ → α → PMF α)
    (hP' : ∀ k < τ', P' k = P (b + k)) (n : ℕ) :
    (∀ k < τ', ∀ y, ruLvLaw P L A ν0 n (b + k, y) ≤
      ∑ i ∈ Finset.range (n + 1), ∑' x, ruEnt P L A ν0 i b x *
        ruLvLaw P' τ' A (PMF.pure (0, x)) (n - i) (k, y)) ∧
    (∀ y, ∑ i ∈ Finset.range (n + 1), ruEnt P L A ν0 i (b + τ') y ≤
      ∑ i ∈ Finset.range (n + 1), ∑' x, ruEnt P L A ν0 i b x *
        ruLvLaw P' τ' A (PMF.pure (0, x)) (n - i) (τ', y)) := by
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, Nat.sub_zero, ruLvLaw_zero]
    constructor
    · intro k hk y
      by_cases h : b + k = 0
      · obtain ⟨rfl, rfl⟩ : b = 0 ∧ k = 0 := by omega
        refine le_trans (le_of_eq ?_) (ENNReal.le_tsum y)
        simp [ruEnt]
      · rw [hν0 _ _ h]; exact bot_le
    · intro y
      rw [show ruEnt P L A ν0 0 (b + τ') y = ν0 (b + τ', y) from rfl, hν0 _ _ (by omega)]
      exact bot_le
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    set s : α → ℕ → PMF (ℕ × α) := fun x m => ruLvLaw P' τ' A (PMF.pure (0, x)) m with hs
    set e : ℕ → α → ℝ≥0∞ := fun i x => ruEnt P L A ν0 i b x with he
    have hdrop : ∀ q, ∑ i ∈ Finset.range (n + 1), ∑' x, e i x * s x (n - i + 1) q ≤
        ∑ i ∈ Finset.range (n + 1 + 1), ∑' x, e i x * s x (n + 1 - i) q := by
      intro q
      rw [Finset.sum_range_succ (n := n + 1)]
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun i hi => ?_)) le_self_add
      rw [show n + 1 - i = n - i + 1 by have := Finset.mem_range.1 hi; omega]
    constructor
    · intro k hk y
      have hbk : b + k < L := by omega
      rw [ruLvLaw_succ_lt ν0 n hbk]
      by_cases hA : A y
      · rw [if_pos hA]
        rcases k with _ | k
        · have hE : (if b + 0 = 0 then 0 else
              ∑' x, ruLvLaw P L A ν0 n (b + 0 - 1, x) * P (b + 0 - 1) x y) = e (n + 1) y := by
            simp only [he, ruEnt, add_zero]
            by_cases hb : b = 0 <;> simp [hb, hA]
          rw [hE, Finset.sum_range_succ (n := n + 1), Nat.sub_self]
          refine le_trans ?_ le_add_self
          refine le_trans (le_of_eq ?_) (ENNReal.le_tsum y)
          simp [he, ruLvLaw_zero]
        · rw [if_neg (show b + (k + 1) ≠ 0 by omega), show b + (k + 1) - 1 = b + k by omega]
          calc ∑' x, ruLvLaw P L A ν0 n (b + k, x) * P (b + k) x y
              ≤ ∑' x, (∑ i ∈ Finset.range (n + 1), ∑' z, e i z * s z (n - i) (k, x)) *
                  P' k x y := by
                rw [hP' k (by omega)]
                exact ENNReal.tsum_le_tsum fun x => mul_le_mul_left (ih1 k (by omega) x) _
            _ = ∑ i ∈ Finset.range (n + 1), ∑' z, e i z *
                  ∑' x, s z (n - i) (k, x) * P' k x y := ru_swap _ _ _ _
            _ = ∑ i ∈ Finset.range (n + 1), ∑' z, e i z * s z (n - i + 1) (k + 1, y) := by
                refine Finset.sum_congr rfl fun i _ => tsum_congr fun z => ?_
                rw [hs, ruLvLaw_succ_lt _ _ hk, if_pos hA, if_neg (Nat.succ_ne_zero k)]
                rfl
            _ ≤ _ := hdrop _
      · rw [if_neg hA]
        calc ∑' x, ruLvLaw P L A ν0 n (b + k, x) * P (b + k) x y
            ≤ ∑' x, (∑ i ∈ Finset.range (n + 1), ∑' z, e i z * s z (n - i) (k, x)) *
                P' k x y := by
              rw [hP' k hk]
              exact ENNReal.tsum_le_tsum fun x => mul_le_mul_left (ih1 k hk x) _
          _ = ∑ i ∈ Finset.range (n + 1), ∑' z, e i z *
                ∑' x, s z (n - i) (k, x) * P' k x y := ru_swap _ _ _ _
          _ = ∑ i ∈ Finset.range (n + 1), ∑' z, e i z * s z (n - i + 1) (k, y) := by
              refine Finset.sum_congr rfl fun i _ => tsum_congr fun z => ?_
              rw [hs, ruLvLaw_succ_lt _ _ hk, if_neg hA]
          _ ≤ _ := hdrop _
    · intro y
      rw [Finset.sum_range_succ (n := n + 1)]
      have hE : ruEnt P L A ν0 (n + 1) (b + τ') y = if A y then
          ∑' x, ruLvLaw P L A ν0 n (b + (τ' - 1), x) * P' (τ' - 1) x y else 0 := by
        simp only [ruEnt]
        rw [hP' (τ' - 1) (by omega), show b + τ' - 1 = b + (τ' - 1) by omega]
        by_cases hA : A y
        · rw [if_pos ⟨hA, by omega⟩, if_pos hA]
        · rw [if_neg (fun h => hA h.1), if_neg hA]
      rw [hE]
      calc ∑ i ∈ Finset.range (n + 1), ruEnt P L A ν0 i (b + τ') y +
            (if A y then ∑' x, ruLvLaw P L A ν0 n (b + (τ' - 1), x) * P' (τ' - 1) x y else 0)
          ≤ ∑ i ∈ Finset.range (n + 1), ∑' z, e i z * s z (n - i) (τ', y) +
            (if A y then ∑' x, (∑ i ∈ Finset.range (n + 1), ∑' z, e i z *
              s z (n - i) (τ' - 1, x)) * P' (τ' - 1) x y else 0) := by
            refine add_le_add (ih2 y) ?_
            · split_ifs
              · exact ENNReal.tsum_le_tsum fun x =>
                  mul_le_mul_left (ih1 (τ' - 1) (by omega) x) _
              · exact le_rfl
        _ = ∑ i ∈ Finset.range (n + 1), ∑' z, e i z * s z (n - i + 1) (τ', y) := by
            have htop : ∀ z m, s z (m + 1) (τ', y) = s z m (τ', y) +
                (if A y then ∑' x, s z m (τ' - 1, x) * P' (τ' - 1) x y else 0) :=
              fun z m => ruLvLaw_succ_top _ m hτ' y
            simp_rw [htop]
            split_ifs with hA
            · rw [ru_swap, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← ENNReal.tsum_add]
              refine tsum_congr fun z => ?_
              rw [mul_add]
            · simp
        _ ≤ _ := hdrop _

end Level

section Dom

variable {β γ : Type}

/-- INTERNAL: an invariant preserved by every step holds on the support of a `loop`. -/
theorem ru_loop_support (f : β → PMF β) (Inv : β → Prop)
    (hInv : ∀ b, Inv b → ∀ b' ∈ (f b).support, Inv b') (n : ℕ) (b : β) (hb : Inv b) :
    ∀ b' ∈ (loop (fun _ => f) n b).support, Inv b' := by
  induction n with
  | zero =>
    intro b' hb'
    rw [loop_zero, PMF.support_pure, Set.mem_singleton_iff] at hb'
    subst hb'; exact hb
  | succ n ih =>
    intro b' hb'
    rw [loop_succ] at hb'
    obtain ⟨b'', h1, h2⟩ := (PMF.mem_support_bind_iff _ _ _).1 hb'
    exact hInv b'' (ih b'' h1) b' h2

/-- INTERNAL: **domination of a loop by a projected loop**: if, from every invariant state,
one step of `f` seen through `ψ` puts at most the mass of one step of `g` on the values in
`G` (and none when the current projection is outside `G`), the same holds for `n` steps.
TEXLINE: sections/algorithm.tex:283-296 -/
theorem ru_loop_dom (f : β → PMF β) (g : γ → PMF γ) (ψ : β → γ) (G : γ → Prop)
    [DecidablePred G] (Inv : β → Prop) (hInv : ∀ b, Inv b → ∀ b' ∈ (f b).support, Inv b')
    (h : ∀ b, Inv b → ∀ c, G c → (f b).map ψ c ≤ if G (ψ b) then g (ψ b) c else 0)
    (n : ℕ) (b : β) (hb : Inv b) (c : γ) (hc : G c) :
    (loop (fun _ => f) n b).map ψ c ≤ loop (fun _ => g) n (ψ b) c := by
  induction n generalizing c with
  | zero => simp [loop_zero, PMF.pure_map]
  | succ n ih =>
    rw [loop_succ, loop_succ, PMF.map_bind, PMF.bind_apply, PMF.bind_apply]
    calc ∑' b', (loop (fun _ => f) n b) b' * ((f b').map ψ) c
        ≤ ∑' b', (loop (fun _ => f) n b) b' *
            (fun d => if G d then g d c else 0) (ψ b') := by
          refine ENNReal.tsum_le_tsum fun b' => ?_
          by_cases hb' : b' ∈ (loop (fun _ => f) n b).support
          · exact mul_le_mul_right (h b' (ru_loop_support f Inv hInv n b hb b' hb') c hc) _
          · rw [PMF.mem_support_iff, not_not] at hb'; simp [hb']
      _ = ∑' d, ((loop (fun _ => f) n b).map ψ) d * (if G d then g d c else 0) :=
          (pexp_map _ ψ (fun d => if G d then g d c else 0)).symm
      _ ≤ ∑' d, (loop (fun _ => g) n (ψ b)) d * g d c :=
          ENNReal.tsum_le_tsum fun d => by
            split_ifs with hd
            · exact mul_le_mul_left (ih d hd) _
            · simp

end Dom

end Cellcounting.Analysis
