import Esa22Copy.Analysis.RelaxedDomination

/-!
# Event bounds for Algorithm 2 from the domination invariant

Two consequences of `relaxed_domination` used in Claim `lm:error-fail`
(esa22-final.tex:701-781):

* `relaxed_level_eq_le` — `Pr[p_m = 2⁻q ∧ X_m ∈ E] ≤ Pr[Y_{q,m} ∈ E]`, the step
  `Pr[Error_{2,q}] ≤ Pr[|Y_{q,m}| ∉ …]` (esa22-final.tex:758-760);
* `relaxed_level_gt_le` — `Pr[p_m < 2⁻ℓ] ≤ Σⱼ Pr[|Y_{ℓ,j}| = thresh]`, the
  bound `Pr[Bad] = Σⱼ Pr[Bad_j]`, `Pr[Bad_j] ≤ Pr[|Y_{ℓ,j}| ≥ thresh]`
  (esa22-final.tex:723-743), proved by induction over the stream: the level
  rises by at most one per iteration, and it rises from `ℓ` exactly when the
  picked set is full.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Esa22Copy.Analysis

open Esa22Copy.Interface (Snapshot)
open Esa22Copy.Interface.Pseudocode

variable {α : Type} [DecidableEq α] [Fintype α]

/-- INTERNAL: the domination invariant integrated against a weight `f`.
TEXLINE: esa22-final.tex:684 -/
theorem relaxed_domination_tsum (thr w : ℕ) (l : List α) (q : ℕ) (hq : q ≤ w)
    (f : Finset α → ℝ≥0∞) :
    ∑' st : Snapshot α, relaxedLoop thr w l init st *
        (if st.level ≤ q then ∑' T, levelSample (q - st.level) st.sample T * f T else 0)
      ≤ ∑' T, levelSample q l.toFinset T * f T := by
  calc _ = ∑' st : Snapshot α, ∑' T, relaxedLoop thr w l init st *
        ((if st.level ≤ q then levelSample (q - st.level) st.sample T else 0) * f T) := by
        refine tsum_congr fun st => ?_
        split_ifs
        · rw [ENNReal.tsum_mul_left]
        · simp
    _ = ∑' T, (∑' st : Snapshot α, relaxedLoop thr w l init st *
        (if st.level ≤ q then levelSample (q - st.level) st.sample T else 0)) * f T := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun T => ?_
        rw [← ENNReal.tsum_mul_right]
        exact tsum_congr fun st => (mul_assoc _ _ _).symm
    _ ≤ _ := ENNReal.tsum_le_tsum fun T =>
        mul_le_mul' (relaxed_domination thr w l q hq T) le_rfl

/-- **`Pr[Error_{2,q}] ≤ Pr[|Y_{q,m}| ∉ …]`, in general form**
(esa22-final.tex:758-760): ending at level `q` with sample set in `E` is at most
as likely as `Y_q ∈ E`.

PAPER: esa22-final.tex:758-760 -/
theorem relaxed_level_eq_le (thr w : ℕ) (l : List α) (q : ℕ) (hq : q ≤ w)
    (E : Set (Finset α)) :
    (relaxedLoop thr w l init).toOuterMeasure {st | st.level = q ∧ st.sample ∈ E} ≤
      (levelSample q l.toFinset).toOuterMeasure E := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  have hR : ∀ T, E.indicator (levelSample q l.toFinset) T =
      levelSample q l.toFinset T * E.indicator 1 T := by
    intro T; by_cases hT : T ∈ E <;> simp [hT]
  simp only [hR]
  refine le_trans (ENNReal.tsum_le_tsum fun st => ?_)
    (relaxed_domination_tsum thr w l q hq (E.indicator 1))
  by_cases h1 : st.level = q ∧ st.sample ∈ E
  · rw [Set.indicator_of_mem (show st ∈ {st : Snapshot α | st.level = q ∧ st.sample ∈ E}
      from h1), if_pos (le_of_eq h1.1), h1.1, Nat.sub_self, levelSample_zero,
      tsum_eq_single st.sample]
    · simp [PMF.pure_apply, h1.2]
    · intro T hT
      simp [PMF.pure_apply, hT]
  · rw [Set.indicator_of_notMem (show st ∉ {st : Snapshot α | st.level = q ∧ st.sample ∈ E}
      from h1)]
    exact bot_le

omit [DecidableEq α] [Fintype α] in
/-- INTERNAL: an event has probability at most one. -/
theorem toOuterMeasure_le_one {β : Type} (μ : PMF β) (G : Set β) : μ.toOuterMeasure G ≤ 1 := by
  rw [PMF.toOuterMeasure_apply, ← μ.tsum_coe]
  exact ENNReal.tsum_le_tsum fun x => Set.indicator_le_self G μ x

/-- INTERNAL: one iteration of Algorithm 2 ends above level `ℓ` only if it starts
above `ℓ`, or starts at `ℓ` and the picked set is full.
TEXLINE: esa22-final.tex:723-731 -/
theorem relaxedStep_level_gt_le (thr w ℓ : ℕ) (st : Snapshot α) (a : α) :
    (relaxedStep thr w st a).toOuterMeasure {st' | ℓ < st'.level} ≤
      {st : Snapshot α | ℓ < st.level}.indicator 1 st +
        (if st.level = ℓ then (pick w ℓ a (drop a st.sample)).toOuterMeasure {X | X.card = thr}
          else 0) := by
  rcases lt_trichotomy ℓ st.level with h | h | h
  · rw [Set.indicator_of_mem (show st ∈ {st : Snapshot α | ℓ < st.level} from h)]
    exact (toOuterMeasure_le_one _ _).trans le_self_add
  · subst h
    rw [Set.indicator_of_notMem (show st ∉ {st' : Snapshot α | st.level < st'.level} from
      fun h' => lt_irrefl st.level h'), if_pos rfl, zero_add, relaxedStep, PMF.toOuterMeasure_bind_apply,
      PMF.toOuterMeasure_apply]
    refine le_of_eq (tsum_congr fun X => ?_)
    by_cases hX : full thr X = true
    · have hc : X.card = thr := by simpa [full] using hX
      rw [if_pos hX, PMF.toOuterMeasure_map_apply,
        Set.indicator_of_mem (show X ∈ {X : Finset α | X.card = thr} from hc)]
      have : (fun Y => (⟨Y, halve st.level⟩ : Snapshot α)) ⁻¹'
          {st' : Snapshot α | st.level < st'.level} = Set.univ := by
        ext Y; simp [halve]
      rw [this, (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _), mul_one]
    · have hc : X.card ≠ thr := by simpa [full] using hX
      rw [if_neg hX, PMF.toOuterMeasure_pure_apply,
        Set.indicator_of_notMem (show X ∉ {X : Finset α | X.card = thr} from hc)]
      simp
  · rw [Set.indicator_of_notMem (show st ∉ {st : Snapshot α | ℓ < st.level} from
      fun h' => absurd h' (not_lt.2 h.le)), if_neg (ne_of_lt h), add_zero]
    rw [relaxedStep, PMF.toOuterMeasure_bind_apply]
    refine le_of_eq (ENNReal.tsum_eq_zero.2 fun X => ?_)
    split_ifs
    · rw [PMF.toOuterMeasure_map_apply]
      have : (fun Y => (⟨Y, halve st.level⟩ : Snapshot α)) ⁻¹'
          {st' : Snapshot α | ℓ < st'.level} = ∅ := by
        ext Y; simp [halve]; omega
      rw [this, MeasureTheory.measure_empty, mul_zero]
    · rw [PMF.toOuterMeasure_pure_apply]
      simp [not_lt.2 h.le]

/-- **`Pr[Bad] ≤ Σⱼ Pr[Bad_j] ≤ Σⱼ Pr[|Y_{ℓ,j}| = thresh]`**
(esa22-final.tex:723-743): Algorithm 2 ends above level `ℓ` only if at some
iteration `j` it is at level `ℓ` and the picked set is full, which by the
domination invariant is at most as likely as `|Y_{ℓ,j}| = thresh`.

PAPER: esa22-final.tex:723-743 -/
theorem relaxed_level_gt_le (thr w : ℕ) (l : List α) (ℓ : ℕ) (hℓ : ℓ ≤ w) :
    (relaxedLoop thr w l init).toOuterMeasure {st | ℓ < st.level} ≤
      ∑ j ∈ Finset.range l.length,
        (levelSample ℓ (l.take (j + 1)).toFinset).toOuterMeasure {T | T.card = thr} := by
  induction l using List.reverseRecOn with
  | nil =>
    simp [relaxedLoop, PMF.toOuterMeasure_pure_apply, init]
  | append_singleton l a ih =>
    have hloop : relaxedLoop thr w (l ++ [a]) init =
        (relaxedLoop thr w l init).bind fun st => relaxedStep thr w st a := by
      rw [relaxedLoop_append]
      congr 1
      funext st
      rw [relaxedLoop_cons]
      exact PMF.bind_pure _
    set P := relaxedLoop thr w l init
    set f : Finset α → ℝ≥0∞ := fun T =>
      (pick w ℓ a (drop a T)).toOuterMeasure {X | X.card = thr}
    -- the new term: leaving level `ℓ` at this iteration
    have hlast : ∑' st : Snapshot α, P st *
        (if st.level = ℓ then f st.sample else 0) ≤
        (levelSample ℓ (l ++ [a]).toFinset).toOuterMeasure {T | T.card = thr} := by
      have hins : (l ++ [a]).toFinset = insert a l.toFinset := by
        ext x; simp
      rw [hins, ← levelSample_bind_pick w ℓ hℓ a, PMF.toOuterMeasure_bind_apply]
      refine le_trans (ENNReal.tsum_le_tsum fun st => ?_)
        (relaxed_domination_tsum thr w l ℓ hℓ f)
      by_cases h : st.level = ℓ
      · rw [if_pos h, if_pos h.le, h, Nat.sub_self, levelSample_zero,
          tsum_eq_single st.sample]
        · simp [PMF.pure_apply, P]
        · intro T hT
          simp [PMF.pure_apply, hT]
      · rw [if_neg h, mul_zero]
        exact bot_le
    rw [hloop, PMF.toOuterMeasure_bind_apply]
    calc _ ≤ ∑' st : Snapshot α, (P st * {st : Snapshot α | ℓ < st.level}.indicator 1 st +
          P st * (if st.level = ℓ then f st.sample else 0)) :=
          ENNReal.tsum_le_tsum fun st => by
            rw [← mul_add]
            exact mul_le_mul' le_rfl (relaxedStep_level_gt_le thr w ℓ st a)
      _ = P.toOuterMeasure {st | ℓ < st.level} +
          ∑' st : Snapshot α, P st * (if st.level = ℓ then f st.sample else 0) := by
          rw [ENNReal.tsum_add, PMF.toOuterMeasure_apply]
          congr 1
          refine tsum_congr fun st => ?_
          by_cases h : ℓ < st.level <;> simp [h]
      _ ≤ (∑ j ∈ Finset.range l.length,
            (levelSample ℓ (l.take (j + 1)).toFinset).toOuterMeasure {T | T.card = thr}) +
          (levelSample ℓ (l ++ [a]).toFinset).toOuterMeasure {T | T.card = thr} :=
          add_le_add ih hlast
      _ = _ := by
          rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
          congr 1
          · refine Finset.sum_congr rfl fun j hj => ?_
            rw [List.take_append_of_le_length (Finset.mem_range.1 hj)]
          · rw [List.take_of_length_le (by simp)]

end Esa22Copy.Analysis
