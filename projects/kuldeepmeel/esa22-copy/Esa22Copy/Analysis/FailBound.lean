import Esa22Copy.Interface.Pseudocode

/-!
# Claim `lm:fail`: Algorithm 1 outputs `⊥` with probability `≤ δ/8`

`Pr[Fail] ≤ Σⱼ Pr[Fail_j] ≤ m · 2^{-thresh} ≤ δ/8` (esa22-final.tex:527-542),
where `Fail_j` is "at iteration `j`, `|𝒳| = thresh` and the throw keeps every
element".  Per the settled repair, `Pr[Fail_j] ≤ 2^{-thresh}` is an inequality
(the paper writes `=`), and the numerics use `thresh ≥ log₂(8m/δ)`.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Esa22Copy.Analysis

open Esa22Copy.Interface.Pseudocode

variable {α : Type} [DecidableEq α] [Fintype α]

/-- INTERNAL: a set `X ⊆ α` has `2^{|α| - |X|}` supersets.
TEXLINE: esa22-final.tex:534 -/
theorem card_supersets (X : Finset α) :
    (Finset.univ.filter (fun S : Finset α => X ⊆ S)).card = 2 ^ (Fintype.card α - X.card) := by
  rw [← Finset.card_compl, ← Finset.card_powerset]
  refine Finset.card_nbij' (fun S => Sᶜ) (fun T => Tᶜ) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hS
    simpa [Finset.compl_subset_compl] using hS
  · intro T hT
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset] at hT
    simpa [Finset.subset_compl_comm] using hT
  · intro S _; simp
  · intro T _; simp

/-- INTERNAL: a uniform subset of `α` (one fair coin per element) contains a given
`X` with probability `2^{-|X|}`: the throw keeps all of `X` with that probability.
TEXLINE: esa22-final.tex:534 -/
theorem prob_superset (X : Finset α) :
    (PMF.uniformOfFintype (Finset α)).toOuterMeasure {S | X ⊆ S} = 2⁻¹ ^ X.card := by
  have hc : Fintype.card {S : Finset α | X ⊆ S} = 2 ^ (Fintype.card α - X.card) := by
    rw [Fintype.card_subtype]; exact card_supersets X
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, hc, Fintype.card_finset]
  have hk : X.card ≤ Fintype.card α := Finset.card_le_univ X
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
  rw [hd, Nat.add_sub_cancel_left, pow_add]
  push_cast
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, ENNReal.inv_pow]


/-- **`Pr[Fail_j] ≤ 2^{-thresh}`** (esa22-final.tex:532-534, as an inequality per
the settled repair): one iteration of Algorithm 1 outputs `⊥` only if `|𝒳| = thresh`
and the throw keeps every element.

PAPER: esa22-final.tex:532-534 -/
theorem step_none_le (thr w : ℕ) (st : Esa22Copy.Interface.Snapshot α) (a : α) :
    step thr w (some st) a none ≤ 2⁻¹ ^ thr := by
  simp only [step, PMF.bind_apply]
  calc _ ≤ ∑' X, pick w st.level a (drop a st.sample) X * 2⁻¹ ^ thr := by
        refine ENNReal.tsum_le_tsum fun X => mul_le_mul' le_rfl ?_
        split_ifs with hX
        · rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply, Esa22Copy.Interface.Pseudocode.throw,
            PMF.toOuterMeasure_map_apply]
          have hcard : X.card = thr := by simpa [full] using hX
          rw [← hcard, ← prob_superset X]
          refine MeasureTheory.measure_mono fun S hS => ?_
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hS
          split_ifs at hS with hY
          · have hYc : (X.filter (· ∈ S)).card = X.card := by
              simpa [full, hcard] using hY
            intro x hx
            exact Finset.filter_card_eq hYc x hx
        · simp [PMF.pure_apply]
    _ = 2⁻¹ ^ thr := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]


/-- INTERNAL: the union bound `Pr[Fail] ≤ Σⱼ Pr[Fail_j] ≤ m · 2^{-thresh}`, by
induction over the loop.
TEXLINE: esa22-final.tex:537-540 -/
theorem loop_none_le (thr w : ℕ) (s : List α) (st : Esa22Copy.Interface.Snapshot α) :
    loop thr w s (some st) none ≤ s.length * 2⁻¹ ^ thr := by
  induction s generalizing st with
  | nil => simp [loop, PMF.pure_apply]
  | cons a s ih =>
    show ((step thr w (some st) a).bind (loop thr w s)) none ≤ _
    rw [PMF.bind_apply]
    set L : ℝ≥0∞ := s.length * 2⁻¹ ^ thr
    have hg : ∀ o, loop thr w s o none ≤ (if o = none then 1 else 0) + L := by
      intro o
      cases o with
      | none => simp only [if_true]; exact le_add_right (PMF.coe_le_one _ _)
      | some y => simpa using ih y
    calc _ ≤ ∑' o, step thr w (some st) a o * ((if o = none then 1 else 0) + L) :=
          ENNReal.tsum_le_tsum fun o => mul_le_mul' le_rfl (hg o)
      _ = step thr w (some st) a none + L := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
            mul_ite, mul_one, mul_zero]
          congr 1
          convert tsum_ite_eq (none : Option (Esa22Copy.Interface.Snapshot α))
            (⇑(step thr w (some st) a)) using 3
      _ ≤ 2⁻¹ ^ thr + L := add_le_add (step_none_le thr w st a) le_rfl
      _ = ((a :: s).length : ℝ≥0∞) * 2⁻¹ ^ thr := by
          simp only [L, List.length_cons]; push_cast; ring

/-- **Claim `lm:fail`** (esa22-final.tex:527-542): `Pr[Fail] ≤ δ/8`, where `Fail`
is "Algorithm 1 outputs `⊥`".

PAPER: esa22-final.tex:527-542 -/
theorem answer_none_le (ε δ : ℝ) (s : List α) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    answer ε δ s none ≤ ENNReal.ofReal (δ / 8) := by
  have hpre : answer ε δ s none =
      loop (thresh ε δ s.length) (s.length + 1) s (some init) none := by
    rw [answer, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      ← PMF.toOuterMeasure_apply_singleton]
    congr 1
    ext o
    cases o <;> simp [report]
  rw [hpre]
  refine (loop_none_le _ _ s init).trans ?_
  set m := s.length
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set thr := thresh ε δ m
  set L := Real.logb 2 (8 * (m : ℝ) / δ)
  have h8 : 1 < 8 * (m : ℝ) / δ := by rw [lt_div_iff₀ hδ0]; nlinarith
  have hL : 0 < L := Real.logb_pos (by norm_num) h8
  have hε2 : 1 ≤ 12 / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hthr : L ≤ (thr : ℝ) :=
    le_trans (le_mul_of_one_le_left hL.le hε2) (Nat.le_ceil _)
  have h2 : 8 * (m : ℝ) / δ ≤ (2 : ℝ) ^ thr := by
    rw [← Real.rpow_natCast]
    calc 8 * (m : ℝ) / δ = (2 : ℝ) ^ L := (Real.rpow_logb (by norm_num) (by norm_num)
            (by linarith)).symm
      _ ≤ (2 : ℝ) ^ (thr : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hthr
  have hreal : (m : ℝ) * (2⁻¹ : ℝ) ^ thr ≤ δ / 8 := by
    have hp : (0 : ℝ) < 2 ^ thr := by positivity
    rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ hp]
    have := (div_le_iff₀ hδ0).mp h2
    linarith
  calc (m : ℝ≥0∞) * 2⁻¹ ^ thr = ENNReal.ofReal ((m : ℝ) * (2⁻¹ : ℝ) ^ thr) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num
    _ ≤ ENNReal.ofReal (δ / 8) := ENNReal.ofReal_le_ofReal hreal

end Esa22Copy.Analysis
