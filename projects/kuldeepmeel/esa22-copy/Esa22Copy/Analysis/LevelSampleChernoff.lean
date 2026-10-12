import Esa22Copy.Analysis.LevelSample
import Arlib.Probability.Chernoff
import Arlib.Probability.BinomialCount

/-!
# Chernoff bounds for level samples

The Chernoff Fact (esa22-final.tex:466-469) for `|Y_{q,j}|`: by Claim `cl:loop`
it is a sum of `|S|` independent Bernoulli(`2⁻q`) indicators, with mean
`μ = |S| · 2⁻q` (eq. `eq:Yellj`, esa22-final.tex:692-697).

The proof transfers arlib's full-independence bounds
`Arlib.Probability.chernoff_upper` and `Arlib.Probability.chernoff_two_sided`
(Arlib/Probability/Chernoff.lean, over `Arlib.prodSpace`) to the law
`levelSample q S`: show that `levelSample q S` is the pushforward of a product of
per-element Bernoulli(`2⁻q`) coins, with `T.card` the success count
(`levelSample_card_event`, through the closed form `levelSample_apply` and
arlib's `Pr_prodSpace_filter_eq_pow`).

The paper states the Fact "for completeness" without proving it and without a
citation; arlib proves it from first principles, so nothing is borrowed.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Esa22Copy.Analysis

open Arlib.Probability

variable {α : Type} [DecidableEq α] [Fintype α]

/-- INTERNAL: one Bernoulli(`r`) coin per element, as arlib's coin law on `Bool`. -/
noncomputable def headMass (r : ℝ) : α → Bool → ℝ := fun _ b => if b then r else 1 - r

omit [DecidableEq α] [Fintype α] in
/-- INTERNAL: the coin law is nonnegative. -/
theorem headMass_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (j : α) (b : Bool) :
    0 ≤ headMass r j b := by
  unfold headMass; split_ifs <;> linarith

omit [DecidableEq α] [Fintype α] in
/-- INTERNAL: the coin law has total mass one. -/
theorem headMass_sum (r : ℝ) (j : α) : ∑ b, headMass r j b = 1 := by
  simp [headMass, Fintype.sum_bool]

/-- INTERNAL: the law of `|levelSample q S|` is that of the number of heads among
the coins of `S` in arlib's product space of Bernoulli(`2^{-q}`) coins.
TEXLINE: esa22-final.tex:688-691 -/
theorem levelSample_card_event (q : ℕ) (S : Finset α) (P : ℕ → Prop) [DecidablePred P] :
    (levelSample q S).toOuterMeasure {T | P T.card} =
      ENNReal.ofReal ((prodSpace (headMass ((2⁻¹ : ℝ) ^ q))
        (headMass_nonneg (by positivity) (pow_le_one₀ (by norm_num) (by norm_num)))
        (headMass_sum _)).toFinProb.Pr
          (Finset.univ.filter fun ω => P (S.filter fun k => ω k = true).card)) := by
  set r : ℝ := (2⁻¹ : ℝ) ^ q with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hp : ((2⁻¹ : ℝ≥0∞) ^ q) = ENNReal.ofReal r := by
    rw [hrdef, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  have hc : levelMiss q = ENNReal.ofReal (1 - r) := by
    have h := levelMiss_add q
    rw [hp] at h
    rw [ENNReal.ofReal_sub _ hr0, ENNReal.ofReal_one, ← h,
      ENNReal.add_sub_cancel_right ENNReal.ofReal_ne_top]
  -- the product-space side, decomposed by the set of heads in `S`
  have hPr : (prodSpace (headMass r)
        (headMass_nonneg hr0 hr1) (headMass_sum _)).toFinProb.Pr
          (Finset.univ.filter fun ω => P (S.filter fun k => ω k = true).card) =
        ∑ T ∈ S.powerset.filter (fun T => P T.card), r ^ T.card * (1 - r) ^ (S.card - T.card) := by
    unfold FinProb.Pr
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun ω : α → Bool => S.filter fun k => ω k = true)
      (t := S.powerset.filter (fun T => P T.card))]
    · refine Finset.sum_congr rfl fun T hT => ?_
      have hTS : T ⊆ S := Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
      have hPT : P T.card := (Finset.mem_filter.1 hT).2
      rw [← Pr_prodSpace_filter_eq_pow (headMass r) (headMass_nonneg hr0 hr1) (headMass_sum r)
        (fun b => b = true) hTS (r := r) (fun j _ => by simp [headMass, Finset.sum_filter, Fintype.sum_bool])]
      unfold FinProb.Pr
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨by rw [h]; exact hPT, h⟩
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      exact Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.filter_subset _ _), hω⟩
  rw [hPr, ENNReal.ofReal_sum_of_nonneg (fun T _ => by
    have : 0 ≤ 1 - r := by linarith
    positivity)]
  rw [PMF.toOuterMeasure_apply, tsum_fintype]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun T : Finset α => T ⊆ S ∧ P T.card)]
  have hzero : ∑ T ∈ Finset.univ.filter (fun T : Finset α => ¬ (T ⊆ S ∧ P T.card)),
      {T : Finset α | P T.card}.indicator (levelSample q S) T = 0 := by
    refine Finset.sum_eq_zero fun T hT => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or] at hT
    rcases hT with h | h
    · by_cases hP : P T.card
      · rw [Set.indicator_of_mem (show T ∈ {T : Finset α | P T.card} from hP), levelSample_apply,
          if_neg h]
      · exact Set.indicator_of_notMem (show T ∉ {T : Finset α | P T.card} from hP) _
    · exact Set.indicator_of_notMem (show T ∉ {T : Finset α | P T.card} from h) _
  rw [hzero, add_zero]
  have hset : Finset.univ.filter (fun T : Finset α => T ⊆ S ∧ P T.card) =
      S.powerset.filter (fun T => P T.card) := by
    ext T; simp
  rw [hset]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hTS : T ⊆ S := Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
  rw [Set.indicator_of_mem (show T ∈ {T : Finset α | P T.card} from (Finset.mem_filter.1 hT).2),
    levelSample_apply, if_pos hTS, hp, hc, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow hr0 T.card, ENNReal.ofReal_pow (show (0 : ℝ) ≤ 1 - r by linarith)]


omit [Fintype α] in
/-- INTERNAL: the mean number of heads among the coins of `S`. -/
theorem indicMean_headMass (r : ℝ) (S : Finset α) :
    indicMean (headMass r) S (fun _ => ({true} : Finset Bool)) = (S.card : ℝ) * r := by
  simp [indicMean, headMass]

omit [Fintype α] in
/-- INTERNAL: the number of heads among the coins of `S`. -/
theorem indicCount_headMass (S : Finset α) (ω : α → Bool) :
    indicCount S (fun _ => ({true} : Finset Bool)) ω = (S.filter fun k => ω k = true).card := by
  simp [indicCount]


/-- **Chernoff Fact, upper tail, for `|Y_{q,j}|`** (esa22-final.tex:466-469):
`Pr[|Y| ≥ (1+t)μ] ≤ exp(-t²μ/(2+t))`, `μ = |S| · 2⁻q`.

PAPER: esa22-final.tex:466-469 -/
theorem levelSample_upper (q : ℕ) (S : Finset α) {t : ℝ} (ht : 0 < t) :
    (levelSample q S).toOuterMeasure
        {T | (1 + t) * ((S.card : ℝ) * (2⁻¹ : ℝ) ^ q) ≤ (T.card : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2 * ((S.card : ℝ) * (2⁻¹ : ℝ) ^ q)) / (2 + t))) := by
  refine (le_of_eq (levelSample_card_event q S
    (fun n : ℕ => (1 + t) * ((S.card : ℝ) * (2⁻¹ : ℝ) ^ q) ≤ (n : ℝ)))).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h := chernoff_upper (headMass ((2⁻¹ : ℝ) ^ q))
    (headMass_nonneg (by positivity) (pow_le_one₀ (by norm_num) (by norm_num)))
    (headMass_sum _) S (fun _ => ({true} : Finset Bool)) ht
  simp only [indicMean_headMass, indicCount_headMass] at h
  exact h


/-- **Chernoff Fact, two-sided, for `|Y_{q,j}|`** (esa22-final.tex:466-469, with
`β = t ≤ 1`, so `2 + β ≤ 3`): `Pr[||Y| - μ| > tμ] ≤ 2 exp(-t²μ/3)`,
`μ = |S| · 2⁻q`.

PAPER: esa22-final.tex:466-469 -/
theorem levelSample_two_sided (q : ℕ) (S : Finset α) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (levelSample q S).toOuterMeasure
        {T | t * ((S.card : ℝ) * (2⁻¹ : ℝ) ^ q) <
          |(T.card : ℝ) - (S.card : ℝ) * (2⁻¹ : ℝ) ^ q|} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2 * ((S.card : ℝ) * (2⁻¹ : ℝ) ^ q)) / 3)) := by
  refine (le_of_eq (levelSample_card_event q S
    (fun n : ℕ => t * ((S.card : ℝ) * (2⁻¹ : ℝ) ^ q) <
      |(n : ℝ) - (S.card : ℝ) * (2⁻¹ : ℝ) ^ q|))).trans (ENNReal.ofReal_le_ofReal ?_)
  have h := chernoff_two_sided (headMass ((2⁻¹ : ℝ) ^ q))
    (headMass_nonneg (by positivity) (pow_le_one₀ (by norm_num) (by norm_num)))
    (headMass_sum _) S (fun _ => ({true} : Finset Bool)) ht0 ht1
  simp only [indicMean_headMass, indicCount_headMass] at h
  exact h


end Esa22Copy.Analysis
