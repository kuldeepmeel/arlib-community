import Esa22Copy.Analysis.RelaxedLevelBounds
import Esa22Copy.Analysis.LevelSampleChernoff
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Claim `lm:error-fail`: the relaxed Algorithm 2 errs with probability `≤ δ/2`

The probability that Algorithm 2 (`relaxedAnswer`, the paper's `algo:bfinal`)
outputs a number outside `[(1-ε)F0, (1+ε)F0]` is at most `δ/2`
(esa22-final.tex:701-781).

The paper's proof goes through Algorithm 3 (`algo:cfinal`), Claim `cl:loop`
(each element of `S_i` is in `Y_k` independently with probability `2⁻ᵏ`), the
coupling `(p_j, X_j) = (p_j, Y_{k,j})` (esa22-final.tex:684), the mean bound
`E|Y_{k,j}| = 2⁻ᵏ|S_j|` (eq. `eq:Yellj`), and the Chernoff Fact
(esa22-final.tex:466-469), split into `Pr[Bad₂] ≤ δ/4` and
`Pr[Error₂ ∩ ¬Bad₂] ≤ δ/4`.  Settled repairs that apply here:

* `log` is `log₂` throughout, including the `log e` of the final chain;
* at esa22-final.tex:737 the mean bound is `E|Y_{ℓ,j}| = 2⁻ˡF0 < thresh/2`, not
  `≤ thresh/4`; the `Bad₂` tail must be re-derived from that;
* the case `F0 < thresh/4` (where the paper's `ℓ` is undefined or negative)
  needs no separate lemma: it is the case `ℓ = 0` below, where `Bad₂` is bounded
  like any other and the level-`0` error is impossible (`Y_0 = S_m`);
* `Pr[Error_{2,q}] ≤ Pr[|Y_{q,m}| ∉ …]` needs the coupling *derived* from the
  construction, not asserted: it comes from `relaxed_domination`
  (`RelaxedDomination.lean`), stated over Algorithm 2 alone.

Route taken.  `ℓ` is the least level with `4F0 < 2^{ℓ+1}·thresh` (so
`2^{-ℓ}F0 < thresh/2`, the settled repair of esa22-final.tex:737, and, when
`ℓ > 0`, `2^{-ℓ}F0 ≥ thresh/4`); this also covers the degenerate case
`F0 < thresh/4`, where `ℓ = 0`.  The error event is contained in
`{level > ℓ} ∪ ⋃_{q ≤ ℓ} {level = q ∧ ||𝒳| - 2^{-q}F0| > ε 2^{-q}F0}`.  The first
part is bounded by `relaxed_level_gt_le` and the upper Chernoff tail with mean
`< thresh/2` (exponent `thresh/6`); each `q`-part by `relaxed_level_eq_le` and
the two-sided Chernoff tail, where `q = 0` contributes nothing (`Y_0 = S_m`
exactly).  Numerics in base 2: `exp(-log₂(8m/δ)) ≤ δ/(16m)`.  The result is
`Pr[Bad₂] ≤ δ/16` and `Pr[Error₂ ∩ ¬Bad₂] ≤ δ/4`.

It uses `relaxed_level_eq_le`, `relaxed_level_gt_le` (`RelaxedLevelBounds.lean`,
from `relaxed_domination`) and `levelSample_upper`, `levelSample_two_sided`
(`LevelSampleChernoff.lean`, from arlib's Chernoff bounds).
-/

set_option autoImplicit false

open scoped ENNReal

namespace Esa22Copy.Analysis

open Esa22Copy.Interface (Snapshot)
open Esa22Copy.Interface.Pseudocode

variable {α : Type} [DecidableEq α] [Fintype α]

/-- INTERNAL: the numeric heart of the final chain of Claim `lm:error-fail`, with
`log = log₂` (esa22-final.tex:327): `e^{-log₂(8m/δ)} ≤ δ/(16m)`.  This is where
the paper's `(δ/8)^{log e}` (esa22-final.tex:764) is used, with room to spare.
TEXLINE: esa22-final.tex:762-765 -/
theorem exp_neg_logb_le (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Real.exp (-Real.logb 2 (8 * (m : ℝ) / δ)) ≤ δ / (16 * m) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set z := 8 * (m : ℝ) / δ with hz
  have hz8 : 8 ≤ z := by rw [hz, le_div_iff₀ hδ0]; nlinarith
  have hzpos : 0 < z := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hlz : 3 * Real.log 2 ≤ Real.log z := by
    have : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    rw [← this]; exact Real.log_le_log (by norm_num) hz8
  have htarget : δ / (16 * m) = Real.exp (-Real.log (2 * z)) := by
    rw [Real.exp_neg, Real.exp_log (by positivity), hz]
    field_simp
    ring
  rw [htarget, Real.exp_le_exp, Real.log_mul (by norm_num) hzpos.ne', Real.logb,
    neg_le_neg_iff, le_div_iff₀ hl2]
  nlinarith

/-- **`Pr[|Y_{ℓ,j}| = thresh] ≤ e^{-thresh/6}` when `E|Y_{ℓ,j}| < thresh/2`**
(esa22-final.tex:737-741, with the settled repair: the mean is only bounded by
`thresh/2`, and the exponent is re-derived from the upper Chernoff tail).

PAPER: esa22-final.tex:737-741 -/
theorem levelSample_card_eq_le (ℓ thr : ℕ) (S : Finset α) (hthr : 1 ≤ thr)
    (hμ : 2 * ((S.card : ℝ) * (2⁻¹ : ℝ) ^ ℓ) < thr) :
    (levelSample ℓ S).toOuterMeasure {T | T.card = thr} ≤
      ENNReal.ofReal (Real.exp (-(thr : ℝ) / 6)) := by
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · have hz : (levelSample ℓ S).toOuterMeasure {T | T.card = thr} = 0 := by
      rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
      intro T hT hc
      have := Finset.card_le_card (levelSample_subset ℓ S T hT)
      simp only [Set.mem_setOf_eq] at hc
      omega
    rw [hz]; exact bot_le
  set μ := (S.card : ℝ) * (2⁻¹ : ℝ) ^ ℓ with hμdef
  have hμpos : 0 < μ := by
    have : (0 : ℝ) < S.card := by exact_mod_cast hpos
    positivity
  have hthr' : (0 : ℝ) < thr := by exact_mod_cast hthr
  set t := (thr : ℝ) / μ - 1 with htdef
  have htμ : t * μ = thr - μ := by rw [htdef, sub_mul, div_mul_cancel₀ _ hμpos.ne', one_mul]
  have ht : 0 < t := by
    have : 2 < (thr : ℝ) / μ := by rw [lt_div_iff₀ hμpos]; linarith
    linarith
  have hsub : {T : Finset α | T.card = thr} ⊆ {T | (1 + t) * μ ≤ (T.card : ℝ)} := by
    intro T hT
    simp only [Set.mem_setOf_eq] at hT ⊢
    rw [hT]
    linarith
  refine (MeasureTheory.measure_mono hsub).trans ((levelSample_upper ℓ S ht).trans ?_)
  apply ENNReal.ofReal_le_ofReal
  rw [Real.exp_le_exp, neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by norm_num)
    (by linarith)]
  have key : (thr : ℝ) * (2 + t) * μ ≤ t ^ 2 * μ * 6 * μ := by
    have e1 : t ^ 2 * μ * 6 * μ = 6 * (t * μ) ^ 2 := by ring
    have e2 : (thr : ℝ) * (2 + t) * μ = thr * (2 * μ + t * μ) := by ring
    rw [e1, e2, htμ]
    nlinarith
  exact le_of_mul_le_mul_right key hμpos

/-- **`Pr[|Y_{q,m}| ∉ [(1-ε)μ, (1+ε)μ]] ≤ 2e^{-ε²c/3}`** for any lower bound `c` on
the mean `μ = |S|·2^{-q}` (esa22-final.tex:758-762, Chernoff with `β = ε`).

PAPER: esa22-final.tex:758-762 -/
theorem levelSample_dev_le (q : ℕ) (S : Finset α) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {c : ℝ} (hc : c ≤ (S.card : ℝ) * (2⁻¹ : ℝ) ^ q) :
    (levelSample q S).toOuterMeasure
        {T | ε * ((S.card : ℝ) * (2⁻¹ : ℝ) ^ q) <
          |(T.card : ℝ) - (S.card : ℝ) * (2⁻¹ : ℝ) ^ q|} ≤
      ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 * c) / 3)) := by
  refine (levelSample_two_sided q S hε0 hε1.le).trans (ENNReal.ofReal_le_ofReal ?_)
  have : ε ^ 2 * c ≤ ε ^ 2 * ((S.card : ℝ) * (2⁻¹ : ℝ) ^ q) :=
    mul_le_mul_of_nonneg_left hc (sq_nonneg ε)
  gcongr

/-- **Claim `lm:error-fail`** (esa22-final.tex:701-781): `Pr[Error₂] ≤ δ/2`, where
`Error₂` is "Algorithm 2 does not output a value in `[(1-ε)F0, (1+ε)F0]`".

PAPER: esa22-final.tex:701-781 -/
theorem relaxedAnswer_error_le (ε δ : ℝ) (s : List α) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (relaxedAnswer ε δ s).toOuterMeasure {c | ¬ Accurate ε (F0 s) (some c)} ≤
      ENNReal.ofReal (δ / 2) := by
  set m := s.length with hmdef
  set F := F0 s with hFdef
  set thr := thresh ε δ m with hthrdef
  -- `m = 0`: the empty stream, answered exactly
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · have hs : s = [] := List.eq_nil_of_length_eq_zero hm0
    subst hs
    have hF : F = 0 := rfl
    simp [relaxedAnswer, relaxedLoop, PMF.toOuterMeasure_pure_apply, init, Accurate, hF]
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  -- the threshold
  set L := Real.logb 2 (8 * (m : ℝ) / δ) with hLdef
  have hL3 : 3 ≤ L := by
    have h8 : (8 : ℝ) ≤ 8 * (m : ℝ) / δ := by rw [le_div_iff₀ hδ0]; nlinarith
    have : Real.logb 2 8 = 3 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow]; simp
    rw [hLdef, ← this]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) h8
  have hε2 : 0 < ε ^ 2 := by positivity
  have hε2' : ε ^ 2 < 1 := by nlinarith
  have hthrL : 12 / ε ^ 2 * L ≤ thr := Nat.le_ceil _
  have hthrL' : L ≤ ε ^ 2 * thr / 12 := by
    rw [le_div_iff₀ (by norm_num)]
    have := mul_le_mul_of_nonneg_left hthrL hε2.le
    rw [← mul_assoc, mul_div_cancel₀ _ hε2.ne'] at this
    linarith
  have hthr12 : 12 * L ≤ thr := by
    have : 12 * L ≤ 12 / ε ^ 2 * L := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      rw [le_div_iff₀ hε2]; nlinarith
    linarith
  have hthr1 : 1 ≤ thr := by
    have : (1 : ℝ) ≤ thr := by linarith
    exact_mod_cast this
  set x := δ / (16 * m) with hxdef
  have hx : Real.exp (-L) ≤ x := exp_neg_logb_le m hm δ hδ0 hδ1
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 16 := by
    rw [hxdef, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  -- the cut-off level `ℓ`
  have hex : ∃ ℓ : ℕ, 4 * F < 2 ^ (ℓ + 1) * thr :=
    ⟨4 * F, lt_of_lt_of_le (Nat.lt_two_pow_self) (by
      calc 2 ^ (4 * F) ≤ 2 ^ (4 * F + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ (4 * F + 1) * 1 := (mul_one _).symm
        _ ≤ 2 ^ (4 * F + 1) * thr := Nat.mul_le_mul_left _ hthr1)⟩
  classical
  set ℓ := Nat.find hex with hℓdef
  have hℓ1 : 4 * F < 2 ^ (ℓ + 1) * thr := Nat.find_spec hex
  have hℓ2 : 0 < ℓ → 2 ^ ℓ * thr ≤ 4 * F := by
    intro hpos
    have := Nat.find_min hex (show ℓ - 1 < ℓ by omega)
    rw [Nat.sub_add_cancel hpos] at this
    omega
  have hFm : F ≤ m := List.toFinset_card_le s
  have hℓw : ℓ ≤ m + 1 := by
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · omega
    · have h1 := hℓ2 h
      have h2 : 2 ^ ℓ ≤ 4 * m := le_trans (Nat.le_mul_of_pos_right _ hthr1) (by omega)
      have h3 : 4 * m < 2 ^ (m + 2) := by
        have := Nat.lt_two_pow_self (n := m)
        rw [pow_add]; omega
      by_contra hc
      have : 2 ^ (m + 2) ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have hFr : (s.toFinset.card : ℝ) = F := rfl
  -- the error event, split by the final level
  set P := relaxedLoop thr (m + 1) s init with hPdef
  set E : ℕ → Set (Finset α) := fun q => {T | ε * ((s.toFinset.card : ℝ) * (2⁻¹ : ℝ) ^ q) <
    |(T.card : ℝ) - (s.toFinset.card : ℝ) * (2⁻¹ : ℝ) ^ q|} with hEdef
  have hsub : (fun st : Snapshot α => st.sample.card * 2 ^ st.level) ⁻¹'
        {c | ¬ Accurate ε F (some c)} ⊆
      {st | ℓ < st.level} ∪ ⋃ q ∈ Finset.range (ℓ + 1), {st | st.level = q ∧ st.sample ∈ E q} := by
    intro st hst
    by_cases hl : ℓ < st.level
    · exact Or.inl hl
    refine Or.inr (Set.mem_biUnion (x := st.level) (by simp; omega) ⟨rfl, ?_⟩)
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Accurate, not_and_or, not_le] at hst
    show ε * _ < |_ - _|
    rw [hFr]
    have hp : (0 : ℝ) < (2⁻¹ : ℝ) ^ st.level := by positivity
    have h2p : (2 : ℝ) ^ st.level * (2⁻¹ : ℝ) ^ st.level = 1 := by
      rw [← mul_pow]; norm_num
    have hc : (st.sample.card : ℝ) = ((st.sample.card * 2 ^ st.level : ℕ) : ℝ) *
        (2⁻¹ : ℝ) ^ st.level := by
      push_cast; rw [mul_assoc, h2p, mul_one]
    rcases hst with h | h
    · have := mul_lt_mul_of_pos_right h hp
      rw [← hc] at this
      rw [lt_abs]; right; nlinarith
    · have := mul_lt_mul_of_pos_right h hp
      rw [← hc] at this
      rw [lt_abs]; left; nlinarith
  -- `Pr[Bad₂] ≤ δ/16`
  have hbad : P.toOuterMeasure {st | ℓ < st.level} ≤ ENNReal.ofReal (δ / 16) := by
    refine (relaxed_level_gt_le thr (m + 1) s ℓ hℓw).trans ?_
    have hterm : ∀ j ∈ Finset.range m,
        (levelSample ℓ (s.take (j + 1)).toFinset).toOuterMeasure {T | T.card = thr} ≤
          ENNReal.ofReal x := by
      intro j _
      refine (levelSample_card_eq_le ℓ thr _ hthr1 ?_).trans (ENNReal.ofReal_le_ofReal ?_)
      · have hSj : ((s.take (j + 1)).toFinset.card : ℝ) ≤ F := by
          exact_mod_cast Finset.card_le_card fun y hy =>
            List.mem_toFinset.2 ((List.take_sublist _ _).subset (List.mem_toFinset.1 hy))
        have hℓ1' : (2 : ℝ) * F < 2 ^ ℓ * thr := by
          have : ((4 * F : ℕ) : ℝ) < ((2 ^ (ℓ + 1) * thr : ℕ) : ℝ) := by exact_mod_cast hℓ1
          push_cast at this
          rw [pow_succ] at this
          linarith
        have hp : (0 : ℝ) < (2⁻¹ : ℝ) ^ ℓ := by positivity
        have h2p : (2 : ℝ) ^ ℓ * (2⁻¹ : ℝ) ^ ℓ = 1 := by rw [← mul_pow]; norm_num
        calc 2 * (((s.take (j + 1)).toFinset.card : ℝ) * (2⁻¹ : ℝ) ^ ℓ)
            ≤ 2 * F * (2⁻¹ : ℝ) ^ ℓ := by nlinarith
          _ < 2 ^ ℓ * thr * (2⁻¹ : ℝ) ^ ℓ := mul_lt_mul_of_pos_right hℓ1' hp
          _ = thr := by rw [mul_comm ((2 : ℝ) ^ ℓ), mul_assoc, h2p, mul_one]
      · calc Real.exp (-(thr : ℝ) / 6) ≤ Real.exp (-L) :=
              Real.exp_le_exp.2 (by rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by norm_num)]; linarith)
          _ ≤ x := hx
    calc _ ≤ ∑ j ∈ Finset.range m, ENNReal.ofReal x := Finset.sum_le_sum hterm
      _ = ENNReal.ofReal (δ / 16) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hxdef]
          field_simp
  -- `Pr[Error₂ ∩ ¬Bad₂] ≤ δ/4`
  have herr : P.toOuterMeasure
      (⋃ q ∈ Finset.range (ℓ + 1), {st | st.level = q ∧ st.sample ∈ E q}) ≤
        ENNReal.ofReal (δ / 4) := by
    refine (MeasureTheory.measure_biUnion_finset_le _ _).trans ?_
    have hterm : ∀ q ∈ Finset.range (ℓ + 1),
        P.toOuterMeasure {st | st.level = q ∧ st.sample ∈ E q} ≤
          ENNReal.ofReal (2 * x * (1 / 2) ^ (ℓ - q)) := by
      intro q hq
      have hqℓ : q ≤ ℓ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
      refine (relaxed_level_eq_le thr (m + 1) s q (hqℓ.trans hℓw) (E q)).trans ?_
      rcases Nat.eq_zero_or_pos q with hq0 | hqpos
      · subst hq0
        rw [levelSample_zero, PMF.toOuterMeasure_pure_apply, if_neg]
        · exact bot_le
        · simp only [hEdef, Set.mem_setOf_eq, pow_zero, mul_one, sub_self, abs_zero, not_lt]
          positivity
      · have h4 := hℓ2 (lt_of_lt_of_le hqpos hqℓ)
        have hi : (2 : ℝ) ^ (ℓ - q) * 2 ^ q = 2 ^ ℓ := by
          rw [← pow_add, Nat.sub_add_cancel hqℓ]
        have h2q : (2 : ℝ) ^ q * (2⁻¹ : ℝ) ^ q = 1 := by rw [← mul_pow]; norm_num
        refine (levelSample_dev_le q s.toFinset hε0 hε1
          (c := 2 ^ (ℓ - q) * thr / 4) ?_).trans (ENNReal.ofReal_le_ofReal ?_)
        · rw [hFr]
          have h4' : (2 : ℝ) ^ ℓ * thr ≤ 4 * F := by exact_mod_cast h4
          have hp : (0 : ℝ) < (2⁻¹ : ℝ) ^ q := by positivity
          calc (2 : ℝ) ^ (ℓ - q) * thr / 4
              = (2 ^ (ℓ - q) * 2 ^ q) * thr / 4 * (2⁻¹ : ℝ) ^ q := by
                rw [show ((2 : ℝ) ^ (ℓ - q) * 2 ^ q) * thr / 4 * (2⁻¹ : ℝ) ^ q =
                  2 ^ (ℓ - q) * thr / 4 * (2 ^ q * (2⁻¹ : ℝ) ^ q) by ring, h2q, mul_one]
            _ = (2 ^ ℓ * thr) / 4 * (2⁻¹ : ℝ) ^ q := by rw [hi]
            _ ≤ (4 * F) / 4 * (2⁻¹ : ℝ) ^ q := by gcongr
            _ = F * (2⁻¹ : ℝ) ^ q := by ring
        · set i := ℓ - q
          have hexp : Real.exp (-(ε ^ 2 * (2 ^ i * thr / 4)) / 3) ≤ Real.exp (-L) ^ (2 ^ i) := by
            rw [← Real.exp_nat_mul, Real.exp_le_exp]
            push_cast
            have : (0 : ℝ) < 2 ^ i := by positivity
            nlinarith
          have hxi : x ^ (2 ^ i) ≤ x * (1 / 2) ^ i := by
            have hi' : i ≤ 2 ^ i - 1 := by have := Nat.lt_two_pow_self (n := i); omega
            calc x ^ (2 ^ i) = x * x ^ (2 ^ i - 1) := by
                  rw [← pow_succ']; congr 1; have := Nat.one_le_two_pow (n := i); omega
              _ ≤ x * (1 / 2) ^ (2 ^ i - 1) := by
                  gcongr; linarith
              _ ≤ x * (1 / 2) ^ i :=
                  mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hi')
                    hx0.le
          calc 2 * Real.exp (-(ε ^ 2 * (2 ^ i * thr / 4)) / 3)
              ≤ 2 * Real.exp (-L) ^ (2 ^ i) := by gcongr
            _ ≤ 2 * x ^ (2 ^ i) := by gcongr
            _ ≤ 2 * (x * (1 / 2) ^ i) := by gcongr
            _ = 2 * x * (1 / 2) ^ i := by ring
    calc _ ≤ ∑ q ∈ Finset.range (ℓ + 1), ENNReal.ofReal (2 * x * (1 / 2) ^ (ℓ - q)) :=
          Finset.sum_le_sum hterm
      _ = ENNReal.ofReal (∑ q ∈ Finset.range (ℓ + 1), 2 * x * (1 / 2) ^ (ℓ - q)) :=
          (ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity).symm
      _ ≤ ENNReal.ofReal (δ / 4) := by
          apply ENNReal.ofReal_le_ofReal
          have hrefl : ∑ q ∈ Finset.range (ℓ + 1), 2 * x * (1 / 2 : ℝ) ^ (ℓ - q) =
              ∑ q ∈ Finset.range (ℓ + 1), 2 * x * (1 / 2 : ℝ) ^ q := by
            rw [← Finset.sum_range_reflect]
            refine Finset.sum_congr rfl fun q hq => ?_
            congr 2
            have := Finset.mem_range.1 hq
            omega
          rw [hrefl, ← Finset.mul_sum]
          have hg := sum_geometric_two_le (ℓ + 1)
          have : 2 * x * 2 ≤ δ / 4 := by
            have : 2 * x * 2 = δ / (4 * m) := by rw [hxdef]; field_simp; ring
            rw [this]
            exact div_le_div_of_nonneg_left hδ0.le (by norm_num) (by linarith)
          nlinarith
  rw [relaxedAnswer, PMF.toOuterMeasure_map_apply]
  refine (MeasureTheory.measure_mono hsub).trans ((MeasureTheory.measure_union_le _ _).trans ?_)
  calc _ ≤ ENNReal.ofReal (δ / 16) + ENNReal.ofReal (δ / 4) := add_le_add hbad herr
    _ = ENNReal.ofReal (δ / 16 + δ / 4) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (δ / 2) := ENNReal.ofReal_le_ofReal (by linarith)

end Esa22Copy.Analysis
