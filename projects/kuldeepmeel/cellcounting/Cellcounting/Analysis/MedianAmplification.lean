import Cellcounting.Interface.Pseudocode

/-!
# Median amplification

`R = 10 s + 1` independent runs of a law that lands in `[lo, hi]` with
probability at least `3/4`; their median (order statistic at `5 s`) lands in
`[lo, hi]` with probability at least `1 - 2^{-s}` (`algorithm.tex:670-690`).

The proof follows the paper.  Let `F` be the number of runs outside `[lo, hi]`.
A median outside `[lo, hi]` forces `F ≥ 5 s + 1`
(`median_countP_of_orderStat_not_mem`).  Independence gives
`E 2^F ≤ (5/4)^R` (`median_four_pow_mul_moment_le`), and Markov's inequality
then bounds the bad event by `(5/4)^R / 2^{5s+1} ≤ 2^{-s}`.
-/

namespace Cellcounting.Analysis

open Cellcounting.Pseudocode

/-- INTERNAL: one more run appends one fresh draw.
TEXLINE: sections/algorithm.tex:670-690 -/
theorem median_repeatRuns_succ (R : ℕ) (μ : PMF ℚ) :
    repeatRuns (R + 1) μ = (repeatRuns R μ).bind (fun l => μ.map fun z => l ++ [z]) := by
  simp only [repeatRuns, loop, List.range_succ, List.foldlM_append, List.foldlM_cons,
    List.foldlM_nil]
  simp [bind_pure]
  rfl

/-- INTERNAL: every list in the support of `repeatRuns R μ` has length `R`. -/
theorem median_length_of_mem_support (R : ℕ) (μ : PMF ℚ) :
    ∀ l ∈ (repeatRuns R μ).support, l.length = R := by
  induction R with
  | zero =>
    intro l hl
    simp only [repeatRuns, loop, List.range_zero, List.foldlM_nil] at hl
    change PMF.pure [] l ≠ 0 at hl
    by_contra h
    exact hl (by simp [PMF.pure_apply]; rintro rfl; exact h rfl)
  | succ R ih =>
    intro l hl
    rw [median_repeatRuns_succ, PMF.mem_support_bind_iff] at hl
    obtain ⟨a, ha, hl⟩ := hl
    rw [PMF.support_map] at hl
    obtain ⟨z, -, rfl⟩ := hl
    simp [ih a ha]

/-- INTERNAL: expectation of a nonnegative function under `PMF.bind`. -/
theorem median_tsum_bind_mul {α β : Type} (p : PMF α) (g : α → PMF β) (f : β → ENNReal) :
    ∑' b, p.bind g b * f b = ∑' a, p a * ∑' b, g a b * f b := by
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  congr 1; ext a
  rw [← ENNReal.tsum_mul_left]
  congr 1; ext b
  ring

/-- INTERNAL: expectation of a nonnegative function under `PMF.map`. -/
theorem median_tsum_map_mul {α β : Type} (p : PMF α) (h : α → β) (f : β → ENNReal) :
    ∑' b, p.map h b * f b = ∑' a, p a * f (h a) := by
  rw [show p.map h = p.bind (PMF.pure ∘ h) from rfl, median_tsum_bind_mul]
  congr 1; ext a; congr 1
  simp [PMF.pure_apply]

/-- INTERNAL: a set and its complement carry total mass one. -/
theorem median_outer_add_compl {α : Type} (p : PMF α) (s : Set α) :
    p.toOuterMeasure s + p.toOuterMeasure sᶜ = 1 := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  simp_rw [Set.indicator_self_add_compl_apply]
  exact p.tsum_coe

/-- INTERNAL: Markov's inequality for a `PMF`, with the lower bound needed only
on the support. -/
theorem median_markov {α : Type} (p : PMF α) (S : Set α) (f : α → ENNReal) (c : ENNReal)
    (h : ∀ x ∈ p.support, x ∈ S → c ≤ f x) :
    c * p.toOuterMeasure S ≤ ∑' x, p x * f x := by
  rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hS : x ∈ S
  · rw [Set.indicator_of_mem hS]
    by_cases hx : p x = 0
    · simp [hx]
    · rw [mul_comm]
      have := h x ((PMF.mem_support_iff p x).2 hx) hS
      gcongr
  · simp [Set.indicator_of_notMem hS]

/-- INTERNAL: a bad median at position `5 s` of `10 s + 1` values needs at least
`5 s + 1` values outside `[lo, hi]` ("a bad median requires at least half the runs
to fail").
TEXLINE: sections/algorithm.tex:680-686 -/
theorem median_countP_of_orderStat_not_mem (l : List ℚ) (lo hi : ℚ) (s : ℕ)
    (hl : l.length = 10 * s + 1)
    (hbad : ¬ (lo ≤ orderStat l (5 * s) ∧ orderStat l (5 * s) ≤ hi)) :
    5 * s + 1 ≤ l.countP (fun z => decide ¬ (lo ≤ z ∧ z ≤ hi)) := by
  set L := (l : Multiset ℚ).sort with hL
  have hperm : L.Perm l := by
    have := Multiset.sort_eq (l : Multiset ℚ) (fun a b => a ≤ b)
    exact Quotient.exact this
  have hlen : L.length = 10 * s + 1 := by rw [hperm.length_eq, hl]
  have hsorted : ∀ i j (hi : i < L.length) (hj : j < L.length), i ≤ j → L[i] ≤ L[j] := by
    intro i j hi hj hij
    rcases hij.lt_or_eq with h | h
    · exact List.pairwise_iff_getElem.1 (Multiset.pairwise_sort _ _) i j hi hj h
    · subst h; exact le_rfl
  have hmid : 5 * s < L.length := by omega
  have hos : orderStat l (5 * s) = L[5 * s] := by
    show L.getD (5 * s) 0 = L[5 * s]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmid, Option.getD_some]
  rw [← hperm.countP_eq]
  rw [hos] at hbad
  rw [not_and_or, not_le, not_le] at hbad
  rcases hbad with h | h
  · calc 5 * s + 1 = (L.take (5 * s + 1)).length := by simp; omega
      _ = (L.take (5 * s + 1)).countP (fun z => decide ¬ (lo ≤ z ∧ z ≤ hi)) := by
          rw [eq_comm, List.countP_eq_length]
          intro x hx
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
          simp only [List.getElem_take, List.length_take] at hi ⊢
          have := hsorted i (5 * s) (by omega) hmid (by omega)
          simp only [decide_eq_true_eq]
          intro h'; linarith [h'.1]
      _ ≤ _ := (List.take_sublist _ _).countP_le
  · calc 5 * s + 1 = (L.drop (5 * s)).length := by simp; omega
      _ = (L.drop (5 * s)).countP (fun z => decide ¬ (lo ≤ z ∧ z ≤ hi)) := by
          rw [eq_comm, List.countP_eq_length]
          intro x hx
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
          simp only [List.getElem_drop, List.length_drop] at hi ⊢
          have := hsorted (5 * s) (5 * s + i) hmid (by omega) (by omega)
          simp only [decide_eq_true_eq]
          intro h'; linarith [h'.2]
      _ ≤ _ := (List.drop_sublist _ _).countP_le

/-- INTERNAL: one run contributes a factor `E 2^{[run fails]} = 1 + P(fail) ≤ 5/4`.
TEXLINE: sections/algorithm.tex:676-679 -/
theorem median_four_mul_step_le (μ : PMF ℚ) (lo hi : ℚ)
    (hμ : (3 / 4 : ENNReal) ≤ μ.toOuterMeasure {z | lo ≤ z ∧ z ≤ hi}) :
    4 * ∑' z, μ z * (2 : ENNReal) ^ ([z].countP (fun z => decide ¬ (lo ≤ z ∧ z ≤ hi))) ≤ 5 := by
  set A := ∑' z, μ z * (2 : ENNReal) ^ ([z].countP (fun z => decide ¬ (lo ≤ z ∧ z ≤ hi)))
  have hsum : A + μ.toOuterMeasure {z | lo ≤ z ∧ z ≤ hi} = 2 := by
    rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
    have : ∀ z, μ z * (2 : ENNReal) ^ ([z].countP (fun z => decide ¬ (lo ≤ z ∧ z ≤ hi))) +
        {z | lo ≤ z ∧ z ≤ hi}.indicator μ z = μ z * 2 := by
      intro z
      by_cases hz : lo ≤ z ∧ z ≤ hi
      · rw [Set.indicator_of_mem (show z ∈ {z | lo ≤ z ∧ z ≤ hi} from hz)]
        simp [hz]; ring
      · rw [Set.indicator_of_notMem (show z ∉ {z | lo ≤ z ∧ z ≤ hi} from hz)]
        simp [hz]
    simp_rw [this]
    rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]
  have h3 : 3 ≤ 4 * μ.toOuterMeasure {z | lo ≤ z ∧ z ≤ hi} := by
    have : 4 * (3 / 4 : ENNReal) ≤ 4 * μ.toOuterMeasure {z | lo ≤ z ∧ z ≤ hi} := by gcongr
    rwa [ENNReal.mul_div_cancel (by norm_num) (by norm_num)] at this
  have h8 : 4 * A + 3 ≤ 5 + 3 := by
    calc 4 * A + 3 ≤ 4 * A + 4 * μ.toOuterMeasure {z | lo ≤ z ∧ z ≤ hi} := by gcongr
      _ = 4 * 2 := by rw [← mul_add, hsum]
      _ = 5 + 3 := by norm_num
  exact (ENNReal.add_le_add_iff_right (by norm_num)).1 h8

/-- INTERNAL: independence gives `4^R E 2^F ≤ 5^R`, i.e. `E 2^F ≤ (5/4)^R`.
TEXLINE: sections/algorithm.tex:676-679 -/
theorem median_four_pow_mul_moment_le (μ : PMF ℚ) (lo hi : ℚ)
    (hμ : (3 / 4 : ENNReal) ≤ μ.toOuterMeasure {z | lo ≤ z ∧ z ≤ hi}) (R : ℕ) :
    4 ^ R * ∑' l, repeatRuns R μ l *
      (2 : ENNReal) ^ (l.countP (fun z => decide ¬ (lo ≤ z ∧ z ≤ hi))) ≤ 5 ^ R := by
  induction R with
  | zero =>
    simp only [repeatRuns, loop, List.range_zero, List.foldlM_nil]
    change 4 ^ 0 * ∑' l, PMF.pure [] l * _ ≤ _
    simp [PMF.pure_apply]
  | succ R ih =>
    rw [median_repeatRuns_succ, median_tsum_bind_mul]
    simp_rw [median_tsum_map_mul, List.countP_append, pow_add]
    have key : ∀ a : List ℚ, ∑' z, μ z *
        ((2 : ENNReal) ^ (a.countP (fun z => decide ¬ (lo ≤ z ∧ z ≤ hi))) *
          (2 : ENNReal) ^ ([z].countP (fun z => decide ¬ (lo ≤ z ∧ z ≤ hi)))) =
        (2 : ENNReal) ^ (a.countP (fun z => decide ¬ (lo ≤ z ∧ z ≤ hi))) *
          ∑' z, μ z * (2 : ENNReal) ^ ([z].countP (fun z => decide ¬ (lo ≤ z ∧ z ≤ hi))) := by
      intro a
      simp_rw [mul_left_comm (μ _)]
      exact ENNReal.tsum_mul_left
    simp_rw [key, ← mul_assoc, ENNReal.tsum_mul_right]
    calc 4 ^ R * 4 ^ 1 * ((∑' a, repeatRuns R μ a *
            (2 : ENNReal) ^ (a.countP (fun z => decide ¬ (lo ≤ z ∧ z ≤ hi)))) *
            ∑' z, μ z * (2 : ENNReal) ^ ([z].countP (fun z => decide ¬ (lo ≤ z ∧ z ≤ hi))))
          = (4 ^ R * ∑' a, repeatRuns R μ a *
            (2 : ENNReal) ^ (a.countP (fun z => decide ¬ (lo ≤ z ∧ z ≤ hi)))) *
            (4 * ∑' z, μ z *
              (2 : ENNReal) ^ ([z].countP (fun z => decide ¬ (lo ≤ z ∧ z ≤ hi)))) := by ring
      _ ≤ 5 ^ R * 5 := by gcongr; exact median_four_mul_step_le μ lo hi hμ
      _ = 5 ^ R * 5 ^ 1 := by ring

/-- **Median amplification.**
PAPER: sections/algorithm.tex:670-690 -/
theorem median_amplification (μ : PMF ℚ) (lo hi : ℚ) (s : ℕ)
    (hμ : (3 / 4 : ENNReal) ≤ μ.toOuterMeasure {z | lo ≤ z ∧ z ≤ hi}) :
    1 - ((2 : ENNReal) ^ s)⁻¹ ≤
      ((repeatRuns (10 * s + 1) μ).map fun outs => orderStat outs (5 * s)).toOuterMeasure
        {z | lo ≤ z ∧ z ≤ hi} := by
  rw [PMF.toOuterMeasure_map_apply]
  set p := repeatRuns (10 * s + 1) μ
  set T := (fun outs => orderStat outs (5 * s)) ⁻¹' {z | lo ≤ z ∧ z ≤ hi}
  have hM : (2 : ENNReal) ^ (5 * s + 1) * p.toOuterMeasure Tᶜ ≤
      ∑' l, p l * (2 : ENNReal) ^ (l.countP (fun z => decide ¬ (lo ≤ z ∧ z ≤ hi))) := by
    refine median_markov p Tᶜ _ _ fun l hl hT => ?_
    exact pow_le_pow_right₀ (by norm_num) (median_countP_of_orderStat_not_mem l lo hi s
      (median_length_of_mem_support _ μ l hl) hT)
  have hE := median_four_pow_mul_moment_le μ lo hi hμ (10 * s + 1)
  have hnum : (5 : ENNReal) ^ (10 * s + 1) * 2 ^ s ≤ 4 ^ (10 * s + 1) * 2 ^ (5 * s + 1) := by
    have h1 : 5 ^ (10 * s + 1) * 2 ^ s = 5 * (5 ^ 10 * 2) ^ s := by
      rw [mul_pow, ← pow_mul]; ring
    have h2 : 4 ^ (10 * s + 1) * 2 ^ (5 * s + 1) = 8 * (4 ^ 10 * 2 ^ 5) ^ s := by
      rw [mul_pow, ← pow_mul, ← pow_mul]; ring
    have : 5 ^ (10 * s + 1) * 2 ^ s ≤ 4 ^ (10 * s + 1) * 2 ^ (5 * s + 1) := by
      rw [h1, h2]
      exact Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left (by norm_num) s)
    exact_mod_cast this
  have hB : p.toOuterMeasure Tᶜ ≤ ((2 : ENNReal) ^ s)⁻¹ := by
    rw [ENNReal.le_inv_iff_mul_le]
    have h0 : (4 : ENNReal) ^ (10 * s + 1) * 2 ^ (5 * s + 1) ≠ 0 := by positivity
    have ht : (4 : ENNReal) ^ (10 * s + 1) * 2 ^ (5 * s + 1) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num)) (ENNReal.pow_ne_top (by norm_num))
    apply (ENNReal.mul_le_mul_iff_right h0 ht).mp
    calc (4 : ENNReal) ^ (10 * s + 1) * 2 ^ (5 * s + 1) * (p.toOuterMeasure Tᶜ * 2 ^ s)
          = (4 ^ (10 * s + 1) * (2 ^ (5 * s + 1) * p.toOuterMeasure Tᶜ)) * 2 ^ s := by ring
      _ ≤ (4 ^ (10 * s + 1) * ∑' l, p l *
            (2 : ENNReal) ^ (l.countP (fun z => decide ¬ (lo ≤ z ∧ z ≤ hi)))) * 2 ^ s := by
          gcongr
      _ ≤ 5 ^ (10 * s + 1) * 2 ^ s := by gcongr
      _ ≤ 4 ^ (10 * s + 1) * 2 ^ (5 * s + 1) := hnum
      _ = _ := (mul_one _).symm
  rw [tsub_le_iff_right]
  calc (1 : ENNReal) = p.toOuterMeasure T + p.toOuterMeasure Tᶜ :=
        (median_outer_add_compl p T).symm
    _ ≤ p.toOuterMeasure T + ((2 : ENNReal) ^ s)⁻¹ := by gcongr

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `median_amplification` via Markov on `E 2^F ≤ (5/4)^R`, as in the paper
-/
