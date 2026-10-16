import Cellcounting.Analysis.RefExperiment
import Cellcounting.Analysis.ForestPenaltyBound
import Cellcounting.Analysis.ImplementationCoupling

/-!
# Adjacent parameters (`lem:initialization`, `eq:alg-adjacent`)

On a feasible instance `0 ≤ D ≤ H` throughout the extended free box
(`lem:forest`), so every summand of `h_{j+1}` lies between one half and one times
the corresponding summand of `h_j`; the factorial factor of `f_j` does not depend
on `j`.  Hence `f_j / 2 ≤ f_{j+1} ≤ f_j` on every state of the paired ground set.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: the small-count profile of any state is box-valid, with no
hypothesis on its `kind` (unlike `profile_valid_of_kind`, whose extra
conclusion about the total needs `kind ≠ .outside`, but whose box-validity half
does not). -/
theorem profile_le_smallB (I : Instance) (ε δ : ℚ) (S : Finset ℕ) :
    ∀ s < nSmall I ε δ, (profile I ε δ S).1 s ≤ smallB I ε δ s ∧
      (profile I ε δ S).2 s ≤ smallB I ε δ s := by
  intro s hs
  have hblock : ∀ (P : ℕ → Prop) [DecidablePred P],
      ((Finset.range (pSmall I ε δ)).filter fun i => pairCell I ε δ i = s ∧ P i).card ≤
        smallB I ε δ s := by
    intro P _
    calc _ ≤ (Finset.Ico (cellFirst I ε δ s) (cellFirst I ε δ s + smallB I ε δ s)).card :=
          Finset.card_le_card (by
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_range] at hi
            obtain ⟨_, h1, h2⟩ := pairCell_spec I ε δ i hi.1
            rw [hi.2.1] at h1 h2
            exact Finset.mem_Ico.2 ⟨h1, h2⟩)
      _ = _ := by simp
  exact ⟨hblock _, hblock _⟩

/-- INTERNAL: `Pseudocode.penalty` is nonnegative, unconditionally. -/
theorem pseudocode_penalty_nonneg (I : Instance) (ε δ : ℚ) (x y : ℕ → ℕ) (z : ℕ → ℚ) :
    0 ≤ penalty I ε δ x y z := by
  unfold penalty
  apply mul_nonneg (by positivity)
  apply add_nonneg
  · apply List.sum_nonneg
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨v, -, rfl⟩ := ha
    exact abs_nonneg _
  · exact Finset.sum_nonneg fun t _ => div_nonneg (boxDist_nonneg _ _) (by positivity)

/-- INTERNAL: every `extendQ` of a `freeBox` vector is a valid penalty argument
in the extended free box of `pseudo_penalty_le_H`. -/
theorem extendQ_mem_extended (I : Instance) (ε δ : ℚ) (z : Fin (nFree I ε δ) → ℕ)
    (hz : z ∈ freeBox I ε δ) :
    ∀ k < nFree I ε δ, 0 ≤ extendQ z k ∧ extendQ z k ≤ ((freeAt I ε δ k).2.2 : ℚ) + 1 := by
  intro k hk
  have hmem := (Fintype.mem_piFinset.1 hz) ⟨k, hk⟩
  simp only [Finset.mem_range] at hmem
  simp only [extendQ, hk, dite_true]
  constructor
  · positivity
  · have : (z ⟨k, hk⟩ : ℚ) ≤ ((freeAt I ε δ k).2.2 : ℚ) := by
      exact_mod_cast (by omega : z ⟨k, hk⟩ ≤ (freeAt I ε δ k).2.2)
    linarith

/-- INTERNAL: the ratio bound of `eq:alg-adjacent` at the level of `h_j`, for
any box-valid small-count profile `(x, y)`, without the factorial factor of
`f_j`.
PAPER: sections/algorithm.tex:35-42 -/
theorem hWeight_adjacent (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (hfeas : feasible I)
    (j : ℕ) (x y : ℕ → ℕ)
    (hxy : ∀ s < nSmall I ε δ, x s ≤ smallB I ε δ s ∧ y s ≤ smallB I ε δ s) :
    hWeight I ε δ j x y / 2 ≤ hWeight I ε δ (j + 1) x y ∧
      hWeight I ε δ (j + 1) x y ≤ hWeight I ε δ j x y := by
  have hH : (0 : ℝ) < (HParam I ε δ : ℝ) := by exact_mod_cast HParam_pos I ε δ hε
  have hterm : ∀ z ∈ freeBox I ε δ,
      (2 : ℝ) ^ (-(((j + 1 : ℕ) : ℝ) * (penalty I ε δ x y (extendQ z) : ℝ) /
          (HParam I ε δ : ℝ))) =
        (2 : ℝ) ^ (-((j : ℝ) * (penalty I ε δ x y (extendQ z) : ℝ) / (HParam I ε δ : ℝ))) *
          (2 : ℝ) ^ (-(penalty I ε δ x y (extendQ z) : ℝ) / (HParam I ε δ : ℝ)) := by
    intro z _
    have heq : -(((j + 1 : ℕ) : ℝ) * (penalty I ε δ x y (extendQ z) : ℝ) /
        (HParam I ε δ : ℝ)) =
        -((j : ℝ) * (penalty I ε δ x y (extendQ z) : ℝ) / (HParam I ε δ : ℝ)) +
          -(penalty I ε δ x y (extendQ z) : ℝ) / (HParam I ε δ : ℝ) := by
      push_cast; ring
    rw [heq, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hbound : ∀ z ∈ freeBox I ε δ,
      (1 / 2 : ℝ) ≤
          (2 : ℝ) ^ (-(penalty I ε δ x y (extendQ z) : ℝ) / (HParam I ε δ : ℝ)) ∧
        (2 : ℝ) ^ (-(penalty I ε δ x y (extendQ z) : ℝ) / (HParam I ε δ : ℝ)) ≤ 1 := by
    intro z hz
    have hz' := extendQ_mem_extended I ε δ z hz
    have hDnn := pseudocode_penalty_nonneg I ε δ x y (extendQ z)
    have hDle := pseudo_penalty_le_H I ε δ hε hfeas x y (extendQ z) hxy hz'
    have hDleR : (penalty I ε δ x y (extendQ z) : ℝ) ≤ (HParam I ε δ : ℝ) := by
      exact_mod_cast hDle
    have hDnnR : (0 : ℝ) ≤ (penalty I ε δ x y (extendQ z) : ℝ) := by
      exact_mod_cast hDnn
    constructor
    · have h1 : (-1 : ℝ) ≤ -(penalty I ε δ x y (extendQ z) : ℝ) / (HParam I ε δ : ℝ) := by
        rw [le_div_iff₀ hH]; nlinarith
      have hmono := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h1
      rw [Real.rpow_neg_one] at hmono
      linarith
    · have h2 : -(penalty I ε δ x y (extendQ z) : ℝ) / (HParam I ε δ : ℝ) ≤ 0 :=
        div_nonpos_iff.2 (Or.inr ⟨by linarith [hDnnR], hH.le⟩)
      have hmono := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h2
      rwa [Real.rpow_zero] at hmono
  have hpos : ∀ z ∈ freeBox I ε δ, (0 : ℝ) ≤
      (2 : ℝ) ^ (-((j : ℝ) * (penalty I ε δ x y (extendQ z) : ℝ) / (HParam I ε δ : ℝ))) :=
    fun z _ => le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  constructor
  · rw [hWeight, hWeight, Finset.sum_div]
    apply Finset.sum_le_sum
    intro z hz
    rw [hterm z hz]
    have h := (hbound z hz).1
    nlinarith [hpos z hz]
  · rw [hWeight, hWeight]
    apply Finset.sum_le_sum
    intro z hz
    rw [hterm z hz]
    have h := (hbound z hz).2
    nlinarith [hpos z hz]

/-- **Adjacent parameters** (`eq:alg-adjacent`): `1/2 ≤ f_{j+1}/f_j ≤ 1` on every
state of the enlarged binary state space.
PAPER: sections/algorithm.tex:35-42 -/
theorem fWeight_adjacent (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (hfeas : feasible I)
    (j : ℕ) (S : Finset ℕ) (hS : S ∈ refStates I ε δ) :
    fWeight I ε δ j S / 2 ≤ fWeight I ε δ (j + 1) S ∧
      fWeight I ε δ (j + 1) S ≤ fWeight I ε δ j S := by
  set x := (profile I ε δ S).1
  set y := (profile I ε δ S).2
  set K : ℝ := ∏ s ∈ Finset.range (nSmall I ε δ),
      ((x s).factorial : ℝ) * ((y s).factorial : ℝ) / ((smallB I ε δ s).factorial : ℝ)
    with hKdef
  have hKnn : 0 ≤ K := by
    apply Finset.prod_nonneg
    intro s _
    positivity
  have hxy := profile_le_smallB I ε δ S
  have hadj := hWeight_adjacent I ε δ hε hfeas j x y hxy
  have hfj : fWeight I ε δ j S = hWeight I ε δ j x y * K := rfl
  have hfj1 : fWeight I ε δ (j + 1) S = hWeight I ε δ (j + 1) x y * K := rfl
  rw [hfj, hfj1]
  refine ⟨?_, mul_le_mul_of_nonneg_right hadj.2 hKnn⟩
  calc hWeight I ε δ j x y * K / 2 = hWeight I ε δ j x y / 2 * K := by ring
    _ ≤ hWeight I ε δ (j + 1) x y * K := mul_le_mul_of_nonneg_right hadj.1 hKnn

end Cellcounting.Analysis
