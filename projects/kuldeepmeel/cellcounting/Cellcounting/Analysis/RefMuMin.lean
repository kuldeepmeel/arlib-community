import Cellcounting.Analysis.RefChainLaw
import Cellcounting.Analysis.FWeightAdjacent
import Cellcounting.Analysis.TransMassEqCpart
import Cellcounting.Analysis.AsgBoxCard
import Cellcounting.Model.Prior

/-!
# Minimum transversal mass of `μ_j` (`eq:alg-minimum-mass`)

`lem:initialization` (`algorithm.tex:48-52`, proof `algorithm.tex:76-82`): for
`0 ≤ j ≤ H`, every transversal has `μ_j`-mass at least `2^{-(H + p + K)}`.  On a
transversal `x_s + y_s = b_s`, so the factorial factor of `f_j` is
`∏_s C(b_s, x_s)⁻¹ ≥ 2^{-p}`; the penalty satisfies `0 ≤ D ≤ H` (`lem:forest`,
`pseudo_penalty_le_H`), so `h_j ≥ M_f 2^{-H} ≥ 2^{-H}`.  The denominator is
`Σ_A f_j = C(j)` (`transMass_eq_Cpart`), and `C(j) ≤ M_f ∏_s (b_s + 1) = |asgBox| ≤ 2^K`
(`asgBox_card_le`) — slightly sharper than the paper's `C(j) ≤ M_f 2^K`, which lets the
`M_f` of the numerator be dropped via `M_f ≥ 1`.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: on a transversal every small cell is balanced, `x_s + y_s = b_s`.
TEXLINE: sections/signatures.tex:13-41 -/
theorem refMu_profile_balance (I : Instance) (ε δ : ℚ) (S : Finset ℕ)
    (hS : S ∈ transStates I ε δ) (s : ℕ) :
    (profile I ε δ S).1 s + (profile I ε δ S).2 s = smallB I ε δ s := by
  classical
  have hkind : kind I ε δ S = .transversal := (Finset.mem_filter.1 hS).2
  have htr := (kind_eq_transversal_iff I ε δ S).1 hkind
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.range (pSmall I ε δ)).filter fun i => pairCell I ε δ i = s)
    (fun i => 2 * i ∈ S)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  have hcol : ((Finset.range (pSmall I ε δ)).filter fun i =>
      pairCell I ε δ i = s ∧ 2 * i + 1 ∈ S) =
      (Finset.range (pSmall I ε δ)).filter fun i =>
        pairCell I ε δ i = s ∧ ¬ 2 * i ∈ S := by
    apply Finset.filter_congr
    intro i hi
    have := htr i (Finset.mem_range.1 hi)
    tauto
  unfold profile
  simp only
  rw [hcol, smallB_eq_card]
  omega

/-- INTERNAL: `x! (b - x)! / b! = C(b, x)⁻¹ ≥ 2^{-b}`.
TEXLINE: sections/algorithm.tex:76-78 -/
theorem factorial_ratio_ge_half_pow (b x : ℕ) (h : x ≤ b) :
    (1 / 2 : ℝ) ^ b ≤ (x.factorial : ℝ) * ((b - x).factorial : ℝ) / (b.factorial : ℝ) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial h
  have h2 : (b.choose x : ℝ) ≤ 2 ^ b := by exact_mod_cast Nat.choose_le_two_pow b x
  have hc : (0 : ℝ) < b.choose x := by exact_mod_cast Nat.choose_pos h
  have hf : ((b.factorial : ℕ) : ℝ) = (b.choose x : ℝ) * x.factorial * (b - x).factorial := by
    exact_mod_cast h1.symm
  rw [hf]
  have hx : (0 : ℝ) < x.factorial := by exact_mod_cast Nat.factorial_pos x
  have hy : (0 : ℝ) < (b - x).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [show (x.factorial : ℝ) * ((b - x).factorial : ℝ) /
      ((b.choose x : ℝ) * x.factorial * (b - x).factorial) = 1 / (b.choose x : ℝ) by
    field_simp]
  rw [one_div_pow]
  exact one_div_le_one_div_of_le hc h2

/-- INTERNAL: `h_j(x, y) ≥ M_f 2^{-H}` for `j ≤ H` and a box-valid profile, since
`0 ≤ D ≤ H` on the extended free box.
TEXLINE: sections/algorithm.tex:78-79 -/
theorem hWeight_ge_half_pow (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (hfeas : feasible I)
    (j : ℕ) (hj : j ≤ HParam I ε δ) (x y : ℕ → ℕ)
    (hxy : ∀ s < nSmall I ε δ, x s ≤ smallB I ε δ s ∧ y s ≤ smallB I ε δ s) :
    (Mf I ε δ : ℝ) * (1 / 2 : ℝ) ^ HParam I ε δ ≤ hWeight I ε δ j x y := by
  have hH : (0 : ℝ) < (HParam I ε δ : ℝ) := by exact_mod_cast HParam_pos I ε δ hε
  have hjR : (j : ℝ) ≤ HParam I ε δ := by exact_mod_cast hj
  rw [hWeight, ← card_freeBox, ← nsmul_eq_mul]
  apply Finset.card_nsmul_le_sum
  intro z hz
  have hDnn : (0 : ℝ) ≤ (penalty I ε δ x y (extendQ z) : ℝ) := by
    exact_mod_cast pseudocode_penalty_nonneg I ε δ x y (extendQ z)
  have hDle : (penalty I ε δ x y (extendQ z) : ℝ) ≤ (HParam I ε δ : ℝ) := by
    exact_mod_cast pseudo_penalty_le_H I ε δ hε hfeas x y (extendQ z) hxy
      (extendQ_mem_extended I ε δ z hz)
  have hexp : -((HParam I ε δ : ℕ) : ℝ) ≤
      -((j : ℝ) * (penalty I ε δ x y (extendQ z) : ℝ) / (HParam I ε δ : ℝ)) := by
    rw [neg_le_neg_iff, div_le_iff₀ hH]
    nlinarith
  have hmono := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast] at hmono
  rw [one_div, inv_pow]
  exact hmono

/-- INTERNAL: `h_j(x, y) ≤ M_f`, since every penalty term is `2^{-(nonneg)} ≤ 1`.
TEXLINE: sections/algorithm.tex:79-81 -/
theorem hWeight_le_Mf (I : Instance) (ε δ : ℚ) (j : ℕ) (x y : ℕ → ℕ) :
    hWeight I ε δ j x y ≤ (Mf I ε δ : ℝ) := by
  rw [hWeight, ← card_freeBox]
  have := Finset.sum_le_card_nsmul (freeBox I ε δ)
    (fun z => (2 : ℝ) ^ (-((j : ℝ) * (penalty I ε δ x y (extendQ z) : ℝ) /
      (HParam I ε δ : ℝ)))) 1
    (by
      intro z _
      have hDnn : (0 : ℝ) ≤ (penalty I ε δ x y (extendQ z) : ℝ) := by
        exact_mod_cast pseudocode_penalty_nonneg I ε δ x y (extendQ z)
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      rw [neg_nonpos]
      positivity)
  simpa using this

/-- **Minimum transversal mass** (`eq:alg-minimum-mass`): for `j ≤ H`, every transversal
has `μ_j`-mass at least `2^{-(H + p + K)}`.
PAPER: sections/algorithm.tex:48-52 -/
theorem refMu_min (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j ≤ HParam I ε δ)
    (S : Finset ℕ) (hS : S ∈ transStates I ε δ) :
    (1 / 2 : ℝ) ^ (HParam I ε δ + pSmall I ε δ + KParam I ε δ) ≤ refMu I ε δ j S := by
  classical
  have hkind : kind I ε δ S = .transversal := (Finset.mem_filter.1 hS).2
  have hbox := profile_le_smallB I ε δ S
  have hbal := refMu_profile_balance I ε δ S hS
  -- `Σ_s b_s = p`
  have hsumB : ∑ s ∈ Finset.range (nSmall I ε δ), smallB I ε δ s = pSmall I ε δ := by
    rw [← (profile_valid_of_kind I ε δ S (by rw [hkind]; simp)).2]
    exact Finset.sum_congr rfl fun s _ => (hbal s).symm
  -- the factorial factor is at least `2^{-p}`
  have hfac : (1 / 2 : ℝ) ^ pSmall I ε δ ≤
      ∏ s ∈ Finset.range (nSmall I ε δ),
        ((((profile I ε δ S).1 s).factorial : ℝ) * (((profile I ε δ S).2 s).factorial : ℝ) /
          ((smallB I ε δ s).factorial : ℝ)) := by
    rw [← hsumB, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun s _ => by positivity) (fun s _ => ?_)
    have hy : (profile I ε δ S).2 s = smallB I ε δ s - (profile I ε δ S).1 s := by
      have := hbal s; omega
    rw [hy]
    exact factorial_ratio_ge_half_pow _ _ (by have := hbal s; omega)
  -- `M_f ≥ 1`
  have hMf : (1 : ℝ) ≤ (Mf I ε δ : ℝ) := by
    have hF : (freeBox I ε δ).Nonempty := ⟨fun _ => 0, by simp [freeBox]⟩
    rw [← card_freeBox]
    exact_mod_cast hF.card_pos
  -- numerator: `f_j(S) ≥ 2^{-(H + p)}`
  have hnum : (1 / 2 : ℝ) ^ (HParam I ε δ + pSmall I ε δ) ≤ fWeight I ε δ j S := by
    have hh := hWeight_ge_half_pow I ε δ hε hfeas j hj (profile I ε δ S).1
      (profile I ε δ S).2 hbox
    rw [fWeight, pow_add]
    have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ HParam I ε δ := by positivity
    have h1 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ pSmall I ε δ := by positivity
    calc (1 / 2 : ℝ) ^ HParam I ε δ * (1 / 2 : ℝ) ^ pSmall I ε δ
        ≤ ((Mf I ε δ : ℝ) * (1 / 2 : ℝ) ^ HParam I ε δ) * (1 / 2 : ℝ) ^ pSmall I ε δ := by
          gcongr; nlinarith
      _ ≤ _ := by
          apply mul_le_mul hh hfac h1
          exact le_trans (by positivity) hh
  -- denominator: `Σ_A f_j = C(j) ≤ |asgBox| ≤ 2^K`
  have hden : transMass I ε δ j ≤ (2 : ℝ) ^ KParam I ε δ := by
    rw [transMass_eq_Cpart, Cpart]
    calc ∑ x ∈ smallBox I ε δ,
          hWeight I ε δ j (extendN x) (fun s => smallB I ε δ s - extendN x s)
        ≤ ∑ _x ∈ smallBox I ε δ, (Mf I ε δ : ℝ) :=
          Finset.sum_le_sum fun x _ => hWeight_le_Mf I ε δ j _ _
      _ = ((asgBox I ε δ).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, asgBox, Finset.card_product, card_freeBox]
          push_cast; ring
      _ ≤ (2 : ℝ) ^ KParam I ε δ := by exact_mod_cast asgBox_card_le I ε δ
  have hpos : 0 < transMass I ε δ j := by
    rw [transMass_eq_Cpart]; exact Cpart_pos I ε δ j
  rw [refMu, if_pos hS, le_div_iff₀ hpos]
  calc (1 / 2 : ℝ) ^ (HParam I ε δ + pSmall I ε δ + KParam I ε δ) * transMass I ε δ j
      ≤ (1 / 2 : ℝ) ^ (HParam I ε δ + pSmall I ε δ + KParam I ε δ) *
          (2 : ℝ) ^ KParam I ε δ := by gcongr
    _ = (1 / 2 : ℝ) ^ (HParam I ε δ + pSmall I ε δ) := by
        rw [pow_add, mul_assoc, ← mul_pow]; norm_num
    _ ≤ fWeight I ε δ j S := hnum

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `refMu_min` via `transMass_eq_Cpart`, `pseudo_penalty_le_H`, `asgBox_card_le`
-/
