import Cellcounting.Analysis.BinChain
import Cellcounting.Analysis.BinExpansion
import Cellcounting.Analysis.BinCovering

/-!
# Conductance of the bin walk (`lem:bin-conductance`)

`Cellcounting.Analysis.bin_conductance`: for `e ≥ 1`, every set `A` of bins with
`π_a(A) ≤ 1/2` has stationary flow `Σ_{v ∈ A, w ∉ A} π_a(v) P_a(v, w)` at least
`κ π_a(A)`, where `κ = 1/(10⁴ d² B)`.

This is `evaluation.tex:214-279`, assembled exactly as in the paper from the continuous
objects of `BinDensity`:
* `bin_expansion` (`eq:bin-expansion`, from the finite-box Prékopa–Leindler inequality
  `integral_interpolation_pi`): `μ(N) ≥ 2^t μ(S)` for the side `S` of smaller continuous
  mass, `t = 1/(4dB)`;
* `bin_covering`: `μ(N) ≤ μ(S) + 4F`, `F = binCutFlow`;
* `binV_sum_le_mass` (`eq:bin-density-comparison`): `S_a π_a(X) ≤ 4 μ(S)`;
* `cut_mul_eq_binCutFlow`: the Arlib `cut` of the chain is `F / (S_a 2^{k_d})`, with
  `2^{k_d} ≤ 8d` (`two_pow_oKd_le`).
If the smaller continuous side is the complement of `A`, reversibility (`flow_comm`)
gives it the same cut and `π_a(Aᶜ) ≥ π_a(A)`. The argument yields the constant
`1/(1024 d² B)`, stronger than the stated `1/(10⁴ d² B)`.
-/

namespace Cellcounting.Analysis

open Pseudocode MeasureTheory Set
open Arlib.Probability Arlib.MarkovChains
open scoped ENNReal
open Classical

variable (I : Instance) (ε δ : ℚ)

/-- INTERNAL: the bins of a set of states of the bin chain, as vectors. -/
noncomputable def binVals (A : Finset (binSet I ε δ)) : Finset (ℕ → ℕ) :=
  A.map (Function.Embedding.subtype _)

theorem binVals_subset (A : Finset (binSet I ε δ)) : binVals I ε δ A ⊆ binSet I ε δ := by
  intro v hv
  simp only [binVals, Finset.mem_map, Function.Embedding.coe_subtype] at hv
  obtain ⟨w, _, rfl⟩ := hv
  exact w.2

/-- INTERNAL: complements in `𝒱` match complements of state sets. -/
theorem binVals_compl (A : Finset (binSet I ε δ)) :
    binSet I ε δ \ binVals I ε δ A = binVals I ε δ Aᶜ := by
  ext v
  simp only [binVals, Finset.mem_sdiff, Finset.mem_map, Function.Embedding.coe_subtype,
    Finset.mem_compl]
  constructor
  · rintro ⟨hv, h⟩
    exact ⟨⟨v, hv⟩, fun hA => h ⟨⟨v, hv⟩, hA, rfl⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w.2, ?_⟩
    rintro ⟨w', hw', he⟩
    exact hw (Subtype.ext he ▸ hw')

theorem sum_binVals (A : Finset (binSet I ε δ)) (f : (ℕ → ℕ) → ℝ) :
    ∑ v ∈ binVals I ε δ A, f v = ∑ v ∈ A, f v.1 := by
  simp [binVals, Finset.sum_map]

/-- INTERNAL: `min{V_a(v), V_a(w)} = V_a(v) min{1, V_a(w)/V_a(v)}`. -/
theorem binV_min (a : ℕ) (x y v w : ℕ → ℕ) :
    min (binV I ε δ a x y v) (binV I ε δ a x y w) =
      binV I ε δ a x y v * (binAcc I ε δ a x y v w).toReal := by
  rw [binV_mul_acc]
  unfold binV
  rcases le_total (binExp I ε δ a x y v) (binExp I ε δ a x y w) with h | h
  · rw [max_eq_right h, min_eq_right (zpow_le_zpow_right₀ one_le_two (neg_le_neg h))]
  · rw [max_eq_left h, min_eq_left (zpow_le_zpow_right₀ one_le_two (neg_le_neg h))]

/-- INTERNAL: one cut term, sorted by its target bin. -/
theorem binCutTerm_eq_sum (a : ℕ) (x y : ℕ → ℕ) (T : Finset (ℕ → ℕ)) {v : ℕ → ℕ}
    (hv : v ∈ binSet I ε δ) (u : ℕ) :
    binCutTerm I ε δ a x y T v u = ∑ w ∈ binSet I ε δ \ T,
      if binProp I ε δ v u = some w then min (binV I ε δ a x y v) (binV I ε δ a x y w) else 0 := by
  unfold binCutTerm
  rcases hp : binProp I ε δ v u with _ | w
  · simp
  · simp only [Option.some.injEq]
    split_ifs with hT
    · refine (Finset.sum_eq_zero fun w' hw' => ?_).symm
      rw [if_neg]
      rintro rfl
      exact (Finset.mem_sdiff.1 hw').2 hT
    · rw [Finset.sum_ite_eq]
      rw [if_pos (Finset.mem_sdiff.2 ⟨binProp_mem I ε δ hv hp, hT⟩)]

/-- INTERNAL: the cut terms from `v`, counted by target bin and proposal multiplicity. -/
theorem binCutTerm_sum_range (a : ℕ) (x y : ℕ → ℕ) (T : Finset (ℕ → ℕ)) {v : ℕ → ℕ}
    (hv : v ∈ binSet I ε δ) :
    ∑ u ∈ Finset.range (2 * nFree I ε δ), binCutTerm I ε δ a x y T v u =
      ∑ w ∈ binSet I ε δ \ T,
        (((Finset.range (2 ^ oKd I)).filter fun u => binProp I ε δ v u = some w).card : ℝ) *
          min (binV I ε δ a x y v) (binV I ε δ a x y w) := by
  simp_rw [binCutTerm_eq_sum I ε δ a x y T hv]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hf : ((Finset.range (2 * nFree I ε δ)).filter fun u => binProp I ε δ v u = some w) =
      ((Finset.range (2 ^ oKd I)).filter fun u => binProp I ε δ v u = some w) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_range]
    have h4 := four_nFree_le I ε δ
    constructor
    · rintro ⟨hu, h⟩; exact ⟨by omega, h⟩
    · rintro ⟨_, h⟩; exact ⟨binProp_lt I ε δ h, h⟩
  rw [hf]

/-- INTERNAL: the stationary flow out of `A` is `F / (S_a 2^{k_d})`, where `F` is the
cut quantity of `evaluation.tex:268-270` and `2^{-k_d}` the directional proposal
probability.
TEXLINE: sections/evaluation.tex:268-279 -/
theorem cut_mul_eq_binCutFlow (a : ℕ) (x y : ℕ → ℕ) (hne : (binSet I ε δ).Nonempty)
    (A : Finset (binSet I ε δ)) :
    cut (binDist I ε δ a x y hne) (binKernel I ε δ a x y) A *
        (binS I ε δ a x y * 2 ^ oKd I) = binCutFlow I ε δ a x y (binVals I ε δ A) := by
  rw [binCutFlow, sum_binVals, cut_apply, flow_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [binCutTerm_sum_range I ε δ a x y _ v.2, binVals_compl, sum_binVals, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hne' : w.1 ≠ v.1 := by
    intro h
    rw [Finset.mem_compl] at hw
    exact hw (Subtype.ext h ▸ hv)
  show binV I ε δ a x y v.1 / binS I ε δ a x y * (walkStep I ε δ a x y v.1 w.1).toReal *
      (binS I ε δ a x y * 2 ^ oKd I) = _
  rw [walkStep_apply_ne I ε δ a x y v.1 w.1 hne', binV_min]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast]
  have hS := binS_pos I ε δ a x y hne
  field_simp

/-- INTERNAL: `2^{⌈log₂ 4d⌉} ≤ 8d`, so each directional proposal has probability
at least `1/(8d)`.
TEXLINE: sections/evaluation.tex:276-277 -/
theorem two_pow_oKd_le : (2 : ℝ) ^ oKd I ≤ 8 * dParam I := by
  have hd : 0 < dParam I := by unfold dParam; omega
  have h1 : oKd I ≤ Nat.log 2 (4 * dParam I) + 1 :=
    (Nat.clog_le_iff_le_pow one_lt_two).2 (Nat.lt_pow_succ_log_self one_lt_two _).le
  have h2 := Nat.pow_log_le_self 2 (x := 4 * dParam I) (by omega)
  have h3 : 2 ^ oKd I ≤ 8 * dParam I :=
    calc 2 ^ oKd I ≤ 2 ^ (Nat.log 2 (4 * dParam I) + 1) := Nat.pow_le_pow_right two_pos h1
      _ = 2 * 2 ^ Nat.log 2 (4 * dParam I) := by ring
      _ ≤ 8 * dParam I := by omega
  exact_mod_cast h3

/-- INTERNAL: `2^t - 1 ≥ t/2` for `t ≥ 0`, as used in `eq:bin-expansion`. -/
theorem one_add_half_le_two_rpow {t : ℝ} (ht : 0 ≤ t) : 1 + t / 2 ≤ (2 : ℝ) ^ t := by
  rw [Real.rpow_def_of_pos two_pos]
  have := Real.add_one_le_exp (Real.log 2 * t)
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
  rw [one_div, Real.log_inv] at h
  nlinarith

/-- INTERNAL: the discrete side mass `Σ_{v ∈ X} V_a(v)` is `S_a π_a(X)`. -/
theorem sum_binVals_binV (a : ℕ) (x y : ℕ → ℕ) (hne : (binSet I ε δ).Nonempty)
    (X : Finset (binSet I ε δ)) :
    ∑ v ∈ binVals I ε δ X, binV I ε δ a x y v =
      binS I ε δ a x y * FinDist.Pr (binDist I ε δ a x y hne) X := by
  rw [sum_binVals, FinDist.Pr_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  show _ = binS I ε δ a x y * (binV I ε δ a x y v.1 / binS I ε δ a x y)
  have hS := binS_pos I ε δ a x y hne
  field_simp

/-- INTERNAL: for the side `X` of smaller continuous mass, expansion, the cut-face
covering and the density comparison combine to `t π_a(X) ≤ 32 · 2^{k_d} · flow(X)`,
`t = 1/(4dB)` (`F ≥ tm/32` in the paper).
TEXLINE: sections/evaluation.tex:226-279 -/
theorem bin_side_bound (hε : 0 < ε) (hfeas : feasible I) (a : ℕ) (ha : a ≤ HParam I ε δ)
    (x y : ℕ → ℕ) (hne : (binSet I ε δ).Nonempty) (X : Finset (binSet I ε δ))
    (hhalf : binMass I ε δ a x y (binSide I ε δ (binVals I ε δ X)) ≤
      binMass I ε δ a x y (binSide I ε δ (binSet I ε δ \ binVals I ε δ X))) :
    1 / (4 * (dParam I : ℝ) * BParam I ε δ) * FinDist.Pr (binDist I ε δ a x y hne) X ≤
      32 * cut (binDist I ε δ a x y hne) (binKernel I ε δ a x y) X * 2 ^ oKd I := by
  have hT := binVals_subset I ε δ X
  set t : ℝ := 1 / (4 * (dParam I : ℝ) * BParam I ε δ) with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hexp := bin_expansion I ε δ hε a x y hT hhalf
  have hcov := bin_covering I ε δ hε hfeas a ha x y hT
  have hden := binV_sum_le_mass I ε δ hε hfeas a ha x y hT
  have hfin := (binMass_side_lt_top I ε δ a x y hT).ne
  have hF := cut_mul_eq_binCutFlow I ε δ a x y hne X
  have hF0 := binCutFlow_nonneg I ε δ a x y (binVals I ε δ X)
  rw [← ht] at hexp
  set μS := binMass I ε δ a x y (binSide I ε δ (binVals I ε δ X))
  set F := binCutFlow I ε δ a x y (binVals I ε δ X)
  have key := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin, ENNReal.ofReal_ne_top⟩)
    (hexp.trans hcov)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_add hfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity)] at key
  rw [ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hfin),
    ENNReal.toReal_mul, ENNReal.toReal_ofNat, sum_binVals_binV I ε δ a x y hne] at hden
  have h2t := one_add_half_le_two_rpow ht0
  have hm0 : 0 ≤ μS.toReal := ENNReal.toReal_nonneg
  have hS := binS_pos I ε δ a x y hne
  have h1 : t / 2 * μS.toReal ≤ 4 * F := by nlinarith
  have h3 : t * (binS I ε δ a x y * FinDist.Pr (binDist I ε δ a x y hne) X) ≤
      t * (4 * μS.toReal) := mul_le_mul_of_nonneg_left hden ht0
  have h4 : binS I ε δ a x y * (t * FinDist.Pr (binDist I ε δ a x y hne) X) ≤
      binS I ε δ a x y * (32 * cut (binDist I ε δ a x y hne) (binKernel I ε δ a x y) X *
        2 ^ oKd I) := by
    rw [← hF] at h1; nlinarith
  exact le_of_mul_le_mul_left h4 hS

/-- **Bin conductance** (`lem:bin-conductance`): for `e ≥ 1`, every cut of the bin
walk has stationary flow at least `κ = 1/(10⁴ d² B)` times its smaller side mass.
PAPER: sections/evaluation.tex:214-279 -/
theorem bin_conductance (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (hε1 : ε < 1)
    (hfeas : feasible I) (x y : ℕ → ℕ)
    (hbox : ∀ s < nSmall I ε δ, x s ≤ smallB I ε δ s ∧ y s ≤ smallB I ε δ s)
    (a : ℕ) (ha : a ≤ HParam I ε δ) (he : nFree I ε δ ≠ 0)
    (hne : (binSet I ε δ).Nonempty) (A : Finset (binSet I ε δ))
    (hA : Pr (binDist I ε δ a x y hne) A ≤ 1 / 2) :
    1 / (10000 * (dParam I : ℝ) ^ 2 * BParam I ε δ) * Pr (binDist I ε δ a x y hne) A ≤
      cut (binDist I ε δ a x y hne) (binKernel I ε δ a x y) A := by
  set π := binDist I ε δ a x y hne
  set K := binKernel I ε δ a x y
  have hcutc : cut π K Aᶜ = cut π K A := by
    rw [cut_apply, cut_apply, compl_compl]
    exact flow_comm (binKernel_reversible I ε δ a x y hne) _ _
  have hPrc : FinDist.Pr π Aᶜ = 1 - FinDist.Pr π A := by
    rw [FinDist.Pr_apply, FinDist.Pr_apply]
    have := Finset.sum_add_sum_compl A (fun v => π v)
    rw [π.sum_coe] at this
    linarith
  obtain ⟨X, hX, hPrX, hcutX⟩ : ∃ X : Finset (binSet I ε δ),
      binMass I ε δ a x y (binSide I ε δ (binVals I ε δ X)) ≤
        binMass I ε δ a x y (binSide I ε δ (binSet I ε δ \ binVals I ε δ X)) ∧
      FinDist.Pr π A ≤ FinDist.Pr π X ∧ cut π K X = cut π K A := by
    by_cases h : binMass I ε δ a x y (binSide I ε δ (binVals I ε δ A)) ≤
        binMass I ε δ a x y (binSide I ε δ (binSet I ε δ \ binVals I ε δ A))
    · exact ⟨A, h, le_rfl, rfl⟩
    · refine ⟨Aᶜ, ?_, ?_, hcutc⟩
      · rw [binVals_compl, compl_compl, ← binVals_compl]
        exact (not_le.1 h).le
      · have : FinDist.Pr π A ≤ 1 / 2 := hA
        rw [hPrc]; linarith
  have hs := bin_side_bound I ε δ hε hfeas a ha x y hne X hX
  rw [hcutX] at hs
  have hk := two_pow_oKd_le I
  have hd : (2 : ℝ) ≤ dParam I := by exact_mod_cast dParam_ge I
  obtain ⟨v, hv⟩ := hne
  have hB : (0 : ℝ) < BParam I ε δ := by
    have := ((mem_binSet_iff I ε δ v).1 hv).1 0 (Nat.pos_of_ne_zero he)
    exact_mod_cast (Nat.zero_le _).trans_lt this
  have hc0 := cut_nonneg π K A
  have hP0 := FinDist.Pr_nonneg π A
  change 1 / (10000 * (dParam I : ℝ) ^ 2 * BParam I ε δ) * FinDist.Pr π A ≤ cut π K A
  generalize cut π K A = c at *
  generalize FinDist.Pr π A = p at *
  generalize FinDist.Pr π X = q at *
  generalize (2 : ℝ) ^ oKd I = k at *
  generalize (dParam I : ℝ) = d at *
  generalize (BParam I ε δ : ℝ) = B at *
  have hdB : 0 < 4 * d * B := by positivity
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hdB] at hs
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  have hkc : 32 * c * k ≤ 32 * c * (8 * d) := mul_le_mul_of_nonneg_left hk (by positivity)
  have : p ≤ 32 * c * (8 * d) * (4 * d * B) := by nlinarith
  nlinarith [mul_nonneg hc0 (mul_nonneg (mul_nonneg hdB.le hdB.le) hB.le)]

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r8 · assembled · proof from `bin_expansion`, `bin_covering`, `binV_sum_le_mass`, `cut_mul_eq_binCutFlow`
-/
