import Cellcounting.Analysis.HyperbolicForm
import Cellcounting.Analysis.PerronKernel

/-!
# The cubic contraction of `lem:binary-contraction` (`signatures.tex:122-153`)

Let `T` be a symmetric cubic tensor on a finite index set with at least three
indices, positive on triples of distinct indices and zero on repetitions, whose slices
`T_i = (T_{iuh})_{u,h}` each have at most one positive eigenvalue (`Hyp`).  For any
nonnegative coefficient vector `a`, the contraction `M = Σ_i a_i T_i` has at most one
positive eigenvalue on the full index set.

* `hyp_cubic_contract_pos` is the case of strictly positive `a`: the paper's argument
  applies the projection inequality to every slice at `a` and sums to
  `xᵀMx ≤ Σ_i a_i (Mx)_i² / (Ma)_i` (`cubic_projection`, `eq:cubic-projection`); together
  with strictly positive off-diagonal entries, the maximum principle (`perron_kernel`,
  in `PerronKernel.lean`) makes `M` nonpositive on `{x : (Ma)ᵀx = 0}`, and
  `hyp_of_kernel` concludes.
* `hyp_cubic_contract` passes to nonnegative `a` through `a + ε 𝟙`, `ε ↓ 0`
  (`hyp_of_affine_limit`).
-/

namespace Cellcounting.Analysis

open Finset

variable {ι : Type*} [Fintype ι]

/-- INTERNAL: `Hyp` is closed under the limit `ε ↓ 0` of an affine family
`Q + ε P`.
TEXLINE: sections/signatures.tex:150-153 -/
theorem hyp_of_affine_limit (Q P : ι → ι → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → Hyp (fun i k => Q i k + ε * P i k)) : Hyp Q := by
  intro u w hu
  have hlin : ∀ (ε : ℝ) (x y : ι → ℝ),
      qf (fun i k => Q i k + ε * P i k) x y = qf Q x y + ε * qf P x y := by
    intro ε x y
    simp only [qf, mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  set A := qf Q u u
  set B := qf Q u w
  set C := qf Q w w
  set A1 := qf P u u
  set B1 := qf P u w
  set C1 := qf P w w
  by_contra hcon
  push Not at hcon
  -- `f(ε) = (B + ε B1)² - (A + ε A1)(C + ε C1) = f₀ + ε c₁ + ε² c₂` with `f₀ < 0`.
  set f0 := B ^ 2 - A * C
  have hf0 : f0 < 0 := by simp only [f0]; linarith
  set c1 := 2 * B * B1 - A * C1 - A1 * C
  set c2 := B1 ^ 2 - A1 * C1
  set ε : ℝ := min 1 (min (A / (2 * (|A1| + 1))) (-f0 / (2 * (|c1| + |c2| + 1))))
  have hε0 : 0 < ε := by
    simp only [ε]
    refine lt_min one_pos (lt_min (by positivity) ?_)
    exact div_pos (by linarith) (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεA : ε ≤ A / (2 * (|A1| + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hεf : ε ≤ -f0 / (2 * (|c1| + |c2| + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hpos : 0 < A + ε * A1 := by
    have h1 : ε * (2 * (|A1| + 1)) ≤ A := by
      rwa [le_div_iff₀ (by positivity)] at hεA
    have h2 : -(ε * |A1|) ≤ ε * A1 := by
      have := neg_abs_le A1
      nlinarith
    nlinarith [abs_nonneg A1]
  have hkey := h ε hε0 u w (by rw [hlin]; exact hpos)
  rw [hlin, hlin, hlin] at hkey
  have hexp : (B + ε * B1) ^ 2 - (A + ε * A1) * (C + ε * C1) = f0 + ε * c1 + ε ^ 2 * c2 := by
    simp only [f0, c1, c2]; ring
  have hbound : ε * c1 + ε ^ 2 * c2 < -f0 := by
    have h1 : ε * (2 * (|c1| + |c2| + 1)) ≤ -f0 := by
      rwa [le_div_iff₀ (by positivity)] at hεf
    have h2 : ε * c1 ≤ ε * |c1| := mul_le_mul_of_nonneg_left (le_abs_self _) hε0.le
    have h3 : ε ^ 2 * c2 ≤ ε * |c2| := by
      have : ε ^ 2 * c2 ≤ ε ^ 2 * |c2| := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      have : ε ^ 2 * |c2| ≤ ε * |c2| := by
        have : ε ^ 2 ≤ ε := by nlinarith
        exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
      linarith
    nlinarith [abs_nonneg c1, abs_nonneg c2]
  nlinarith

variable [DecidableEq ι]

/-- INTERNAL: `T` is nonnegative everywhere (positive on distinct triples, zero on
repetitions).
TEXLINE: sections/signatures.tex:122-127 -/
theorem cubicSum_T_nonneg (T : ι → ι → ι → ℝ)
    (hpos : ∀ i u h, i ≠ u → i ≠ h → u ≠ h → 0 < T i u h)
    (hzero : ∀ i u h, (i = u ∨ i = h ∨ u = h) → T i u h = 0) (i u h : ι) : 0 ≤ T i u h := by
  by_cases h1 : i = u ∨ i = h ∨ u = h
  · exact (hzero i u h h1).ge
  · push_neg at h1
    exact (hpos i u h h1.1 h1.2.1 h1.2.2).le

/-- INTERNAL: given at least three indices, any two fixed indices `u ≠ h` can be
avoided by a third. -/
theorem cubicSum_third_index (hcard : 3 ≤ Fintype.card ι) (u h : ι) (huh : u ≠ h) :
    ∃ i, i ≠ u ∧ i ≠ h := by
  have hcard' : 0 < (Finset.univ \ ({u, h} : Finset ι)).card := by
    have hle : ({u, h} : Finset ι).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hcard'
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton] at hi
  push_neg at hi
  exact ⟨i, hi.1, hi.2⟩

/-- INTERNAL: given at least three indices, any one fixed index `i` is avoided by
two further distinct indices. -/
theorem cubicSum_two_others (hcard : 3 ≤ Fintype.card ι) (i : ι) :
    ∃ u h : ι, u ≠ i ∧ h ≠ i ∧ u ≠ h := by
  have hcard' : 1 < (Finset.univ \ ({i} : Finset ι)).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Finset.card_singleton]
    omega
  obtain ⟨u, hu, h, hh, huh⟩ := Finset.one_lt_card.mp hcard'
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton] at hu hh
  exact ⟨u, h, hu, hh, huh⟩

/-- INTERNAL: the cubic contraction `M = Σ_i a_i T_i` is symmetric. -/
theorem cubicSum_symm (T : ι → ι → ι → ℝ) (hsymm2 : ∀ i u h, T i u h = T i h u) (a : ι → ℝ) :
    QSymm (fun u h => ∑ i, a i * T i u h) :=
  fun u h => Finset.sum_congr rfl fun i _ => by rw [hsymm2 i u h]

/-- INTERNAL: the cubic contraction has zero diagonal, since every `T i u u` is
zero. -/
theorem cubicSum_diag_zero (T : ι → ι → ι → ℝ)
    (hzero : ∀ i u h, (i = u ∨ i = h ∨ u = h) → T i u h = 0) (a : ι → ℝ) (u : ι) :
    (∑ i, a i * T i u u) = 0 :=
  Finset.sum_eq_zero fun i _ => by rw [hzero i u u (Or.inr (Or.inr rfl))]; ring

/-- INTERNAL: every off-diagonal entry of the cubic contraction is strictly
positive: a third index contributes a strictly positive term, and every other
term is nonnegative.
PAPER: sections/signatures.tex:142-144 -/
theorem cubicSum_offDiag_pos (hcard : 3 ≤ Fintype.card ι) (T : ι → ι → ι → ℝ)
    (hpos : ∀ i u h, i ≠ u → i ≠ h → u ≠ h → 0 < T i u h)
    (hzero : ∀ i u h, (i = u ∨ i = h ∨ u = h) → T i u h = 0) (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (u h : ι) (huh : u ≠ h) : 0 < ∑ i, a i * T i u h := by
  obtain ⟨i0, hi0u, hi0h⟩ := cubicSum_third_index hcard u h huh
  refine Finset.sum_pos' (fun i _ => mul_nonneg (ha i).le (cubicSum_T_nonneg T hpos hzero i u h))
    ⟨i0, Finset.mem_univ i0, mul_pos (ha i0) (hpos i0 u h hi0u hi0h huh)⟩

/-- INTERNAL: tensor symmetry gives `aᵀ T_i a = (Ma)_i > 0` (`eq:cubic-projection`'s
opening identity): the slice quadratic form at `a` is strictly positive, using a
third index outside `{u,h}` as in `cubicSum_offDiag_pos`.
PAPER: sections/signatures.tex:128-130, 134-135 -/
theorem cubicSum_mass_pos (hcard : 3 ≤ Fintype.card ι) (T : ι → ι → ι → ℝ)
    (hpos : ∀ i u h, i ≠ u → i ≠ h → u ≠ h → 0 < T i u h)
    (hzero : ∀ i u h, (i = u ∨ i = h ∨ u = h) → T i u h = 0) (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (i : ι) : 0 < qf (T i) a a := by
  obtain ⟨u0, h0, hu0, hh0, huh0⟩ := cubicSum_two_others hcard i
  have hinner_nonneg : ∀ u, 0 ≤ ∑ h, a u * T i u h * a h := fun u =>
    Finset.sum_nonneg fun h _ =>
      mul_nonneg (mul_nonneg (ha u).le (cubicSum_T_nonneg T hpos hzero i u h)) (ha h).le
  have hinner_pos : 0 < ∑ h, a u0 * T i u0 h * a h := by
    refine Finset.sum_pos'
      (fun h _ => mul_nonneg (mul_nonneg (ha u0).le (cubicSum_T_nonneg T hpos hzero i u0 h))
        (ha h).le)
      ⟨h0, Finset.mem_univ h0, mul_pos (mul_pos (ha u0) (hpos i u0 h0 hu0.symm hh0.symm huh0))
        (ha h0)⟩
  have hqf : qf (T i) a a = ∑ u, ∑ h, a u * T i u h * a h := rfl
  rw [hqf]
  exact Finset.sum_pos' (fun u _ => hinner_nonneg u) ⟨u0, Finset.mem_univ u0, hinner_pos⟩

omit [DecidableEq ι] in
/-- INTERNAL: tensor symmetry gives `xᵀ T_i a = (M x)_i` for `M = Σ_j a_j T_j`.
TEXLINE: sections/signatures.tex:131-135 -/
theorem cubicSum_slice_apply (T : ι → ι → ι → ℝ) (hsymm1 : ∀ i u h, T i u h = T u i h)
    (a x : ι → ℝ) (i : ι) :
    qf (T i) a x = ∑ k, (∑ j, a j * T j i k) * x k := by
  unfold qf
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [hsymm1 i j k]

/-- INTERNAL: the projection inequality `eq:cubic-projection`:
`xᵀMx ≤ Σ_i a_i (Mx)_i² / (Ma)_i` for `M = Σ_i a_i T_i`.
PAPER: sections/signatures.tex:136-148 -/
theorem cubic_projection (hcard : 3 ≤ Fintype.card ι) (T : ι → ι → ι → ℝ)
    (hsymm1 : ∀ i u h, T i u h = T u i h)
    (hpos : ∀ i u h, i ≠ u → i ≠ h → u ≠ h → 0 < T i u h)
    (hzero : ∀ i u h, (i = u ∨ i = h ∨ u = h) → T i u h = 0)
    (hslice : ∀ i, Hyp (T i)) (a : ι → ℝ) (ha : ∀ i, 0 < a i) (x : ι → ℝ) :
    qf (fun u h => ∑ i, a i * T i u h) x x ≤
      ∑ i, a i * (∑ k, (∑ j, a j * T j i k) * x k) ^ 2 / ∑ k, (∑ j, a j * T j i k) * a k := by
  rw [qf_matrix_sum Finset.univ (fun i u h => a i * T i u h)]
  refine Finset.sum_le_sum fun i _ => ?_
  have hsc : qf (fun u h => a i * T i u h) x x = a i * qf (T i) x x := by
    simp only [qf, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun h _ => by ring
  rw [hsc, ← cubicSum_slice_apply T hsymm1 a x i, ← cubicSum_slice_apply T hsymm1 a a i,
    mul_div_assoc]
  exact mul_le_mul_of_nonneg_left
    ((hslice i).proj (cubicSum_mass_pos hcard T hpos hzero a ha i) x) (ha i).le

/-- **Cubic contraction, positive coefficients** (`lem:binary-contraction`, the
full-matrix assertion for `a > 0`): for a symmetric cubic tensor on at least three
indices, positive on distinct triples, zero on repetitions, with every slice `Hyp`,
the contraction `Σ_i a_i T_i` with all `a_i > 0` is `Hyp`.

The paper's route: the projection inequality summed over slices
(`cubic_projection`), positivity of off-diagonal entries (`cubicSum_offDiag_pos`) and
the maximum principle (`perron_kernel`) make `M` nonpositive on `{x : (Ma)ᵀx = 0}`,
and `hyp_of_kernel` concludes.  The paper's diagonal congruence
`M' = D_*^{-1/2} M D_*^{-1/2}` is absorbed into `perron_kernel`, which works with the
pencil `(M, D_*)` directly.
PAPER: sections/signatures.tex:122-162 -/
theorem hyp_cubic_contract_pos (hcard : 3 ≤ Fintype.card ι) (T : ι → ι → ι → ℝ)
    (hsymm1 : ∀ i u h, T i u h = T u i h) (hsymm2 : ∀ i u h, T i u h = T i h u)
    (hpos : ∀ i u h, i ≠ u → i ≠ h → u ≠ h → 0 < T i u h)
    (hzero : ∀ i u h, (i = u ∨ i = h ∨ u = h) → T i u h = 0)
    (hslice : ∀ i, Hyp (T i)) (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    Hyp (fun u h => ∑ i, a i * T i u h) := by
  have hM := cubicSum_symm T hsymm2 a
  refine hyp_of_kernel hM (fun i => ∑ k, (∑ j, a j * T j i k) * a k) ?_
  exact perron_kernel _ hM a ha (cubicSum_offDiag_pos hcard T hpos hzero a ha)
    (fun i => by
      rw [← cubicSum_slice_apply T hsymm1 a a i]
      exact cubicSum_mass_pos hcard T hpos hzero a ha i)
    (cubic_projection hcard T hsymm1 hpos hzero hslice a ha)

/-- **Cubic contraction** (`lem:binary-contraction`, "the cubic contraction used to
sum a pair has at most one positive eigenvalue on its full remaining index set"): the
contraction `Σ_i a_i T_i` with all `a_i ≥ 0` is `Hyp`.
PAPER: sections/signatures.tex:122-153 -/
theorem hyp_cubic_contract (hcard : 3 ≤ Fintype.card ι) (T : ι → ι → ι → ℝ)
    (hsymm1 : ∀ i u h, T i u h = T u i h) (hsymm2 : ∀ i u h, T i u h = T i h u)
    (hpos : ∀ i u h, i ≠ u → i ≠ h → u ≠ h → 0 < T i u h)
    (hzero : ∀ i u h, (i = u ∨ i = h ∨ u = h) → T i u h = 0)
    (hslice : ∀ i, Hyp (T i)) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    Hyp (fun u h => ∑ i, a i * T i u h) := by
  apply hyp_of_affine_limit _ (fun u h => ∑ i, T i u h)
  intro ε hε
  have := hyp_cubic_contract_pos hcard T hsymm1 hsymm2 hpos hzero hslice
    (fun i => a i + ε) (fun i => by linarith [ha i])
  convert this using 2 with u h
  simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r9 · proved · `hyp_cubic_contract_pos` via `cubic_projection` + `perron_kernel` (compactness and first variation, no spectral theorem)
-/
