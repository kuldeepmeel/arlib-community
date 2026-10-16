import Cellcounting.Analysis.HyperbolicForm
import Cellcounting.Analysis.HypCubicContract

/-!
# The full-matrix cubic contraction (`lem:binary-contraction`, `signatures.tex:120-170`)

Let `T` be a symmetric cubic tensor on a finite index type, positive on triples of
distinct indices and zero on repetitions, each of whose slices `T_a = (T a u h)_{u,h}`
has at most one positive eigenvalue (`Hyp`).  Then for every nonnegative vector `c`
the contraction `M = Σ_a c_a T_a` again satisfies `Hyp` on the full index set.

* `cubic_contraction_pos` is the case of a strictly positive vector `c` (with at least
  three indices, so that `T` is not identically zero);
* `cubic_contraction` follows: with fewer than three indices `T = 0`; otherwise apply
  the positive case to `c + ε𝟙` and let `ε ↓ 0` (`Hyp` is closed under such limits).

Suggested route for `cubic_contraction_pos` (equivalent to the paper's Perron–Frobenius
argument, without eigenvalues): put `d_i = (Mc)_i / c_i > 0`.
1. Slice projection (`Hyp.proj` at `u = c`, using `cᵀT_i c = (Mc)_i`, `xᵀT_i c = (Mx)_i`)
   and summation with weights `c_i` give `xᵀMx ≤ Σ_i (Mx)_i² / d_i`
   (`eq:cubic-projection`).
2. Dirichlet identity: `Σ_i d_i x_i² - xᵀMx = ½ Σ_{i,h} M_ih c_i c_h (x_i/c_i - x_h/c_h)²`,
   with `M_ih > 0` for `i ≠ h`.
3. By `hyp_of_kernel` it suffices that `xᵀMx ≤ 0` when `Σ_i d_i c_i x_i = 0`.  If not,
   maximize `xᵀMx` on the compact set `{Σ d_i c_i x_i = 0, Σ d_i x_i² = 1}`; at a
   maximizer `x*` with value `λ > 0`, nonnegativity of `λ Σ d_i x_i² - xᵀMx` on the
   hyperplane forces `Mx* = λ D x*`.  Step 1 gives `λ ≤ λ²`, so `λ ≥ 1`; step 2 gives
   `λ ≤ 1`, hence the Dirichlet form vanishes at `x*`, so `x* ∝ c`, contradicting
   `Σ d_i c_i x*_i = 0` and `Σ d_i x*_i² = 1`.
-/

namespace Cellcounting.Analysis

open Finset Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Cubic contraction, positive vector** (`lem:binary-contraction`, the step
`eq:cubic-projection` and the maximum principle): the contraction of a positive
symmetric cubic tensor with `Hyp` slices along a strictly positive vector satisfies
`Hyp`.
PAPER: sections/signatures.tex:128-165 -/
theorem cubic_contraction_pos (T : ι → ι → ι → ℝ)
    (hs1 : ∀ a u h, T a u h = T u a h) (hs2 : ∀ a u h, T a u h = T a h u)
    (hpos : ∀ a u h, a ≠ u → a ≠ h → u ≠ h → 0 < T a u h)
    (hzero : ∀ a u h, (a = u ∨ a = h ∨ u = h) → T a u h = 0)
    (hslice : ∀ a, Hyp (T a)) (h3 : ∃ a u h : ι, a ≠ u ∧ a ≠ h ∧ u ≠ h)
    (c : ι → ℝ) (hc : ∀ a, 0 < c a) :
    Hyp (fun u h => ∑ a, c a * T a u h) := by
  obtain ⟨a, u, h, hau, hah, huh⟩ := h3
  have hcard : 3 ≤ Fintype.card ι := by
    have hsub : ({a, u, h} : Finset ι).card ≤ Fintype.card ι := Finset.card_le_univ _
    have hcard3 : ({a, u, h} : Finset ι).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hau, hah]),
        Finset.card_insert_of_notMem (by simp [huh]), Finset.card_singleton]
    omega
  exact hyp_cubic_contract_pos hcard T hs1 hs2 hpos hzero hslice c hc

omit [DecidableEq ι] in
/-- INTERNAL: `Hyp` passes to the limit `ε ↓ 0` of `Q + ε P`.
TEXLINE: sections/signatures.tex:165-167 -/
theorem hyp_of_eps (Q P : ι → ι → ℝ) (h : ∀ ε : ℝ, 0 < ε → Hyp (fun u v => Q u v + ε * P u v)) :
    Hyp Q := by
  intro u w hu
  have hlin : ∀ (ε : ℝ) (x y : ι → ℝ),
      qf (fun u v => Q u v + ε * P u v) x y = qf Q x y + ε * qf P x y := by
    intro ε x y
    simp only [qf, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  by_contra hlt
  push Not at hlt
  have hc1 : Tendsto (fun ε : ℝ => qf Q u u + ε * qf P u u) (𝓝[>] 0) (𝓝 (qf Q u u)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have : Continuous (fun ε : ℝ => qf Q u u + ε * qf P u u) := by fun_prop
    simpa using this.tendsto 0
  have hc2 : Tendsto (fun ε : ℝ => (qf Q u u + ε * qf P u u) * (qf Q w w + ε * qf P w w) -
      (qf Q u w + ε * qf P u w) ^ 2) (𝓝[>] 0)
      (𝓝 (qf Q u u * qf Q w w - qf Q u w ^ 2)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have : Continuous (fun ε : ℝ => (qf Q u u + ε * qf P u u) * (qf Q w w + ε * qf P w w) -
      (qf Q u w + ε * qf P u w) ^ 2) := by fun_prop
    simpa using this.tendsto 0
  have e1 := hc1.eventually_const_lt hu
  have e2 := hc2.eventually_const_lt (by linarith : (0 : ℝ) < _)
  have e3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, h1, h2, h3⟩ := (e1.and (e2.and e3)).exists
  have := h ε h3 u w (by rw [hlin]; exact h1)
  rw [hlin, hlin, hlin] at this
  linarith

/-- **Full-matrix cubic contraction** (`lem:binary-contraction`, last assertion): the
contraction of a positive symmetric cubic tensor with `Hyp` slices along a nonnegative
vector satisfies `Hyp` on the full index set.
PAPER: sections/signatures.tex:120-170 -/
theorem cubic_contraction (T : ι → ι → ι → ℝ)
    (hs1 : ∀ a u h, T a u h = T u a h) (hs2 : ∀ a u h, T a u h = T a h u)
    (hpos : ∀ a u h, a ≠ u → a ≠ h → u ≠ h → 0 < T a u h)
    (hzero : ∀ a u h, (a = u ∨ a = h ∨ u = h) → T a u h = 0)
    (hslice : ∀ a, Hyp (T a)) (c : ι → ℝ) (hc : ∀ a, 0 ≤ c a) :
    Hyp (fun u h => ∑ a, c a * T a u h) := by
  by_cases h3 : ∃ a u h : ι, a ≠ u ∧ a ≠ h ∧ u ≠ h
  · refine hyp_of_eps _ (fun u h => ∑ a, T a u h) fun ε hε => ?_
    have := cubic_contraction_pos T hs1 hs2 hpos hzero hslice h3 (fun a => c a + ε)
      fun a => by linarith [hc a]
    convert this using 2 with u h
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  · have hT : ∀ a u h, T a u h = 0 := by
      intro a u h
      apply hzero
      by_contra hne
      push Not at hne
      exact h3 ⟨a, u, h, hne.1, hne.2.1, hne.2.2⟩
    intro u w hu
    simp [qf, hT] at hu

end Cellcounting.Analysis
