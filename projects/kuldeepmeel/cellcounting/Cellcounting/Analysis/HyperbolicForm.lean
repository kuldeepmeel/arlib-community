import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Quadratic forms with at most one positive eigenvalue

The elementary signature facts of `integer-signatures.tex:20-60`, stated without
eigenvalues.  A real symmetric matrix `Q` "has at most one positive eigenvalue"
exactly when it satisfies the reverse Cauchy–Schwarz inequality

  `0 < uᵀQu → (uᵀQu)(wᵀQw) ≤ (uᵀQw)²`,

which is how `Hyp Q` is defined here.  This form of the property is the
projection inequality `eq:signature-projection` itself, and it is the one the
balanced-summation argument uses.

* `hyp_of_kernel`: nonpositive on the kernel of one linear functional implies
  `Hyp` (the converse direction stated in the paper);
* `hyp_null_axis`: the boundary case `eᵀQe = 0`, `Qe ≠ 0`;
* `hyp_sub_psd`: subtracting a positive semidefinite matrix preserves `Hyp`;
* `hyp_congr`: congruence `Q ↦ c · D Q D` by a positive scalar and any diagonal;
* `hyp_rank_one_sub`: `𝟙𝟙ᵀ - Σ_G c_G 𝟙_G 𝟙_Gᵀ` with `c_G ≥ 0` satisfies `Hyp`.
-/

namespace Cellcounting.Analysis

open Finset

variable {ι : Type*} [Fintype ι]

/-- INTERNAL: the bilinear form `uᵀ Q w`. -/
def qf (Q : ι → ι → ℝ) (u w : ι → ℝ) : ℝ := ∑ i, ∑ h, u i * Q i h * w h

/-- INTERNAL: `Q` has at most one positive eigenvalue, in reverse Cauchy–Schwarz
form.
TEXLINE: sections/integer-signatures.tex:20-35 -/
def Hyp (Q : ι → ι → ℝ) : Prop :=
  ∀ u w : ι → ℝ, 0 < qf Q u u → qf Q u u * qf Q w w ≤ qf Q u w ^ 2

/-- INTERNAL: a symmetric matrix. -/
def QSymm (Q : ι → ι → ℝ) : Prop := ∀ i h, Q i h = Q h i

theorem qf_add_left (Q : ι → ι → ℝ) (u v w : ι → ℝ) :
    qf Q (u + v) w = qf Q u w + qf Q v w := by
  simp only [qf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem qf_add_right (Q : ι → ι → ℝ) (u v w : ι → ℝ) :
    qf Q u (v + w) = qf Q u v + qf Q u w := by
  simp only [qf, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem qf_smul_left (Q : ι → ι → ℝ) (c : ℝ) (u w : ι → ℝ) :
    qf Q (c • u) w = c * qf Q u w := by
  simp only [qf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun h _ => by ring

theorem qf_smul_right (Q : ι → ι → ℝ) (c : ℝ) (u w : ι → ℝ) :
    qf Q u (c • w) = c * qf Q u w := by
  simp only [qf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun h _ => by ring

theorem qf_symm {Q : ι → ι → ℝ} (hQ : QSymm Q) (u w : ι → ℝ) : qf Q u w = qf Q w u := by
  unfold qf
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun h _ => ?_
  rw [hQ]; ring

theorem qf_matrix_add (Q P : ι → ι → ℝ) (u w : ι → ℝ) :
    qf (fun i h => Q i h + P i h) u w = qf Q u w + qf P u w := by
  simp only [qf, mul_add, add_mul, Finset.sum_add_distrib]

theorem qf_matrix_sub (Q P : ι → ι → ℝ) (u w : ι → ℝ) :
    qf (fun i h => Q i h - P i h) u w = qf Q u w - qf P u w := by
  simp only [qf, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem qf_matrix_sum {κ : Type*} (s : Finset κ) (Q : κ → ι → ι → ℝ) (u w : ι → ℝ) :
    qf (fun i h => ∑ k ∈ s, Q k i h) u w = ∑ k ∈ s, qf (Q k) u w := by
  unfold qf
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm (s := s)]

/-- INTERNAL: expansion of the form on a combination of two vectors. -/
theorem qf_comb {Q : ι → ι → ℝ} (hQ : QSymm Q) (s t : ℝ) (u w : ι → ℝ) :
    qf Q (s • u + t • w) (s • u + t • w) =
      s ^ 2 * qf Q u u + 2 * s * t * qf Q u w + t ^ 2 * qf Q w w := by
  simp only [qf_add_left, qf_add_right, qf_smul_left, qf_smul_right]
  rw [qf_symm hQ w u]; ring

/-- INTERNAL: the projection inequality `eq:signature-projection`.
TEXLINE: sections/integer-signatures.tex:28-35 -/
theorem Hyp.proj {Q : ι → ι → ℝ} (h : Hyp Q) {u : ι → ℝ} (hu : 0 < qf Q u u) (w : ι → ℝ) :
    qf Q w w ≤ qf Q u w ^ 2 / qf Q u u := by
  rw [le_div_iff₀ hu, mul_comm]; exact h u w hu

/-- INTERNAL: a form nonpositive on the kernel of the functional `v ↦ Σ c_i v_i`
satisfies `Hyp`.
TEXLINE: sections/integer-signatures.tex:36-38 -/
theorem hyp_of_kernel {Q : ι → ι → ℝ} (hQ : QSymm Q) (c : ι → ℝ)
    (hker : ∀ v : ι → ℝ, ∑ i, c i * v i = 0 → qf Q v v ≤ 0) : Hyp Q := by
  intro u w hu
  set f : (ι → ℝ) → ℝ := fun v => ∑ i, c i * v i with hf
  have hfu : f u ≠ 0 := by
    intro h0; have := hker u h0; linarith
  set s0 := -(f w) / f u
  have hx : f (s0 • u + (1 : ℝ) • w) = 0 := by
    simp only [hf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    have : ∑ i, c i * (s0 * u i) = s0 * f u := by
      simp only [hf, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    have : ∑ i, c i * (1 * w i) = f w := by simp [hf]
    rw [this]; simp only [s0]; field_simp; ring
  have h1 := hker _ hx
  rw [qf_comb hQ] at h1
  nlinarith [sq_nonneg (qf Q u u * s0 + qf Q u w)]

/-- INTERNAL: the boundary case of the projection inequality: if `eᵀQe = 0` but
`Qe ≠ 0`, then `Q` is nonpositive on `{v : vᵀQe = 0}`.
TEXLINE: sections/integer-signatures.tex:40-52 -/
theorem hyp_null_axis {Q : ι → ι → ℝ} (hQ : QSymm Q) (h : Hyp Q) (e : ι → ℝ)
    (he : qf Q e e = 0) (hne : ∃ i, ∑ k, Q i k * e k ≠ 0) (v : ι → ℝ)
    (hv : qf Q v e = 0) : qf Q v v ≤ 0 := by
  by_contra hpos
  push Not at hpos
  set w : ι → ℝ := fun i => ∑ k, Q i k * e k with hw
  set n := qf Q e w with hn
  have hnpos : 0 < n := by
    have : n = ∑ i, w i ^ 2 := by
      simp only [hn, qf, hw]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hQ k i]; ring
    rw [this]
    obtain ⟨i, hi⟩ := hne
    have : 0 < w i ^ 2 := by positivity
    exact lt_of_lt_of_le this (Finset.single_le_sum (fun j _ => sq_nonneg (w j))
      (Finset.mem_univ i))
  set P := qf Q v v
  set β := qf Q v w
  set γ := qf Q w w
  set t := P * n / (|β ^ 2 - P * γ| + 1) with ht
  have htpos : 0 < t := by positivity
  have hkey := h v ((1 : ℝ) • e + t • w) hpos
  rw [qf_comb hQ, qf_add_right, qf_smul_right, qf_smul_right] at hkey
  rw [hv, he] at hkey
  -- `P (2 t n + t² γ) ≤ t² β²`, i.e. `2 P n ≤ t (β² - P γ)`.
  have h2 : 2 * P * n ≤ t * (β ^ 2 - P * γ) := by
    have : t * (2 * P * n) ≤ t * (t * (β ^ 2 - P * γ)) := by nlinarith
    have := le_of_mul_le_mul_left this htpos
    linarith
  have h3 : t * (β ^ 2 - P * γ) ≤ t * |β ^ 2 - P * γ| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) htpos.le
  have h4 : t * |β ^ 2 - P * γ| < P * n := by
    rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg (β ^ 2 - P * γ), mul_pos hpos hnpos]
  nlinarith [mul_pos hpos hnpos]

/-- INTERNAL: subtracting a positive semidefinite matrix preserves `Hyp`.
TEXLINE: sections/integer-signatures.tex:37-39 -/
theorem hyp_sub_psd {Q P : ι → ι → ℝ} (hQs : QSymm Q) (hPs : QSymm P) (hQ : Hyp Q)
    (hP : ∀ v, 0 ≤ qf P v v) : Hyp (fun i h => Q i h - P i h) := by
  have hRs : QSymm (fun i h => Q i h - P i h) := fun i h => by simp only [hQs i h, hPs i h]
  intro u w hu
  by_contra hlt
  push Not at hlt
  set R : ι → ι → ℝ := fun i h => Q i h - P i h
  set a' := qf R u u
  set b' := qf R u w
  set c' := qf R w w
  -- `R` is positive definite on `span {u, w}`.
  have hRpd : ∀ s t : ℝ, (s ≠ 0 ∨ t ≠ 0) → 0 < qf R (s • u + t • w) (s • u + t • w) := by
    intro s t hst
    rw [qf_comb hRs]
    have key : a' * (s ^ 2 * a' + 2 * s * t * b' + t ^ 2 * c') =
        (a' * s + b' * t) ^ 2 + (a' * c' - b' ^ 2) * t ^ 2 := by ring
    have : 0 < a' * (s ^ 2 * a' + 2 * s * t * b' + t ^ 2 * c') := by
      rw [key]
      rcases hst with hs | ht
      · by_cases ht : t = 0
        · subst ht; simp; positivity
        · have : 0 < (a' * c' - b' ^ 2) * t ^ 2 := mul_pos (by linarith) (by positivity)
          nlinarith [sq_nonneg (a' * s + b' * t)]
      · have : 0 < (a' * c' - b' ^ 2) * t ^ 2 := mul_pos (by linarith) (by positivity)
        nlinarith [sq_nonneg (a' * s + b' * t)]
    exact pos_of_mul_pos_right this hu.le
  have hQpd : ∀ s t : ℝ, (s ≠ 0 ∨ t ≠ 0) → 0 < qf Q (s • u + t • w) (s • u + t • w) := by
    intro s t hst
    have h1 := hRpd s t hst
    have : qf R (s • u + t • w) (s • u + t • w) =
        qf Q (s • u + t • w) (s • u + t • w) - qf P (s • u + t • w) (s • u + t • w) :=
      qf_matrix_sub Q P _ _
    linarith [hP (s • u + t • w)]
  have hau : 0 < qf Q u u := by
    have := hQpd 1 0 (Or.inl one_ne_zero); simpa using this
  have hcs := hQ u w hau
  have hx := hQpd (-(qf Q u w)) (qf Q u u) (Or.inr hau.ne')
  rw [qf_comb hQs] at hx
  nlinarith

/-- INTERNAL: congruence by a diagonal matrix and a positive scalar preserves
`Hyp`: `(c · d_i Q_ih d_h)`.
TEXLINE: sections/integer-signatures.tex:37-39 -/
theorem hyp_congr {Q : ι → ι → ℝ} (hQ : Hyp Q) (c : ℝ) (hc : 0 < c) (d : ι → ℝ) :
    Hyp (fun i h => c * (d i * Q i h * d h)) := by
  have hrw : ∀ u w : ι → ℝ, qf (fun i h => c * (d i * Q i h * d h)) u w =
      c * qf Q (fun i => d i * u i) (fun i => d i * w i) := by
    intro u w
    simp only [qf, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun h _ => by ring
  intro u w hu
  simp only [hrw] at hu ⊢
  have hu' : 0 < qf Q (fun i => d i * u i) (fun i => d i * u i) := pos_of_mul_pos_right hu hc.le
  have := hQ _ (fun i => d i * w i) hu'
  have hc2 : 0 ≤ c * c := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this hc2]

/-- INTERNAL: `Hyp` for `𝟙𝟙ᵀ - Σ_a c_a 𝟙_{G_a} 𝟙_{G_a}ᵀ` with `c_a ≥ 0`: the
right side of `eq:laminar-rank-one`.
TEXLINE: sections/integer-signatures.tex:120-140 -/
theorem hyp_rank_one_sub {α : Type*} (A : Finset α) (G : α → Finset ι) (c : α → ℝ)
    (hc : ∀ a ∈ A, 0 ≤ c a) [DecidableEq ι] :
    Hyp (fun i h => 1 - ∑ a ∈ A, if i ∈ G a ∧ h ∈ G a then c a else 0) := by
  apply hyp_of_kernel (c := fun _ => 1)
  · intro i h
    simp only [and_comm]
  · intro v hv
    simp only [one_mul] at hv
    have hone : qf (fun _ _ => (1 : ℝ)) v v = (∑ i, v i) ^ 2 := by
      simp only [qf, mul_one, sq, Finset.sum_mul_sum]
    have hG : ∀ a, qf (fun i h => if i ∈ G a ∧ h ∈ G a then c a else 0) v v =
        c a * (∑ i ∈ G a, v i) ^ 2 := by
      intro a
      have h1 : ∀ i h, (if i ∈ G a ∧ h ∈ G a then c a else 0) =
          c a * ((if i ∈ G a then 1 else 0) * (if h ∈ G a then 1 else 0)) := by
        intro i h; by_cases hi : i ∈ G a <;> by_cases hh : h ∈ G a <;> simp [hi, hh]
      have h2 : ∑ i ∈ G a, v i = ∑ i, v i * (if i ∈ G a then 1 else 0) := by
        simp [mul_ite, Finset.sum_ite_mem]
      rw [h2, sq, Finset.sum_mul_sum, Finset.mul_sum]
      unfold qf
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      simp only [h1]; ring
    have hexp := qf_matrix_sub (fun _ _ => (1 : ℝ))
      (fun i h => ∑ a ∈ A, if i ∈ G a ∧ h ∈ G a then c a else 0) v v
    rw [hexp, hone, hv, qf_matrix_sum A (fun a i h => if i ∈ G a ∧ h ∈ G a then c a else 0)]
    simp only [hG]
    have : 0 ≤ ∑ a ∈ A, c a * (∑ i ∈ G a, v i) ^ 2 :=
      Finset.sum_nonneg fun a ha => mul_nonneg (hc a ha) (sq_nonneg _)
    linarith

end Cellcounting.Analysis
