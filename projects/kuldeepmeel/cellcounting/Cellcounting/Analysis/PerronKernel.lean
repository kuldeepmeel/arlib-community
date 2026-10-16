import Cellcounting.Analysis.HyperbolicForm

/-!
# The maximum-principle step of `lem:binary-contraction` (`signatures.tex:146-162`)

Let `M` be a symmetric matrix with strictly positive off-diagonal entries and `a` a
strictly positive vector with `m := M a` strictly positive.  Put `d_i = m_i / a_i`, so
that `a` is an eigenvector of the pencil `M x = λ D x` with eigenvalue one.  If `M`
satisfies the projection inequality `xᵀMx ≤ Σ_i a_i (Mx)_i² / m_i = xᵀ M D⁻¹ M x`
(`eq:cubic-projection`), then `M` is nonpositive on the hyperplane `{x : mᵀx = 0}`.

This is the paper's argument "the maximum principle bounds the eigenvalues by one, the
eigenvalue one is simple, and `λ ≤ λ²` forces every positive eigenvalue to be at least
one", phrased without eigen-decompositions:

* `perron_dirichlet`: `Σ_i d_i x_i² - xᵀMx = ½ Σ_{i,h} M_ih a_i a_h (x_i/a_i - x_h/a_h)²`
  (the maximum principle: generalized eigenvalues are at most one, and equality forces
  `x ∝ a` by irreducibility);
* `perron_kernel`: maximize `xᵀMx` on the compact set `{mᵀx = 0, Σ d_i x_i² = 1}`; a
  maximizer with positive value `λ` is a generalized eigenvector (`Mx = λ D x`, by a
  first-variation argument), so the projection inequality gives `λ ≤ λ²`, the Dirichlet
  identity gives `λ ≤ 1`, hence `λ = 1` and `x ∝ a`, contradicting `mᵀx = 0`.
-/

namespace Cellcounting.Analysis

open Finset

variable {ι : Type*} [Fintype ι]

/-- INTERNAL: the Dirichlet identity for the pencil `(M, D)` with `D a = M a`.
TEXLINE: sections/signatures.tex:151-157 -/
theorem perron_dirichlet (M : ι → ι → ℝ) (hM : QSymm M) (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (x : ι → ℝ) :
    ∑ i, (∑ k, M i k * a k) / a i * x i ^ 2 - qf M x x =
      (∑ i, ∑ h, M i h * a i * a h * (x i / a i - x h / a h) ^ 2) / 2 := by
  have hterm : ∀ i h, M i h * a i * a h * (x i / a i - x h / a h) ^ 2 =
      M i h * a h / a i * x i ^ 2 + M i h * a i / a h * x h ^ 2 - 2 * (x i * M i h * x h) := by
    intro i h
    have := (ha i).ne'; have := (ha h).ne'
    field_simp
    ring
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h1 : ∑ i, ∑ h, M i h * a h / a i * x i ^ 2 = ∑ i, (∑ k, M i k * a k) / a i * x i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div, Finset.sum_mul]
  have h2 : ∑ i, ∑ h, M i h * a i / a h * x h ^ 2 = ∑ i, (∑ k, M i k * a k) / a i * x i ^ 2 := by
    rw [Finset.sum_comm, ← h1]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun h _ => ?_
    rw [hM h i]
  have h3 : ∑ i, ∑ h, 2 * (x i * M i h * x h) = 2 * qf M x x := by
    simp only [qf, Finset.mul_sum]
  rw [h1, h2, h3]
  ring

/-- INTERNAL: the generalized eigenvalues of `(M, D)` are at most one: `xᵀMx ≤ Σ d_i x_i²`.
TEXLINE: sections/signatures.tex:151-157 -/
theorem perron_dirichlet_le (M : ι → ι → ℝ) (hM : QSymm M) (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hoff : ∀ i h, i ≠ h → 0 < M i h) (x : ι → ℝ) :
    qf M x x ≤ ∑ i, (∑ k, M i k * a k) / a i * x i ^ 2 := by
  have h := perron_dirichlet M hM a ha x
  have hnn : 0 ≤ ∑ i, ∑ h, M i h * a i * a h * (x i / a i - x h / a h) ^ 2 := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun h _ => ?_
    by_cases hih : i = h
    · subst hih; simp
    · exact mul_nonneg (mul_nonneg (mul_nonneg (hoff i h hih).le (ha i).le) (ha h).le)
        (sq_nonneg _)
  linarith

/-- INTERNAL: equality in `perron_dirichlet_le` forces `x ∝ a` (irreducibility: every
off-diagonal entry is positive).
TEXLINE: sections/signatures.tex:151-157 -/
theorem perron_dirichlet_eq (M : ι → ι → ℝ) (hM : QSymm M) (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hoff : ∀ i h, i ≠ h → 0 < M i h) (x : ι → ℝ)
    (heq : qf M x x = ∑ i, (∑ k, M i k * a k) / a i * x i ^ 2) (i h : ι) :
    x i / a i = x h / a h := by
  have hid := perron_dirichlet M hM a ha x
  rw [heq, sub_self] at hid
  have hterm : ∀ i h, 0 ≤ M i h * a i * a h * (x i / a i - x h / a h) ^ 2 := by
    intro i h
    by_cases hih : i = h
    · subst hih; simp
    · exact mul_nonneg (mul_nonneg (mul_nonneg (hoff i h hih).le (ha i).le) (ha h).le)
        (sq_nonneg _)
  have hsum : ∑ i, ∑ h, M i h * a i * a h * (x i / a i - x h / a h) ^ 2 = 0 := by linarith
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    Finset.sum_nonneg fun h _ => hterm i h).mp hsum i (Finset.mem_univ i)
  have hent := (Finset.sum_eq_zero_iff_of_nonneg fun h _ => hterm i h).mp hrow h
    (Finset.mem_univ h)
  by_cases hih : i = h
  · rw [hih]
  · have hc : 0 < M i h * a i * a h := mul_pos (mul_pos (hoff i h hih) (ha i)) (ha h)
    have : (x i / a i - x h / a h) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hent with h0 | h0
      · exact absurd h0 hc.ne'
      · exact h0
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith

/-- INTERNAL: the maximum-principle step of `lem:binary-contraction`.  A symmetric
matrix `M` with positive off-diagonal entries, positive `m = M a` for a positive vector
`a`, satisfying the projection inequality `xᵀMx ≤ Σ_i a_i (Mx)_i² / m_i`
(`eq:cubic-projection`), is nonpositive on the hyperplane `mᵀx = 0`.
TEXLINE: sections/signatures.tex:146-162 -/
theorem perron_kernel (M : ι → ι → ℝ) (hM : QSymm M) (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hoff : ∀ i h, i ≠ h → 0 < M i h) (hmass : ∀ i, 0 < ∑ k, M i k * a k)
    (hproj : ∀ x : ι → ℝ,
      qf M x x ≤ ∑ i, a i * (∑ k, M i k * x k) ^ 2 / ∑ k, M i k * a k)
    (x : ι → ℝ) (hx : ∑ i, (∑ k, M i k * a k) * x i = 0) : qf M x x ≤ 0 := by
  set m : ι → ℝ := fun i => ∑ k, M i k * a k with hm_def
  set d : ι → ℝ := fun i => m i / a i with hd_def
  have hd : ∀ i, 0 < d i := fun i => div_pos (hmass i) (ha i)
  set E : (ι → ℝ) → ℝ := fun y => ∑ i, d i * y i ^ 2 with hE_def
  set L : (ι → ℝ) → ℝ := fun y => ∑ i, m i * y i with hL_def
  have hdir : ∀ y, qf M y y ≤ E y := fun y => perron_dirichlet_le M hM a ha hoff y
  have hE0 : ∀ y, 0 ≤ E y := fun y =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hd i).le (sq_nonneg _)
  have hEzero : ∀ y, E y = 0 → ∀ i, y i = 0 := by
    intro y hy i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_nonneg (hd i).le (sq_nonneg (y i))).mp hy i (Finset.mem_univ i)
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (hd i).ne'
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
  have hqf0 : ∀ y : ι → ℝ, (∀ i, y i = 0) → qf M y y = 0 := by
    intro y hy; simp [qf, hy]
  have hLsmul : ∀ (s : ℝ) y, L (s • y) = s * L y := by
    intro s y; simp only [hL_def, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hEsmul : ∀ (s : ℝ) y, E (s • y) = s ^ 2 * E y := by
    intro s y; simp only [hE_def, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hqfsmul : ∀ (s : ℝ) y, qf M (s • y) (s • y) = s ^ 2 * qf M y y := by
    intro s y; rw [qf_smul_left, qf_smul_right]; ring
  -- normalization onto `S`
  set S : Set (ι → ℝ) := {y | L y = 0 ∧ E y = 1} with hS_def
  have hnorm : ∀ y, L y = 0 → 0 < E y →
      (1 / Real.sqrt (E y)) • y ∈ S ∧
        qf M ((1 / Real.sqrt (E y)) • y) ((1 / Real.sqrt (E y)) • y) = qf M y y / E y := by
    intro y hy hEy
    have hs : (1 / Real.sqrt (E y)) ^ 2 = 1 / E y := by
      rw [div_pow, Real.sq_sqrt hEy.le, one_pow]
    refine ⟨⟨by rw [hLsmul, hy, mul_zero], ?_⟩, ?_⟩
    · rw [hEsmul, hs]; field_simp
    · rw [hqfsmul, hs]; ring
  by_contra hneg
  push Not at hneg
  have hEx : 0 < E x := by
    rcases (hE0 x).lt_or_eq with h | h
    · exact h
    · exact absurd (hqf0 x (hEzero x h.symm)) hneg.ne'
  -- compactness of `S`
  have hLc : Continuous L :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)
  have hEc : Continuous E :=
    continuous_finsetSum _ fun i _ => continuous_const.mul ((continuous_apply i).pow 2)
  have hqfc : Continuous fun y : ι → ℝ => qf M y y :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun h _ =>
      ((continuous_apply i).mul continuous_const).mul (continuous_apply h)
  have hSclosed : IsClosed S :=
    (isClosed_eq hLc continuous_const).inter (isClosed_eq hEc continuous_const)
  have hSbdd : Bornology.IsBounded S := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨∑ i, (1 + 1 / d i), fun y hy => ?_⟩
    have hC : ∀ i, 0 ≤ 1 + 1 / d i := fun i => by have := hd i; positivity
    rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => hC i)]
    intro i
    rw [Real.norm_eq_abs]
    have h1 : d i * y i ^ 2 ≤ 1 := by
      rw [← hy.2]
      exact Finset.single_le_sum (f := fun i => d i * y i ^ 2)
        (fun i _ => mul_nonneg (hd i).le (sq_nonneg _)) (Finset.mem_univ i)
    have h2 : y i ^ 2 ≤ 1 / d i := by
      rw [le_div_iff₀ (hd i)]; linarith
    have h3 : |y i| ≤ 1 + y i ^ 2 := by
      nlinarith [sq_abs (y i), abs_nonneg (y i), sq_nonneg (|y i| - 1)]
    have h4 : 1 + 1 / d i ≤ ∑ i, (1 + 1 / d i) :=
      Finset.single_le_sum (f := fun i => 1 + 1 / d i) (fun i _ => hC i) (Finset.mem_univ i)
    linarith
  have hScpt : IsCompact S := Metric.isCompact_of_isClosed_isBounded hSclosed hSbdd
  obtain ⟨hx1, hx2⟩ := hnorm x hx hEx
  obtain ⟨xs, hxs, hmax⟩ := hScpt.exists_isMaxOn ⟨_, hx1⟩ hqfc.continuousOn
  set lam := qf M xs xs with hlam_def
  have hlam_pos : 0 < lam := by
    have := hmax hx1
    simp only [Set.mem_ofPred_eq] at this
    rw [hx2] at this
    exact lt_of_lt_of_le (div_pos hneg hEx) this
  -- every vector of the hyperplane obeys `yᵀMy ≤ λ E y`
  have hhom : ∀ y, L y = 0 → qf M y y ≤ lam * E y := by
    intro y hy
    rcases (hE0 y).lt_or_eq with hEy | hEy
    · obtain ⟨hy1, hy2⟩ := hnorm y hy hEy
      have := hmax hy1
      simp only [Set.mem_ofPred_eq] at this
      rw [hy2, div_le_iff₀ hEy] at this
      exact this
    · rw [hqf0 y (hEzero y hEy.symm), ← hEy, mul_zero]
  have hxsL : L xs = 0 := hxs.1
  have hxsE : E xs = 1 := hxs.2
  -- first variation: `λ Σ d_i xs_i z_i = xsᵀ M z` on the hyperplane
  have hvar : ∀ z, L z = 0 → lam * ∑ i, d i * xs i * z i - qf M xs z = 0 := by
    intro z hz
    set B := lam * ∑ i, d i * xs i * z i - qf M xs z
    set G := lam * E z - qf M z z
    have hquad : ∀ t : ℝ, 0 ≤ 2 * t * B + t ^ 2 * G := by
      intro t
      have hL' : L ((1 : ℝ) • xs + t • z) = 0 := by
        simp only [hL_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
          Finset.sum_add_distrib]
        have e1 : ∑ i, m i * (1 * xs i) = L xs := by simp [hL_def]
        have e2 : ∑ i, m i * (t * z i) = t * L z := by
          simp only [hL_def, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
        rw [e1, e2, hxsL, hz, mul_zero, add_zero]
      have h1 := hhom _ hL'
      rw [qf_comb hM] at h1
      have hE' : E ((1 : ℝ) • xs + t • z) =
          E xs + 2 * t * ∑ i, d i * xs i * z i + t ^ 2 * E z := by
        simp only [hE_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hE', hxsE] at h1
      simp only [B, G]
      nlinarith
    have hG1 : 0 < |G| + 1 := by positivity
    have := hquad (-B / (|G| + 1))
    have hB2 : B ^ 2 * (|G| + 2) ≤ 0 := by
      have h' : 0 ≤ (2 * (-B / (|G| + 1)) * B + (-B / (|G| + 1)) ^ 2 * G) * (|G| + 1) ^ 2 :=
        mul_nonneg this (by positivity)
      have heq : (2 * (-B / (|G| + 1)) * B + (-B / (|G| + 1)) ^ 2 * G) * (|G| + 1) ^ 2 =
          -2 * B ^ 2 * (|G| + 1) + B ^ 2 * G := by
        field_simp
      rw [heq] at h'
      nlinarith [le_abs_self G, sq_nonneg B]
    have : B ^ 2 ≤ 0 := by
      by_contra hc; push Not at hc
      have : 0 < B ^ 2 * (|G| + 2) := mul_pos hc (by positivity)
      linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg B))
  -- the residual `r = λ D xs - M xs` vanishes
  set r : ι → ℝ := fun i => lam * d i * xs i - ∑ k, M i k * xs k with hr_def
  have hzr : ∀ z, ∑ i, z i * r i = lam * ∑ i, d i * xs i * z i - qf M xs z := by
    intro z
    rw [qf_symm hM xs z]
    simp only [hr_def, qf, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hdm : ∀ i, a i * d i = m i := fun i => by
    simp only [hd_def]; field_simp [(ha i).ne']
  have har : ∑ i, a i * r i = 0 := by
    rw [hzr a]
    have e1 : ∑ i, d i * xs i * a i = L xs := by
      simp only [hL_def]; exact Finset.sum_congr rfl fun i _ => by rw [← hdm i]; ring
    have e2 : qf M xs a = L xs := by
      simp only [qf, hL_def, hm_def]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e1, e2, hxsL]; ring
  have hι : Nonempty ι := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · simp [qf] at hneg
    · exact hι
  have hLa : 0 < L a := Finset.sum_pos (fun i _ => mul_pos (hmass i) (ha i))
    Finset.univ_nonempty
  have hr0 : ∀ i, r i = 0 := by
    set s0 := L r / L a
    set z : ι → ℝ := fun i => r i - s0 * a i with hz_def
    have hzL : L z = 0 := by
      have : L z = L r - s0 * L a := by
        simp only [hL_def, hz_def, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
        congr 1; exact Finset.sum_congr rfl fun i _ => by ring
      rw [this]; simp only [s0]; field_simp; ring
    have h1 := hzr z
    rw [hvar z hzL] at h1
    have h2 : ∑ i, z i * r i = ∑ i, r i ^ 2 - s0 * ∑ i, a i * r i := by
      simp only [hz_def, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
    rw [har, mul_zero, sub_zero, h1] at h2
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (r i)).mp h2.symm i
      (Finset.mem_univ i)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have hMxs : ∀ i, ∑ k, M i k * xs k = lam * d i * xs i := fun i => by
    have := hr0 i; simp only [hr_def] at this; linarith
  -- the projection inequality gives `λ ≤ λ²`
  have hp := hproj xs
  have hp' : ∑ i, a i * (∑ k, M i k * xs k) ^ 2 / ∑ k, M i k * a k = lam ^ 2 * E xs := by
    simp only [hMxs, hE_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hmi : (∑ k, M i k * a k) = a i * d i := (hdm i).symm
    rw [hmi]
    have := (ha i).ne'; have := (hd i).ne'
    field_simp
  rw [hp', hxsE, mul_one] at hp
  have hlam1 : 1 ≤ lam := by nlinarith
  have hlam2 : lam ≤ 1 := by have := hdir xs; rw [hxsE] at this; exact this
  have heq : qf M xs xs = ∑ i, (∑ k, M i k * a k) / a i * xs i ^ 2 := by
    have : E xs = ∑ i, (∑ k, M i k * a k) / a i * xs i ^ 2 := rfl
    rw [← this, hxsE]; linarith
  -- equality forces `xs ∝ a`, which is incompatible with `mᵀxs = 0`
  have hprop := perron_dirichlet_eq M hM a ha hoff xs heq
  obtain ⟨i0⟩ := hι
  set t := xs i0 / a i0
  have hxt : ∀ i, xs i = t * a i := by
    intro i
    have hq := hprop i i0
    have hai := (ha i).ne'
    simp only [t]
    rw [← hq]; field_simp
  have hLt : L xs = t * L a := by
    simp only [hL_def, hxt, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have ht0 : t = 0 := by
    rw [hxsL] at hLt
    rcases mul_eq_zero.mp hLt.symm with h | h
    · exact h
    · exact absurd h hLa.ne'
  have : E xs = 0 := by
    simp only [hE_def, hxt, ht0, zero_mul]; simp
  rw [hxsE] at this
  exact one_ne_zero this

end Cellcounting.Analysis
