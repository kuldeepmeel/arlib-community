import Cellcounting.Analysis.HyperbolicForm

/-!
# Integer signature under balanced summation (`lem:integer-signature`)

`integer-signatures.tex:62-300`, removal assertion.  Coordinates are a finite
type `ι`; a *display* is an integer vector `z : ι → ℤ`.  A weight
`W : (ι → ℤ) → ℝ` is `Good m S r` when it vanishes off the box-valid displays
of total `r` supported on the active coordinates `S`, is positive on them, and
at every valid display of total `r + 2` its two-removal matrix
`(W (z - e_i - e_h))_{i,h}` satisfies `Hyp` (at most one positive eigenvalue).

* `good_laminar` is the case without summation: a positive product of
  log-concave factors of the coordinate sums over a laminar family.
* `good_sumPair` is the induction step: summing one pair `{a, b}` of equal
  capacity `M ≥ 1` at balance keeps the weight `Good`.

Coordinates that have been summed are kept in `ι` but leave the active set, so
the rows and columns of the removal matrix at them vanish.
-/

namespace Cellcounting.Analysis

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- INTERNAL: a box-valid display of total `r` supported on the active set `S`. -/
def Valid (m : ι → ℤ) (S : Finset ι) (r : ℤ) (z : ι → ℤ) : Prop :=
  (∀ i, 0 ≤ z i) ∧ (∀ i ∈ S, z i ≤ m i) ∧ (∀ i, i ∉ S → z i = 0) ∧ ∑ i, z i = r

/-- INTERNAL: the two-removal matrix `(W (z - e_i - e_h))_{i,h}` of
`eq:integer-removal-signature`. -/
def remMat (W : (ι → ℤ) → ℝ) (z : ι → ℤ) : ι → ι → ℝ :=
  fun i h => W (z - Pi.single i 1 - Pi.single h 1)

/-- INTERNAL: the weight vanishes off the valid displays, is positive on them,
and has the removal signature property at total `r + 2`.
TEXLINE: sections/integer-signatures.tex:90-110 -/
def Good (m : ι → ℤ) (S : Finset ι) (r : ℤ) (W : (ι → ℤ) → ℝ) : Prop :=
  (∀ z, ¬ Valid m S r z → W z = 0) ∧ (∀ z, Valid m S r z → 0 < W z) ∧
    ∀ z, Valid m S (r + 2) z → Hyp (remMat W z)

/-- INTERNAL: summing the pair `{a, b}` of capacity `M` at balance:
profiles `(k, M - k)`, `0 ≤ k ≤ M`.
TEXLINE: sections/integer-signatures.tex:84-89 -/
noncomputable def sumPair (a b : ι) (M : ℕ) (W : (ι → ℤ) → ℝ) : (ι → ℤ) → ℝ := fun z =>
  if z a = 0 ∧ z b = 0 then
    ∑ k ∈ Finset.range (M + 1), W (z + Pi.single a (k : ℤ) + Pi.single b ((M : ℤ) - k))
  else 0

theorem remMat_symm (W : (ι → ℤ) → ℝ) (z : ι → ℤ) : QSymm (remMat W z) := by
  intro i h; simp only [remMat, sub_right_comm]

theorem Good.nonneg {m : ι → ℤ} {S : Finset ι} {r : ℤ} {W : (ι → ℤ) → ℝ}
    (hW : Good m S r W) (z : ι → ℤ) : 0 ≤ W z := by
  by_cases h : Valid m S r z
  · exact (hW.2.1 z h).le
  · rw [hW.1 z h]

/-! ### Linear algebra with coordinate vectors -/

/-- INTERNAL: the real coordinate vector `e_i`. -/
noncomputable def ev (i : ι) : ι → ℝ := Pi.single i 1

theorem qf_ev_right (Q : ι → ι → ℝ) (v : ι → ℝ) (h : ι) :
    qf Q v (ev h) = ∑ i, v i * Q i h := by
  simp only [qf, ev, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem qf_ev_ev (Q : ι → ι → ℝ) (i h : ι) : qf Q (ev i) (ev h) = Q i h := by
  rw [qf_ev_right]
  simp only [ev, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- INTERNAL: evaluation of `Valid` from its four parts. -/
theorem valid_iff (m : ι → ℤ) (S : Finset ι) (r : ℤ) (z : ι → ℤ) :
    Valid m S r z ↔
      (∀ i, 0 ≤ z i) ∧ (∀ i ∈ S, z i ≤ m i) ∧ (∀ i, i ∉ S → z i = 0) ∧ ∑ i, z i = r :=
  Iff.rfl

theorem sum_single_int (a : ι) (k : ℤ) : ∑ i, (Pi.single a k : ι → ℤ) i = k := by
  simp [Pi.single_apply]

theorem Good.zero_of_neg {m : ι → ℤ} {S : Finset ι} {r : ℤ} {W : (ι → ℤ) → ℝ}
    (hW : Good m S r W) {w : ι → ℤ} (j : ι) (hj : w j < 0) : W w = 0 :=
  hW.1 w fun hv => by have := hv.1 j; omega

theorem qf_comm_of_symm {Q : ι → ι → ℝ} (hQ : QSymm Q) (u w : ι → ℝ) : qf Q u w = qf Q w u :=
  qf_symm hQ u w

/-- INTERNAL: expansion of `qf` on `v + s e_a + t e_b`. -/
theorem qf_expand {Q : ι → ι → ℝ} (hQ : QSymm Q) (v : ι → ℝ) (s t : ℝ) (a b : ι) :
    qf Q (v + s • ev a + t • ev b) (v + s • ev a + t • ev b) =
      qf Q v v + 2 * s * qf Q v (ev a) + 2 * t * qf Q v (ev b) + s ^ 2 * Q a a +
        2 * s * t * Q a b + t ^ 2 * Q b b := by
  simp only [qf_add_left, qf_add_right, qf_smul_left, qf_smul_right, qf_ev_ev]
  rw [qf_symm hQ (ev a) v, qf_symm hQ (ev b) v, hQ b a]; ring

theorem qf_expand_left {Q : ι → ι → ℝ} (hQ : QSymm Q) (v : ι → ℝ) (s t : ℝ) (a b c : ι) :
    qf Q (ev c) (v + s • ev a + t • ev b) = qf Q v (ev c) + s * Q a c + t * Q b c := by
  simp only [qf_add_right, qf_smul_right, qf_ev_ev]
  rw [qf_symm hQ (ev c) v, hQ c a, hQ c b]

/-- INTERNAL: the per-index telescoping inequality `eq:integer-telescoping`,
from the three projection bounds of `eq:integer-projection-bound`.
TEXLINE: sections/integer-signatures.tex:255-290 -/
theorem telescope_step (X Qv σm σp um u0 up g gm gp p1 p2 : ℝ)
    (hum : 0 ≤ um) (hup : 0 ≤ up)
    (hσm : σm = u0 * g - um * gm) (hσp : σp = up * gp - u0 * g)
    (hX : X = Qv + 2 * g * σm + 2 * (-g) * σp + g ^ 2 * um + 2 * g * (-g) * u0 +
      (-g) ^ 2 * up)
    (hp1 : p1 = σm + g * um + (-g) * u0) (hp2 : p2 = σp + g * u0 + (-g) * up)
    (H1 : 0 < um → um * X ≤ p1 ^ 2) (H2 : 0 < up → up * X ≤ p2 ^ 2)
    (H3 : 0 < um + 2 * u0 + up → (um + 2 * u0 + up) * X ≤ (p1 + p2) ^ 2)
    (hpos : 0 < um ∨ 0 < up ∨ 0 < u0) :
    Qv + 2 * u0 * g ^ 2 - um * gm ^ 2 - up * gp ^ 2 ≤ 0 := by
  subst hσm hσp
  have hp1' : p1 = um * (g - gm) := by rw [hp1]; ring
  have hp2' : p2 = up * (gp - g) := by rw [hp2]; ring
  have hXY : X = (Qv + 2 * u0 * g ^ 2 - um * gm ^ 2 - up * gp ^ 2) +
      um * (g - gm) ^ 2 + up * (g - gp) ^ 2 := by rw [hX]; ring
  rcases hpos with h | h | h
  · have h1 := H1 h
    rw [hp1'] at h1
    have : X ≤ um * (g - gm) ^ 2 := by
      have : um * X ≤ um * (um * (g - gm) ^ 2) := by nlinarith
      exact le_of_mul_le_mul_left this h
    nlinarith [mul_nonneg hup (sq_nonneg (g - gp))]
  · have h2 := H2 h
    rw [hp2'] at h2
    have : X ≤ up * (g - gp) ^ 2 := by
      have : up * X ≤ up * (up * (g - gp) ^ 2) := by
        have : (up * (gp - g)) ^ 2 = up * (up * (g - gp) ^ 2) := by ring
        linarith
      exact le_of_mul_le_mul_left this h
    nlinarith [mul_nonneg hum (sq_nonneg (g - gm))]
  · by_cases hm0 : 0 < um
    · have h1 := H1 hm0
      rw [hp1'] at h1
      have : X ≤ um * (g - gm) ^ 2 := by
        have : um * X ≤ um * (um * (g - gm) ^ 2) := by nlinarith
        exact le_of_mul_le_mul_left this hm0
      nlinarith [mul_nonneg hup (sq_nonneg (g - gp))]
    by_cases hp0 : 0 < up
    · have h2 := H2 hp0
      rw [hp2'] at h2
      have : X ≤ up * (g - gp) ^ 2 := by
        have : up * X ≤ up * (up * (g - gp) ^ 2) := by
          have : (up * (gp - g)) ^ 2 = up * (up * (g - gp) ^ 2) := by ring
          linarith
        exact le_of_mul_le_mul_left this hp0
      nlinarith [mul_nonneg hum (sq_nonneg (g - gm))]
    have hum0 : um = 0 := le_antisymm (not_lt.1 hm0) hum
    have hup0 : up = 0 := le_antisymm (not_lt.1 hp0) hup
    subst hum0 hup0
    have h3 := H3 (by linarith)
    rw [hp1', hp2'] at h3
    have : X ≤ 0 := by nlinarith
    rw [hXY] at this; nlinarith

section pair

variable {m : ι → ℤ} {S : Finset ι} {a b : ι} {M : ℕ}

/-- INTERNAL: lifting a display on the remaining coordinates by a pair profile. -/
theorem valid_add_pair (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hma : m a = M) (hmb : m b = M)
    {t : ℤ} {z : ι → ℤ} (hz : Valid m ((S.erase a).erase b) t z) (p q : ℤ) (hp : 0 ≤ p)
    (hpM : p ≤ M) (hq : 0 ≤ q) (hqM : q ≤ M) :
    Valid m S (t + p + q) (z + Pi.single a p + Pi.single b q) := by
  obtain ⟨h0, h1, h2, h3⟩ := hz
  have hza : z a = 0 := h2 a (by simp)
  have hzb : z b = 0 := h2 b (by simp)
  refine ⟨fun j => ?_, fun j hj => ?_, fun j hj => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.single_apply]
    have := h0 j; split_ifs <;> omega
  · simp only [Pi.add_apply, Pi.single_apply]
    by_cases hja : j = a
    · subst hja; simp [hab, hza]; omega
    by_cases hjb : j = b
    · subst hjb; simp [hja, hzb]; omega
    have := h1 j (by simp [hja, hjb, hj])
    simp [hja, hjb]; exact this
  · have hja : j ≠ a := fun h => hj (h ▸ ha)
    have hjb : j ≠ b := fun h => hj (h ▸ hb)
    simp only [Pi.add_apply, Pi.single_apply, hja, hjb, if_false, add_zero]
    exact h2 j (by simp [hj])
  · simp only [Pi.add_apply, Finset.sum_add_distrib, sum_single_int, h3]

/-- INTERNAL: removing one unit from a positive remaining coordinate. -/
theorem valid_sub_single {S' : Finset ι} {t : ℤ} {z : ι → ℤ} (hz : Valid m S' t z) (i : ι)
    (hi : 1 ≤ z i) : Valid m S' (t - 1) (z - Pi.single i 1) := by
  obtain ⟨h0, h1, h2, h3⟩ := hz
  have hiS : i ∈ S' := by by_contra h; have := h2 i h; omega
  refine ⟨fun j => ?_, fun j hj => ?_, fun j hj => ?_, ?_⟩
  · simp only [Pi.sub_apply, Pi.single_apply]
    have := h0 j; split_ifs with h <;> [subst h; skip] <;> omega
  · simp only [Pi.sub_apply, Pi.single_apply]
    have := h1 j hj; split_ifs <;> omega
  · have hji : j ≠ i := fun h => hj (h ▸ hiS)
    simp only [Pi.sub_apply, Pi.single_apply, hji, if_false, sub_zero]
    exact h2 j hj
  · simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_single_int, h3]

/-- INTERNAL: a display that is valid after adding a pair profile was valid on
the remaining coordinates. -/
theorem valid_of_add_pair (hab : a ≠ b) {r : ℤ} {z : ι → ℤ} (hza : z a = 0) (hzb : z b = 0)
    (p q : ℤ) (h : Valid m S r (z + Pi.single a p + Pi.single b q)) :
    Valid m ((S.erase a).erase b) (r - p - q) z := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨fun j => ?_, fun j hj => ?_, fun j hj => ?_, ?_⟩
  · by_cases hja : j = a
    · rw [hja, hza]
    by_cases hjb : j = b
    · rw [hjb, hzb]
    have := h0 j
    simpa [Pi.single_apply, hja, hjb] using this
  · simp only [Finset.mem_erase] at hj
    have := h1 j hj.2.2
    simpa [Pi.single_apply, hj.1, hj.2.1] using this
  · by_cases hja : j = a
    · rw [hja, hza]
    by_cases hjb : j = b
    · rw [hjb, hzb]
    have hjS : j ∉ S := by simpa [hja, hjb] using hj
    have := h2 j hjS
    simpa [Pi.single_apply, hja, hjb] using this
  · simp only [Pi.add_apply, Finset.sum_add_distrib, sum_single_int] at h3
    linarith

end pair


section step

variable {m : ι → ℤ} {S : Finset ι} {r : ℤ} {W : (ι → ℤ) → ℝ} {a b : ι} {M : ℕ}

/-- INTERNAL: the core of the balanced-summation step: on old vectors in the
kernel of `v ↦ vᵀ Σ_l S(l)`, the sum of the forms `N_k` is nonpositive.
TEXLINE: sections/integer-signatures.tex:200-300 -/
theorem sumPair_core (hW : Good m S r W) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hma : m a = M) (hmb : m b = M) (hM : 1 ≤ M) {z : ι → ℤ}
    (hz : Valid m ((S.erase a).erase b) (r - M + 2) z) (v : ι → ℝ) (hva : v a = 0)
    (hvb : v b = 0)
    (hv : ∑ i, (∑ l ∈ Finset.range M,
        W (z - Pi.single i 1 + Pi.single a (l : ℤ) + Pi.single b ((M : ℤ) - 1 - l))) * v i = 0) :
    ∑ k ∈ Finset.range (M + 1),
      qf (remMat W (z + Pi.single a (k : ℤ) + Pi.single b ((M : ℤ) - k))) v v ≤ 0 := by
  have hza : z a = 0 := hz.2.2.1 a (by simp)
  have hzb : z b = 0 := hz.2.2.1 b (by simp)
  set N : ℤ → ι → ι → ℝ := fun k => remMat W (z + Pi.single a k + Pi.single b ((M : ℤ) - k))
    with hNdef
  set Sl : ℤ → ι → ℝ := fun l i =>
    W (z - Pi.single i 1 + Pi.single a l + Pi.single b ((M : ℤ) - 1 - l)) with hSldef
  set u : ℤ → ℝ := fun k => W (z + Pi.single a (k - 1) + Pi.single b ((M : ℤ) - 1 - k))
    with hudef
  have hNhyp : ∀ k : ℤ, 0 ≤ k → k ≤ M → Hyp (N k) := by
    intro k hk0 hkM
    apply hW.2.2
    have := valid_add_pair ha hb hab hma hmb hz k ((M : ℤ) - k) hk0 hkM (by omega) (by omega)
    convert this using 1; ring
  have hNsym : ∀ k, QSymm (N k) := fun k => remMat_symm _ _
  -- entries of `N_k`
  have hNia : ∀ k i, N k i a = Sl (k - 1) i := by
    intro k i
    simp only [hNdef, hSldef, remMat]
    congr 1
    rw [show (M : ℤ) - 1 - (k - 1) = M - k by ring, Pi.single_sub (f := fun _ => ℤ) a k 1]; abel
  have hNib : ∀ k i, N k i b = Sl k i := by
    intro k i
    simp only [hNdef, hSldef, remMat]
    congr 1
    rw [show (M : ℤ) - 1 - k = M - k - 1 by ring, Pi.single_sub (f := fun _ => ℤ) b ((M : ℤ) - k) 1]
    abel
  have hNaa : ∀ k, N k a a = u (k - 1) := by
    intro k
    simp only [hNdef, hudef, remMat]
    congr 1
    rw [show (M : ℤ) - 1 - (k - 1) = M - k by ring, Pi.single_sub (f := fun _ => ℤ) a (k - 1) 1,
      Pi.single_sub (f := fun _ => ℤ) a k 1]; abel
  have hNab : ∀ k, N k a b = u k := by
    intro k
    simp only [hNdef, hudef, remMat]
    congr 1
    rw [show (M : ℤ) - 1 - k = M - k - 1 by ring, Pi.single_sub (f := fun _ => ℤ) a k 1,
      Pi.single_sub (f := fun _ => ℤ) b ((M : ℤ) - k) 1]
    abel
  have hNba : ∀ k, N k b a = u k := by
    intro k; rw [hNsym k b a, hNab]
  have hNbb : ∀ k, N k b b = u (k + 1) := by
    intro k
    simp only [hNdef, hudef, remMat]
    congr 1
    rw [show (k : ℤ) + 1 - 1 = k by ring, show (M : ℤ) - 1 - (k + 1) = M - k - 1 - 1 by ring,
      Pi.single_sub (f := fun _ => ℤ) b ((M : ℤ) - k - 1) 1,
      Pi.single_sub (f := fun _ => ℤ) b ((M : ℤ) - k) 1]
    abel
  -- signs and vanishing
  have hu_nn : ∀ k, 0 ≤ u k := fun k => hW.nonneg _
  have hu_low : ∀ k : ℤ, k ≤ 0 → u k = 0 := by
    intro k hk
    apply hW.zero_of_neg a
    simp [Pi.single_apply, hab, hza]; omega
  have hu_high : ∀ k : ℤ, (M : ℤ) ≤ k → u k = 0 := by
    intro k hk
    apply hW.zero_of_neg b
    simp [Pi.single_apply, hab.symm, hzb]; omega
  have hu_pos : ∀ k : ℤ, 1 ≤ k → k ≤ M - 1 → 0 < u k := by
    intro k hk1 hk2
    apply hW.2.1
    have := valid_add_pair ha hb hab hma hmb hz (k - 1) ((M : ℤ) - 1 - k) (by omega) (by omega)
      (by omega) (by omega)
    convert this using 1; ring
  have hSl_low : ∀ l : ℤ, l < 0 → ∀ i, Sl l i = 0 := by
    intro l hl i
    apply hW.zero_of_neg a
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, hab, if_false, hza, if_true]
    split_ifs <;> omega
  have hSl_high : ∀ l : ℤ, (M : ℤ) - 1 < l → ∀ i, Sl l i = 0 := by
    intro l hl i
    apply hW.zero_of_neg b
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, hab.symm, if_false, hzb, if_true]
    split_ifs <;> omega
  set σ : ℤ → ℝ := fun l => ∑ i, v i * Sl l i with hσdef
  have hσa : ∀ k, qf (N k) v (ev a) = σ (k - 1) := by
    intro k; rw [qf_ev_right]; simp only [hσdef, hNia]
  have hσb : ∀ k, qf (N k) v (ev b) = σ k := by
    intro k; rw [qf_ev_right]; simp only [hσdef, hNib]
  have hσ_low : ∀ l : ℤ, l < 0 → σ l = 0 := by
    intro l hl; simp only [hσdef, hSl_low l hl, mul_zero, Finset.sum_const_zero]
  have hσ_high : ∀ l : ℤ, (M : ℤ) - 1 < l → σ l = 0 := by
    intro l hl; simp only [hσdef, hSl_high l hl, mul_zero, Finset.sum_const_zero]
  have hPM : ∑ l ∈ Finset.range M, σ l = 0 := by
    rw [← hv]
    simp only [hσdef, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [hSldef]; ring
  rcases Nat.lt_or_ge M 2 with hM1 | hM2
  · -- width one
    have hM1' : M = 1 := by omega
    have hσ0 : σ 0 = 0 := by
      have := hPM; rw [hM1', Finset.sum_range_one] at this; exact_mod_cast this
    have hk : ∀ k : ℤ, (k = 0 ∨ k = 1) → qf (N k) v v ≤ 0 := by
      by_cases hex : ∃ i, Sl 0 i ≠ 0
      · obtain ⟨i0, hi0⟩ := hex
        intro k hk
        rcases hk with rfl | rfl
        · refine hyp_null_axis (hNsym 0) (hNhyp 0 le_rfl (by positivity)) (ev b) ?_ ⟨i0, ?_⟩ v ?_
          · rw [qf_ev_ev, hNbb]; exact hu_high _ (by push_cast; omega)
          · have : ∑ k, N 0 i0 k * ev b k = N 0 i0 b := by
              simp [ev, Pi.single_apply]
            rw [this, hNib]; exact hi0
          · rw [hσb]; exact hσ0
        · refine hyp_null_axis (hNsym 1) (hNhyp 1 (by norm_num) (by push_cast; omega)) (ev a) ?_
            ⟨i0, ?_⟩ v ?_
          · rw [qf_ev_ev, hNaa]; exact hu_low _ (by norm_num)
          · have : ∑ k, N 1 i0 k * ev a k = N 1 i0 a := by
              simp [ev, Pi.single_apply]
            rw [this, hNia]; simpa using hi0
          · rw [hσa]; simpa using hσ0
      · push Not at hex
        intro k hk
        apply le_of_eq
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun h _ => ?_
        by_cases hvi : v i = 0
        · simp [hvi]
        have hia : i ≠ a := fun h => hvi (h ▸ hva)
        have hib : i ≠ b := fun h => hvi (h ▸ hvb)
        by_cases hzi : z i = 0
        · have : N k i h = 0 := by
            apply hW.zero_of_neg i
            simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, hia, hib, if_false, hzi,
              if_true]
            split_ifs <;> omega
          rw [this]; ring
        · exfalso
          have hpos : 0 < Sl 0 i := by
            apply hW.2.1
            have h1 := valid_sub_single hz i (by have := hz.1 i; omega)
            have h2 := valid_add_pair ha hb hab hma hmb h1 0 ((M : ℤ) - 1 - 0) le_rfl
              (by positivity) (by omega) (by omega)
            convert h2 using 1; omega
          rw [hex i] at hpos; exact lt_irrefl _ hpos
    rw [hM1', Finset.sum_range_succ, Finset.sum_range_one]
    have h0 := hk 0 (Or.inl rfl)
    have h1 := hk 1 (Or.inr rfl)
    simp only [hNdef, hM1'] at h0 h1
    norm_num at h0 h1 ⊢
    linarith
  · -- width at least two: the cumulative-sum potentials `g_k`
    set P : ℕ → ℝ := fun n => ∑ l ∈ Finset.range n, σ l with hPdef
    set g : ℤ → ℝ := fun k => if 1 ≤ k ∧ k ≤ (M : ℤ) - 1 then P k.toNat / u k else 0 with hgdef
    have hug : ∀ k, u k * g k = if 1 ≤ k ∧ k ≤ (M : ℤ) - 1 then P k.toNat else 0 := by
      intro k
      simp only [hgdef]
      split_ifs with h
      · exact mul_div_cancel₀ _ (hu_pos k h.1 h.2).ne'
      · ring
    have hcum : ∀ l : ℤ, σ l = u (l + 1) * g (l + 1) - u l * g l := by
      intro l
      rw [hug, hug]
      by_cases hl0 : l < 0
      · rw [hσ_low l hl0, if_neg (by omega), if_neg (by omega)]; ring
      by_cases hlM : (M : ℤ) - 1 < l
      · rw [hσ_high l hlM, if_neg (by omega), if_neg (by omega)]; ring
      have hsucc : P (l + 1).toNat = P l.toNat + σ l := by
        rw [show (l + 1).toNat = l.toNat + 1 by omega, hPdef]
        simp only [Finset.sum_range_succ]
        congr 2; omega
      by_cases hl1 : l + 1 ≤ (M : ℤ) - 1
      · rw [if_pos ⟨by omega, hl1⟩]
        by_cases hl : 1 ≤ l
        · rw [if_pos ⟨hl, by omega⟩, hsucc]; ring
        · rw [if_neg (by omega), hsucc]
          have : l = 0 := by omega
          subst this
          simp [hPdef]
      · have hlM' : l = (M : ℤ) - 1 := by omega
        rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩]
        have : P (l + 1).toNat = 0 := by
          rw [show (l + 1).toNat = M by omega]; exact hPM
        rw [hsucc] at this; linarith
    -- per-index inequality
    have hstep : ∀ k : ℕ, k ≤ M →
        qf (N k) v v + 2 * u k * g k ^ 2 - u (k - 1) * g (k - 1) ^ 2 -
          u (k + 1) * g (k + 1) ^ 2 ≤ 0 := by
      intro k hkM
      set K : ℤ := (k : ℤ) with hK
      set V := v + g K • ev a + (-g K) • ev b
      have hH := hNhyp K (by rw [hK]; positivity) (by rw [hK]; exact_mod_cast hkM)
      refine telescope_step (qf (N K) V V) _ (σ (K - 1)) (σ K) (u (K - 1)) (u K) (u (K + 1))
        (g K) (g (K - 1)) (g (K + 1)) (qf (N K) (ev a) V) (qf (N K) (ev b) V)
        (hu_nn _) (hu_nn _) ?_ (hcum K) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · have := hcum (K - 1); rw [show K - 1 + 1 = K by ring] at this; exact this
      · rw [qf_expand (hNsym K), hσa, hσb, hNaa, hNab, hNbb]
      · rw [qf_expand_left (hNsym K), hσa, hNaa, hNba]
      · rw [qf_expand_left (hNsym K), hσb, hNab, hNbb]
      · intro h
        have := hH (ev a) V (by rw [qf_ev_ev, hNaa]; exact h)
        rwa [qf_ev_ev, hNaa] at this
      · intro h
        have := hH (ev b) V (by rw [qf_ev_ev, hNbb]; exact h)
        rwa [qf_ev_ev, hNbb] at this
      · intro h
        have hee : qf (N K) (ev a + ev b) (ev a + ev b) = u (K - 1) + 2 * u K + u (K + 1) := by
          rw [qf_add_left, qf_add_right, qf_add_right, qf_ev_ev, qf_ev_ev, qf_ev_ev, qf_ev_ev,
            hNaa, hNab, hNba, hNbb]; ring
        have := hH (ev a + ev b) V (by rw [hee]; exact h)
        have h2 : qf (N K) (ev a + ev b) V = qf (N K) (ev a) V + qf (N K) (ev b) V :=
          qf_add_left _ _ _ _
        rw [hee, h2] at this; exact this
      · by_cases hk0 : k = 0
        · right; left
          apply hu_pos <;> simp [K, hk0] <;> omega
        by_cases hkM' : k = M
        · left
          apply hu_pos <;> simp [K, hkM'] <;> omega
        · right; right
          apply hu_pos <;> simp only [K] <;> omega
    -- telescoping
    set φ : ℤ → ℝ := fun j => u j * g j ^ 2 with hφdef
    have hsum := Finset.sum_le_sum (s := Finset.range (M + 1)) fun k hk =>
      hstep k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
    have ht1 : ∑ k ∈ Finset.range (M + 1), (φ ((k : ℤ) + 1) - φ k) = φ ((M : ℤ) + 1) - φ 0 := by
      have := Finset.sum_range_sub (fun k : ℕ => φ (k : ℤ)) (M + 1)
      simpa using this
    have ht2 : ∑ k ∈ Finset.range (M + 1), (φ (k : ℤ) - φ ((k : ℤ) - 1)) = φ M - φ (-1) := by
      have := Finset.sum_range_sub (fun k : ℕ => φ ((k : ℤ) - 1)) (M + 1)
      simpa using this
    have hφ0 : φ 0 = 0 := by simp [hφdef, hu_low 0 le_rfl]
    have hφm1 : φ (-1) = 0 := by simp [hφdef, hu_low (-1) (by norm_num)]
    have hφM : φ M = 0 := by simp [hφdef, hu_high M le_rfl]
    have hφM1 : φ ((M : ℤ) + 1) = 0 := by simp [hφdef, hu_high ((M : ℤ) + 1) (by omega)]
    have hexp : ∑ k ∈ Finset.range (M + 1), (qf (N k) v v + 2 * u k * g k ^ 2 -
        u (k - 1) * g (k - 1) ^ 2 - u (k + 1) * g (k + 1) ^ 2) =
        ∑ k ∈ Finset.range (M + 1), qf (N k) v v -
          (∑ k ∈ Finset.range (M + 1), (φ ((k : ℤ) + 1) - φ k)) +
          (∑ k ∈ Finset.range (M + 1), (φ (k : ℤ) - φ ((k : ℤ) - 1))) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hφdef]; ring
    rw [hexp, ht1, ht2, hφ0, hφm1, hφM, hφM1] at hsum
    simp only [Finset.sum_const_zero, sub_zero, add_zero] at hsum
    simpa [hNdef] using hsum

/-- INTERNAL: the removal signature after summing one pair.
TEXLINE: sections/integer-signatures.tex:150-300 -/
theorem hyp_sumPair (hW : Good m S r W) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hma : m a = M) (hmb : m b = M) (hM : 1 ≤ M) {z : ι → ℤ}
    (hz : Valid m ((S.erase a).erase b) (r - M + 2) z) :
    Hyp (remMat (sumPair a b M W) z) := by
  have hza : z a = 0 := hz.2.2.1 a (by simp)
  have hzb : z b = 0 := hz.2.2.1 b (by simp)
  set pa : ι → ℝ := fun i => if i ≠ a ∧ i ≠ b then 1 else 0 with hpa
  set cc : ι → ℝ := fun i => ∑ l ∈ Finset.range M,
    W (z - Pi.single i 1 + Pi.single a (l : ℤ) + Pi.single b ((M : ℤ) - 1 - l))
  have hE : ∀ i h, remMat (sumPair a b M W) z i h = ∑ k ∈ Finset.range (M + 1),
      pa i * remMat W (z + Pi.single a (k : ℤ) + Pi.single b ((M : ℤ) - k)) i h * pa h := by
    intro i h
    simp only [remMat, sumPair, hpa]
    by_cases hi : i ≠ a ∧ i ≠ b
    · by_cases hh : h ≠ a ∧ h ≠ b
      · rw [if_pos]
        · refine Finset.sum_congr rfl fun k _ => ?_
          rw [if_pos hi, if_pos hh, one_mul, mul_one]
          congr 1; abel
        · simp [Pi.single_apply, hza, hzb, hi.1.symm, hi.2.symm, hh.1.symm, hh.2.symm]
      · rw [if_neg, eq_comm]
        · exact Finset.sum_eq_zero fun k _ => by rw [if_neg hh, mul_zero]
        · intro hc
          rcases not_and_or.1 hh with hh | hh <;> push Not at hh <;> subst hh
          · have := hc.1; simp [Pi.single_apply, hza, hi.1.symm] at this
          · have := hc.2; simp [Pi.single_apply, hzb, hi.2.symm] at this
    · rw [if_neg, eq_comm]
      · exact Finset.sum_eq_zero fun k _ => by rw [if_neg hi, zero_mul, zero_mul]
      · intro hc
        rcases not_and_or.1 hi with hi | hi <;> push Not at hi <;> subst hi
        · have := hc.1; simp [Pi.single_apply, hza] at this; split_ifs at this <;> omega
        · have := hc.2; simp [Pi.single_apply, hzb] at this; split_ifs at this <;> omega
  apply hyp_of_kernel (remMat_symm _ _) (fun i => pa i * cc i)
  intro v hv
  have hqE : qf (remMat (sumPair a b M W) z) v v = ∑ k ∈ Finset.range (M + 1),
      qf (remMat W (z + Pi.single a (k : ℤ) + Pi.single b ((M : ℤ) - k)))
        (fun i => pa i * v i) (fun i => pa i * v i) := by
    have : remMat (sumPair a b M W) z = fun i h => ∑ k ∈ Finset.range (M + 1),
        pa i * remMat W (z + Pi.single a (k : ℤ) + Pi.single b ((M : ℤ) - k)) i h * pa h :=
      funext fun i => funext fun h => hE i h
    rw [this, qf_matrix_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [qf]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun h _ => by ring
  rw [hqE]
  refine sumPair_core hW ha hb hab hma hmb hM hz _ (by simp [hpa]) (by simp [hpa]) ?_
  rw [← hv]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Balanced summation of one pair** (the induction step of
`lem:integer-signature`): summing a pair of equal capacity `M ≥ 1` at balance
keeps the weight `Good`, with the pair removed from the active set and the
total lowered by `M`.
PAPER: sections/integer-signatures.tex:150-300 -/
theorem good_sumPair (hW : Good m S r W) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hma : m a = M) (hmb : m b = M) (hM : 1 ≤ M) :
    Good m ((S.erase a).erase b) (r - M) (sumPair a b M W) := by
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · unfold sumPair
    split_ifs with h0
    · refine Finset.sum_eq_zero fun k _ => hW.1 _ fun hv => hz ?_
      have := valid_of_add_pair hab h0.1 h0.2 _ _ hv
      convert this using 1; ring
    · rfl
  · have hza : z a = 0 := hz.2.2.1 a (by simp)
    have hzb : z b = 0 := hz.2.2.1 b (by simp)
    unfold sumPair
    rw [if_pos ⟨hza, hzb⟩]
    apply Finset.sum_pos
    · intro k hk
      apply hW.2.1
      have hk' : k ≤ M := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have := valid_add_pair ha hb hab hma hmb hz (k : ℤ) ((M : ℤ) - k) (by positivity)
        (by exact_mod_cast hk') (by omega) (by omega)
      convert this using 1; ring
    · exact ⟨0, by simp⟩
  · exact hyp_sumPair hW ha hb hab hma hmb hM (by convert hz using 1)

end step

section laminar

/-- INTERNAL: telescoping along a chain, `eq:laminar-rank-one` entrywise:
`∏_{a ∈ C} γ_a = 1 - Σ_{a ∈ C} (1 - γ_a) ∏_{a' ∈ C, a ≺ a'} γ_{a'}` for any order
given by an injective key.
TEXLINE: sections/integer-signatures.tex:125-135 -/
theorem prod_telescope {α : Type*} [DecidableEq α] (f : α → ℕ) (hf : Function.Injective f)
    (γ : α → ℝ) (C : Finset α) :
    ∏ a ∈ C, γ a = 1 - ∑ a ∈ C, (1 - γ a) * ∏ a' ∈ C.filter (fun a' => f a < f a'), γ a' := by
  induction C using Finset.induction_on_min_value (f := f) with
  | empty => simp
  | insert a C haC hmin ih =>
    rw [Finset.prod_insert haC, Finset.sum_insert haC]
    have h1 : (insert a C).filter (fun a' => f a < f a') = C := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hlt⟩
        · exact absurd hlt (lt_irrefl _)
        · exact hx
      · intro hx
        refine ⟨Or.inr hx, lt_of_le_of_ne (hmin x hx) fun h => ?_⟩
        exact haC (hf h ▸ hx)
    have h2 : ∀ b ∈ C, (insert a C).filter (fun a' => f b < f a') =
        C.filter (fun a' => f b < f a') := by
      intro b hb
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hlt⟩
        · exact absurd (lt_of_lt_of_le hlt (hmin b hb)) (lt_irrefl _)
        · exact ⟨hx, hlt⟩
      · rintro ⟨hx, hlt⟩; exact ⟨Or.inr hx, hlt⟩
    rw [h1, Finset.sum_congr rfl fun b hb => by rw [h2 b hb]]
    have : ∑ x ∈ C, (1 - γ x) * ∏ a' ∈ C.filter (fun a' => f x < f a'), γ a' =
        1 - ∏ a ∈ C, γ a := by rw [ih]; ring
    rw [this]; ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- INTERNAL: the laminar product weight `eq:laminar-weight`, restricted to the
box-valid displays of total `R`.
TEXLINE: sections/integer-signatures.tex:66-80 -/
noncomputable def laminarWeight (m : ι → ℤ) (R : ℤ) (G : α → Finset ι) (ψ : α → ℤ → ℝ) :
    (ι → ℤ) → ℝ := fun z =>
  haveI := Classical.propDecidable (Valid m Finset.univ R z)
  if Valid m Finset.univ R z then ∏ a, ψ a (∑ i ∈ G a, z i) else 0

/-- INTERNAL: `Γ = (∏_{G ⊇ {i,h}} γ_G)` has at most one positive eigenvalue for a
laminar family and `0 < γ ≤ 1`.
TEXLINE: sections/integer-signatures.tex:120-140 -/
theorem hyp_laminar_gamma (G : α → Finset ι)
    (hlam : ∀ a a', G a ⊆ G a' ∨ G a' ⊆ G a ∨ Disjoint (G a) (G a')) (γ : α → ℝ)
    (hγ0 : ∀ a, 0 < γ a) (hγ1 : ∀ a, γ a ≤ 1) :
    Hyp (fun i h => ∏ a, if i ∈ G a ∧ h ∈ G a then γ a else 1) := by
  set N := Fintype.card α
  set f : α → ℕ := fun a => (G a).card * N + (Fintype.equivFin α a : ℕ) with hfdef
  have henc : ∀ a, (Fintype.equivFin α a : ℕ) < N := fun a => (Fintype.equivFin α a).2
  have hf : Function.Injective f := by
    intro a a' h
    simp only [hfdef] at h
    have h1 := henc a; have h2 := henc a'
    have hc : (G a).card = (G a').card := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have : (G a).card * N + N ≤ (G a').card * N := by nlinarith
        omega
      · have : (G a').card * N + N ≤ (G a).card * N := by nlinarith
        omega
    rw [hc] at h
    exact (Fintype.equivFin α).injective (Fin.ext (by omega))
  have hfmono : ∀ a a', f a < f a' → (G a).card ≤ (G a').card := by
    intro a a' h
    by_contra hlt; push Not at hlt
    have h1 := henc a; have h2 := henc a'
    simp only [hfdef] at h
    have : (G a').card * N + N ≤ (G a).card * N := by nlinarith
    omega
  set c : α → ℝ := fun a =>
    (1 - γ a) * ∏ a' ∈ Finset.univ.filter (fun a' => f a < f a' ∧ G a ⊆ G a'), γ a'
  have hc : ∀ a ∈ (Finset.univ : Finset α), 0 ≤ c a := fun a _ =>
    mul_nonneg (by linarith [hγ1 a]) (Finset.prod_nonneg fun a' _ => (hγ0 a').le)
  have hid : (fun i h => ∏ a, if i ∈ G a ∧ h ∈ G a then γ a else 1) =
      fun i h => 1 - ∑ a ∈ Finset.univ, if i ∈ G a ∧ h ∈ G a then c a else 0 := by
    funext i h
    set C := Finset.univ.filter (fun a => i ∈ G a ∧ h ∈ G a)
    rw [← Finset.prod_filter, ← Finset.sum_filter, prod_telescope f hf γ C]
    congr 1
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [c]
    congr 1
    refine Finset.prod_congr ?_ fun _ _ => rfl
    ext a'
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    constructor
    · rintro ⟨⟨hi', hh'⟩, hlt⟩
      refine ⟨hlt, ?_⟩
      rcases hlam a a' with hs | hs | hd
      · exact hs
      · have := Finset.eq_of_subset_of_card_le hs (hfmono a a' hlt)
        rw [this]
      · exact absurd hi' (Finset.disjoint_left.1 hd ha.1)
    · rintro ⟨hlt, hs⟩
      exact ⟨⟨hs ha.1, hs ha.2⟩, hlt⟩
  rw [hid]
  exact hyp_rank_one_sub Finset.univ G c hc

/-- INTERNAL: validity of a two-removal display when no pair has been summed. -/
theorem valid_remove_two {m : ι → ℤ} {R : ℤ} {z : ι → ℤ} (hz : Valid m Finset.univ (R + 2) z)
    (i h : ι) :
    Valid m Finset.univ R (z - Pi.single i 1 - Pi.single h 1) ↔
      1 ≤ z i ∧ 1 ≤ z h ∧ (i = h → 2 ≤ z i) := by
  obtain ⟨h0, h1, -, h3⟩ := hz
  constructor
  · rintro ⟨g0, -, -, -⟩
    have gi := g0 i; have gh := g0 h
    simp only [Pi.sub_apply, Pi.single_apply] at gi gh
    refine ⟨?_, ?_, fun hih => ?_⟩
    · split_ifs at gi <;> omega
    · split_ifs at gh <;> omega
    · subst hih; simp at gi; omega
  · rintro ⟨hi, hh, hih⟩
    refine ⟨fun j => ?_, fun j _ => ?_, fun j hj => absurd (Finset.mem_univ j) hj, ?_⟩
    · simp only [Pi.sub_apply, Pi.single_apply]
      have := h0 j
      by_cases hji : j = i <;> by_cases hjh : j = h
      · subst hji; subst hjh; simp; have := hih rfl; omega
      · subst hji; simp [hjh]; omega
      · subst hjh; simp [hji]; omega
      · simp [hji, hjh]; omega
    · have := h1 j (Finset.mem_univ j)
      simp only [Pi.sub_apply, Pi.single_apply]
      split_ifs <;> omega
    · simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_single_int, h3]; ring

/-- **The laminar case of `lem:integer-signature`** (no pairs summed yet): a
product of positive log-concave factors of the coordinate sums over a laminar
family, on the box-valid total slice, is `Good`.
PAPER: sections/integer-signatures.tex:100-150 -/
theorem good_laminar (m : ι → ℤ) (R : ℤ) (G : α → Finset ι) (ψ : α → ℤ → ℝ)
    (hψ : ∀ a s, 0 < ψ a s) (hlc : ∀ a s, ψ a (s - 1) * ψ a (s + 1) ≤ ψ a s ^ 2)
    (hlam : ∀ a a', G a ⊆ G a' ∨ G a' ⊆ G a ∨ Disjoint (G a) (G a')) :
    Good m Finset.univ R (laminarWeight m R G ψ) := by
  classical
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · simp only [laminarWeight]; rw [if_neg hz]
  · simp only [laminarWeight]; rw [if_pos hz]; exact Finset.prod_pos fun a _ => hψ a _
  set l : α → ℤ := fun a => ∑ i ∈ G a, z i with hl
  set ind : ι → α → ℤ := fun i a => if i ∈ G a then 1 else 0 with hind
  set T : ι → ι → ℝ := fun i h => ∏ a, ψ a (l a - ind i a - ind h a) with hT
  set D : ι → ℝ := fun i => if 1 ≤ z i then 1 else 0 with hD
  set P : ι → ι → ℝ := fun i h => if i = h ∧ z i = 1 then T i i else 0 with hP
  have hTpos : ∀ i h, 0 < T i h := fun i h => Finset.prod_pos fun a _ => hψ a _
  have hsumG : ∀ a i h, ∑ j ∈ G a, (z - Pi.single i (1 : ℤ) - Pi.single h 1 : ι → ℤ) j =
      l a - ind i a - ind h a := by
    intro a i h
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single', hl, hind]
  have hrem : remMat (laminarWeight m R G ψ) z = fun i h => 1 * (D i * T i h * D h) - P i h := by
    funext i h
    simp only [remMat, laminarWeight, hsumG]
    have hv := valid_remove_two hz i h
    by_cases hih : i = h
    · subst hih
      by_cases h2 : 2 ≤ z i
      · rw [if_pos (hv.2 ⟨by omega, by omega, fun _ => h2⟩)]
        simp only [hD, hP, hT, if_pos (show 1 ≤ z i by omega), true_and]
        rw [if_neg (by omega)]; ring
      · rw [if_neg (fun hc => h2 ((hv.1 hc).2.2 rfl))]
        simp only [hD, hP, hT, true_and]
        by_cases h1 : 1 ≤ z i
        · rw [if_pos h1, if_pos (by omega)]; ring
        · rw [if_neg h1, if_neg (by omega)]; ring
    · simp only [hP, hih, false_and, if_false, sub_zero, hD, hT]
      by_cases hi : 1 ≤ z i <;> by_cases hh : 1 ≤ z h
      · rw [if_pos (hv.2 ⟨hi, hh, fun c => absurd c hih⟩), if_pos hi, if_pos hh]; ring
      · rw [if_neg (fun hc => hh (hv.1 hc).2.1), if_neg hh]; ring
      · rw [if_neg (fun hc => hi (hv.1 hc).1), if_neg hi]; ring
      · rw [if_neg (fun hc => hi (hv.1 hc).1), if_neg hi]; ring
  -- the factorisation `T = Cst · ρ_i Γ_ih ρ_h`
  set ρ : α → ℝ := fun a => ψ a (l a - 1) / ψ a (l a) with hρ
  set γ : α → ℝ := fun a => ψ a (l a) * ψ a (l a - 2) / ψ a (l a - 1) ^ 2 with hγ
  set ρv : ι → ℝ := fun i => ∏ a, if i ∈ G a then ρ a else 1 with hρv
  set Γ : ι → ι → ℝ := fun i h => ∏ a, if i ∈ G a ∧ h ∈ G a then γ a else 1 with hΓ
  set Cst : ℝ := ∏ a, ψ a (l a) with hCst
  have hfac : ∀ a i h, ψ a (l a - ind i a - ind h a) =
      ψ a (l a) * ((if i ∈ G a then ρ a else 1) * (if i ∈ G a ∧ h ∈ G a then γ a else 1) *
        (if h ∈ G a then ρ a else 1)) := by
    intro a i h
    have p0 := hψ a (l a); have p1 := hψ a (l a - 1); have p2 := hψ a (l a - 2)
    simp only [hind, hρ, hγ]
    by_cases hi : i ∈ G a <;> by_cases hh : h ∈ G a <;> simp only [hi, hh, if_true, if_false,
      and_self, and_false, false_and]
    · rw [show l a - 1 - 1 = l a - 2 by ring]; field_simp
    · rw [sub_zero]; field_simp
    · rw [sub_zero]; field_simp
    · simp
  have hTfac : T = fun i h => Cst * (ρv i * Γ i h * ρv h) := by
    funext i h
    simp only [hT, hfac, Finset.prod_mul_distrib, hCst, hρv, hΓ]
  have hΓhyp : Hyp Γ := by
    apply hyp_laminar_gamma G hlam γ
    · intro a; simp only [hγ]; have := hψ a (l a); have := hψ a (l a - 1)
      have := hψ a (l a - 2); positivity
    · intro a
      simp only [hγ]
      have hq := hψ a (l a - 1)
      rw [div_le_one (by positivity)]
      have := hlc a (l a - 1)
      rw [show l a - 1 - 1 = l a - 2 by ring, show l a - 1 + 1 = l a by ring] at this
      linarith
  have hThyp : Hyp T := by
    rw [hTfac]; exact hyp_congr hΓhyp Cst (Finset.prod_pos fun a _ => hψ a _) ρv
  have hTsym : QSymm T := by
    intro i h; simp only [hT]; congr 1; funext a; congr 1; ring
  rw [hrem]
  refine hyp_sub_psd ?_ ?_ (hyp_congr hThyp 1 one_pos D) ?_
  · intro i h
    show 1 * (D i * T i h * D h) = 1 * (D h * T h i * D i)
    rw [hTsym i h]; ring
  · intro i h; simp only [hP]
    by_cases hih : i = h
    · subst hih; rfl
    · rw [if_neg (fun c => hih c.1), if_neg (fun c => hih c.1.symm)]
  · intro v
    simp only [qf, hP]
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun h _ => ?_
    split_ifs with hc
    · rw [hc.1]; have := hTpos h h; nlinarith [sq_nonneg (v h)]
    · simp

end laminar

end Cellcounting.Analysis
