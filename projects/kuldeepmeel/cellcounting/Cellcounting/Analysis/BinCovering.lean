import Cellcounting.Analysis.BinDensity
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Covering the added mass by cut faces

`Cellcounting.Analysis.bin_covering`: the mass of the sup-norm `r`-neighbourhood
`N = binNbhd T` of `S = binSide T` exceeds `μ(S)` by at most `4F`, where `F` is the cut
quantity `binCutFlow T`. A point `z ∈ N \ S` is within `r` of some `x ∈ S`; replacing the
coordinates of `x` by those of `z` one at a time walks from a bin of `T` to the bin of `z`
outside `T`, so some single-coordinate move `v → w` leaves `T`, and `z` lies in the box of
width `2r` around the common face of `v` and `w`, widened by `r` in the other directions.
That box (`binCutSet`, from `binFaceLo`/`binFaceHi`) has volume `2r(1+2r)^{e-1} ≤ 2`
(`binCov_volume_le`) and density at most `2 min{V_a(v), V_a(w)}` (`binRho_le`), so mass at
most `4 min{V_a(v), V_a(w)}` (`binCov_cutSet_mass`) (`evaluation.tex:239-270`). Bins are
half-open and face boxes closed, so the covering (`binCov_diff_subset`) holds pointwise,
with no null set of grid hyperplanes to discard.
-/

namespace Cellcounting.Analysis

open Pseudocode MeasureTheory Set
open scoped ENNReal
open Classical

variable (I : Instance) (ε δ : ℚ)

/-- INTERNAL: `2 ≤ d`. -/
theorem binCov_two_le_dParam : (2 : ℝ) ≤ dParam I := by
  have : 2 ≤ dParam I := by unfold dParam; omega
  exact_mod_cast this

/-- INTERNAL: the radius `r = 1/(4d)` is positive. -/
theorem binCov_rad_pos : 0 < binRad I := by
  have := binCov_two_le_dParam I
  unfold binRad; positivity

/-- INTERNAL: `r ≤ 1/8`. -/
theorem binCov_rad_le : binRad I ≤ 1 / 8 := by
  have := binCov_two_le_dParam I
  unfold binRad
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith

/-- INTERNAL: `e ≤ d` (a local copy of `nFree_le_dParam`, which lives downstream). -/
theorem binCov_nFree_le : nFree I ε δ ≤ dParam I := by
  have := cells_count_le I ε δ
  unfold dParam; omega

/-- INTERNAL: flipping the coordinates of `v₀ ∈ T` to those of `w₀ ∉ T` one at a time, some
single flip leaves `T`.
TEXLINE: sections/evaluation.tex:241-246 -/
theorem binCov_walk_exit {T : Finset (ℕ → ℕ)} {v0 w0 : ℕ → ℕ} (e : ℕ)
    (hout : ∀ k, e ≤ k → v0 k = w0 k) (hv : v0 ∈ T) (hw : w0 ∉ T) :
    ∃ b ∈ T, ∃ i < e, b i = v0 i ∧ v0 i ≠ w0 i ∧ (∀ k, b k = v0 k ∨ b k = w0 k) ∧
      Function.update b i (w0 i) ∉ T := by
  suffices H : ∀ n, ∀ b ∈ T, (∀ k, b k = v0 k ∨ b k = w0 k) →
      ((Finset.range e).filter fun k => b k ≠ w0 k).card = n →
      ∃ b ∈ T, ∃ i < e, b i = v0 i ∧ v0 i ≠ w0 i ∧ (∀ k, b k = v0 k ∨ b k = w0 k) ∧
        Function.update b i (w0 i) ∉ T from
    H _ v0 hv (fun k => Or.inl rfl) rfl
  intro n
  induction n with
  | zero =>
    intro b hb hbk hc
    exfalso; apply hw
    have hbw : b = w0 := by
      funext k
      by_cases hk : k < e
      · by_contra hne
        have hmem : k ∈ (Finset.range e).filter fun k => b k ≠ w0 k := by simp [hk, hne]
        rw [Finset.card_eq_zero] at hc
        rw [hc] at hmem; simp at hmem
      · rcases hbk k with h | h
        · rw [h, hout k (not_lt.1 hk)]
        · exact h
    rwa [← hbw]
  | succ n ih =>
    intro b hb hbk hc
    obtain ⟨i, hi⟩ : ((Finset.range e).filter fun k => b k ≠ w0 k).Nonempty :=
      Finset.card_pos.1 (by omega)
    have hi' := hi
    rw [Finset.mem_filter, Finset.mem_range] at hi'
    have hbi : b i = v0 i := (hbk i).resolve_right hi'.2
    by_cases hu : Function.update b i (w0 i) ∈ T
    · apply ih _ hu
      · intro k
        rcases eq_or_ne k i with rfl | hk
        · simp
        · rw [Function.update_of_ne hk]; exact hbk k
      · have hset : ((Finset.range e).filter fun k => Function.update b i (w0 i) k ≠ w0 k) =
            ((Finset.range e).filter fun k => b k ≠ w0 k).erase i := by
          ext k
          rcases eq_or_ne k i with rfl | hk
          · simp
          · simp [hk]
        rw [hset, Finset.card_erase_of_mem hi, hc]; rfl
    · exact ⟨b, hb, i, hi'.1, hbi, hbi ▸ hi'.2, hbk, hu⟩

/-- INTERNAL: lower corner of the box around the common face of adjacent bins `v`, `w`:
width `2r` across the face, `1 + 2r` along it.
TEXLINE: sections/evaluation.tex:246-264 -/
noncomputable def binFaceLo (v w : ℕ → ℕ) : Fin (nFree I ε δ) → ℝ :=
  fun j => ((max (v j) (w j) : ℕ) : ℝ) - binRad I

/-- INTERNAL: upper corner of the face box (see `binFaceLo`). -/
noncomputable def binFaceHi (v w : ℕ → ℕ) : Fin (nFree I ε δ) → ℝ :=
  fun j => ((max (v j) (w j) : ℕ) : ℝ) + (if v j = w j then 1 else 0) + binRad I

/-- INTERNAL: the face box of the move `u` from `v`, if it leaves `T`; otherwise empty. -/
noncomputable def binCutSet (T : Finset (ℕ → ℕ)) (v : ℕ → ℕ) (u : ℕ) :
    Set (Fin (nFree I ε δ) → ℝ) :=
  match binProp I ε δ v u with
  | some w => if w ∈ T then ∅ else Icc (binFaceLo I ε δ v w) (binFaceHi I ε δ v w)
  | none => ∅

/-- INTERNAL: a proposed move changes each coordinate by at most one. -/
theorem binCov_prop_adj {v w : ℕ → ℕ} {u : ℕ} (h : binProp I ε δ v u = some w) (k : ℕ) :
    w k ≤ v k + 1 ∧ v k ≤ w k + 1 := by
  unfold binProp at h
  split_ifs at h <;> cases h <;>
    rcases eq_or_ne k (u / 2) with rfl | hk <;> simp [Function.update_of_ne, *] <;> omega

/-- INTERNAL: a face box lies within sup distance `8` of the corner of `v`. -/
theorem binCov_face_norm {v w : ℕ → ℕ} (hadj : ∀ k, w k ≤ v k + 1 ∧ v k ≤ w k + 1)
    {z : Fin (nFree I ε δ) → ℝ} (hz : z ∈ Icc (binFaceLo I ε δ v w) (binFaceHi I ε δ v w)) :
    ‖z - binCorner I ε δ v‖ ≤ 8 := by
  have hr := binCov_rad_pos I
  have hr8 := binCov_rad_le I
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun j => ?_
  have h1 := hz.1 j
  have h2 := hz.2 j
  simp only [binFaceLo, binFaceHi] at h1 h2
  have hm1 : (v j : ℝ) ≤ ((max (v j) (w j) : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
  have hm2 : ((max (v j) (w j) : ℕ) : ℝ) ≤ v j + 1 := by
    have := (hadj j).1; exact_mod_cast (by omega : max (v j) (w j) ≤ v j + 1)
  have hite : (if v j = w j then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  simp only [binCorner]
  constructor <;> linarith

/-- INTERNAL: a face box has volume `2r (1+2r)^{e-1} ≤ 2`.
TEXLINE: sections/evaluation.tex:261-264 -/
theorem binCov_volume_le {v w : ℕ → ℕ} {j0 : Fin (nFree I ε δ)} (hj0 : v j0 ≠ w j0) :
    volume (Icc (binFaceLo I ε δ v w) (binFaceHi I ε δ v w)) ≤ 2 := by
  have hr := binCov_rad_pos I
  have hr8 := binCov_rad_le I
  set r := binRad I
  set f : Fin (nFree I ε δ) → ℝ := fun j => (if v j = w j then 1 else 0) + 2 * r
  have hf0 : ∀ j, 0 ≤ f j := fun j => by simp only [f]; split_ifs <;> linarith
  have hfle : ∀ j, f j ≤ 1 + 2 * r := fun j => by simp only [f]; split_ifs <;> linarith
  rw [Real.volume_Icc_pi]
  have hsub : ∀ j, binFaceHi I ε δ v w j - binFaceLo I ε δ v w j = f j := fun j => by
    simp only [binFaceHi, binFaceLo, f]; ring
  simp only [hsub]
  rw [← ENNReal.ofReal_prod_of_nonneg fun j _ => hf0 j,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j0)]
  have hfj0 : f j0 = 2 * r := by simp [f, hj0]
  have hprod : ∏ j ∈ Finset.univ.erase j0, f j ≤ (1 + 2 * r) ^ nFree I ε δ := by
    calc ∏ j ∈ Finset.univ.erase j0, f j ≤ ∏ _j ∈ Finset.univ.erase j0, (1 + 2 * r) :=
          Finset.prod_le_prod₀ (fun j _ => hf0 j) (fun j _ => hfle j)
      _ = (1 + 2 * r) ^ (nFree I ε δ - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin]
      _ ≤ (1 + 2 * r) ^ nFree I ε δ := pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _)
  have hexp : (1 + 2 * r) ^ nFree I ε δ ≤ 8 := by
    have he : ((nFree I ε δ : ℕ) : ℝ) ≤ dParam I := by exact_mod_cast binCov_nFree_le I ε δ
    have hd := binCov_two_le_dParam I
    have h2re : (nFree I ε δ : ℝ) * (2 * r) ≤ 1 := by
      simp only [r, binRad]
      rw [show (nFree I ε δ : ℝ) * (2 * (1 / (4 * dParam I))) = nFree I ε δ / (2 * dParam I) by
        field_simp; ring]
      rw [div_le_one (by positivity)]; linarith
    calc (1 + 2 * r) ^ nFree I ε δ ≤ Real.exp (2 * r) ^ nFree I ε δ :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (2 * r)]) _
      _ = Real.exp (nFree I ε δ * (2 * r)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp 1 := Real.exp_le_exp.2 h2re
      _ ≤ 8 := by linarith [Real.exp_one_lt_three]
  rw [hfj0]
  nlinarith [pow_nonneg (show (0:ℝ) ≤ 1 + 2 * r by linarith) (nFree I ε δ),
    Finset.prod_nonneg fun j (_ : j ∈ Finset.univ.erase j0) => hf0 j]

/-- INTERNAL: the mass of one cut-face box is at most `4 min{V_a(v), V_a(w)}`.
TEXLINE: sections/evaluation.tex:261-270 -/
theorem binCov_cutSet_mass (hε : 0 < ε) (hfeas : feasible I) (a : ℕ) (ha : a ≤ HParam I ε δ)
    (x y : ℕ → ℕ) (T : Finset (ℕ → ℕ)) {v : ℕ → ℕ} (hv : v ∈ binSet I ε δ) (u : ℕ) :
    binMass I ε δ a x y (binCutSet I ε δ T v u) ≤
      ENNReal.ofReal (4 * binCutTerm I ε δ a x y T v u) := by
  unfold binCutSet binCutTerm
  rcases hp : binProp I ε δ v u with _ | w
  · simp [binMass]
  · dsimp only
    split_ifs with hwT
    · simp [binMass]
    · have hw := binProp_mem I ε δ hv hp
      have hne := binProp_ne I ε δ hp
      have hadj := binCov_prop_adj I ε δ hp
      obtain ⟨j0, hj0⟩ : ∃ j0 : Fin (nFree I ε δ), v j0 ≠ w j0 := by
        by_contra hall
        push Not at hall
        apply hne
        funext k
        by_cases hk : k < nFree I ε δ
        · exact (hall ⟨k, hk⟩).symm
        · rw [((mem_binSet_iff I ε δ v).1 hv).2 k (not_lt.1 hk),
            ((mem_binSet_iff I ε δ w).1 hw).2 k (not_lt.1 hk)]
      set m := min (binV I ε δ a x y v) (binV I ε δ a x y w)
      have hm0 : 0 ≤ m := le_min (binV_pos I ε δ a x y v).le (binV_pos I ε δ a x y w).le
      have hrho : ∀ z ∈ Icc (binFaceLo I ε δ v w) (binFaceHi I ε δ v w),
          binRho I ε δ a x y z ≤ ENNReal.ofReal (2 * m) := by
        intro z hz
        have h1 := binRho_le I ε δ hε hfeas a ha x y hv z (binCov_face_norm I ε δ hadj hz)
        have hz' : z ∈ Icc (binFaceLo I ε δ w v) (binFaceHi I ε δ w v) := by
          have e1 : binFaceLo I ε δ w v = binFaceLo I ε δ v w := by
            funext j; simp only [binFaceLo, max_comm]
          have e2 : binFaceHi I ε δ w v = binFaceHi I ε δ v w := by
            funext j; simp only [binFaceHi, max_comm, eq_comm]
          rwa [e1, e2]
        have h2 := binRho_le I ε δ hε hfeas a ha x y hw z
          (binCov_face_norm I ε δ (fun k => ⟨(hadj k).2, (hadj k).1⟩) hz')
        have : ENNReal.ofReal (2 * m) =
            min (ENNReal.ofReal (2 * binV I ε δ a x y v)) (ENNReal.ofReal (2 * binV I ε δ a x y w)) := by
          simp only [m, mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_min]
        rw [this]; exact le_min h1 h2
      calc binMass I ε δ a x y (Icc (binFaceLo I ε δ v w) (binFaceHi I ε δ v w))
          ≤ ∫⁻ _ in Icc (binFaceLo I ε δ v w) (binFaceHi I ε δ v w), ENNReal.ofReal (2 * m) :=
            setLIntegral_mono measurable_const hrho
        _ = ENNReal.ofReal (2 * m) * volume (Icc (binFaceLo I ε δ v w) (binFaceHi I ε δ v w)) :=
            setLIntegral_const _ _
        _ ≤ ENNReal.ofReal (2 * m) * 2 := by gcongr; exact binCov_volume_le I ε δ hj0
        _ = ENNReal.ofReal (4 * m) := by
            rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity)]
            ring_nf

/-- INTERNAL: `N \ S` is covered by the face boxes of the moves leaving `T`.
TEXLINE: sections/evaluation.tex:239-258 -/
theorem binCov_diff_subset {T : Finset (ℕ → ℕ)} (hT : T ⊆ binSet I ε δ) :
    binNbhd I ε δ T \ binSide I ε δ T ⊆
      ⋃ v ∈ T, ⋃ u ∈ Finset.range (2 * nFree I ε δ), binCutSet I ε δ T v u := by
  rintro z ⟨⟨hzc, x, hx, hzx⟩, hzS⟩
  simp only [binSide, mem_iUnion] at hx
  obtain ⟨v0, hv0, hxv⟩ := hx
  have hr := binCov_rad_pos I
  have hr8 := binCov_rad_le I
  let w0 : ℕ → ℕ := fun k => if h : k < nFree I ε δ then ⌊z ⟨k, h⟩⌋₊ else 0
  have hz0 : ∀ j : Fin (nFree I ε δ), 0 ≤ z j ∧ z j < BParam I ε δ := fun j => by
    simpa using hzc j (mem_univ _)
  have hw0j : ∀ j : Fin (nFree I ε δ), w0 j = ⌊z j⌋₊ := fun j => by simp [w0, j.isLt]
  have hzw : ∀ j : Fin (nFree I ε δ), (w0 j : ℝ) ≤ z j ∧ z j < w0 j + 1 := fun j => by
    rw [hw0j]; exact ⟨Nat.floor_le (hz0 j).1, Nat.lt_floor_add_one _⟩
  have hw0 : w0 ∈ binSet I ε δ := by
    rw [mem_binSet_iff]
    refine ⟨fun k hk => ?_, fun k hk => by simp [w0, not_lt.2 hk]⟩
    rw [hw0j ⟨k, hk⟩]
    exact (Nat.floor_lt (hz0 _).1).2 (hz0 _).2
  have hw0T : w0 ∉ T := by
    intro h; apply hzS
    simp only [binSide, mem_iUnion]
    exact ⟨w0, h, fun j _ => by simpa using hzw j⟩
  have hxv' : ∀ j : Fin (nFree I ε δ), (v0 j : ℝ) ≤ x j ∧ x j < v0 j + 1 := fun j => by
    simpa using hxv j (mem_univ _)
  have hzx' : ∀ j : Fin (nFree I ε δ), |z j - x j| < binRad I := fun j =>
    lt_of_le_of_lt (by simpa using norm_le_pi_norm (z - x) j) hzx
  have hv0b := hT hv0
  have hdiff : ∀ j : Fin (nFree I ε δ), w0 j ≤ v0 j + 1 ∧ v0 j ≤ w0 j + 1 := fun j => by
    have h1 := hzw j; have h2 := hxv' j; have h3 := abs_lt.1 (hzx' j)
    have a1 : (w0 j : ℝ) < v0 j + 2 := by linarith
    have a2 : (v0 j : ℝ) < w0 j + 2 := by linarith
    have b1 : w0 j < v0 j + 2 := by exact_mod_cast a1
    have b2 : v0 j < w0 j + 2 := by exact_mod_cast a2
    omega
  obtain ⟨b, hb, i, hi, hbi, hvw, hbk, hbT⟩ := binCov_walk_exit (nFree I ε δ)
    (fun k hk => by rw [((mem_binSet_iff I ε δ v0).1 hv0b).2 k hk,
      ((mem_binSet_iff I ε δ w0).1 hw0).2 k hk]) hv0 hw0T
  set b' := Function.update b i (w0 i)
  have hi' : w0 i ≤ v0 i + 1 ∧ v0 i ≤ w0 i + 1 := hdiff ⟨i, hi⟩
  have hwB := ((mem_binSet_iff I ε δ w0).1 hw0).1 i hi
  -- the proposal pattern that moves `b` to `b'`
  obtain ⟨u, hu, hprop⟩ : ∃ u < 2 * nFree I ε δ, binProp I ε δ b u = some b' := by
    rcases (by omega : w0 i = v0 i + 1 ∨ v0 i = w0 i + 1) with h | h
    · refine ⟨2 * i + 1, by omega, ?_⟩
      unfold binProp
      have e1 : (2 * i + 1) / 2 = i := by omega
      rw [if_pos (by omega), if_pos (by omega), e1, if_neg (by omega)]
      simp only [b', hbi, h]
    · refine ⟨2 * i, by omega, ?_⟩
      unfold binProp
      have e1 : (2 * i) / 2 = i := by omega
      rw [if_pos (by omega), if_neg (by omega), e1, if_neg (by omega)]
      simp only [b', hbi, h]; rfl
  simp only [mem_iUnion, Finset.mem_range]
  refine ⟨b, hb, u, hu, ?_⟩
  unfold binCutSet
  rw [hprop]
  dsimp only
  rw [if_neg hbT]
  have key : ∀ j, binFaceLo I ε δ b b' j ≤ z j ∧ z j ≤ binFaceHi I ε δ b b' j := by
    intro j
    simp only [binFaceLo, binFaceHi]
    have h1 := hzw j; have h2 := hxv' j; have h3 := abs_lt.1 (hzx' j)
    rcases eq_or_ne (j : ℕ) i with hj | hj
    · have hbj : b j = v0 j := hj ▸ hbi
      have hb'j : b' j = w0 j := by simp only [b', hj, Function.update_self]
      have hne : v0 j ≠ w0 j := hj ▸ hvw
      rw [hbj, hb'j, if_neg hne]
      rcases (by have := hdiff j; omega : w0 j = v0 j + 1 ∨ v0 j = w0 j + 1) with h | h
      · rw [max_eq_right (by omega), h]; push_cast
        rw [h] at h1; push_cast at h1
        constructor <;> linarith
      · rw [max_eq_left (by omega), h]; push_cast
        rw [h] at h2; push_cast at h2
        constructor <;> linarith
    · have hb'j : b' j = b j := by simp only [b', Function.update_of_ne hj]
      rw [hb'j, if_pos rfl, max_self]
      rcases hbk j with h | h
      · rw [h]; constructor <;> linarith
      · rw [h]; constructor <;> linarith
  exact ⟨fun j => (key j).1, fun j => (key j).2⟩

/-- **Covering by cut faces**: `μ(N \ S) ≤ 4F`.
PAPER: sections/evaluation.tex:239-270 -/
theorem bin_covering (hε : 0 < ε) (hfeas : feasible I) (a : ℕ) (ha : a ≤ HParam I ε δ)
    (x y : ℕ → ℕ) {T : Finset (ℕ → ℕ)} (hT : T ⊆ binSet I ε δ) :
    binMass I ε δ a x y (binNbhd I ε δ T) ≤
      binMass I ε δ a x y (binSide I ε δ T) + ENNReal.ofReal (4 * binCutFlow I ε δ a x y T) := by
  set μ' : Measure (Fin (nFree I ε δ) → ℝ) := volume.withDensity (binRho I ε δ a x y)
  have hm : ∀ X, binMass I ε δ a x y X = μ' X := fun X => (withDensity_apply' _ X).symm
  have hflow : ENNReal.ofReal (4 * binCutFlow I ε δ a x y T) =
      ∑ v ∈ T, ∑ u ∈ Finset.range (2 * nFree I ε δ),
        ENNReal.ofReal (4 * binCutTerm I ε δ a x y T v u) := by
    unfold binCutFlow
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun v _ => mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun u _ => binCutTerm_nonneg I ε δ a x y T v u)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun u _ => mul_nonneg (by norm_num)
      (binCutTerm_nonneg I ε δ a x y T v u)]
  rw [hm, hm, hflow]
  calc μ' (binNbhd I ε δ T)
      ≤ μ' (binSide I ε δ T ∪ (binNbhd I ε δ T \ binSide I ε δ T)) :=
        measure_mono fun z hz => by
          by_cases h : z ∈ binSide I ε δ T
          · exact Or.inl h
          · exact Or.inr ⟨hz, h⟩
    _ ≤ μ' (binSide I ε δ T) + μ' (binNbhd I ε δ T \ binSide I ε δ T) := measure_union_le _ _
    _ ≤ μ' (binSide I ε δ T) + ∑ v ∈ T, ∑ u ∈ Finset.range (2 * nFree I ε δ),
          ENNReal.ofReal (4 * binCutTerm I ε δ a x y T v u) := by
        gcongr
        calc μ' (binNbhd I ε δ T \ binSide I ε δ T)
            ≤ μ' (⋃ v ∈ T, ⋃ u ∈ Finset.range (2 * nFree I ε δ), binCutSet I ε δ T v u) :=
              measure_mono (binCov_diff_subset I ε δ hT)
          _ ≤ ∑ v ∈ T, μ' (⋃ u ∈ Finset.range (2 * nFree I ε δ), binCutSet I ε δ T v u) :=
              measure_biUnion_finset_le _ _
          _ ≤ ∑ v ∈ T, ∑ u ∈ Finset.range (2 * nFree I ε δ), μ' (binCutSet I ε δ T v u) :=
              Finset.sum_le_sum fun v _ => measure_biUnion_finset_le _ _
          _ ≤ _ := Finset.sum_le_sum fun v hv => Finset.sum_le_sum fun u _ => by
              rw [← hm]; exact binCov_cutSet_mass I ε δ hε hfeas a ha x y T (hT hv) u


end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `bin_covering` via walk-exit covering by closed face boxes; closed outright
-/
