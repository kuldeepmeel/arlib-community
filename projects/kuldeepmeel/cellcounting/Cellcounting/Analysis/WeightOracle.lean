import Cellcounting.Analysis.Contamination
import Cellcounting.Analysis.BinLaw
import Cellcounting.Analysis.SampleBinClose
import Cellcounting.Analysis.PenaltyLipschitz
import Cellcounting.Analysis.Pow2Approx
import Cellcounting.Analysis.AvgChebyshev
import Cellcounting.Analysis.OracleCorrection

/-!
# Accuracy of the weight oracle

`prop:weight-oracle` (`evaluation.tex:15-37`), accuracy clause, for the
pseudocode oracle `Pseudocode.oracle` (`ĥ_j(x, y) = M_f · ∏_{a<j} R̂_a · T̂`):
at a box-valid small profile `(x, y)` of total `p`, a level `j ≤ H`, and
`0 < ξ_in, θ < 1/4`, the output lies in `[(1 - ξ_in) h_j(x, y), (1 + ξ_in) h_j(x, y)]`
with probability at least `1 - θ`.  `h_j` is `hWeight` of `Contamination.lean`
(`eq:hj`).

The pseudocode's bin intervals, cube point, ratio samples, correction exponent
`β = ⌊jD(v)/H⌋ - jD(z)/H` and walk length `ℓ_in` were compared with
`evaluation.tex:40-125` and `evaluation.tex:327-400` and agree with them.

The proof follows `evaluation.tex:40-482`.  The *ideal oracle* `oracleIdeal`
replaces every bin walk by an exact draw from the bin law `π_a` (`binLaw`) and
every dyadic offset draw by an exact uniform draw (`idealOffsets`).

* **Closeness** (`oracle_close`): the oracle is within total variation
  `j N_in ζ + N_in (e + 1) ζ ≤ Q_in ζ = θ/8` of the ideal oracle, by the bin-walk
  mixing bound `sampleBin_close` (`eq:bin-mixing`, `SampleBinClose.lean`) and
  `lem:dyadic-integer-draw` (`binOffsets_close`).
* **Means** (`eq:oracle-telescope`): a ratio sample has mean `S_{a+1}/S_a`
  (`pexp_ratioLaw`) and values in `[1/2, 1]` (`ratioSample_mem`, from `0 ≤ D ≤ H`);
  a correction sample has mean within `(1 ± σ)` of `B^e h_j / (M_f S_j)` and values
  in `[0, 16]` (`corr_mean`: the free box is the disjoint union of the bins,
  `sum_bins`; `1/2 ≤ α_v ≤ 2`, `alpha_bounds`; `β ∈ [-2, 2]` from the Lipschitz
  bound for `D`, `beta_bounds`; the bisection error of `pow2Approx_close`).  Since
  `S_0 = B^e`, `M_f ∏_{a<j} (S_{a+1}/S_a) · B^e h_j / (M_f S_j) = h_j`.
* **Chebyshev** (`avg_chebyshev`, giving `ratioIdeal_bad` at cost `2/(N_in σ²)` and
  `corrIdeal_bad` at cost `144/(N_in σ²)`) and a union bound over the `j + 1`
  averages (`loop_bad_le`): the ideal oracle stays in
  `[(1 - σ)^{j+2} h_j, (1 + σ)^{j+2} h_j]` except with probability at most
  `(2j + 144)/(N_in σ²) ≤ θ/4` (`oracleIdeal_bad`).

`σ = ξ_in/(50(H+1))` makes `(1 ± σ)^{j+2}` lie within `1 ± ξ_in` (`pow_window`).
`weight_oracle_accurate` adds the two failure budgets: `θ/8 + θ/4 < θ`.

The accuracy clause rests on `sampleBin_close` (`SampleBinClose.lean`), whose
`e ≥ 1` case (the bin-walk conductance bound) is proved in that file, not here.
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal
open Classical

/-! ### Generic union bounds -/

/-- INTERNAL: closeness at cost one holds for any two laws. -/
theorem PClose.one {α : Type*} (μ ν : PMF α) : PClose μ ν 1 := fun f hf =>
  (pexp_le_one μ f hf).trans le_add_self

/-- INTERNAL: union bound across one `bind`. -/
theorem bind_bad_le {α β : Type*} (μ : PMF α) (f : α → PMF β) (A : Set α) (s : Set β)
    (c : ℝ≥0∞) (h : ∀ a ∈ A, (f a).toOuterMeasure s ≤ c) :
    (μ.bind f).toOuterMeasure s ≤ μ.toOuterMeasure Aᶜ + c := by
  rw [outer_eq_pexp, outer_eq_pexp, pexp_bind, ← pexp_add_const]
  refine pexp_mono _ fun a => ?_
  by_cases ha : a ∈ A
  · have : a ∉ Aᶜ := fun h' => h' ha
    rw [Set.indicator_of_notMem this, zero_add, ← outer_eq_pexp]
    exact h a ha
  · rw [Set.indicator_of_mem (show a ∈ Aᶜ from ha)]
    refine (pexp_le_one _ _ fun b => ?_).trans le_self_add
    by_cases hb : b ∈ s <;> simp [hb]

/-- INTERNAL: union bound along a `loop`: if each of the first `K` steps leaves the
invariant with probability at most `p i` from inside it, then after `k ≤ K` steps
the invariant fails with probability at most `Σ_{i<k} p i`. -/
theorem loop_bad_le {β : Type} (f : ℕ → β → PMF β) (G : ℕ → Set β) (p : ℕ → ℝ≥0∞) (b : β)
    (hb : b ∈ G 0) (K : ℕ)
    (hstep : ∀ i < K, ∀ c ∈ G i, (f i c).toOuterMeasure (G (i + 1))ᶜ ≤ p i) :
    ∀ k ≤ K, (loop f k b).toOuterMeasure (G k)ᶜ ≤ ∑ i ∈ Finset.range k, p i := by
  intro k hk
  induction k with
  | zero =>
    rw [loop_zero, Finset.sum_range_zero, PMF.toOuterMeasure_pure_apply, if_neg]
    exact fun h => h hb
  | succ k ih =>
    rw [loop_succ, Finset.sum_range_succ]
    exact (bind_bad_le _ _ (G k) _ (p k) (hstep k (by omega))).trans
      (add_le_add (ih (by omega)) le_rfl)

/-- INTERNAL: an event and its complement have total probability one. -/
theorem outer_add_compl {α : Type*} (μ : PMF α) (s : Set α) :
    μ.toOuterMeasure s + μ.toOuterMeasure sᶜ = 1 := by
  rw [outer_eq_pexp, outer_eq_pexp, ← pexp_add]
  have : (fun a => s.indicator (1 : α → ℝ≥0∞) a + sᶜ.indicator 1 a) = fun _ => 1 := by
    funext a; by_cases ha : a ∈ s <;> simp [ha]
  rw [this, pexp_const]

/-- INTERNAL: a law whose expectations are weighted sums over `φ(s)` is supported
on `φ(s)`. -/
theorem support_of_pexp {α ι : Type*} (μ : PMF α) (s : Finset ι) (w : ι → ℝ≥0∞) (φ : ι → α)
    (h : ∀ f : α → ℝ≥0∞, pexp μ f = ∑ i ∈ s, w i * f (φ i)) :
    ∀ a ∈ μ.support, ∃ i ∈ s, φ i = a := by
  intro a ha
  by_contra hn
  push_neg at hn
  rw [PMF.mem_support_iff] at ha
  apply ha
  have h1 := h (fun b => if b = a then 1 else 0)
  have h2 : pexp μ (fun b => if b = a then 1 else 0) = μ a := by
    unfold pexp
    simp_rw [mul_ite, mul_one, mul_zero]
    exact tsum_ite_eq a _
  rw [← h2, h1]
  exact Finset.sum_eq_zero fun i hi => by rw [if_neg (hn i hi), mul_zero]

/-! ### The bins of the instance -/

section inst
variable (I : Instance) (ε δ : ℚ)

/-- INTERNAL: a list product read through `getD`. -/
theorem list_prod_range_getD {α : Type*} (l : List α) (g : α → ℕ) (d : α) :
    ∏ i ∈ Finset.range l.length, g (l.getD i d) = (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih, List.map_cons, List.prod_cons, mul_comm]

/-- INTERNAL: `M_f = ∏_{k < e} (b_k + 1)`. -/
theorem Mf_eq_prod :
    Mf I ε δ = ∏ k ∈ Finset.range (nFree I ε δ), ((freeAt I ε δ k).2.2 + 1) := by
  unfold Mf nFree freeAt
  exact (list_prod_range_getD _ (fun e : Entry => e.2.2 + 1) _).symm

/-- INTERNAL: `B > 0`. -/
theorem BParam_pos (hε : 0 < ε) : 0 < BParam I ε δ := by
  unfold BParam
  have := AParam_pos I ε δ hε
  have := dParam_ge I
  positivity

/-- INTERNAL: every free cell is large, `b_k ≥ W = 100 d B`. -/
theorem free_large {k : ℕ} (hk : k < nFree I ε δ) :
    100 * dParam I * BParam I ε δ ≤ (freeAt I ε δ k).2.2 :=
  (large_mem I ε δ (Or.inr (freeAt_mem I ε δ hk))).2

/-- INTERNAL: `e ≤ d`. -/
theorem nFree_le_d : nFree I ε δ ≤ dParam I := by
  have := cells_count_le I ε δ
  unfold dParam
  have : I.m * I.n ≤ I.m * I.n + I.m + I.n + 2 := by omega
  omega

/-- INTERNAL: `extendN` reads back its vector. -/
theorem extendN_val {N : ℕ} (u : Fin N → ℕ) (k : Fin N) : extendN u k = u k := by
  simp [extendN]

theorem extendN_injective {N : ℕ} : Function.Injective (extendN (N := N)) := by
  intro u₁ u₂ h
  funext k
  have := congrFun h k
  rwa [extendN_val, extendN_val] at this

/-- INTERNAL: sums over the bin space as sums over `{0, …, B-1}^e`. -/
theorem sum_binSet (G : (ℕ → ℕ) → ℝ) :
    ∑ v ∈ binSet I ε δ, G v =
      ∑ u ∈ Fintype.piFinset (fun _ : Fin (nFree I ε δ) => Finset.range (BParam I ε δ)),
        G (extendN u) := by
  unfold binSet
  rw [Finset.sum_image fun u₁ _ u₂ _ h => extendN_injective h]

/-- INTERNAL: one coordinate of a bin: `N - B < B |I| < N + B`. -/
theorem binLen_bounds (hε : 0 < ε) (v : ℕ → ℕ) {k : ℕ} (hk : k < nFree I ε δ) :
    (freeAt I ε δ k).2.2 + 1 < BParam I ε δ * binLen I ε δ k v + BParam I ε δ ∧
      BParam I ε δ * binLen I ε δ k v < (freeAt I ε δ k).2.2 + 1 + BParam I ε δ ∧
      0 < binLen I ε δ k v := by
  have hB := BParam_pos I ε δ hε
  have hL := free_large I ε δ hk
  have hd := dParam_ge I
  set N := (freeAt I ε δ k).2.2 + 1
  set B := BParam I ε δ
  have hNB : B ≤ N := by
    have : B ≤ 100 * dParam I * B := by nlinarith
    omega
  have h1 := le_mul_ceilDiv hB (N * v k)
  have h2 := mul_ceilDiv_lt hB (N * v k)
  have h3 := le_mul_ceilDiv hB (N * (v k + 1))
  have h4 := mul_ceilDiv_lt hB (N * (v k + 1))
  unfold binLen binHi binLo
  change B * (N * v k ⌈/⌉ B) ≥ N * v k at h1
  set lo := N * v k ⌈/⌉ B
  set hi := N * (v k + 1) ⌈/⌉ B
  have hN1 : N * (v k + 1) = N * v k + N := by ring
  rw [hN1] at h3 h4
  have hlohi : lo < hi := by
    by_contra h
    push_neg at h
    have : B * hi ≤ B * lo := Nat.mul_le_mul_left _ h
    omega
  have hmul : B * (hi - lo) = B * hi - B * lo := Nat.mul_sub _ _ _
  rw [hmul]
  refine ⟨by omega, by omega, by omega⟩

/-- **Bin populations** (`eq:bin-populations`): `1/2 ≤ α_v = B^e |I_v| / M_f ≤ 2`.
PAPER: sections/evaluation.tex:62-69 -/
theorem alpha_bounds (hε : 0 < ε) (v : ℕ → ℕ) :
    1 / 2 ≤ (BParam I ε δ : ℝ) ^ nFree I ε δ *
        (∏ k ∈ Finset.range (nFree I ε δ), (binLen I ε δ k v : ℝ)) / (Mf I ε δ : ℝ) ∧
      (BParam I ε δ : ℝ) ^ nFree I ε δ *
        (∏ k ∈ Finset.range (nFree I ε δ), (binLen I ε δ k v : ℝ)) / (Mf I ε δ : ℝ) ≤ 2 := by
  have hB := BParam_pos I ε δ hε
  have hBr : (0 : ℝ) < BParam I ε δ := by exact_mod_cast hB
  have hd : (2 : ℝ) ≤ dParam I := by exact_mod_cast dParam_ge I
  have heq : (BParam I ε δ : ℝ) ^ nFree I ε δ *
        (∏ k ∈ Finset.range (nFree I ε δ), (binLen I ε δ k v : ℝ)) / (Mf I ε δ : ℝ) =
      ∏ k ∈ Finset.range (nFree I ε δ),
        ((BParam I ε δ : ℝ) * binLen I ε δ k v / (((freeAt I ε δ k).2.2 + 1 : ℕ) : ℝ)) := by
    rw [Mf_eq_prod, Nat.cast_prod, Finset.prod_div_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_range]
  rw [heq]
  refine prod_near_one _ _ (1 / (100 * dParam I)) (by positivity) ?_ (fun k hk => ?_)
  · have he : (nFree I ε δ : ℝ) ≤ dParam I := by exact_mod_cast nFree_le_d I ε δ
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  · obtain ⟨h1, h2, -⟩ := binLen_bounds I ε δ hε v hk
    have hL := free_large I ε δ hk
    set N := (freeAt I ε δ k).2.2 + 1 with hNdef
    have hNr : (100 * dParam I * BParam I ε δ : ℝ) + 1 ≤ N := by
      rw [hNdef]; push_cast; exact_mod_cast (by omega : 100 * dParam I * BParam I ε δ + 1 ≤ (freeAt I ε δ k).2.2 + 1)
    have hN0 : (0 : ℝ) < N := by
      have : (0 : ℝ) ≤ 100 * dParam I * BParam I ε δ := by positivity
      linarith
    have h1r : (N : ℝ) < BParam I ε δ * binLen I ε δ k v + BParam I ε δ := by exact_mod_cast h1
    have h2r : (BParam I ε δ : ℝ) * binLen I ε δ k v < N + BParam I ε δ := by exact_mod_cast h2
    have hc : (BParam I ε δ : ℝ) / N ≤ 1 / (100 * dParam I) := by
      rw [div_le_div_iff₀ hN0 (by positivity)]
      nlinarith
    constructor
    · rw [le_div_iff₀ hN0]
      have : (1 - 1 / (100 * (dParam I : ℝ))) * N ≤ N - BParam I ε δ := by
        have := (div_le_iff₀ hN0).1 hc
        nlinarith
      linarith
    · rw [div_le_iff₀ hN0]
      have := (div_le_iff₀ hN0).1 hc
      nlinarith

/-- INTERNAL: the integer points of a bin are within one cube unit of its lower corner. -/
theorem binPoint_close (hε : 0 < ε) (v : ℕ → ℕ) (o : Fin (nFree I ε δ) → ℕ)
    (ho : ∀ k : Fin (nFree I ε δ), o k < binLen I ε δ k v) :
    ∀ k < nFree I ε δ, |binPoint I ε δ v k - drawPt (fun k => binLo I ε δ k v) (nFree I ε δ) o k| ≤
      1 * (((freeAt I ε δ k).2.2 : ℚ) + 1) / BParam I ε δ := by
  intro k hk
  have hB := BParam_pos I ε δ hε
  have hBq : (0 : ℚ) < BParam I ε δ := by exact_mod_cast hB
  set N := (freeAt I ε δ k).2.2 + 1 with hNdef
  have h1 := le_mul_ceilDiv hB (N * v k)
  have h4 := mul_ceilDiv_lt hB (N * (v k + 1))
  have hok := ho ⟨k, hk⟩
  unfold binLen binHi binLo at hok
  set lo := N * v k ⌈/⌉ BParam I ε δ
  set hi := N * (v k + 1) ⌈/⌉ BParam I ε δ
  -- `N v ≤ B z < N v + N`
  have hz1 : N * v k ≤ BParam I ε δ * (lo + o ⟨k, hk⟩) := by
    calc N * v k ≤ BParam I ε δ * lo := h1
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have hz2 : BParam I ε δ * (lo + o ⟨k, hk⟩) < N * v k + N := by
    have : lo + o ⟨k, hk⟩ + 1 ≤ hi := by omega
    have h5 : BParam I ε δ * (lo + o ⟨k, hk⟩ + 1) ≤ BParam I ε δ * hi := Nat.mul_le_mul_left _ this
    have hN1 : N * (v k + 1) = N * v k + N := by ring
    rw [hN1] at h4
    rw [Nat.mul_succ] at h5
    omega
  have hz1q : (N : ℚ) * v k ≤ BParam I ε δ * ((lo + o ⟨k, hk⟩ : ℕ) : ℚ) := by exact_mod_cast hz1
  have hz2q : (BParam I ε δ : ℚ) * ((lo + o ⟨k, hk⟩ : ℕ) : ℚ) < N * v k + N := by exact_mod_cast hz2
  have hdraw : drawPt (fun k => binLo I ε δ k v) (nFree I ε δ) o k = ((lo + o ⟨k, hk⟩ : ℕ) : ℚ) := by
    simp only [drawPt, dif_pos hk]; rfl
  rw [hdraw]
  unfold binPoint
  have hNq : ((N : ℕ) : ℚ) = ((freeAt I ε δ k).2.2 : ℚ) + 1 := by rw [hNdef]; push_cast; ring
  rw [one_mul, ← hNq]
  set z : ℚ := ((lo + o ⟨k, hk⟩ : ℕ) : ℚ)
  have e1 : (((N * v k : ℕ) : ℚ)) / BParam I ε δ - z =
      ((N : ℚ) * v k - BParam I ε δ * z) / BParam I ε δ := by
    push_cast; field_simp
  rw [e1, abs_le, ← neg_div, div_le_div_iff_of_pos_right hBq, div_le_div_iff_of_pos_right hBq]
  constructor <;> linarith

/-- INTERNAL: the penalty is nonnegative, at any free vector. -/
theorem pseudo_penalty_nonneg (x y : ℕ → ℕ) (z : ℕ → ℚ) : 0 ≤ penalty I ε δ x y z := by
  unfold penalty
  apply mul_nonneg (by positivity)
  apply add_nonneg
  · apply List.sum_nonneg
    intro a ha
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 ha
    exact abs_nonneg _
  · exact Finset.sum_nonneg fun t _ => div_nonneg (boxDist_nonneg _ _) (by positivity)

/-- INTERNAL: the integer points of bin `v`, as offset vectors. -/
noncomputable def binPts (v : ℕ → ℕ) : Finset (Fin (nFree I ε δ) → ℕ) :=
  Fintype.piFinset fun k : Fin (nFree I ε δ) => Finset.range (binLen I ε δ k v)

/-- INTERNAL: the integer point of bin `v` with offsets `o`. -/
noncomputable def binZ (v : ℕ → ℕ) (o : Fin (nFree I ε δ) → ℕ) : ℕ → ℚ :=
  drawPt (fun k => binLo I ε δ k v) (nFree I ε δ) o

/-- INTERNAL: `|I_v| = ∏_k |I_{v_k}|`. -/
noncomputable def binL (v : ℕ → ℕ) : ℕ := ∏ k ∈ Finset.range (nFree I ε δ), binLen I ε δ k v

/-- **The correction exponent** `β = ⌊jD(v)/H⌋ - jD(z)/H ∈ [-2, 2]`
(`evaluation.tex:417-421`): the floor loses less than one and `D` moves by at most
`1/8` inside a bin.
PAPER: sections/evaluation.tex:417-421 -/
theorem beta_bounds (hε : 0 < ε) (hfeas : feasible I) (x y : ℕ → ℕ) (j : ℕ)
    (hj : j ≤ HParam I ε δ) (v : ℕ → ℕ) (o : Fin (nFree I ε δ) → ℕ)
    (ho : ∀ k : Fin (nFree I ε δ), o k < binLen I ε δ k v) :
    -2 ≤ (binExp I ε δ j x y v : ℚ) - (j : ℚ) * penalty I ε δ x y (binZ I ε δ v o) /
        (HParam I ε δ : ℚ) ∧
      (binExp I ε δ j x y v : ℚ) - (j : ℚ) * penalty I ε δ x y (binZ I ε δ v o) /
        (HParam I ε δ : ℚ) ≤ 2 := by
  have hH : (0 : ℚ) < HParam I ε δ := by exact_mod_cast HParam_pos I ε δ hε
  have hlip := penalty_lipschitz I ε δ hε hfeas x y (binPoint I ε δ v) (binZ I ε δ v o) 1
    zero_le_one (binPoint_close I ε δ hε v o ho)
  set Dv := penalty I ε δ x y (binPoint I ε δ v)
  set Dz := penalty I ε δ x y (binZ I ε δ v o)
  have hjq : (j : ℚ) ≤ HParam I ε δ := by exact_mod_cast hj
  have hj0 : (0 : ℚ) ≤ j := by positivity
  have hdiff : |(j : ℚ) * Dv / HParam I ε δ - (j : ℚ) * Dz / HParam I ε δ| ≤ 1 / 8 := by
    rw [← sub_div, ← mul_sub, abs_div, abs_mul, abs_of_nonneg hj0, abs_of_pos hH,
      div_le_iff₀ hH]
    calc (j : ℚ) * |Dv - Dz| ≤ HParam I ε δ * (1 / 8) := by
          apply mul_le_mul hjq hlip (abs_nonneg _) hH.le
      _ = 1 / 8 * HParam I ε δ := by ring
  have hfl1 := Int.floor_le ((j : ℚ) * Dv / HParam I ε δ)
  have hfl2 := Int.lt_floor_add_one ((j : ℚ) * Dv / HParam I ε δ)
  have hbe : (binExp I ε δ j x y v : ℚ) = (⌊(j : ℚ) * Dv / HParam I ε δ⌋ : ℚ) := rfl
  rw [hbe]
  have := abs_le.1 hdiff
  constructor <;> linarith

/-- INTERNAL: `V_j(v) · 2^β = 2^{-jD(z)/H}`. -/
theorem binV_mul_two_rpow (j : ℕ) (x y v : ℕ → ℕ) (D : ℚ) :
    binV I ε δ j x y v *
        (2 : ℝ) ^ ((((binExp I ε δ j x y v : ℚ) - (j : ℚ) * D / (HParam I ε δ : ℚ) : ℚ)) : ℝ) =
      (2 : ℝ) ^ (-((j : ℝ) * (D : ℝ) / (HParam I ε δ : ℝ))) := by
  unfold binV
  rw [← Real.rpow_intCast, ← Real.rpow_add two_pos]
  congr 1
  push_cast
  ring

/-- INTERNAL: one correction observation under the ideal laws: an exact bin, then
exact uniform offsets in it.
TEXLINE: sections/evaluation.tex:95-104 -/
noncomputable def corrLaw (ξin : ℚ) (j : ℕ) (x y : ℕ → ℕ) : PMF ℚ :=
  (binLaw I ε δ j x y).bind fun v =>
    (idealOffsets I ε δ v).map fun zl => corrSample I ε δ ξin j x y v zl.1 zl.2

theorem pexp_idealOffsets (hε : 0 < ε) (v : ℕ → ℕ) (g : (ℕ → ℚ) × ℕ → ℝ≥0∞) :
    pexp (idealOffsets I ε δ v) g =
      ∑ o ∈ binPts I ε δ v, ENNReal.ofReal (1 / ∏ k ∈ Finset.range (nFree I ε δ),
        (binLen I ε δ k v : ℝ)) * g (binZ I ε δ v o, binL I ε δ v) :=
  pexp_loop_draws (fun k => binLo I ε δ k v) (fun k => binLen I ε δ k v) (nFree I ε δ)
    (fun k hk => (binLen_bounds I ε δ hε v hk).2.2) g

theorem pexp_corrLaw (hε : 0 < ε) (ξin : ℚ) (j : ℕ) (x y : ℕ → ℕ) (f : ℚ → ℝ≥0∞) :
    pexp (corrLaw I ε δ ξin j x y) f =
      ∑ v ∈ binSet I ε δ, ENNReal.ofReal (binV I ε δ j x y v / binS I ε δ j x y) *
        ∑ o ∈ binPts I ε δ v, ENNReal.ofReal (1 / ∏ k ∈ Finset.range (nFree I ε δ),
          (binLen I ε δ k v : ℝ)) *
            f (corrSample I ε δ ξin j x y v (binZ I ε δ v o) (binL I ε δ v)) := by
  unfold corrLaw
  rw [pexp_bind, pexp_binLaw I ε δ j x y (binSet_nonempty I ε δ (BParam_pos I ε δ hε))]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [pexp_map, pexp_idealOffsets I ε δ hε]
  rfl

/-- INTERNAL: the correction sample is `α_v` times the bisection value of `2^β`. -/
theorem corrSample_eq (ξin : ℚ) (j : ℕ) (x y v : ℕ → ℕ) (z : ℕ → ℚ) (L : ℕ) :
    (corrSample I ε δ ξin j x y v z L : ℝ) =
      (BParam I ε δ : ℝ) ^ nFree I ε δ * L / (Mf I ε δ : ℝ) *
        (pow2Approx I ε δ ξin ((binExp I ε δ j x y v : ℚ) -
          (j : ℚ) * penalty I ε δ x y z / (HParam I ε δ : ℚ)) : ℝ) := by
  unfold corrSample
  push_cast
  ring

/-- INTERNAL: the real mean of one ideal correction observation. -/
noncomputable def corrMean (ξin : ℚ) (j : ℕ) (x y : ℕ → ℕ) : ℝ :=
  ∑ v ∈ binSet I ε δ, binV I ε δ j x y v / binS I ε δ j x y *
    ∑ o ∈ binPts I ε δ v, 1 / (∏ k ∈ Finset.range (nFree I ε δ), (binLen I ε δ k v : ℝ)) *
      (corrSample I ε δ ξin j x y v (binZ I ε δ v o) (binL I ε δ v) : ℝ)

/-- INTERNAL: bounds on one correction observation. -/
theorem corr_term (hε : 0 < ε) (hfeas : feasible I) (x y : ℕ → ℕ) (j : ℕ)
    (hj : j ≤ HParam I ε δ) (ξin : ℚ) (hσ0 : 0 < oSigma I ε δ ξin)
    (hσ1 : oSigma I ε δ ξin ≤ 1 / 200) (v : ℕ → ℕ) {o : Fin (nFree I ε δ) → ℕ}
    (ho : o ∈ binPts I ε δ v) :
    let L : ℝ := ∏ k ∈ Finset.range (nFree I ε δ), (binLen I ε δ k v : ℝ)
    let cs : ℝ := corrSample I ε δ ξin j x y v (binZ I ε δ v o) (binL I ε δ v)
    let w : ℝ := (2 : ℝ) ^ (-((j : ℝ) * (penalty I ε δ x y (binZ I ε δ v o) : ℝ) /
      (HParam I ε δ : ℝ)))
    let σ : ℝ := oSigma I ε δ ξin
    0 < L ∧ 0 ≤ cs ∧ cs ≤ 16 ∧ (1 / 2) * (1 - σ) * (1 / 4) ≤ cs ∧
      (1 - σ) * ((BParam I ε δ : ℝ) ^ nFree I ε δ / (Mf I ε δ : ℝ) * w) ≤
        binV I ε δ j x y v * (1 / L * cs) ∧
      binV I ε δ j x y v * (1 / L * cs) ≤
        (1 + σ) * ((BParam I ε δ : ℝ) ^ nFree I ε δ / (Mf I ε δ : ℝ) * w) := by
  intro L cs w σ
  have ho' : ∀ k : Fin (nFree I ε δ), o k < binLen I ε δ k v := fun k =>
    Finset.mem_range.1 (Fintype.mem_piFinset.1 ho k)
  have hL : 0 < L := Finset.prod_pos fun k hk => by
    exact_mod_cast (binLen_bounds I ε δ hε v (Finset.mem_range.1 hk)).2.2
  have hLcast : ((binL I ε δ v : ℕ) : ℝ) = L := by unfold binL; push_cast; rfl
  obtain ⟨hα1, hα2⟩ := alpha_bounds I ε δ hε v
  set α : ℝ := (BParam I ε δ : ℝ) ^ nFree I ε δ * L / (Mf I ε δ : ℝ) with hαdef
  set β : ℚ := (binExp I ε δ j x y v : ℚ) - (j : ℚ) * penalty I ε δ x y (binZ I ε δ v o) /
    (HParam I ε δ : ℚ) with hβdef
  obtain ⟨hβ1, hβ2⟩ := beta_bounds I ε δ hε hfeas x y j hj v o ho'
  have hpow := pow2Approx_close I ε δ ξin hσ0 hσ1 β hβ1 hβ2
  have hp8 : (pow2Approx I ε δ ξin β : ℝ) ≤ 8 := by exact_mod_cast pow2Approx_le_eight I ε δ ξin β
  set P : ℝ := (2 : ℝ) ^ (β : ℝ)
  have hP1 : (1 / 4 : ℝ) ≤ P := by
    have : (2 : ℝ) ^ (-2 : ℝ) ≤ P := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by exact_mod_cast hβ1)
    norm_num at this ⊢; linarith
  have hσr : (σ : ℝ) ≤ 1 / 200 := by
    have h := (Rat.cast_le (K := ℝ)).2 hσ1
    rw [show (((1 / 200 : ℚ)) : ℝ) = 1 / 200 by norm_num] at h
    exact h
  have hσr0 : (0 : ℝ) < σ := by
    show (0 : ℝ) < ((oSigma I ε δ ξin : ℚ) : ℝ); exact_mod_cast hσ0
  have hp_lo : (1 - σ) * P ≤ pow2Approx I ε δ ξin β := by
    have := (abs_le.1 hpow).1; linarith
  have hp_hi : (pow2Approx I ε δ ξin β : ℝ) ≤ (1 + σ) * P := by
    have := (abs_le.1 hpow).2; linarith
  have hcs : cs = α * pow2Approx I ε δ ξin β := by
    show (corrSample I ε δ ξin j x y v (binZ I ε δ v o) (binL I ε δ v) : ℝ) = _
    rw [corrSample_eq, hLcast]
  have hVP : binV I ε δ j x y v * P = w := binV_mul_two_rpow I ε δ j x y v _
  have hV0 : 0 < binV I ε δ j x y v := binV_pos I ε δ j x y v
  have hMf : (0 : ℝ) < Mf I ε δ := by
    have : 0 < Mf I ε δ := by
      rw [Mf_eq_prod]; exact Finset.prod_pos fun k _ => Nat.succ_pos _
    exact_mod_cast this
  have hBe : (BParam I ε δ : ℝ) ^ nFree I ε δ / (Mf I ε δ : ℝ) = α / L := by
    rw [hαdef]; field_simp
  have hterm : binV I ε δ j x y v * (1 / L * cs) =
      (BParam I ε δ : ℝ) ^ nFree I ε δ / (Mf I ε δ : ℝ) * binV I ε δ j x y v *
        pow2Approx I ε δ ξin β := by
    rw [hcs, hBe]; field_simp
  have hK : 0 ≤ (BParam I ε δ : ℝ) ^ nFree I ε δ / (Mf I ε δ : ℝ) := by positivity
  refine ⟨hL, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcs]; apply mul_nonneg (by linarith); nlinarith
  · rw [hcs]
    calc α * pow2Approx I ε δ ξin β ≤ 2 * 8 :=
          mul_le_mul hα2 hp8 (by nlinarith) (by norm_num)
      _ = 16 := by norm_num
  · rw [hcs]
    have h1 : (1 - σ) * (1 / 4) ≤ (pow2Approx I ε δ ξin β : ℝ) := by nlinarith
    calc 1 / 2 * (1 - σ) * (1 / 4) = (1 / 2) * ((1 - σ) * (1 / 4)) := by ring
      _ ≤ α * pow2Approx I ε δ ξin β :=
          mul_le_mul hα1 h1 (by nlinarith) (by linarith)
  · rw [hterm, ← hVP]
    have := mul_le_mul_of_nonneg_left hp_lo (mul_nonneg hK hV0.le)
    nlinarith
  · rw [hterm, ← hVP]
    have := mul_le_mul_of_nonneg_left hp_hi (mul_nonneg hK hV0.le)
    nlinarith

/-- INTERNAL: the bins of the free box add up to `h_j`. -/
theorem sum_bins_hWeight (hε : 0 < ε) (j : ℕ) (x y : ℕ → ℕ) :
    ∑ v ∈ binSet I ε δ, ∑ o ∈ binPts I ε δ v,
      (2 : ℝ) ^ (-((j : ℝ) * (penalty I ε δ x y (binZ I ε δ v o) : ℝ) / (HParam I ε δ : ℝ))) =
    hWeight I ε δ j x y := by
  rw [sum_binSet]
  have hB := BParam_pos I ε δ hε
  have key := sum_bins (BParam I ε δ) hB (fun k : Fin (nFree I ε δ) => (freeAt I ε δ k).2.2 + 1)
    (fun k => Nat.succ_pos _) (fun z => (2 : ℝ) ^ (-((j : ℝ) *
      (penalty I ε δ x y (extendQ z) : ℝ) / (HParam I ε δ : ℝ))))
  unfold hWeight freeBox
  rw [← key]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hpts : binPts I ε δ (extendN u) = Fintype.piFinset (fun k : Fin (nFree I ε δ) =>
      Finset.range (((freeAt I ε δ k).2.2 + 1) * (u k + 1) ⌈/⌉ BParam I ε δ -
        ((freeAt I ε δ k).2.2 + 1) * u k ⌈/⌉ BParam I ε δ)) := by
    unfold binPts binLen binHi binLo
    simp only [extendN_val]
  rw [hpts]
  refine Finset.sum_congr rfl fun o _ => ?_
  have hz : binZ I ε δ (extendN u) o =
      extendQ (fun k : Fin (nFree I ε δ) => ((freeAt I ε δ k).2.2 + 1) * u k ⌈/⌉ BParam I ε δ + o k) := by
    funext k
    unfold binZ drawPt extendQ binLo
    by_cases hk : k < nFree I ε δ
    · rw [dif_pos hk, dif_pos hk]
      have := extendN_val u ⟨k, hk⟩
      simp only at this
      simp only [this]
    · rw [dif_neg hk, dif_neg hk]
  rw [hz]

set_option maxHeartbeats 1000000 in
/-- **Mean of the correction** (`eq:oracle-correction` and the identity below it):
under the ideal laws the correction observation has mean within relative error `σ`
of `E T = B^e h_j / (M_f S_j)`, at least `(1 - σ)/8`, and its values lie in `[0, 16]`.
PAPER: sections/evaluation.tex:95-112 -/
theorem corr_mean (hε : 0 < ε) (hfeas : feasible I) (x y : ℕ → ℕ) (j : ℕ)
    (hj : j ≤ HParam I ε δ) (ξin : ℚ) (hσ0 : 0 < oSigma I ε δ ξin)
    (hσ1 : oSigma I ε δ ξin ≤ 1 / 200) :
    pexp (corrLaw I ε δ ξin j x y) (fun q => ENNReal.ofReal (q : ℝ)) =
        ENNReal.ofReal (corrMean I ε δ ξin j x y) ∧
      (1 - (oSigma I ε δ ξin : ℝ)) * ((BParam I ε δ : ℝ) ^ nFree I ε δ * hWeight I ε δ j x y /
          ((Mf I ε δ : ℝ) * binS I ε δ j x y)) ≤ corrMean I ε δ ξin j x y ∧
      corrMean I ε δ ξin j x y ≤ (1 + (oSigma I ε δ ξin : ℝ)) * ((BParam I ε δ : ℝ) ^ nFree I ε δ *
          hWeight I ε δ j x y / ((Mf I ε δ : ℝ) * binS I ε δ j x y)) ∧
      (1 / 2) * (1 - (oSigma I ε δ ξin : ℝ)) * (1 / 4) ≤ corrMean I ε δ ξin j x y ∧
      ∀ q ∈ (corrLaw I ε δ ξin j x y).support, 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 16 := by
  have hne := binSet_nonempty I ε δ (BParam_pos I ε δ hε)
  have hS := binS_pos I ε δ j x y hne
  have hT := fun v o (ho : o ∈ binPts I ε δ v) =>
    corr_term I ε δ hε hfeas x y j hj ξin hσ0 hσ1 v ho
  set σ : ℝ := ((oSigma I ε δ ξin : ℚ) : ℝ)
  set K : ℝ := (BParam I ε δ : ℝ) ^ nFree I ε δ / (Mf I ε δ : ℝ)
  -- the mean, as a double sum of bounded terms
  have hmean : corrMean I ε δ ξin j x y = ∑ v ∈ binSet I ε δ, ∑ o ∈ binPts I ε δ v,
      (binV I ε δ j x y v * (1 / (∏ k ∈ Finset.range (nFree I ε δ), (binLen I ε δ k v : ℝ)) *
        (corrSample I ε δ ξin j x y v (binZ I ε δ v o) (binL I ε δ v) : ℝ))) /
          binS I ε δ j x y := by
    unfold corrMean
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    ring
  have hW := sum_bins_hWeight I ε δ hε j x y
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the `ENNReal` expectation is the real mean
    rw [pexp_corrLaw I ε δ hε, corrMean, ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl fun v _ => ?_
      rw [ENNReal.ofReal_mul (div_nonneg (binV_pos I ε δ j x y v).le hS.le),
        ENNReal.ofReal_sum_of_nonneg]
      · congr 1
        refine Finset.sum_congr rfl fun o ho => ?_
        obtain ⟨hL, hcs0, -⟩ := hT v o ho
        rw [ENNReal.ofReal_mul (by positivity)]
      · intro o ho
        obtain ⟨hL, hcs0, -⟩ := hT v o ho
        positivity
    · intro v _
      apply mul_nonneg (div_nonneg (binV_pos I ε δ j x y v).le hS.le)
      exact Finset.sum_nonneg fun o ho => by
        obtain ⟨hL, hcs0, -⟩ := hT v o ho
        positivity
  · rw [hmean]
    calc (1 - σ) * ((BParam I ε δ : ℝ) ^ nFree I ε δ * hWeight I ε δ j x y /
          ((Mf I ε δ : ℝ) * binS I ε δ j x y))
        = ∑ v ∈ binSet I ε δ, ∑ o ∈ binPts I ε δ v, (1 - σ) * (K * (2 : ℝ) ^ (-((j : ℝ) *
            (penalty I ε δ x y (binZ I ε δ v o) : ℝ) / (HParam I ε δ : ℝ)))) /
              binS I ε δ j x y := by
          rw [← hW]
          simp_rw [← Finset.sum_div, ← Finset.mul_sum]
          simp only [K]
          ring
      _ ≤ _ := by
          refine Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun o ho => ?_
          exact div_le_div_of_nonneg_right (hT v o ho).2.2.2.2.1 hS.le
  · rw [hmean]
    calc _ ≤ ∑ v ∈ binSet I ε δ, ∑ o ∈ binPts I ε δ v, (1 + σ) * (K * (2 : ℝ) ^ (-((j : ℝ) *
            (penalty I ε δ x y (binZ I ε δ v o) : ℝ) / (HParam I ε δ : ℝ)))) /
              binS I ε δ j x y := by
          refine Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun o ho => ?_
          exact div_le_div_of_nonneg_right (hT v o ho).2.2.2.2.2 hS.le
      _ = (1 + σ) * ((BParam I ε δ : ℝ) ^ nFree I ε δ * hWeight I ε δ j x y /
          ((Mf I ε δ : ℝ) * binS I ε δ j x y)) := by
          rw [← hW]
          simp_rw [← Finset.sum_div, ← Finset.mul_sum]
          simp only [K]
          ring
  · -- the lower bound `(1 - σ)/8`
    unfold corrMean
    have hsum1 : ∑ v ∈ binSet I ε δ, binV I ε δ j x y v / binS I ε δ j x y = 1 := by
      rw [← Finset.sum_div]; exact div_self hS.ne'
    have hcard : ∀ v, ∑ o ∈ binPts I ε δ v, 1 / (∏ k ∈ Finset.range (nFree I ε δ),
        (binLen I ε δ k v : ℝ)) * ((1 / 2) * (1 - σ) * (1 / 4)) = (1 / 2) * (1 - σ) * (1 / 4) := by
      intro v
      have hL : (0 : ℝ) < ∏ k ∈ Finset.range (nFree I ε δ), (binLen I ε δ k v : ℝ) :=
        Finset.prod_pos fun k hk => by
          exact_mod_cast (binLen_bounds I ε δ hε v (Finset.mem_range.1 hk)).2.2
      rw [← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, binPts, Fintype.card_piFinset]
      simp only [Finset.card_range]
      rw [Fin.prod_univ_eq_prod_range (fun k => binLen I ε δ k v)]
      push_cast
      field_simp
    calc (1 / 2) * (1 - σ) * (1 / 4)
        = (∑ v ∈ binSet I ε δ, binV I ε δ j x y v / binS I ε δ j x y) *
            ((1 / 2) * (1 - σ) * (1 / 4)) := by rw [hsum1, one_mul]
      _ = ∑ v ∈ binSet I ε δ, binV I ε δ j x y v / binS I ε δ j x y *
            ∑ o ∈ binPts I ε δ v, 1 / (∏ k ∈ Finset.range (nFree I ε δ),
              (binLen I ε δ k v : ℝ)) * ((1 / 2) * (1 - σ) * (1 / 4)) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun v _ => by rw [hcard v]
      _ ≤ _ := by
          refine Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun o ho => ?_) (div_nonneg (binV_pos I ε δ j x y v).le hS.le)
          obtain ⟨hL, -, -, hlow, -⟩ := hT v o ho
          exact mul_le_mul_of_nonneg_left hlow (by positivity)
  · -- the support
    intro q hq
    have hform : ∀ f : ℚ → ℝ≥0∞, pexp (corrLaw I ε δ ξin j x y) f =
        ∑ p ∈ (binSet I ε δ).sigma fun v => binPts I ε δ v,
          (ENNReal.ofReal (binV I ε δ j x y p.1 / binS I ε δ j x y) *
            ENNReal.ofReal (1 / ∏ k ∈ Finset.range (nFree I ε δ), (binLen I ε δ k p.1 : ℝ))) *
          f (corrSample I ε δ ξin j x y p.1 (binZ I ε δ p.1 p.2) (binL I ε δ p.1)) := by
      intro f
      rw [pexp_corrLaw I ε δ hε, Finset.sum_sigma]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun o _ => by ring
    obtain ⟨p, hp, rfl⟩ := support_of_pexp _ _ _ _ hform q hq
    obtain ⟨-, hp2⟩ := Finset.mem_sigma.1 hp
    obtain ⟨-, h0, h16, -⟩ := hT p.1 p.2 hp2
    exact ⟨h0, h16⟩

/-! ### Ratio observations and the telescoping product -/

/-- INTERNAL: one ratio observation `R_a(v) = V_{a+1}(v)/V_a(v)` at an exact bin `v ~ π_a`.
TEXLINE: sections/evaluation.tex:93-99 -/
noncomputable def ratioLaw (a : ℕ) (x y : ℕ → ℕ) : PMF ℚ :=
  (binLaw I ε δ a x y).map (ratioSample I ε δ a x y)

/-- INTERNAL: `V_a(v) R_a(v) = V_{a+1}(v)`. -/
theorem binV_mul_ratio (a : ℕ) (x y v : ℕ → ℕ) :
    binV I ε δ a x y v * (ratioSample I ε δ a x y v : ℝ) = binV I ε δ (a + 1) x y v := by
  unfold binV ratioSample binExp
  push_cast
  rw [← zpow_add₀ two_ne_zero]
  congr 1
  ring

/-- INTERNAL: the ratio observation has mean `S_{a+1}/S_a`.
TEXLINE: sections/evaluation.tex:93-99 -/
theorem pexp_ratioLaw (hε : 0 < ε) (a : ℕ) (x y : ℕ → ℕ) :
    pexp (ratioLaw I ε δ a x y) (fun q => ENNReal.ofReal (q : ℝ)) =
      ENNReal.ofReal (binS I ε δ (a + 1) x y / binS I ε δ a x y) := by
  have hne := binSet_nonempty I ε δ (BParam_pos I ε δ hε)
  have hS := binS_pos I ε δ a x y hne
  unfold ratioLaw
  rw [pexp_map, pexp_binLaw I ε δ a x y hne]
  have hR : ∀ v, (0 : ℝ) ≤ ratioSample I ε δ a x y v := fun v => by
    unfold ratioSample; push_cast; positivity
  rw [show binS I ε δ (a + 1) x y / binS I ε δ a x y =
      ∑ v ∈ binSet I ε δ, binV I ε δ a x y v / binS I ε δ a x y * ratioSample I ε δ a x y v by
    rw [binS, Finset.sum_div]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← binV_mul_ratio]; ring,
    ENNReal.ofReal_sum_of_nonneg fun v _ =>
      mul_nonneg (div_nonneg (binV_pos I ε δ a x y v).le hS.le) (hR v)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [ENNReal.ofReal_mul (div_nonneg (binV_pos I ε δ a x y v).le hS.le)]
  rfl

/-- INTERNAL: the ratio observations lie in `[1/2, 1]`, since `0 ≤ D/H ≤ 1` on the bins.
TEXLINE: sections/evaluation.tex:97-99 -/
theorem ratioSample_mem (hε : 0 < ε) (hfeas : feasible I) (x y : ℕ → ℕ)
    (hbox : ∀ s < nSmall I ε δ, x s ≤ smallB I ε δ s ∧ y s ≤ smallB I ε δ s) (a : ℕ)
    {v : ℕ → ℕ} (hv : v ∈ binSet I ε δ) :
    (1 / 2 : ℝ) ≤ ratioSample I ε δ a x y v ∧ (ratioSample I ε δ a x y v : ℝ) ≤ 1 := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
  have hB := BParam_pos I ε δ hε
  have hBq : (0 : ℚ) < BParam I ε δ := by exact_mod_cast hB
  have hH : (0 : ℚ) < HParam I ε δ := by exact_mod_cast HParam_pos I ε δ hε
  set D := penalty I ε δ x y (binPoint I ε δ (extendN u))
  have hD0 : 0 ≤ D := pseudo_penalty_nonneg I ε δ x y _
  have hDH : D ≤ HParam I ε δ := by
    refine pseudo_penalty_le_H I ε δ hε hfeas x y _ hbox (fun k hk => ?_)
    have huk : extendN u k < BParam I ε δ := by
      have := extendN_val u ⟨k, hk⟩
      simp only at this
      rw [this]
      exact Finset.mem_range.1 (Fintype.mem_piFinset.1 hu _)
    unfold binPoint
    constructor
    · positivity
    · rw [div_le_iff₀ hBq]
      push_cast
      have : ((extendN u k : ℕ) : ℚ) ≤ BParam I ε δ := by exact_mod_cast huk.le
      nlinarith
  set t : ℚ := (a : ℚ) * D / HParam I ε δ with hdef_t
  have hshift : ((a + 1 : ℕ) : ℚ) * D / HParam I ε δ = t + D / HParam I ε δ := by
    rw [hdef_t]; push_cast; ring
  have hq0 : (0 : ℚ) ≤ D / HParam I ε δ := div_nonneg hD0 hH.le
  have hq1 : D / HParam I ε δ ≤ 1 := (div_le_one hH).2 hDH
  have hk1 : levelExp I ε δ a D ≤ levelExp I ε δ (a + 1) D := by
    unfold levelExp; rw [hshift]; exact Int.floor_mono (by linarith)
  have hk2 : levelExp I ε δ (a + 1) D ≤ levelExp I ε δ a D + 1 := by
    unfold levelExp
    rw [hshift]
    have h1 := Int.floor_le (t + D / HParam I ε δ)
    have h2 := Int.lt_floor_add_one t
    have h3 : ((⌊t + D / HParam I ε δ⌋ : ℤ) : ℚ) < ((⌊t⌋ + 2 : ℤ) : ℚ) := by
      push_cast; linarith
    have h4 : ⌊t + D / HParam I ε δ⌋ < ⌊t⌋ + 2 := by exact_mod_cast h3
    change ⌊t + D / HParam I ε δ⌋ ≤ ⌊t⌋ + 1
    omega
  have hcase : levelExp I ε δ a D - levelExp I ε δ (a + 1) D = 0 ∨
      levelExp I ε δ a D - levelExp I ε δ (a + 1) D = -1 := by omega
  unfold ratioSample
  change (1 / 2 : ℝ) ≤ (((2 : ℚ) ^ (levelExp I ε δ a D - levelExp I ε δ (a + 1) D) : ℚ) : ℝ) ∧
    ((((2 : ℚ) ^ (levelExp I ε δ a D - levelExp I ε δ (a + 1) D) : ℚ) : ℝ) ≤ 1)
  rcases hcase with h | h <;> rw [h] <;> norm_num

/-- INTERNAL: `S_0 = B^e`, since `V_0 = 1`. -/
theorem binS_zero (x y : ℕ → ℕ) : binS I ε δ 0 x y = (BParam I ε δ : ℝ) ^ nFree I ε δ := by
  unfold binS
  have : ∀ v, binV I ε δ 0 x y v = 1 := fun v => by
    unfold binV binExp levelExp; simp
  simp_rw [this]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  unfold binSet
  rw [Finset.card_image_of_injective _ extendN_injective, Fintype.card_piFinset]
  simp

/-- INTERNAL: the ratio means telescope, `∏_{a<j} S_{a+1}/S_a = S_j/S_0`.
TEXLINE: sections/evaluation.tex:113-118 -/
theorem prod_ratio_means (hε : 0 < ε) (x y : ℕ → ℕ) (j : ℕ) :
    ∏ a ∈ Finset.range j, binS I ε δ (a + 1) x y / binS I ε δ a x y =
      binS I ε δ j x y / binS I ε δ 0 x y := by
  have hne := binSet_nonempty I ε δ (BParam_pos I ε δ hε)
  induction j with
  | zero => simp [div_self (binS_pos I ε δ 0 x y hne).ne']
  | succ j ih =>
    rw [Finset.prod_range_succ, ih]
    have h1 := binS_pos I ε δ j x y hne
    have h2 := binS_pos I ε δ 0 x y hne
    field_simp

/-! ### The ideal oracle -/

/-- INTERNAL: `R̂_a` with exact bin draws.
TEXLINE: sections/evaluation.tex:392-406 -/
noncomputable def ratioIdeal (ξin θ : ℚ) (a : ℕ) (x y : ℕ → ℕ) : PMF ℚ :=
  (sumLoop (ratioLaw I ε δ a x y) (oN I ε δ ξin θ)).map (· / (oN I ε δ ξin θ : ℚ))

/-- INTERNAL: `T̂` with exact bin and offset draws.
TEXLINE: sections/evaluation.tex:392-406 -/
noncomputable def corrIdeal (ξin θ : ℚ) (j : ℕ) (x y : ℕ → ℕ) : PMF ℚ :=
  (sumLoop (corrLaw I ε δ ξin j x y) (oN I ε δ ξin θ)).map (· / (oN I ε δ ξin θ : ℚ))

/-- INTERNAL: the oracle with every bin walk and offset draw replaced by an exact draw.
TEXLINE: sections/evaluation.tex:373-388 -/
noncomputable def oracleIdeal (x y : ℕ → ℕ) (j : ℕ) (ξin θ : ℚ) : PMF ℚ :=
  (loop (fun a P => (ratioIdeal I ε δ ξin θ a x y).map fun r => P * r) j 1).bind fun P =>
    (corrIdeal I ε δ ξin θ j x y).bind fun T => PMF.pure ((Mf I ε δ : ℚ) * P * T)

section close
variable (hε : 0 < ε) (hε1 : ε < 1) (hfeas : feasible I) (x y : ℕ → ℕ)
  (hbox : ∀ s < nSmall I ε δ, x s ≤ smallB I ε δ s ∧ y s ≤ smallB I ε δ s)
  (ξin θ : ℚ) (hξ : 0 < ξin) (hξ1 : ξin < 1 / 4) (hθ : 0 < θ) (hθ1 : θ < 1 / 4)
include hε hε1 hfeas hbox hξ hξ1 hθ hθ1

/-- INTERNAL: `R̂_a` is within `N_in ζ` of its ideal version.
TEXLINE: sections/evaluation.tex:373-388 -/
theorem ratioAvg_close (a : ℕ) (ha : a ≤ HParam I ε δ) :
    PClose (ratioAvg I ε δ ξin θ a x y) (ratioIdeal I ε δ ξin θ a x y)
      (oN I ε δ ξin θ * ENNReal.ofReal (oZeta I ε δ ξin θ)) := by
  unfold ratioAvg ratioIdeal sumLoop ratioLaw
  refine PClose.map ?_ _
  have := PClose.loop (ζ := fun _ => ENNReal.ofReal (oZeta I ε δ ξin θ))
    (f := fun _ s => (sampleBin I ε δ ξin θ a x y).map fun v => s + ratioSample I ε δ a x y v)
    (g := fun _ s => ((binLaw I ε δ a x y).map (ratioSample I ε δ a x y)).map (s + ·))
    (fun i s => by
      rw [PMF.map_comp]
      exact (sampleBin_close I ε δ hε hε1 hfeas x y hbox a ha ξin θ hξ hξ1 hθ hθ1).map _)
    (oN I ε δ ξin θ) 0
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  exact this

/-- INTERNAL: `T̂` is within `N_in (e + 1) ζ` of its ideal version.
TEXLINE: sections/evaluation.tex:373-388 -/
theorem corrAvg_close (j : ℕ) (hj : j ≤ HParam I ε δ) (hζ : 0 < oZeta I ε δ ξin θ) :
    PClose (corrAvg I ε δ ξin θ j x y) (corrIdeal I ε δ ξin θ j x y)
      (oN I ε δ ξin θ * ((nFree I ε δ + 1) * ENNReal.ofReal (oZeta I ε δ ξin θ))) := by
  unfold corrAvg corrIdeal sumLoop corrLaw
  refine PClose.map ?_ _
  have := PClose.loop (ζ := fun _ => (nFree I ε δ + 1) * ENNReal.ofReal (oZeta I ε δ ξin θ))
    (f := fun _ s => (sampleBin I ε δ ξin θ j x y).bind fun v =>
      (binOffsets I ε δ ξin θ v).map fun zl => s + corrSample I ε δ ξin j x y v zl.1 zl.2)
    (g := fun _ s => ((binLaw I ε δ j x y).bind fun v =>
      (idealOffsets I ε δ v).map fun zl => corrSample I ε δ ξin j x y v zl.1 zl.2).map (s + ·))
    (fun i s => by
      rw [PMF.map_bind]
      simp_rw [PMF.map_comp]
      simp only [Function.comp_def]
      have hK : ∀ v ∈ (sampleBin I ε δ ξin θ j x y).support,
          PClose ((binOffsets I ε δ ξin θ v).map fun zl =>
              s + corrSample I ε δ ξin j x y v zl.1 zl.2)
            ((idealOffsets I ε δ v).map fun zl => s + corrSample I ε δ ξin j x y v zl.1 zl.2)
            ((nFree I ε δ : ℝ≥0∞) * ENNReal.ofReal (oZeta I ε δ ξin θ)) := fun v _ =>
        PClose.map (binOffsets_close I ε δ ξin θ v hζ)
          (fun zl => s + corrSample I ε δ ξin j x y v zl.1 zl.2)
      have h := PClose.bind (sampleBin_close I ε δ hε hε1 hfeas x y hbox j hj ξin θ hξ hξ1 hθ hθ1)
        hK
      refine h.mono (le_of_eq ?_)
      ring)
    (oN I ε δ ξin θ) 0
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  convert this using 2
  funext i s
  simp only [bind_pure_comp]
  rfl

/-- INTERNAL: the oracle is within `j N_in ζ + N_in (e + 1) ζ` of the ideal oracle.
TEXLINE: sections/evaluation.tex:373-388 -/
theorem oracle_close (j : ℕ) (hj : j ≤ HParam I ε δ) (hζ : 0 < oZeta I ε δ ξin θ) :
    PClose (oracle I ε δ x y j ξin θ) (oracleIdeal I ε δ x y j ξin θ)
      (j * (oN I ε δ ξin θ * ENNReal.ofReal (oZeta I ε δ ξin θ)) +
        (oN I ε δ ξin θ * ((nFree I ε δ + 1) * ENNReal.ofReal (oZeta I ε δ ξin θ)) + 0)) := by
  have hloop := PClose.loop
    (ζ := fun i => if i < j then oN I ε δ ξin θ * ENNReal.ofReal (oZeta I ε δ ξin θ) else 1)
    (f := fun a P => (ratioAvg I ε δ ξin θ a x y).map fun r => P * r)
    (g := fun a P => (ratioIdeal I ε δ ξin θ a x y).map fun r => P * r)
    (fun i P => by
      by_cases hi : i < j
      · rw [if_pos hi]
        exact (ratioAvg_close I ε δ hε hε1 hfeas x y hbox ξin θ hξ hξ1 hθ hθ1 i (by omega)).map _
      · rw [if_neg hi]; exact PClose.one _ _) j 1
  rw [Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.1 hi)), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hloop
  exact hloop.bind fun P _ =>
    (corrAvg_close I ε δ hε hε1 hfeas x y hbox ξin θ hξ hξ1 hθ hθ1 j hj hζ).bind fun T _ =>
      PClose.refl _ 0

end close

end inst

/-! ### Chebyshev for the ideal oracle -/

/-- INTERNAL: `n` factors `1 ± σ` with `n σ ≤ ξ/2` stay within `1 ± ξ`. -/
theorem pow_window (σ ξ : ℝ) (n : ℕ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hn : (n : ℝ) * σ ≤ ξ / 2)
    (hξ : ξ ≤ 1) : 1 - ξ ≤ (1 - σ) ^ n ∧ (1 + σ) ^ n ≤ 1 + ξ := by
  have hbern : 1 - (n : ℝ) * σ ≤ (1 - σ) ^ n := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -σ by linarith) n
    rw [sub_eq_add_neg, sub_eq_add_neg]; nlinarith
  have hn0 : (0 : ℝ) ≤ n * σ := by positivity
  refine ⟨by linarith, ?_⟩
  have hprod : (1 + σ) ^ n * (1 - σ) ^ n ≤ 1 := by
    rw [← mul_pow]; exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have hpos : 0 < 1 - (n : ℝ) * σ := by linarith
  have h1 : (1 + σ) ^ n * (1 - (n : ℝ) * σ) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hbern (by positivity)).trans hprod
  have h2 : 1 ≤ (1 + 2 * ((n : ℝ) * σ)) * (1 - (n : ℝ) * σ) := by nlinarith
  have : (1 + σ) ^ n ≤ 1 + 2 * ((n : ℝ) * σ) := by
    by_contra hc
    push_neg at hc
    nlinarith
  linarith

/-- INTERNAL: the error window of the assembled ideal oracle: `M_f P T` lies within
`1 ± ξ` of `h = M_f Π K` when `P` is within `(1 ± σ)^n` of `Π` and `T` within
`(1 ± σ)²` of `K`. -/
theorem oracle_err_window (Mf Pm K hW P T σ ξ : ℝ) (n : ℕ) (hMf : 0 ≤ Mf) (hPm : 0 ≤ Pm)
    (hK : 0 ≤ K) (hW0 : 0 ≤ hW) (hid : Mf * Pm * K = hW) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hlo : 1 - ξ ≤ (1 - σ) ^ (n + 2)) (hhi : (1 + σ) ^ (n + 2) ≤ 1 + ξ)
    (hP : (1 - σ) ^ n * Pm ≤ P ∧ P ≤ (1 + σ) ^ n * Pm)
    (hT : (1 - σ) * ((1 - σ) * K) ≤ T ∧ T ≤ (1 + σ) * ((1 + σ) * K)) :
    (1 - ξ) * hW ≤ Mf * P * T ∧ Mf * P * T ≤ (1 + ξ) * hW := by
  have hu : 0 ≤ 1 - σ := by linarith
  have hLP : 0 ≤ (1 - σ) ^ n * Pm := by positivity
  have hLT : 0 ≤ (1 - σ) * ((1 - σ) * K) := by positivity
  have hP0 : 0 ≤ P := hLP.trans hP.1
  have hT0 : 0 ≤ T := hLT.trans hT.1
  constructor
  · calc (1 - ξ) * hW ≤ (1 - σ) ^ (n + 2) * hW := mul_le_mul_of_nonneg_right hlo hW0
      _ = Mf * ((1 - σ) ^ n * Pm) * ((1 - σ) * ((1 - σ) * K)) := by rw [← hid]; ring
      _ ≤ Mf * P * T := by
        rw [mul_assoc, mul_assoc Mf]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hP.1 hT.1 hLT hP0) hMf
  · calc Mf * P * T ≤ Mf * ((1 + σ) ^ n * Pm) * ((1 + σ) * ((1 + σ) * K)) := by
          rw [mul_assoc, mul_assoc Mf]
          exact mul_le_mul_of_nonneg_left (mul_le_mul hP.2 hT.2 hT0 (by positivity)) hMf
      _ = (1 + σ) ^ (n + 2) * hW := by rw [← hid]; ring
      _ ≤ (1 + ξ) * hW := mul_le_mul_of_nonneg_right hhi hW0

/-- INTERNAL: the Chebyshev budget `2j + 144 ≤ θ N σ²/4`. -/
theorem budget_arith (j H t X : ℝ) (hj : j ≤ H) (hj0 : 0 ≤ j) (h : 1000000 * (H + 1) ≤ t * X) :
    2 * j + 144 ≤ t / 4 * X := by
  nlinarith

section ideal
variable (I : Instance) (ε δ : ℚ)

/-- INTERNAL: `0 < σ ≤ 1/200` and `(H + 2) σ ≤ ξ_in / 2`. -/
theorem oSigma_bounds (ξin : ℚ) (hξ : 0 < ξin) (hξ1 : ξin < 1 / 4) :
    0 < oSigma I ε δ ξin ∧ oSigma I ε δ ξin ≤ 1 / 200 ∧
      ((HParam I ε δ : ℚ) + 2) * oSigma I ε δ ξin ≤ ξin / 2 := by
  have hH : (0 : ℚ) ≤ HParam I ε δ := by positivity
  unfold oSigma
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]; nlinarith
  · rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith

/-- INTERNAL: `N_in > 0` and `θ N_in σ² ≥ 10⁶ (H + 1)`. -/
theorem oN_spec (ξin θ : ℚ) (hξ : 0 < ξin) (hθ : 0 < θ) :
    0 < oN I ε δ ξin θ ∧
      1000000 * ((HParam I ε δ : ℝ) + 1) ≤
        θ * ((oN I ε δ ξin θ : ℝ) * (oSigma I ε δ ξin : ℝ) ^ 2) := by
  have hσ : 0 < oSigma I ε δ ξin := by unfold oSigma; positivity
  have hq : (0 : ℚ) < 1000000 * ((HParam I ε δ : ℚ) + 1) / (θ * oSigma I ε δ ξin ^ 2) := by
    positivity
  refine ⟨Nat.ceil_pos.2 hq, ?_⟩
  have h := Nat.le_ceil (1000000 * ((HParam I ε δ : ℚ) + 1) / (θ * oSigma I ε δ ξin ^ 2))
  rw [div_le_iff₀ (by positivity)] at h
  have : 1000000 * ((HParam I ε δ : ℚ) + 1) ≤ θ * ((oN I ε δ ξin θ : ℚ) * oSigma I ε δ ξin ^ 2) := by
    unfold oN; linarith
  exact_mod_cast this

/-- INTERNAL: Chebyshev for one ideal ratio average: it leaves `(1 ± σ) S_{a+1}/S_a`
with probability at most `2/(N_in σ²)`.
TEXLINE: sections/evaluation.tex:398-406 -/
theorem ratioIdeal_bad (hε : 0 < ε) (hfeas : feasible I) (x y : ℕ → ℕ)
    (hbox : ∀ s < nSmall I ε δ, x s ≤ smallB I ε δ s ∧ y s ≤ smallB I ε δ s)
    (ξin θ : ℚ) (hξ : 0 < ξin) (hθ : 0 < θ) (a : ℕ) :
    (ratioIdeal I ε δ ξin θ a x y).toOuterMeasure
        {r | ¬ ((1 - (oSigma I ε δ ξin : ℝ)) * (binS I ε δ (a + 1) x y / binS I ε δ a x y) ≤
            (r : ℝ) ∧
          (r : ℝ) ≤ (1 + (oSigma I ε δ ξin : ℝ)) * (binS I ε δ (a + 1) x y / binS I ε δ a x y))} ≤
      ENNReal.ofReal (2 / ((oN I ε δ ξin θ : ℝ) * (oSigma I ε δ ξin : ℝ) ^ 2)) := by
  have hne := binSet_nonempty I ε δ (BParam_pos I ε δ hε)
  have hS := binS_pos I ε δ a x y hne
  have hσ : (0 : ℝ) < oSigma I ε δ ξin := by
    have : 0 < oSigma I ε δ ξin := by unfold oSigma; positivity
    exact_mod_cast this
  have hN := (oN_spec I ε δ ξin θ hξ hθ).1
  have hNr : (0 : ℝ) < oN I ε δ ξin θ := by exact_mod_cast hN
  have hsupp : ∀ q ∈ (ratioLaw I ε δ a x y).support, 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 1 := by
    intro q hq
    unfold ratioLaw at hq
    rw [PMF.support_map] at hq
    obtain ⟨v, hv, rfl⟩ := hq
    have := ratioSample_mem I ε δ hε hfeas x y hbox a (binLaw_support I ε δ a x y hne v hv)
    exact ⟨by linarith [this.1], this.2⟩
  have hm : 1 / 2 ≤ binS I ε δ (a + 1) x y / binS I ε δ a x y := by
    rw [le_div_iff₀ hS, binS, binS, Finset.mul_sum]
    refine Finset.sum_le_sum fun v hv => ?_
    rw [← binV_mul_ratio]
    have := ratioSample_mem I ε δ hε hfeas x y hbox a hv
    nlinarith [binV_pos I ε δ a x y v]
  unfold ratioIdeal
  refine (avg_chebyshev (ratioLaw I ε δ a x y) 1 hsupp zero_le_one _
    (pexp_ratioLaw I ε δ hε a x y) (by linarith) _ hN _ hσ).trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hX : 0 < (oN I ε δ ξin θ : ℝ) * (oSigma I ε δ ξin : ℝ) ^ 2 := by positivity
  nlinarith

/-- INTERNAL: Chebyshev for the ideal correction average: it leaves `(1 ± σ)` times its
mean with probability at most `144/(N_in σ²)`.
TEXLINE: sections/evaluation.tex:398-406 -/
theorem corrIdeal_bad (hε : 0 < ε) (hfeas : feasible I) (x y : ℕ → ℕ) (j : ℕ)
    (hj : j ≤ HParam I ε δ) (ξin θ : ℚ) (hξ : 0 < ξin) (hξ1 : ξin < 1 / 4) (hθ : 0 < θ) :
    (corrIdeal I ε δ ξin θ j x y).toOuterMeasure
        {t | ¬ ((1 - (oSigma I ε δ ξin : ℝ)) * corrMean I ε δ ξin j x y ≤ (t : ℝ) ∧
          (t : ℝ) ≤ (1 + (oSigma I ε δ ξin : ℝ)) * corrMean I ε δ ξin j x y)} ≤
      ENNReal.ofReal (144 / ((oN I ε δ ξin θ : ℝ) * (oSigma I ε δ ξin : ℝ) ^ 2)) := by
  obtain ⟨hσ0, hσ1, -⟩ := oSigma_bounds I ε δ ξin hξ hξ1
  have hσ : (0 : ℝ) < oSigma I ε δ ξin := by exact_mod_cast hσ0
  have hσ1r : (oSigma I ε δ ξin : ℝ) ≤ 1 / 200 := by
    rw [show (1 / 200 : ℝ) = ((1 / 200 : ℚ) : ℝ) by norm_num]; exact_mod_cast hσ1
  have hN := (oN_spec I ε δ ξin θ hξ hθ).1
  have hNr : (0 : ℝ) < oN I ε δ ξin θ := by exact_mod_cast hN
  obtain ⟨hmean, -, -, hlow, hsupp⟩ := corr_mean I ε δ hε hfeas x y j hj ξin hσ0 hσ1
  have hm : 1 / 9 ≤ corrMean I ε δ ξin j x y := by nlinarith
  unfold corrIdeal
  refine (avg_chebyshev (corrLaw I ε δ ξin j x y) 16 hsupp (by norm_num) _ hmean
    (by linarith) _ hN _ hσ).trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hX : 0 < (oN I ε δ ξin θ : ℝ) * (oSigma I ε δ ξin : ℝ) ^ 2 := by positivity
  nlinarith

/-- INTERNAL: the ideal oracle leaves `[(1 - ξ_in) h_j, (1 + ξ_in) h_j]` with
probability at most `θ/4`: Chebyshev for each of the `j + 1` averages, a union bound,
and the telescoping identity `M_f ∏_{a<j} (S_{a+1}/S_a) · B^e h_j/(M_f S_j) = h_j`.
TEXLINE: sections/evaluation.tex:392-416 -/
theorem oracleIdeal_bad (hε : 0 < ε) (hfeas : feasible I) (x y : ℕ → ℕ)
    (hbox : ∀ s < nSmall I ε δ, x s ≤ smallB I ε δ s ∧ y s ≤ smallB I ε δ s)
    (j : ℕ) (hj : j ≤ HParam I ε δ) (ξin θ : ℚ) (hξ : 0 < ξin) (hξ1 : ξin < 1 / 4)
    (hθ : 0 < θ) :
    (oracleIdeal I ε δ x y j ξin θ).toOuterMeasure
        {h : ℚ | (1 - (ξin : ℝ)) * hWeight I ε δ j x y ≤ (h : ℝ) ∧
          (h : ℝ) ≤ (1 + (ξin : ℝ)) * hWeight I ε δ j x y}ᶜ ≤
      ENNReal.ofReal ((θ : ℝ) / 4) := by
  have hne := binSet_nonempty I ε δ (BParam_pos I ε δ hε)
  obtain ⟨hσ0, hσ1, hσH⟩ := oSigma_bounds I ε δ ξin hξ hξ1
  set σ : ℝ := (oSigma I ε δ ξin : ℝ) with hσdef
  have hσ : 0 < σ := by rw [hσdef]; exact_mod_cast hσ0
  have hσ1r : σ ≤ 1 / 200 := by
    rw [hσdef, show (1 / 200 : ℝ) = ((1 / 200 : ℚ) : ℝ) by norm_num]; exact_mod_cast hσ1
  have hσHr : ((HParam I ε δ : ℝ) + 2) * σ ≤ (ξin : ℝ) / 2 := by
    rw [hσdef]; exact_mod_cast hσH
  obtain ⟨hN, hNθ⟩ := oN_spec I ε δ ξin θ hξ hθ
  set X : ℝ := (oN I ε δ ξin θ : ℝ) * σ ^ 2 with hXdef
  have hX : 0 < X := by
    have : (0 : ℝ) < oN I ε δ ξin θ := by exact_mod_cast hN
    positivity
  set m : ℕ → ℝ := fun a => binS I ε δ (a + 1) x y / binS I ε δ a x y with hmdef
  have hm0 : ∀ a, 0 < m a := fun a =>
    div_pos (binS_pos I ε δ (a + 1) x y hne) (binS_pos I ε δ a x y hne)
  let G : ℕ → Set ℚ := fun i =>
    {P | (1 - σ) ^ i * ∏ a ∈ Finset.range i, m a ≤ (P : ℝ) ∧
      (P : ℝ) ≤ (1 + σ) ^ i * ∏ a ∈ Finset.range i, m a}
  have hloop := loop_bad_le (fun a P => (ratioIdeal I ε δ ξin θ a x y).map fun r => P * r) G
    (fun _ => ENNReal.ofReal (2 / X)) 1 (by simp [G]) j (fun i _ c hc => by
      rw [PMF.toOuterMeasure_map_apply]
      refine le_trans (PMF.toOuterMeasure_mono _ ?_)
        (ratioIdeal_bad I ε δ hε hfeas x y hbox ξin θ hξ hθ i)
      rintro r ⟨hr, -⟩ hgood
      apply hr
      have hLc : 0 ≤ (1 - σ) ^ i * ∏ a ∈ Finset.range i, m a :=
        mul_nonneg (pow_nonneg (by linarith) _) (Finset.prod_nonneg fun a _ => (hm0 a).le)
      have hLr : 0 ≤ (1 - σ) * m i := mul_nonneg (by linarith) (hm0 i).le
      have hc0 : (0 : ℝ) ≤ c := hLc.trans hc.1
      have hr0 : (0 : ℝ) ≤ r := hLr.trans hgood.1
      simp only [G, Set.mem_setOf_eq, Rat.cast_mul]
      rw [pow_succ, pow_succ, Finset.prod_range_succ]
      constructor
      · calc (1 - σ) ^ i * (1 - σ) * ((∏ a ∈ Finset.range i, m a) * m i)
            = ((1 - σ) ^ i * ∏ a ∈ Finset.range i, m a) * ((1 - σ) * m i) := by ring
          _ ≤ (c : ℝ) * r := mul_le_mul hc.1 hgood.1 hLr hc0
      · calc (c : ℝ) * r ≤ ((1 + σ) ^ i * ∏ a ∈ Finset.range i, m a) * ((1 + σ) * m i) :=
              mul_le_mul hc.2 hgood.2 hr0 (hc0.trans hc.2)
          _ = (1 + σ) ^ i * (1 + σ) * ((∏ a ∈ Finset.range i, m a) * m i) := by ring) j le_rfl
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hloop
  obtain ⟨-, hK1, hK2, hlow, -⟩ := corr_mean I ε δ hε hfeas x y j hj ξin hσ0 hσ1
  set K : ℝ := (BParam I ε δ : ℝ) ^ nFree I ε δ * hWeight I ε δ j x y /
    ((Mf I ε δ : ℝ) * binS I ε δ j x y) with hKdef
  have hW0 : 0 ≤ hWeight I ε δ j x y := Finset.sum_nonneg fun _ _ => by positivity
  have hMf : (0 : ℝ) < Mf I ε δ := by
    rw [Mf_eq_prod]; push_cast
    exact Finset.prod_pos fun k _ => by positivity
  have hB : (0 : ℝ) < BParam I ε δ := by exact_mod_cast BParam_pos I ε δ hε
  have hSj := binS_pos I ε δ j x y hne
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hid : (Mf I ε δ : ℝ) * (∏ a ∈ Finset.range j, m a) * K = hWeight I ε δ j x y := by
    rw [hmdef]
    simp only
    rw [prod_ratio_means I ε δ hε x y j, binS_zero, hKdef]
    field_simp
  have hwin := pow_window σ (ξin : ℝ) (j + 2) hσ.le (by linarith)
    (by
      have : ((j + 2 : ℕ) : ℝ) ≤ (HParam I ε δ : ℝ) + 2 := by
        push_cast; have : (j : ℝ) ≤ HParam I ε δ := by exact_mod_cast hj
        linarith
      exact (mul_le_mul_of_nonneg_right this hσ.le).trans hσHr)
    (by have : (ξin : ℝ) < 1 / 4 := by
          rw [show (1 / 4 : ℝ) = ((1 / 4 : ℚ) : ℝ) by norm_num]; exact_mod_cast hξ1
        linarith)
  unfold oracleIdeal
  refine (bind_bad_le _ _ (G j) _ (ENNReal.ofReal (144 / X)) (fun P hP => ?_)).trans ?_
  · refine (bind_bad_le _ _ {t : ℚ | (1 - σ) * corrMean I ε δ ξin j x y ≤ (t : ℝ) ∧
        (t : ℝ) ≤ (1 + σ) * corrMean I ε δ ξin j x y} _ 0 (fun T hT => ?_)).trans ?_
    · rw [PMF.toOuterMeasure_pure_apply, if_neg]
      intro hmem
      apply hmem
      have hu : 0 ≤ 1 - σ := by linarith
      have hT' : (1 - σ) * ((1 - σ) * K) ≤ (T : ℝ) ∧ (T : ℝ) ≤ (1 + σ) * ((1 + σ) * K) :=
        ⟨(mul_le_mul_of_nonneg_left hK1 hu).trans hT.1,
          hT.2.trans (mul_le_mul_of_nonneg_left hK2 (by linarith))⟩
      have := oracle_err_window (Mf I ε δ) (∏ a ∈ Finset.range j, m a) K (hWeight I ε δ j x y)
        P T σ ξin j hMf.le (Finset.prod_nonneg fun a _ => (hm0 a).le) hK0 hW0
        hid hσ.le (by linarith) hwin.1 hwin.2 hP hT'
      simp only [Set.mem_setOf_eq]
      push_cast
      exact this
    · rw [add_zero]
      exact corrIdeal_bad I ε δ hε hfeas x y j hj ξin θ hξ hξ1 hθ
  · refine (add_le_add hloop le_rfl).trans ?_
    have hθr : (0 : ℝ) < θ := by exact_mod_cast hθ
    have hjr : (j : ℝ) ≤ HParam I ε δ := by exact_mod_cast hj
    have e1 : (j : ℝ≥0∞) * ENNReal.ofReal (2 / X) = ENNReal.ofReal (j * (2 / X)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg j), ENNReal.ofReal_natCast]
    rw [e1, ← ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg j) (div_nonneg (by norm_num) hX.le))
      (div_nonneg (by norm_num) hX.le)]
    apply ENNReal.ofReal_le_ofReal
    rw [show (j : ℝ) * (2 / X) + 144 / X = (2 * j + 144) / X by ring, div_le_iff₀ hX]
    exact budget_arith _ _ _ _ hjr (Nat.cast_nonneg j) hNθ

end ideal

/-- **Weight evaluation, accuracy** (`prop:weight-oracle`): with probability at
least `1 - θ` the oracle is within relative error `ξ_in` of `h_j(x, y)`.  The oracle is
within `θ/8` of the ideal oracle (`oracle_close`), which fails with probability at most
`θ/4` (`oracleIdeal_bad`).
PAPER: sections/evaluation.tex:15-37 -/
theorem weight_oracle_accurate (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (x y : ℕ → ℕ)
    (hbox : ∀ s < nSmall I ε δ, x s ≤ smallB I ε δ s ∧ y s ≤ smallB I ε δ s)
    (htot : ∑ s ∈ Finset.range (nSmall I ε δ), (x s + y s) = pSmall I ε δ)
    (j : ℕ) (hj : j ≤ HParam I ε δ) (ξin θ : ℚ) (hξ : 0 < ξin) (hξ1 : ξin < 1 / 4)
    (hθ : 0 < θ) (hθ1 : θ < 1 / 4) :
    ENNReal.ofReal (1 - (θ : ℝ)) ≤ (oracle I ε δ x y j ξin θ).toOuterMeasure
      {h | (1 - (ξin : ℝ)) * hWeight I ε δ j x y ≤ (h : ℝ) ∧
        (h : ℝ) ≤ (1 + (ξin : ℝ)) * hWeight I ε δ j x y} := by
  set s : Set ℚ := {h | (1 - (ξin : ℝ)) * hWeight I ε δ j x y ≤ (h : ℝ) ∧
    (h : ℝ) ≤ (1 + (ξin : ℝ)) * hWeight I ε δ j x y} with hs
  have hN := (oN_spec I ε δ ξin θ hξ hθ).1
  have hQ : 0 < oQ I ε δ ξin θ := by unfold oQ; positivity
  have hζ : 0 < oZeta I ε δ ξin θ := by unfold oZeta; positivity
  have hθr : (0 : ℝ) < θ := by exact_mod_cast hθ
  have hclose := (oracle_close I ε δ hε hε1 hfeas x y hbox ξin θ hξ hξ1 hθ hθ1 j hj hζ).outer_le sᶜ
  have hideal := oracleIdeal_bad I ε δ hε hfeas x y hbox j hj ξin θ hξ hξ1 hθ
  -- the closeness budget `j N ζ + N (e + 1) ζ ≤ Q ζ = θ/8`
  set N : ℝ := (oN I ε δ ξin θ : ℝ) with hNdef
  set ζ : ℝ := (oZeta I ε δ ξin θ : ℝ) with hζdef
  have hζ0 : 0 ≤ ζ := by rw [hζdef]; exact_mod_cast hζ.le
  have hNζ : N * ζ * (((dParam I : ℝ) + 1) * ((HParam I ε δ : ℝ) + 1)) = θ / 8 := by
    have hQr : (0 : ℝ) < oQ I ε δ ξin θ := by exact_mod_cast hQ
    have hQeq : (oQ I ε δ ξin θ : ℝ) = ((dParam I : ℝ) + 1) * ((HParam I ε δ : ℝ) + 1) * N := by
      rw [hNdef]; unfold oQ; push_cast; ring
    have hζeq : ζ = θ / (8 * (oQ I ε δ ξin θ : ℝ)) := by
      rw [hζdef]; unfold oZeta; push_cast; ring
    rw [hζeq, ← mul_comm (((dParam I : ℝ) + 1) * ((HParam I ε δ : ℝ) + 1)), ← mul_assoc,
      ← hQeq]
    field_simp
  have hcl : (j : ℝ≥0∞) * ((oN I ε δ ξin θ : ℝ≥0∞) * ENNReal.ofReal ζ) +
      ((oN I ε δ ξin θ : ℝ≥0∞) * (((nFree I ε δ : ℝ≥0∞) + 1) * ENNReal.ofReal ζ) + 0) ≤
        ENNReal.ofReal ((θ : ℝ) / 8) := by
    have e1 : (j : ℝ≥0∞) * ((oN I ε δ ξin θ : ℝ≥0∞) * ENNReal.ofReal ζ) =
        ENNReal.ofReal (j * (N * ζ)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg j), ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    have e2 : (oN I ε δ ξin θ : ℝ≥0∞) * (((nFree I ε δ : ℝ≥0∞) + 1) * ENNReal.ofReal ζ) =
        ENNReal.ofReal (N * (((nFree I ε δ : ℝ) + 1) * ζ)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast, ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
        ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    rw [e1, e2, add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hjr : (j : ℝ) ≤ HParam I ε δ := by exact_mod_cast hj
    have her : (nFree I ε δ : ℝ) ≤ dParam I := by exact_mod_cast nFree_le_d I ε δ
    have hH0 : (0 : ℝ) ≤ HParam I ε δ := Nat.cast_nonneg _
    have hd0 : (0 : ℝ) ≤ dParam I := Nat.cast_nonneg _
    have hsum : (j : ℝ) + ((nFree I ε δ : ℝ) + 1) ≤
        ((dParam I : ℝ) + 1) * ((HParam I ε δ : ℝ) + 1) := by nlinarith
    calc (j : ℝ) * (N * ζ) + N * (((nFree I ε δ : ℝ) + 1) * ζ)
        = N * ζ * ((j : ℝ) + ((nFree I ε δ : ℝ) + 1)) := by ring
      _ ≤ N * ζ * (((dParam I : ℝ) + 1) * ((HParam I ε δ : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg hN0 hζ0)
      _ = θ / 8 := hNζ
  have hbad : (oracle I ε δ x y j ξin θ).toOuterMeasure sᶜ ≤ ENNReal.ofReal θ := by
    refine hclose.trans ((add_le_add hideal hcl).trans ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have h1 := outer_add_compl (oracle I ε δ x y j ξin θ) s
  rw [ENNReal.ofReal_sub _ hθr.le, ENNReal.ofReal_one, tsub_le_iff_right]
  calc (1 : ℝ≥0∞) = (oracle I ε δ x y j ξin θ).toOuterMeasure s +
        (oracle I ε δ x y j ξin θ).toOuterMeasure sᶜ := h1.symm
    _ ≤ (oracle I ε δ x y j ξin θ).toOuterMeasure s + ENNReal.ofReal θ := add_le_add le_rfl hbad

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r5 · proved · `weight_oracle_accurate` closed; staging file `WeightOracle/new.lean` folded in
-/
