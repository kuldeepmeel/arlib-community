import Cellcounting.Interface.Pseudocode
import Cellcounting.Model.Prior
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Cellcounting.Analysis.ContaminationBoxes
import Cellcounting.Analysis.ContaminationParams
import Cellcounting.Analysis.MarginalTail
import Cellcounting.Analysis.PenaltyFarNear
import Cellcounting.Analysis.AsgBoxCard
import Cellcounting.Analysis.TighteningCount
import Cellcounting.Analysis.TreeMarginal

/-!
# The partition functions `h_j`, `C(j)` and the contamination bound

`eq:hj` and `eq:Cj` (`scales.tex:265-282`) over the pseudocode's tightened data:

* `freeBox` is `∏_{e ∈ F} {0, …, b_e}`, as functions on `Fin (nFree I ε δ)`
  (defined, with `smallBox`, `extendQ`, `extendN`, in `ContaminationBoxes.lean`);
* `hWeight I ε δ j x y = Σ_{z ∈ freeBox} 2^{-j D(x, y, z) / H}`, with `D` the
  pseudocode's `penalty` (whose small-cell convention R1, row `x_s` and column
  `b_s - y_s`, is the paper's own, `scales.tex:101-108`);
* `Cpart I ε δ j = Σ h_j(x, y)` over the balanced profiles `x_s + y_s = b_s`,
  parametrised by `x ∈ ∏_s {0, …, b_s}` with `y_s = b_s - x_s`.

`contamination` is `prop:contamination` (`scales.tex:282-287`, proved in
`integer-signatures.tex:485-549`): `Z ≤ C(H) ≤ (1 + ε/32) Z`.  It is used by
the single-run bounds for both `p ≥ 1` (`annealRun_good`) and `p = 0`.

The proof follows the paper.  `C(H) = Σ_{assignments} 2^{-D}`; the zero-penalty
assignments are the `Z` feasible tables (`zero_pen_card`), so `Z ≤ C(H)`.  Every
other assignment is far (`D ≥ 4K`, total mass `≤ 2^K 2^{-4K} ≤ ε/128`) or has a
near tree violation; the near mass of each tree cell is at most `4γK C(H)` by the
log-concave tail bound (`tree_marginal_interp`, `marginal_tail`) with the two
attained endpoints (`tree_endpoints`), and there are at most `d` tree cells, so
`C(H) - Z ≤ ε C(H)/64`.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- **`h_j(x, y)`** (`eq:hj`): `Σ_{z ∈ ∏_e {0..b_e}} 2^{-j D(x, y, z)/H}`.
PAPER: sections/scales.tex:265-270 -/
noncomputable def hWeight (I : Instance) (ε δ : ℚ) (j : ℕ) (x y : ℕ → ℕ) : ℝ :=
  ∑ z ∈ freeBox I ε δ,
    (2 : ℝ) ^ (-((j : ℝ) * (penalty I ε δ x y (extendQ z) : ℝ) / (HParam I ε δ : ℝ)))

/-- **`C(j)`** (`eq:Cj`): `Σ h_j(x, y)` over balanced profiles `x_s + y_s = b_s`.
PAPER: sections/scales.tex:279-282 -/
noncomputable def Cpart (I : Instance) (ε δ : ℚ) (j : ℕ) : ℝ :=
  ∑ x ∈ smallBox I ε δ,
    hWeight I ε δ j (extendN x) (fun s => smallB I ε δ s - extendN x s)

/-- INTERNAL: a nonnegative sum over a union is at most the sum of the sums. -/
theorem sum_union_le_of_nonneg {α : Type*} [DecidableEq α] (A B : Finset α) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) : ∑ a ∈ A ∪ B, f a ≤ ∑ a ∈ A, f a + ∑ a ∈ B, f a := by
  rw [← Finset.sum_union_inter]
  have : 0 ≤ ∑ a ∈ A ∩ B, f a := Finset.sum_nonneg fun a _ => hf a
  linarith

/-- INTERNAL: union bound for a nonnegative sum over a `biUnion`. -/
theorem sum_biUnion_le_of_nonneg {α ι : Type*} [DecidableEq α] [DecidableEq ι] (s : Finset ι)
    (t : ι → Finset α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ s.biUnion t, f a ≤ ∑ i ∈ s, ∑ a ∈ t i, f a := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact le_trans (sum_union_le_of_nonneg _ _ f hf) (by linarith)

/-- INTERNAL: `C(H) = Σ_{(x, z)} 2^{-D(x, z)}` over the assignments.
TEXLINE: sections/integer-signatures.tex:485-487 -/
theorem cpart_H_eq (I : Instance) (ε δ : ℚ) (hε : 0 < ε) :
    Cpart I ε δ (HParam I ε δ) =
      ∑ p ∈ asgBox I ε δ, (2 : ℝ) ^ (-(asgPen I ε δ p : ℝ)) := by
  have hH : (HParam I ε δ : ℝ) ≠ 0 := by
    have := HParam_pos I ε δ hε; positivity
  simp only [Cpart, hWeight, asgBox, Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
  congr 2
  simp only [asgPen]
  field_simp
  rfl

/-- INTERNAL: the marginals of one tree cell over any set of values have total
mass at most `C(H)`.
TEXLINE: sections/integer-signatures.tex:430-431 -/
theorem treeMarg_sum_le (I : Instance) (ε δ : ℚ) (t : ℕ) (S : Finset ℤ) :
    ∑ k ∈ S, treeMarg I ε δ t k ≤
      ∑ p ∈ asgBox I ε δ, (2 : ℝ) ^ (-(asgPen I ε δ p : ℝ)) := by
  classical
  simp only [treeMarg]
  rw [← Finset.sum_biUnion]
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => by positivity
    intro p hp
    simp only [Finset.mem_biUnion, Finset.mem_filter] at hp
    obtain ⟨_, _, hp, _⟩ := hp
    exact hp
  · intro k _ k' _ hkk'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_filter] at hp hp'
    exact hkk' (by exact_mod_cast hp.2.symm.trans hp'.2)

/-- INTERNAL: each marginal mass is at most `2^K`.
TEXLINE: sections/integer-signatures.tex:504-506 -/
theorem treeMarg_le (I : Instance) (ε δ : ℚ) (t : ℕ) (k : ℤ) :
    treeMarg I ε δ t k ≤ 2 ^ KParam I ε δ := by
  have h1 : treeMarg I ε δ t k ≤ ((asgBox I ε δ).filter (fun p => asgTree I ε δ p t = k)).card := by
    simp only [treeMarg]
    rw [← nsmul_one, ← Finset.sum_const]
    refine Finset.sum_le_sum fun p _ => ?_
    have : (0 : ℝ) ≤ asgPen I ε δ p := by exact_mod_cast asgPen_nonneg I ε δ p
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    linarith
  have h2 : ((asgBox I ε δ).filter (fun p => asgTree I ε δ p t = k)).card ≤ 2 ^ KParam I ε δ :=
    le_trans (Finset.card_filter_le _ _) (asgBox_card_le I ε δ)
  calc treeMarg I ε δ t k ≤ _ := h1
    _ ≤ ((2 ^ KParam I ε δ : ℕ) : ℝ) := by exact_mod_cast h2
    _ = 2 ^ KParam I ε δ := by push_cast; ring

/-- INTERNAL: an attained zero-penalty value carries marginal mass at least one.
TEXLINE: sections/integer-signatures.tex:506-508 -/
theorem one_le_treeMarg (I : Instance) (ε δ : ℚ) (t : ℕ) (k : ℤ)
    (h : ∃ p ∈ asgBox I ε δ, asgPen I ε δ p = 0 ∧ asgTree I ε δ p t = k) :
    1 ≤ treeMarg I ε δ t k := by
  obtain ⟨p, hp, h0, hk⟩ := h
  simp only [treeMarg]
  have hmem : p ∈ (asgBox I ε δ).filter (fun p => asgTree I ε δ p t = k) :=
    Finset.mem_filter.2 ⟨hp, hk⟩
  calc (1 : ℝ) = (2 : ℝ) ^ (-(asgPen I ε δ p : ℝ)) := by rw [h0]; simp
    _ ≤ _ := Finset.single_le_sum (f := fun p => (2 : ℝ) ^ (-(asgPen I ε δ p : ℝ)))
          (fun p _ => by positivity) hmem

/-- **Contamination bound** (`prop:contamination`): for the feasible tightened
instance, `Z ≤ C(H) ≤ (1 + ε/32) Z`.
PAPER: sections/scales.tex:282-287 -/
theorem contamination (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) :
    (I.Z : ℝ) ≤ Cpart I ε δ (HParam I ε δ) ∧
      Cpart I ε δ (HParam I ε δ) ≤ (1 + (ε : ℝ) / 32) * (I.Z : ℝ) := by
  classical
  set P := asgBox I ε δ with hP
  set w : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ) → ℝ :=
    fun p => (2 : ℝ) ^ (-(asgPen I ε δ p : ℝ)) with hw
  set K := KParam I ε δ with hK
  set T := (forest I ε δ).tree.length with hT
  rw [cpart_H_eq I ε δ hε]
  set C := ∑ p ∈ P, w p with hCdef
  have hw_nn : ∀ p, 0 ≤ w p := fun p => by positivity
  have hw0 : ∀ p, asgPen I ε δ p = 0 → w p = 1 := fun p h => by simp [hw, h]
  set Z0 := P.filter (fun p => asgPen I ε δ p = 0)
  set Bad := P.filter (fun p => ¬ asgPen I ε δ p = 0)
  have hZ : (I.Z : ℝ) = ∑ p ∈ Z0, w p := by
    rw [Finset.sum_congr rfl fun p hp => hw0 p (Finset.mem_filter.1 hp).2, Finset.sum_const,
      nsmul_one, zero_pen_card I ε δ hfeas]
  have hsplit : C = (I.Z : ℝ) + ∑ p ∈ Bad, w p := by
    rw [hZ, hCdef, Finset.sum_filter_add_sum_filter_not]
  have hBad_nn : 0 ≤ ∑ p ∈ Bad, w p := Finset.sum_nonneg fun p _ => hw_nn p
  refine ⟨by linarith, ?_⟩
  -- `Z ≥ 1`
  have hZ1 : (1 : ℝ) ≤ I.Z := by
    have : 0 < I.Z := Finset.card_pos.2 hfeas
    exact_mod_cast this
  have hC1 : 1 ≤ C := by linarith
  have hK1 : 1 ≤ K := le_trans (by norm_num) (KParam_ge I ε δ)
  have hγ := γParam_pos I ε δ hε
  -- far assignments
  set Far := P.filter (fun p => 4 * (K : ℚ) ≤ asgPen I ε δ p)
  have hfar : ∑ p ∈ Far, w p ≤ (ε : ℝ) / 128 := by
    have h1 : ∀ p ∈ Far, w p ≤ ((2 : ℝ) ^ (4 * K))⁻¹ := by
      intro p hp
      have hp' := (Finset.mem_filter.1 hp).2
      simp only [hw]
      rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : ((4 * K : ℕ) : ℝ) ≤ (asgPen I ε δ p : ℝ) := by
        have : ((4 * K : ℕ) : ℚ) ≤ asgPen I ε δ p := by push_cast; exact hp'
        exact_mod_cast this
      linarith
    have h2 : (Far.card : ℝ) ≤ 2 ^ K := by
      have h' : Far.card ≤ P.card := Finset.card_filter_le _ _
      have := le_trans h' (asgBox_card_le I ε δ)
      exact_mod_cast this
    have h3 : (128 : ℝ) ≤ ε * 2 ^ (3 * K) := by
      have := two_pow_three_K I ε δ hε
      exact_mod_cast this
    calc ∑ p ∈ Far, w p ≤ Far.card * ((2 : ℝ) ^ (4 * K))⁻¹ := by
          rw [← nsmul_eq_mul, ← Finset.sum_const]; exact Finset.sum_le_sum h1
      _ ≤ 2 ^ K * ((2 : ℝ) ^ (4 * K))⁻¹ := by gcongr
      _ = ((2 : ℝ) ^ (3 * K))⁻¹ := by
          rw [show 4 * K = K + 3 * K by ring, pow_add]; field_simp
      _ ≤ (ε : ℝ) / 128 := by
          rw [inv_le_iff_one_le_mul₀ (by positivity)]
          nlinarith
  -- near assignments, one tree cell at a time
  set bt : ℕ → ℕ := fun t => (treeAt I ε δ t).2.2 with hbt
  set Near : ℕ → Finset _ := fun t => P.filter (fun p =>
    0 < boxDist (asgTree I ε δ p t) (bt t : ℚ) ∧
      boxDist (asgTree I ε δ p t) (bt t : ℚ) < γParam I ε δ * bt t) with hNear
  have hnear : ∀ t < T, ∑ p ∈ Near t, w p ≤
      4 * (γParam I ε δ : ℝ) * K * C := by
    intro t ht
    have hb : 0 < bt t := lt_of_lt_of_le (by
      have := dParam_ge I; have := AParam_pos I ε δ hε
      simp only [WParam, BParam]; positivity) (tree_bound_ge I ε δ t ht)
    set c : ℤ := ⌈γParam I ε δ * bt t⌉ with hc
    set NS : Finset ℤ := Finset.Ioo (-c) 0 ∪ Finset.Ioo (bt t : ℤ) (bt t + c) with hNS
    have hc1 : 1 ≤ c := by
      rw [hc, Int.one_le_ceil_iff]; have : (0 : ℚ) < bt t := by exact_mod_cast hb
      positivity
    have hcγ : ((c - 1 : ℤ) : ℝ) ≤ (γParam I ε δ : ℝ) * bt t := by
      have := Int.ceil_lt_add_one (γParam I ε δ * bt t)
      have h' : ((c - 1 : ℤ) : ℚ) ≤ γParam I ε δ * bt t := by push_cast; linarith
      exact_mod_cast h'
    have hNScard : (NS.card : ℝ) ≤ 2 * ((γParam I ε δ : ℝ) * bt t) := by
      have h1 : NS.card ≤ (Finset.Ioo (-c) 0).card + (Finset.Ioo (bt t : ℤ) (bt t + c)).card :=
        Finset.card_union_le _ _
      rw [Int.card_Ioo, Int.card_Ioo] at h1
      have h2 : ((0 - -c).toNat + (bt t + c - bt t).toNat : ℕ) = 2 * (c - 1).toNat + 2 := by
        omega
      have h3 : (NS.card : ℤ) ≤ 2 * (c - 1) := by omega
      have h4 : (NS.card : ℝ) ≤ 2 * ((c - 1 : ℤ) : ℝ) := by exact_mod_cast h3
      linarith
    -- every near assignment has its tree value in `NS`
    have hmaps : ∀ p ∈ Near t, ⌊asgTree I ε δ p t⌋ ∈ NS := by
      intro p hp
      obtain ⟨n, hn⟩ := asgTree_int I ε δ p t
      have hp' := (Finset.mem_filter.1 hp).2
      rw [hn] at hp' ⊢
      rw [Int.floor_intCast]
      simp only [boxDist] at hp'
      have hcq : γParam I ε δ * bt t ≤ c := Int.le_ceil _
      simp only [hNS, Finset.mem_union, Finset.mem_Ioo]
      by_cases hn0 : (n : ℚ) < 0
      · rw [if_pos hn0] at hp'
        left
        have : (-(c : ℚ)) < n := by linarith [hp'.2]
        constructor
        · exact_mod_cast this
        · exact_mod_cast hn0
      · rw [if_neg hn0] at hp'
        by_cases hnb : (bt t : ℚ) < n
        · rw [if_pos hnb] at hp'
          right
          have : (n : ℚ) < bt t + c := by linarith [hp'.2]
          constructor
          · exact_mod_cast hnb
          · exact_mod_cast this
        · rw [if_neg hnb] at hp'; exact absurd hp'.1 (lt_irrefl _)
    have hfib : ∑ p ∈ Near t, w p ≤ ∑ k ∈ NS, treeMarg I ε δ t k := by
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      refine Finset.sum_le_sum fun k _ => ?_
      simp only [treeMarg]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => hw_nn p
      intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      refine ⟨(Finset.mem_filter.1 hp.1).1, ?_⟩
      obtain ⟨n, hn⟩ := asgTree_int I ε δ p t
      rw [hn, Int.floor_intCast] at hp
      rw [hn, hp.2]
    -- the tail bound at every value of `NS`
    have hends := tree_endpoints I ε δ hfeas t ht
    have htail : ∀ k ∈ NS, treeMarg I ε δ t k ≤ 2 * K * C / bt t := by
      intro k hk
      refine marginal_tail (treeMarg I ε δ t) C K (bt t) hK1 hb
        (fun k => Finset.sum_nonneg fun p _ => hw_nn p) (treeMarg_sum_le I ε δ t)
        (treeMarg_le I ε δ t) (one_le_treeMarg I ε δ t 0 (by simpa using hends.1))
        (one_le_treeMarg I ε δ t (bt t) (by simpa [hbt] using hends.2))
        (fun v k w hvk hkw hv hw => tree_marginal_interp I ε δ hε t ht v k w hvk hkw hv hw) k ?_
      simp only [hNS, Finset.mem_union, Finset.mem_Ioo] at hk
      omega
    have hbr : (0 : ℝ) < bt t := by exact_mod_cast hb
    calc ∑ p ∈ Near t, w p ≤ ∑ k ∈ NS, treeMarg I ε δ t k := hfib
      _ ≤ NS.card * (2 * K * C / bt t) := by
          rw [← nsmul_eq_mul, ← Finset.sum_const]; exact Finset.sum_le_sum htail
      _ ≤ 2 * ((γParam I ε δ : ℝ) * bt t) * (2 * K * C / bt t) := by
          gcongr
      _ = 4 * (γParam I ε δ : ℝ) * K * C := by field_simp; ring
  -- every bad assignment is far or near
  have hcover : Bad ⊆ Far ∪ (Finset.range T).biUnion Near := by
    intro p hp
    have hpP := (Finset.mem_filter.1 hp).1
    rcases asgPen_far_or_near I ε δ hε hε1 p (Finset.mem_filter.1 hp).2 with h | ⟨t, ht, h⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hpP, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.2
        ⟨t, Finset.mem_range.2 ht, Finset.mem_filter.2 ⟨hpP, h⟩⟩)
  have hbad : ∑ p ∈ Bad, w p ≤ (ε : ℝ) / 128 + T * (4 * (γParam I ε δ : ℝ) * K * C) := by
    calc ∑ p ∈ Bad, w p ≤ ∑ p ∈ Far ∪ (Finset.range T).biUnion Near, w p :=
          Finset.sum_le_sum_of_subset_of_nonneg hcover fun p _ _ => hw_nn p
      _ ≤ ∑ p ∈ Far, w p + ∑ p ∈ (Finset.range T).biUnion Near, w p :=
          sum_union_le_of_nonneg _ _ w hw_nn
      _ ≤ (ε : ℝ) / 128 + ∑ t ∈ Finset.range T, ∑ p ∈ Near t, w p := by
          gcongr
          exact sum_biUnion_le_of_nonneg _ _ w hw_nn
      _ ≤ (ε : ℝ) / 128 + T * (4 * (γParam I ε δ : ℝ) * K * C) := by
          gcongr
          calc ∑ t ∈ Finset.range T, ∑ p ∈ Near t, w p
              ≤ ∑ t ∈ Finset.range T, 4 * (γParam I ε δ : ℝ) * K * C :=
                Finset.sum_le_sum fun t ht => hnear t (Finset.mem_range.1 ht)
            _ = T * (4 * (γParam I ε δ : ℝ) * K * C) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- `T · 4 γ K ≤ 4 d γ K = ε/128`
  have hTd : (T : ℝ) * (4 * (γParam I ε δ : ℝ) * K) ≤ (ε : ℝ) / 128 := by
    have h1 : (T : ℝ) ≤ dParam I := by exact_mod_cast tree_length_le I ε δ
    have h2 : (4 * (dParam I : ℝ) * γParam I ε δ * K) = (ε : ℝ) / 128 := by
      have := four_d_γ_K I ε δ hε
      exact_mod_cast this
    have hγr : (0 : ℝ) ≤ γParam I ε δ := by exact_mod_cast hγ.le
    have h3 : (T : ℝ) * (4 * (γParam I ε δ : ℝ) * K) ≤ dParam I * (4 * (γParam I ε δ : ℝ) * K) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    linarith
  have hε0 : (0 : ℝ) < ε := by exact_mod_cast hε
  have hε1' : (ε : ℝ) < 1 := by exact_mod_cast hε1
  have hbad' : ∑ p ∈ Bad, w p ≤ (ε : ℝ) / 64 * C := by
    have : T * (4 * (γParam I ε δ : ℝ) * K * C) ≤ (ε : ℝ) / 128 * C := by
      have := mul_le_mul_of_nonneg_right hTd (by linarith : (0 : ℝ) ≤ C)
      linarith
    nlinarith
  nlinarith

end Cellcounting.Analysis
