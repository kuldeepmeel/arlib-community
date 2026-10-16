import Cellcounting.Analysis.FeasibleValProof

/-!
# Tightening: the program's search for the least value of a cell

`cellMin_val`: on a feasible instance, the program's binary search `Program.cellMin`
returns `l_ij = Pseudocode.cellLow`, the least value of cell `(i, j)` over `Ω`
(`sections/scales.tex:24-28`).

* `mem_Omega_iff`: membership in `Ω` spelled out.
* `getD_set2`: reading a matrix after one entry is overwritten.
* `feasible_set2_iff`: the flow test on the bounds with `b_ij` replaced by `v ≤ b_ij`
  decides whether some table in `Ω` has `X_ij ≤ v` (`feasible_val_proof`).
* `bsearch_low`: a binary search over `[0, B]` whose step moves to the lower half exactly when
  the target `ℓ` lies there returns `ℓ` after `k` rounds once `B < 2 ^ k`; the invariant is
  `lo ≤ ℓ ≤ hi` with `hi - lo ≤ B / 2 ^ t` after `t` rounds.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Model.Operations

/-- INTERNAL: membership in `Ω` spelled out. -/
theorem mem_Omega_iff (I : Instance) (X : Fin I.m → Fin I.n → ℕ) :
    X ∈ I.Omega ↔ (∀ i j, X i j ≤ I.b i j) ∧ (∀ i, ∑ j, X i j = I.r i) ∧
      (∀ j, ∑ i, X i j = I.c j) := by
  simp [Instance.Omega, Fintype.mem_piFinset, Nat.lt_succ_iff]

/-- INTERNAL: reading a matrix after overwriting one in-range entry. -/
theorem getD_set2 (b : List (List SNat)) (i j : ℕ) (v : SNat) (hi : i < b.length)
    (hj : j < (b.getD i []).length) (i' j' : ℕ) :
    ((Program.set2 b i j v).val.getD i' []).getD j' default =
      if i' = i ∧ j' = j then v else (b.getD i' []).getD j' default := by
  have e : (Program.set2 b i j v).val = b.set i ((b.getD i []).set j v) := by
    simp [Program.set2]; rfl
  rw [e]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hii : i = i'
  · subst hii
    simp only [hi, if_true, Option.getD_some, true_and]
    rw [List.getD_eq_getElem?_getD] at hj
    by_cases hjj : j = j'
    · subst hjj
      simp only [List.getD_eq_getElem?_getD] at hj ⊢
      simp [hj]
    · simp [hjj, Ne.symm hjj]
  · simp [hii, Ne.symm hii]

/-- INTERNAL: the flow test with the bound of cell `(i, j)` lowered to `v ≤ b_ij` decides
whether some feasible table has `X_ij ≤ v`.
TEXLINE: sections/scales.tex:24-28 -/
theorem feasible_set2_iff (I : Instance) (r c : List SNat) (b : List (List SNat))
    (hr : r.length = I.m) (hc : c.length = I.n) (hb : b.length = I.m)
    (hbrow : ∀ row ∈ b, row.length = I.n)
    (hrv : ∀ i : Fin I.m, (r.getD i.val default).get = I.r i)
    (hcv : ∀ j : Fin I.n, (c.getD j.val default).get = I.c j)
    (hbv : ∀ (i : Fin I.m) (j : Fin I.n), ((b.getD i.val []).getD j.val default).get = I.b i j)
    (i : Fin I.m) (j : Fin I.n) (v : SNat) (hv : v.get ≤ I.b i j) :
    (Program.feasible I.m I.n r c (Program.set2 b i.val j.val v).val).val = true ↔
      ∃ X ∈ I.Omega, X i j ≤ v.get := by
  have hrow : j.val < (b.getD i.val []).length := by
    have hmem : b.getD i.val [] ∈ b := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem _
    rw [hbrow _ hmem]; exact j.isLt
  have hent : ∀ (i' : Fin I.m) (j' : Fin I.n),
      (((Program.set2 b i.val j.val v).val.getD i'.val []).getD j'.val default).get =
        if i' = i ∧ j' = j then v.get else I.b i' j' := by
    intro i' j'
    rw [getD_set2 b i.val j.val v (by omega) hrow]
    by_cases h : i' = i ∧ j' = j
    · rw [if_pos ⟨congrArg Fin.val h.1, congrArg Fin.val h.2⟩, if_pos h]
    · rw [if_neg (fun h' => h ⟨Fin.ext h'.1, Fin.ext h'.2⟩), if_neg h, hbv]
  rw [feasible_val_proof I.m I.n r c _ hr hc, decide_eq_true_iff]
  unfold Pseudocode.feasible
  constructor
  · rintro ⟨X, hX⟩
    rw [mem_Omega_iff] at hX
    obtain ⟨hXb, hXr, hXc⟩ := hX
    simp only at hXb hXr hXc
    have hij : X i j ≤ v.get := by have := hXb i j; rw [hent, if_pos ⟨rfl, rfl⟩] at this; exact this
    refine ⟨X, (mem_Omega_iff I X).2 ⟨fun i' j' => ?_, fun i' => ?_, fun j' => ?_⟩, hij⟩
    · by_cases h : i' = i ∧ j' = j
      · rw [h.1, h.2]; exact hij.trans hv
      · have := hXb i' j'; rw [hent, if_neg h] at this; exact this
    · rw [hXr i', hrv]
    · rw [hXc j', hcv]
  · rintro ⟨X, hX, hij⟩
    rw [mem_Omega_iff] at hX
    obtain ⟨hXb, hXr, hXc⟩ := hX
    refine ⟨X, ?_⟩
    rw [mem_Omega_iff]
    refine ⟨fun i' j' => ?_, fun i' => ?_, fun j' => ?_⟩
    · show X i' j' ≤ (((Program.set2 b i.val j.val v).val.getD i'.val []).getD j'.val default).get
      rw [hent]
      split_ifs with h
      · rw [h.1, h.2]; exact hij
      · exact hXb i' j'
    · show ∑ j, X i' j = (r.getD i'.val default).get
      rw [hrv, hXr]
    · show ∑ i, X i j' = (c.getD j'.val default).get
      rw [hcv, hXc]

/-- INTERNAL: a binary search for the least `v ∈ [0, B]` with `ℓ ≤ v`, whose step halves
`[lo, hi]` toward `ℓ`, finds `ℓ` within `k` rounds once `B < 2 ^ k`. -/
theorem bsearch_low (F : ℕ → SNat × SNat → Program.Prog (SNat × SNat)) (ℓ B k : ℕ)
    (hk : B < 2 ^ k)
    (hstep : ∀ t (st : SNat × SNat), st.1.get ≤ ℓ → ℓ ≤ st.2.get → st.2.get ≤ B →
      (st.1.get < st.2.get → ℓ ≤ (st.1.get + st.2.get) / 2 →
        (F t st).val.1.get = st.1.get ∧ (F t st).val.2.get = (st.1.get + st.2.get) / 2) ∧
      (st.1.get < st.2.get → ¬ ℓ ≤ (st.1.get + st.2.get) / 2 →
        (F t st).val.1.get = (st.1.get + st.2.get) / 2 + 1 ∧ (F t st).val.2.get = st.2.get) ∧
      (¬ st.1.get < st.2.get → (F t st).val.1.get = st.1.get ∧ (F t st).val.2.get = st.2.get))
    (st0 : SNat × SNat) (h0 : st0.1.get = 0) (h1 : st0.2.get = B) (hℓ : ℓ ≤ B) :
    (Charged.repeatFor F k st0).val.2.get = ℓ := by
  obtain ⟨g1, g2, -, g4⟩ := nv_loop_inv F
    (fun t st => st.1.get ≤ ℓ ∧ ℓ ≤ st.2.get ∧ st.2.get ≤ B ∧ st.2.get - st.1.get ≤ B / 2 ^ t)
    k st0 ⟨by omega, by omega, by omega, by simp [h0, h1]⟩
    (fun t st _ ⟨p1, p2, p3, p4⟩ => by
      obtain ⟨s1, s2, s3⟩ := hstep t st p1 p2 p3
      have hdiv : B / 2 ^ (t + 1) = B / 2 ^ t / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
      have hhalf : (st.2.get - st.1.get) / 2 ≤ B / 2 ^ t / 2 := Nat.div_le_div_right p4
      by_cases ho : st.1.get < st.2.get
      · by_cases hl : ℓ ≤ (st.1.get + st.2.get) / 2
        · obtain ⟨e1, e2⟩ := s1 ho hl
          refine ⟨by omega, by omega, by omega, ?_⟩
          rw [e1, e2, hdiv]; omega
        · obtain ⟨e1, e2⟩ := s2 ho hl
          refine ⟨by omega, by omega, by omega, ?_⟩
          rw [e1, e2, hdiv]; omega
      · obtain ⟨e1, e2⟩ := s3 ho
        refine ⟨by omega, by omega, by omega, ?_⟩
        rw [e1, e2]; omega)
  have : B / 2 ^ k = 0 := Nat.div_eq_of_lt hk
  omega

/-- The program's binary search finds the least feasible value of a cell.
PAPER: sections/scales.tex:24-28 -/
theorem cellMin_val (I : Instance) (hfeas : Pseudocode.feasible I)
    (r c : List SNat) (b : List (List SNat))
    (hr : r.length = I.m) (hc : c.length = I.n) (hb : b.length = I.m)
    (hbrow : ∀ row ∈ b, row.length = I.n)
    (hrv : ∀ i : Fin I.m, (r.getD i.val default).get = I.r i)
    (hcv : ∀ j : Fin I.n, (c.getD j.val default).get = I.c j)
    (hbv : ∀ (i : Fin I.m) (j : Fin I.n), ((b.getD i.val []).getD j.val default).get = I.b i j)
    (i : Fin I.m) (j : Fin I.n) :
    (Program.cellMin I.m I.n r c b i.val j.val).val.get = Pseudocode.cellLow I i j := by
  have hne : I.Omega.Nonempty := hfeas
  set ℓ := Pseudocode.cellLow I i j with hℓdef
  have hℓ : ∀ v, (∃ X ∈ I.Omega, X i j ≤ v) ↔ ℓ ≤ v := by
    intro v
    simp only [hℓdef, Pseudocode.cellLow, dif_pos hne]
    constructor
    · rintro ⟨X, hX, hle⟩
      exact (Finset.min'_le _ _ (Finset.mem_image_of_mem _ hX)).trans hle
    · intro h
      obtain ⟨X, hX, hXe⟩ := Finset.mem_image.1 (Finset.min'_mem (I.Omega.image fun X => X i j) (hne.image _))
      exact ⟨X, hX, hXe ▸ h⟩
  have hℓb : ℓ ≤ I.b i j := by
    obtain ⟨X, hX⟩ := hne
    exact (hℓ _).1 ⟨X, hX, ((mem_Omega_iff I X).1 hX).1 i j⟩
  have hbij : (Program.get2 b i.val j.val).val.get = I.b i j := by
    simp only [Program.get2, Charged.val_bind, Cellcounting.Interface.val_get]
    exact hbv i j
  unfold Program.cellMin
  simp only [Charged.val_bind, Charged.val_pure, Program.searchRounds,
    Cellcounting.Interface.SNat.val_index, Cellcounting.Interface.SNat.get_bitLen]
  rw [hbij]
  refine bsearch_low _ ℓ (I.b i j) _ ?_ (fun t st p1 p2 p3 => ?_) _ rfl hbij hℓb
  · unfold Cellcounting.bitLen
    exact (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  · have hmid : (Program.half (SNat.add st.1 st.2).val).val.get = (st.1.get + st.2.get) / 2 := by
      simp [Program.half]
    refine ⟨fun ho hl => ?_, fun ho hl => ?_, fun ho => ?_⟩
    · have hok := (feasible_set2_iff I r c b hr hc hb hbrow hrv hcv hbv i j
        (Program.half (SNat.add st.1 st.2).val).val (by rw [hmid]; omega)).2
        ((hℓ _).2 (by rw [hmid]; exact hl))
      simp only [Charged.val_bind, Cellcounting.Interface.SNat.val_lt, decide_eq_true ho,
        if_true, hok, Charged.val_pure]
      exact ⟨by first | rfl | trivial, by first | exact hmid | trivial⟩
    · have hok : (Program.feasible I.m I.n r c
          (Program.set2 b i.val j.val (Program.half (SNat.add st.1 st.2).val).val).val).val = false := by
        cases h : (Program.feasible I.m I.n r c
          (Program.set2 b i.val j.val (Program.half (SNat.add st.1 st.2).val).val).val).val
        · rfl
        · exact absurd ((hℓ _).1 ((feasible_set2_iff I r c b hr hc hb hbrow hrv hcv hbv i j
            _ (by rw [hmid]; omega)).1 h)) (by rw [hmid]; exact hl)
      simp only [Charged.val_bind, Cellcounting.Interface.SNat.val_lt, decide_eq_true ho,
        if_true, hok, Bool.false_eq_true, if_false, Charged.val_pure,
        Cellcounting.Interface.SNat.get_add, Cellcounting.Interface.SNat.get_lit]
      exact ⟨by first | rw [hmid] | trivial, by first | rfl | trivial⟩
    · simp only [Charged.val_bind, Cellcounting.Interface.SNat.val_lt, decide_eq_false ho,
        Bool.false_eq_true, if_false, Charged.val_pure]
      exact ⟨by first | rfl | trivial, by first | rfl | trivial⟩

end Cellcounting.Analysis
