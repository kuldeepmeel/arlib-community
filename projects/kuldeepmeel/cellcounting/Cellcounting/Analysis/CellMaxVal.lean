import Cellcounting.Analysis.CellMinVal

/-!
# Tightening: the program's search for the greatest value of a cell

`cellMax_val`: on a feasible instance, started at `l_ij`, the program's binary search
`Program.cellMax` returns `u_ij = Pseudocode.cellHigh`, the greatest value of cell `(i, j)`
over `Ω` (`sections/scales.tex:24-30`).

* `feasibleAtLeast_iff`: `Program.feasibleAtLeast … v` subtracts `v` from `r_i`, `c_j` and
  `b_ij` (rejecting if any is smaller than `v`) and runs the flow test; it decides whether
  some table in `Ω` has `X_ij ≥ v`.  Adding `v` at `(i, j)` is the bijection between the
  shifted feasible set and `{X ∈ Ω | X_ij ≥ v}` (`sections/scales.tex:27-30`).
* `bsearch_high`: the search with upper midpoints `(lo + hi + 1) / 2` keeps
  `lo ≤ u ≤ hi` with `hi - lo ≤ B / 2 ^ t` after `t` rounds and returns `u`.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Model.Operations

/-- INTERNAL: reading a list after overwriting one in-range entry. -/
theorem getD_set_snat (l : List SNat) (i i' : ℕ) (x : SNat) (hi : i < l.length) :
    (l.set i x).getD i' default = if i' = i then x else l.getD i' default := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = i'
  · subst h; simp [hi]
  · simp [h, Ne.symm h]

/-- INTERNAL: adding `v` at one cell adds `v` to that row's sum. -/
theorem sum_row_shift {m n : ℕ} (Y Y' : Fin m → Fin n → ℕ) (i : Fin m) (j : Fin n) (v : ℕ)
    (h : ∀ i' j', Y i' j' = Y' i' j' + if i' = i ∧ j' = j then v else 0) (i' : Fin m) :
    ∑ j', Y i' j' = ∑ j', Y' i' j' + if i' = i then v else 0 := by
  simp only [h, Finset.sum_add_distrib]
  congr 1
  by_cases hi : i' = i
  · simp [hi]
  · simp [hi]

/-- INTERNAL: adding `v` at one cell adds `v` to that column's sum. -/
theorem sum_col_shift {m n : ℕ} (Y Y' : Fin m → Fin n → ℕ) (i : Fin m) (j : Fin n) (v : ℕ)
    (h : ∀ i' j', Y i' j' = Y' i' j' + if i' = i ∧ j' = j then v else 0) (j' : Fin n) :
    ∑ i', Y i' j' = ∑ i', Y' i' j' + if j' = j then v else 0 := by
  simp only [h, Finset.sum_add_distrib]
  congr 1
  by_cases hj : j' = j
  · simp [hj]
  · simp [hj]

/-- INTERNAL: the flow test with the lower bound `X_ij ≥ v` decides whether some feasible
table has `X_ij ≥ v`.
TEXLINE: sections/scales.tex:24-30 -/
theorem feasibleAtLeast_iff (I : Instance) (r c : List SNat) (b : List (List SNat))
    (hr : r.length = I.m) (hc : c.length = I.n) (hb : b.length = I.m)
    (hbrow : ∀ row ∈ b, row.length = I.n)
    (hrv : ∀ i : Fin I.m, (r.getD i.val default).get = I.r i)
    (hcv : ∀ j : Fin I.n, (c.getD j.val default).get = I.c j)
    (hbv : ∀ (i : Fin I.m) (j : Fin I.n), ((b.getD i.val []).getD j.val default).get = I.b i j)
    (i : Fin I.m) (j : Fin I.n) (v : SNat) :
    (Program.feasibleAtLeast I.m I.n r c b i.val j.val v).val = true ↔
      ∃ X ∈ I.Omega, v.get ≤ X i j := by
  -- an entry is at most its row margin, its column margin and its bound
  have hcap : ∀ X ∈ I.Omega, X i j ≤ I.r i ∧ X i j ≤ I.c j ∧ X i j ≤ I.b i j := by
    intro X hX
    obtain ⟨hXb, hXr, hXc⟩ := (mem_Omega_iff I X).1 hX
    refine ⟨?_, ?_, hXb i j⟩
    · rw [← hXr i]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    · rw [← hXc j]
      exact Finset.single_le_sum (f := fun i' => X i' j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hbij : (Program.get2 b i.val j.val).val.get = I.b i j := by
    simp only [Program.get2, Charged.val_bind, Cellcounting.Interface.val_get]
    exact hbv i j
  unfold Program.feasibleAtLeast
  by_cases hR : v.get ≤ I.r i
  · by_cases hC : v.get ≤ I.c j
    · by_cases hB : v.get ≤ I.b i j
      · simp only [Charged.val_bind, Cellcounting.Interface.val_get,
          Cellcounting.Interface.SNat.val_le, hrv, hcv, hbij, hR, hC, hB, decide_true, if_true,
          Cellcounting.Interface.val_set]
        set r' := r.set i.val (SNat.sub (r.getD i.val default) v).val
        set c' := c.set j.val (SNat.sub (c.getD j.val default) v).val
        set b' := (Program.set2 b i.val j.val (SNat.sub (Program.get2 b i.val j.val).val v).val).val
        have hrow : j.val < (b.getD i.val []).length := by
          have hmem : b.getD i.val [] ∈ b := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
            exact List.getElem_mem _
          rw [hbrow _ hmem]; exact j.isLt
        have hr' : ∀ i' : Fin I.m, (r'.getD i'.val default).get =
            if i' = i then I.r i - v.get else I.r i' := by
          intro i'
          rw [getD_set_snat r i.val i'.val _ (by omega)]
          by_cases h : i' = i
          · rw [if_pos (congrArg Fin.val h), if_pos h, Cellcounting.Interface.SNat.get_sub, hrv]
          · rw [if_neg (fun h' => h (Fin.ext h')), if_neg h, hrv]
        have hc' : ∀ j' : Fin I.n, (c'.getD j'.val default).get =
            if j' = j then I.c j - v.get else I.c j' := by
          intro j'
          rw [getD_set_snat c j.val j'.val _ (by omega)]
          by_cases h : j' = j
          · rw [if_pos (congrArg Fin.val h), if_pos h, Cellcounting.Interface.SNat.get_sub, hcv]
          · rw [if_neg (fun h' => h (Fin.ext h')), if_neg h, hcv]
        have hb' : ∀ (i' : Fin I.m) (j' : Fin I.n), ((b'.getD i'.val []).getD j'.val default).get =
            if i' = i ∧ j' = j then I.b i j - v.get else I.b i' j' := by
          intro i' j'
          rw [getD_set2 b i.val j.val _ (by omega) hrow]
          by_cases h : i' = i ∧ j' = j
          · rw [if_pos ⟨congrArg Fin.val h.1, congrArg Fin.val h.2⟩, if_pos h,
              Cellcounting.Interface.SNat.get_sub, hbij]
          · rw [if_neg (fun h' => h ⟨Fin.ext h'.1, Fin.ext h'.2⟩), if_neg h, hbv]
        rw [feasible_val_proof I.m I.n r' c' b' (by simp [r', hr]) (by simp [c', hc]),
          decide_eq_true_iff]
        unfold Pseudocode.feasible
        constructor
        · rintro ⟨X', hX'⟩
          rw [mem_Omega_iff] at hX'
          obtain ⟨hXb, hXr, hXc⟩ := hX'
          let X : Fin I.m → Fin I.n → ℕ := fun i' j' => X' i' j' + if i' = i ∧ j' = j then v.get else 0
          refine ⟨X, (mem_Omega_iff I X).2 ⟨fun i' j' => ?_, fun i' => ?_, fun j' => ?_⟩, ?_⟩
          · have := hXb i' j'
            simp only at this
            rw [hb'] at this
            simp only [X]
            by_cases h : i' = i ∧ j' = j
            · simp only [if_pos h] at this ⊢
              rw [h.1, h.2] at this ⊢; omega
            · simp only [if_neg h] at this ⊢
              omega
          · rw [sum_row_shift X X' i j v.get (fun _ _ => rfl) i']
            have := hXr i'
            simp only at this
            rw [this, hr']
            by_cases h : i' = i
            · simp only [h, if_true]; omega
            · simp only [h, if_false, add_zero]
          · rw [sum_col_shift X X' i j v.get (fun _ _ => rfl) j']
            have := hXc j'
            simp only at this
            rw [this, hc']
            by_cases h : j' = j
            · simp only [h, if_true]; omega
            · simp only [h, if_false, add_zero]
          · simp [X]
        · rintro ⟨X, hX, hvX⟩
          obtain ⟨hXb, hXr, hXc⟩ := (mem_Omega_iff I X).1 hX
          let X' : Fin I.m → Fin I.n → ℕ := fun i' j' => X i' j' - if i' = i ∧ j' = j then v.get else 0
          have hXX : ∀ i' j', X i' j' = X' i' j' + if i' = i ∧ j' = j then v.get else 0 := by
            intro i' j'
            simp only [X']
            split_ifs with h
            · rw [h.1, h.2]; omega
            · omega
          refine ⟨X', ?_⟩
          rw [mem_Omega_iff]
          refine ⟨fun i' j' => ?_, fun i' => ?_, fun j' => ?_⟩
          · show X' i' j' ≤ ((b'.getD i'.val []).getD j'.val default).get
            rw [hb']
            have := hXb i' j'
            simp only [X']
            split_ifs with h
            · rw [h.1, h.2] at this ⊢; omega
            · omega
          · show ∑ j', X' i' j' = (r'.getD i'.val default).get
            have := sum_row_shift X X' i j v.get hXX i'
            rw [hXr i'] at this
            rw [hr']
            by_cases h : i' = i
            · simp only [h, if_true] at this ⊢; omega
            · simp only [h, if_false, add_zero] at this ⊢; omega
          · show ∑ i', X' i' j' = (c'.getD j'.val default).get
            have := sum_col_shift X X' i j v.get hXX j'
            rw [hXc j'] at this
            rw [hc']
            by_cases h : j' = j
            · simp only [h, if_true] at this ⊢; omega
            · simp only [h, if_false, add_zero] at this ⊢; omega
      · simp only [Charged.val_bind, Cellcounting.Interface.val_get,
          Cellcounting.Interface.SNat.val_le, hrv, hcv, hbij, hR, hC, hB, decide_true,
          decide_false, if_true, Bool.false_eq_true, if_false,
          Charged.val_pure, false_iff, not_exists, not_and, not_le]
        intro X hX; have := (hcap X hX).2.2; omega
    · simp only [Charged.val_bind, Cellcounting.Interface.val_get,
        Cellcounting.Interface.SNat.val_le, hrv, hcv, hbij, hR, hC, decide_true,
        decide_false, if_true, Bool.false_eq_true, if_false,
        Charged.val_pure, false_iff, not_exists, not_and, not_le]
      intro X hX; have := (hcap X hX).2.1; omega
  · simp only [Charged.val_bind, Cellcounting.Interface.val_get,
      Cellcounting.Interface.SNat.val_le, hrv, hcv, hbij, hR, decide_false, Bool.false_eq_true,
      if_false, Charged.val_pure, false_iff, not_exists, not_and, not_le]
    intro X hX; have := (hcap X hX).1; omega

/-- INTERNAL: a binary search for the greatest `v ∈ [lo, B]` with `v ≤ u`, using upper
midpoints, finds `u` within `k` rounds once `B < 2 ^ k`. -/
theorem bsearch_high (F : ℕ → SNat × SNat → Program.Prog (SNat × SNat)) (u B k : ℕ)
    (hk : B < 2 ^ k)
    (hstep : ∀ t (st : SNat × SNat), st.1.get ≤ u → u ≤ st.2.get → st.2.get ≤ B →
      (st.1.get < st.2.get → (st.1.get + st.2.get + 1) / 2 ≤ u →
        (F t st).val.1.get = (st.1.get + st.2.get + 1) / 2 ∧ (F t st).val.2.get = st.2.get) ∧
      (st.1.get < st.2.get → ¬ (st.1.get + st.2.get + 1) / 2 ≤ u →
        (F t st).val.1.get = st.1.get ∧ (F t st).val.2.get = (st.1.get + st.2.get + 1) / 2 - 1) ∧
      (¬ st.1.get < st.2.get → (F t st).val.1.get = st.1.get ∧ (F t st).val.2.get = st.2.get))
    (st0 : SNat × SNat) (h0 : st0.1.get ≤ u) (h1 : st0.2.get = B) (hu : u ≤ B) :
    (Charged.repeatFor F k st0).val.1.get = u := by
  obtain ⟨g1, g2, -, g4⟩ := nv_loop_inv F
    (fun t st => st.1.get ≤ u ∧ u ≤ st.2.get ∧ st.2.get ≤ B ∧ st.2.get - st.1.get ≤ B / 2 ^ t)
    k st0 ⟨h0, by omega, by omega, by simp [h1]⟩
    (fun t st _ ⟨p1, p2, p3, p4⟩ => by
      obtain ⟨s1, s2, s3⟩ := hstep t st p1 p2 p3
      have hdiv : B / 2 ^ (t + 1) = B / 2 ^ t / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
      have hhalf : (st.2.get - st.1.get) / 2 ≤ B / 2 ^ t / 2 := Nat.div_le_div_right p4
      by_cases ho : st.1.get < st.2.get
      · by_cases hl : (st.1.get + st.2.get + 1) / 2 ≤ u
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

/-- The program's binary search, started at the least value, finds the greatest feasible
value of a cell.
PAPER: sections/scales.tex:24-30 -/
theorem cellMax_val (I : Instance) (hfeas : Pseudocode.feasible I)
    (r c : List SNat) (b : List (List SNat))
    (hr : r.length = I.m) (hc : c.length = I.n) (hb : b.length = I.m)
    (hbrow : ∀ row ∈ b, row.length = I.n)
    (hrv : ∀ i : Fin I.m, (r.getD i.val default).get = I.r i)
    (hcv : ∀ j : Fin I.n, (c.getD j.val default).get = I.c j)
    (hbv : ∀ (i : Fin I.m) (j : Fin I.n), ((b.getD i.val []).getD j.val default).get = I.b i j)
    (i : Fin I.m) (j : Fin I.n) (l : SNat) (hl : l.get = Pseudocode.cellLow I i j) :
    (Program.cellMax I.m I.n r c b i.val j.val l).val.get = Pseudocode.cellHigh I i j := by
  have hne : I.Omega.Nonempty := hfeas
  set u := Pseudocode.cellHigh I i j with hudef
  have hu : ∀ v, (∃ X ∈ I.Omega, v ≤ X i j) ↔ v ≤ u := by
    intro v
    simp only [hudef, Pseudocode.cellHigh, dif_pos hne]
    constructor
    · rintro ⟨X, hX, hle⟩
      exact hle.trans (Finset.le_max' _ _ (Finset.mem_image_of_mem (fun X => X i j) hX))
    · intro h
      obtain ⟨X, hX, hXe⟩ := Finset.mem_image.1 (Finset.max'_mem (I.Omega.image fun X => X i j) (hne.image _))
      exact ⟨X, hX, hXe ▸ h⟩
  have hlu : Pseudocode.cellLow I i j ≤ u := by
    simp only [hudef, Pseudocode.cellLow, Pseudocode.cellHigh, dif_pos hne]
    obtain ⟨X, hX⟩ := hne
    exact (Finset.min'_le _ _ (Finset.mem_image_of_mem _ hX)).trans
      (Finset.le_max' _ _ (Finset.mem_image_of_mem (fun X => X i j) hX))
  have hub : u ≤ I.b i j := by
    obtain ⟨X, hX, hXu⟩ := (hu u).2 le_rfl
    exact hXu.trans (((mem_Omega_iff I X).1 hX).1 i j)
  have hbij : (Program.get2 b i.val j.val).val.get = I.b i j := by
    simp only [Program.get2, Charged.val_bind, Cellcounting.Interface.val_get]
    exact hbv i j
  unfold Program.cellMax
  simp only [Charged.val_bind, Charged.val_pure, Program.searchRounds,
    Cellcounting.Interface.SNat.val_index, Cellcounting.Interface.SNat.get_bitLen]
  rw [hbij]
  refine bsearch_high _ u (I.b i j) _ ?_ (fun t st p1 p2 p3 => ?_) _ (by rw [hl]; exact hlu)
    hbij hub
  · unfold Cellcounting.bitLen
    exact (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  · have hmid : (Program.half (SNat.add (SNat.add st.1 st.2).val (SNat.lit 1).val).val).val.get =
        (st.1.get + st.2.get + 1) / 2 := by
      simp [Program.half]
    refine ⟨fun ho hl' => ?_, fun ho hl' => ?_, fun ho => ?_⟩
    · have hok := (feasibleAtLeast_iff I r c b hr hc hb hbrow hrv hcv hbv i j
        (Program.half (SNat.add (SNat.add st.1 st.2).val (SNat.lit 1).val).val).val).2
        ((hu _).2 (by rw [hmid]; exact hl'))
      simp only [Charged.val_bind, Cellcounting.Interface.SNat.val_lt, decide_eq_true ho,
        if_true, hok, Charged.val_pure]
      exact ⟨by first | exact hmid | trivial, by first | rfl | trivial⟩
    · have hok : (Program.feasibleAtLeast I.m I.n r c b i.val j.val
          (Program.half (SNat.add (SNat.add st.1 st.2).val (SNat.lit 1).val).val).val).val = false := by
        cases h : (Program.feasibleAtLeast I.m I.n r c b i.val j.val
          (Program.half (SNat.add (SNat.add st.1 st.2).val (SNat.lit 1).val).val).val).val
        · rfl
        · exact absurd ((hu _).1 ((feasibleAtLeast_iff I r c b hr hc hb hbrow hrv hcv hbv i j
            _).1 h)) (by rw [hmid]; exact hl')
      simp only [Charged.val_bind, Cellcounting.Interface.SNat.val_lt, decide_eq_true ho,
        if_true, hok, Bool.false_eq_true, if_false, Charged.val_pure,
        Cellcounting.Interface.SNat.get_sub, Cellcounting.Interface.SNat.get_lit]
      exact ⟨by first | rfl | trivial, by first | rw [hmid] | trivial⟩
    · simp only [Charged.val_bind, Cellcounting.Interface.SNat.val_lt, decide_eq_false ho,
        Bool.false_eq_true, if_false, Charged.val_pure]
      exact ⟨by first | rfl | trivial, by first | rfl | trivial⟩

end Cellcounting.Analysis
