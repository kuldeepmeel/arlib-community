import Cellcounting.Analysis.PseudoElimOrderValid

/-!
# A feasible table of the tightened instance

`scales.tex:35-44`: for `X ∈ Ω(r, c, b)`, the table `X* = X - l` lies in the
tightened box `0 ≤ X*_s ≤ b_s = u_s - l_s` and has the tightened margins; it
vanishes on the deleted cells (`b_s = 0`).  Splitting the retained cells into
small, tree and free cells, every tightened margin is the sum of `X*` over the
cells incident to its vertex (`margin_split`).  This is the fixed feasible table
`X*` of `lem:forest` (`scales.tex:141-143`).
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: a sum over a `flatMap`. -/
theorem list_sum_flatMap {α β : Type*} (l : List α) (f : α → List β) (g : β → ℚ) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- INTERNAL: a sum over a `filterMap`. -/
theorem list_sum_filterMap {α β : Type*} (l : List α) (f : α → Option β) (g : β → ℚ) :
    ((l.filterMap f).map g).sum = (l.map fun a => (f a).elim 0 g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => cases h : f a <;> simp [h, ih]

/-- INTERNAL: a list sum as a sum over positions. -/
theorem list_sum_range {α : Type*} (L : List α) (d : α) (h : α → ℚ) :
    (L.map h).sum = ∑ k ∈ Finset.range L.length, h (L.getD k d) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

variable (I : Instance)

/-- INTERNAL: a sum over the retained cells of a function vanishing on deleted
cells is the sum over the whole table. -/
theorem retained_sum (g : ℕ → ℕ → ℚ)
    (hg : ∀ (i : Fin I.m) (j : Fin I.n), cellRange I i j = 0 → g i j = 0) :
    ((retained I).map fun e => g e.1 e.2.1).sum = ∑ i : Fin I.m, ∑ j : Fin I.n, g i j := by
  unfold retained
  rw [list_sum_flatMap, Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [list_sum_filterMap, Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro j _
  split_ifs with h
  · rfl
  · simp only [Option.elim]
    exact (hg i j (by omega)).symm

/-- INTERNAL: a retained cell is `(i, j, u_ij - l_ij)` with positive range. -/
theorem mem_retained_iff {e : Entry} (he : e ∈ retained I) :
    ∃ (i : Fin I.m) (j : Fin I.n), e = (i.val, j.val, cellRange I i j) ∧ 0 < cellRange I i j := by
  unfold retained at he
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and] at he
  obtain ⟨i, j, hj⟩ := he
  split_ifs at hj with hcond
  · cases hj
    exact ⟨i, j, rfl, hcond⟩

/-- INTERNAL: `X* = X - l` on the table, `0` outside. -/
noncomputable def xStar (X : Fin I.m → Fin I.n → ℕ) (i j : ℕ) : ℕ :=
  if h : i < I.m ∧ j < I.n then X ⟨i, h.1⟩ ⟨j, h.2⟩ - cellLow I ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

variable {I}

theorem cellLow_le {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) (i : Fin I.m) (j : Fin I.n) :
    cellLow I i j ≤ X i j := by
  unfold cellLow
  rw [dif_pos ⟨X, hX⟩]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem (fun X : Fin I.m → Fin I.n → ℕ => X i j) hX)

theorem le_cellHigh {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) (i : Fin I.m) (j : Fin I.n) :
    X i j ≤ cellHigh I i j := by
  unfold cellHigh
  rw [dif_pos ⟨X, hX⟩]
  exact Finset.le_max' _ _ (Finset.mem_image_of_mem (fun X : Fin I.m → Fin I.n → ℕ => X i j) hX)

theorem xStar_le {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) (i : Fin I.m) (j : Fin I.n) :
    xStar I X i j ≤ cellRange I i j := by
  unfold xStar cellRange
  rw [dif_pos ⟨i.2, j.2⟩]
  simp only [Fin.eta]
  have := le_cellHigh hX i j
  omega

/-- INTERNAL: `X*` is bounded by the bound of every retained cell. -/
theorem xStar_le_of_retained {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) {e : Entry}
    (he : e ∈ retained I) : xStar I X e.1 e.2.1 ≤ e.2.2 := by
  obtain ⟨i, j, rfl, -⟩ := mem_retained_iff I he
  exact xStar_le hX i j

theorem tRow_eq {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) (i : Fin I.m) :
    (tRow I i : ℚ) = ∑ j : Fin I.n, (xStar I X i j : ℚ) := by
  have hrow := (Finset.mem_filter.1 hX).2.1 i
  unfold tRow xStar
  rw [dif_pos i.2]
  simp only [Fin.eta, Fin.is_lt, and_true, i.2, dif_pos]
  rw [← Nat.cast_sum, Finset.sum_tsub_distrib _ (fun j _ => cellLow_le hX i j), hrow]

theorem tCol_eq {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) (j : Fin I.n) :
    (tCol I j : ℚ) = ∑ i : Fin I.m, (xStar I X i j : ℚ) := by
  have hcol := (Finset.mem_filter.1 hX).2.2 j
  unfold tCol xStar
  rw [dif_pos j.2]
  simp only [Fin.eta, Fin.is_lt, true_and, j.2, dif_pos]
  rw [← Nat.cast_sum, Finset.sum_tsub_distrib _ (fun i _ => cellLow_le hX i j), hcol]

/-- INTERNAL: the indicator that a cell is incident to vertex `u`. -/
def incQ (m : ℕ) (e : Entry) (u : ℕ) : ℚ :=
  (if e.1 = u then 1 else 0) + (if m + e.2.1 = u then 1 else 0)

/-- INTERNAL: every tightened margin is the sum of `X*` over the table cells
incident to its vertex. -/
theorem margin_eq_table {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) (u : ℕ) :
    (margin I u : ℚ) = ∑ i : Fin I.m, ∑ j : Fin I.n,
      incQ I.m (i.val, j.val, 0) u * (xStar I X i j : ℚ) := by
  unfold incQ
  simp only [add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib]
  unfold margin
  split_ifs with hu
  · rw [Finset.sum_eq_single ⟨u, hu⟩ (fun i _ hi => Finset.sum_eq_zero fun j _ => by
        rw [if_neg (fun h => hi (Fin.ext h))]) (by simp)]
    simp only [if_true]
    rw [tRow_eq hX ⟨u, hu⟩]
    have : ∑ i : Fin I.m, ∑ j : Fin I.n, (if I.m + (j : ℕ) = u then (xStar I X i j : ℚ) else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by rw [if_neg (by omega)]
    rw [this, add_zero]
  · have h0 : ∑ i : Fin I.m, ∑ j : Fin I.n, (if (i : ℕ) = u then (xStar I X i j : ℚ) else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by rw [if_neg (by omega)]
    rw [h0, zero_add, Finset.sum_comm]
    by_cases hn : u - I.m < I.n
    · rw [Finset.sum_eq_single ⟨u - I.m, hn⟩ (fun j _ hj => Finset.sum_eq_zero fun i _ => by
          rw [if_neg (fun h => hj (Fin.ext (by simp; omega)))]) (by simp)]
      simp only [show I.m + (u - I.m) = u by omega, if_true]
      exact tCol_eq hX ⟨u - I.m, hn⟩
    · rw [Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => by
        rw [if_neg (by have := j.2; omega)]]
      unfold tCol
      rw [dif_neg hn]
      simp

variable (I) (ε δ : ℚ)

/-- INTERNAL: the retained cells are the small, tree and free cells. -/
theorem retained_split (h : Entry → ℚ) :
    ((retained I).map h).sum = ((smallCells I ε δ).map h).sum +
      ((forest I ε δ).tree.map h).sum + ((forest I ε δ).free.map h).sum := by
  have h1 := ((List.filter_append_perm (fun e : Entry => decide (e.2.2 < WParam I ε δ))
    (retained I)).map h).sum_eq
  rw [← h1, List.map_append, List.sum_append]
  have h2 : (retained I).filter (fun e : Entry => !decide (e.2.2 < WParam I ε δ)) =
      largeCells I ε δ := by
    unfold largeCells
    exact List.filter_congr (fun e _ => by
      rcases Nat.lt_or_ge e.2.2 (WParam I ε δ) with h | h <;>
        simp [h, Nat.not_lt.2 h])
  rw [h2, add_assoc]
  congr 1
  have h3 := ((((forest_perm I ε δ).trans (sortedLarge_perm I ε δ))).map h).sum_eq
  rw [← h3, List.map_append, List.sum_append]

/-- **The margins of `X*`.**  For `X ∈ Ω`, `X* = X - l` has every tightened
margin as the sum of `X*` over the incident small, free and tree cells, and lies
below the bound of every retained cell.
PAPER: sections/scales.tex:141-143 ("any fixed feasible table `X*` of the
tightened instance", via the tightening bijection `scales.tex:35-44`). -/
theorem margin_split {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) (u : ℕ) :
    (margin I u : ℚ) =
      ∑ k ∈ Finset.range (nSmall I ε δ),
          incQ I.m (smallAt I ε δ k) u * (xStar I X (smallAt I ε δ k).1 (smallAt I ε δ k).2.1 : ℚ) +
        ∑ k ∈ Finset.range (nFree I ε δ),
          incQ I.m (freeAt I ε δ k) u * (xStar I X (freeAt I ε δ k).1 (freeAt I ε δ k).2.1 : ℚ) +
        ∑ t ∈ Finset.range (forest I ε δ).tree.length,
          incQ I.m (treeAt I ε δ t) u * (xStar I X (treeAt I ε δ t).1 (treeAt I ε δ t).2.1 : ℚ) := by
  rw [margin_eq_table hX]
  have hr := retained_sum I (fun i j => incQ I.m (i, j, 0) u * (xStar I X i j : ℚ))
    (fun i j h0 => by
      have := xStar_le hX i j
      rw [h0, Nat.le_zero] at this
      simp [this])
  rw [← hr]
  have hinc : ∀ e : Entry, incQ I.m (e.1, e.2.1, 0) u = incQ I.m e u := fun e => rfl
  simp only [hinc]
  rw [retained_split I ε δ, list_sum_range _ (0, 0, 0), list_sum_range _ (0, 0, 0),
    list_sum_range _ (0, 0, 0)]
  unfold nSmall nFree smallAt freeAt treeAt
  ring

end Cellcounting.Analysis
