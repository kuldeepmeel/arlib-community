import Cellcounting.Analysis.ContaminationBoxes
import Cellcounting.Analysis.FeasibleMargin
import Cellcounting.Analysis.PenaltyFarNear

/-!
# Zero-penalty assignments are the feasible tables

The first paragraph of the proof of `prop:contamination`
(`integer-signatures.tex:485-493`) together with the tightening bijection
(`scales.tex:35-44`): for a feasible instance and `ε > 0`, the assignments of
penalty zero are in bijection with `Ω(r, c, b)`, so there are exactly `Z` of them;
and for every tree cell both endpoints `0` and `b_t` of its tightened range are
attained by a zero-penalty assignment (endpoint attainability after tightening).

* `tableAsg X` is the assignment `(x, z)` of a table `X ∈ Ω`: `X* = X - l` read on
  the small and free cells.  It lies in the box, has penalty zero, and its tree
  values are `X*` on the tree cells (`tableAsg_spec`), by uniqueness of the
  leaf-elimination completion (`tvFin_unique`) and the margins of `X*`
  (`margin_split`).
* `asgTable p` is the table `l + (x, z)` of an assignment, reading tree values off
  leaf elimination.  For a zero-penalty assignment it is feasible
  (`asgTable_mem`): every vertex is a root or eliminated (`elim_cover`), so all
  margin equations hold, and the tree values are integers in their boxes.
* `tree_endpoints` uses `tableAsg` at tables minimising and maximising the cell.
* `zero_pen_card` needs `0 < ε`: at `ε ≤ 0` the multiplier `A = ⌈4K/γ⌉₊` is `0`, the
  penalty vanishes identically and the count is the whole box.
-/

namespace Cellcounting.Analysis

open Pseudocode

section tableAsg

variable (I : Instance) (ε δ : ℚ)

variable {ε δ}

/-- INTERNAL: small cells lie in the retained list. -/
theorem smallAt_mem_retained {s : ℕ} (hs : s < nSmall I ε δ) : smallAt I ε δ s ∈ retained I := by
  exact List.mem_of_mem_filter (eo_getD_mem (ht := hs))

/-- INTERNAL: large (tree or free) cells lie in the retained list. -/
theorem forest_mem_retained {e : Entry}
    (he : e ∈ (forest I ε δ).tree ∨ e ∈ (forest I ε δ).free) : e ∈ retained I :=
  mem_largeCells ((sortedLarge_perm I ε δ).mem_iff.1
    ((forest_perm I ε δ).mem_iff.1 (List.mem_append.2 he)))

/-- INTERNAL: free cells lie in the retained list. -/
theorem freeAt_mem_retained {k : ℕ} (hk : k < nFree I ε δ) : freeAt I ε δ k ∈ retained I := by
  exact forest_mem_retained I (Or.inr (eo_getD_mem (ht := hk)))

/-- INTERNAL: tree cells lie in the retained list. -/
theorem treeAt_mem_retained {t : ℕ} (ht : t < (forest I ε δ).tree.length) :
    treeAt I ε δ t ∈ retained I := by
  exact forest_mem_retained I (Or.inl (eo_getD_mem (ht := ht)))

variable (ε δ)

/-- INTERNAL: the assignment `(x, z)` of a table `X`: `X* = X - l` read on the
small and the free cells. -/
noncomputable def tableAsg (X : Fin I.m → Fin I.n → ℕ) :
    (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ) :=
  (fun s => xStar I X (smallAt I ε δ s).1 (smallAt I ε δ s).2.1,
    fun k => xStar I X (freeAt I ε δ k).1 (freeAt I ε δ k).2.1)

variable {I}

/-- INTERNAL: the assignment of a feasible table lies in the box. -/
theorem tableAsg_mem {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) :
    tableAsg I ε δ X ∈ asgBox I ε δ := by
  unfold asgBox smallBox freeBox tableAsg
  simp only [Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]
  exact ⟨fun s => xStar_le_of_retained hX (smallAt_mem_retained I s.2),
    fun k => xStar_le_of_retained hX (freeAt_mem_retained I k.2)⟩

/-- INTERNAL: leaf elimination is the generic `tvFin`. -/
theorem treeValues_eq_tvFin (x y : ℕ → ℕ) (z : ℕ → ℚ) :
    treeValues I ε δ x y z = tvFin (fun t => (treeAt I ε δ t).1)
      (fun t => I.m + (treeAt I ε δ t).2.1) (margin I) (baseLoad I ε δ x y z)
      (elimOrder I ε δ) := rfl

/-- INTERNAL: the non-tree load of `tableAsg X` is the sum of `X*` over the
incident small and free cells. -/
theorem baseLoad_tableAsg {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) (u : ℕ) :
    baseLoad I ε δ (extendN (tableAsg I ε δ X).1) (balY I ε δ (tableAsg I ε δ X).1)
        (extendQ (tableAsg I ε δ X).2) u =
      ∑ k ∈ Finset.range (nSmall I ε δ),
          incQ I.m (smallAt I ε δ k) u * (xStar I X (smallAt I ε δ k).1 (smallAt I ε δ k).2.1 : ℚ) +
        ∑ k ∈ Finset.range (nFree I ε δ),
          incQ I.m (freeAt I ε δ k) u * (xStar I X (freeAt I ε δ k).1 (freeAt I ε δ k).2.1 : ℚ) := by
  unfold baseLoad
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    have hx : extendN (tableAsg I ε δ X).1 k =
        xStar I X (smallAt I ε δ k).1 (smallAt I ε δ k).2.1 := by
      simp [extendN, tableAsg, hk']
    have hle := xStar_le_of_retained hX (smallAt_mem_retained I hk')
    have hy : (smallAt I ε δ k).2.2 - balY I ε δ (tableAsg I ε δ X).1 k =
        xStar I X (smallAt I ε δ k).1 (smallAt I ε δ k).2.1 := by
      unfold balY smallB; rw [hx]; omega
    rw [hy, hx]
    unfold incQ
    split_ifs <;> ring
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    have hz : extendQ (tableAsg I ε δ X).2 k =
        (xStar I X (freeAt I ε δ k).1 (freeAt I ε δ k).2.1 : ℚ) := by
      simp [extendQ, tableAsg, hk']
    rw [hz]
    unfold incQ
    split_ifs <;> ring

/-- INTERNAL: **the assignment of a feasible table has penalty zero**, and its
tree values are `X*` on the tree cells.
TEXLINE: sections/integer-signatures.tex:485-493 -/
theorem tableAsg_spec {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) :
    asgPen I ε δ (tableAsg I ε δ X) = 0 ∧
      ∀ t < (forest I ε δ).tree.length, asgTree I ε δ (tableAsg I ε δ X) t =
        (xStar I X (treeAt I ε δ t).1 (treeAt I ε δ t).2.1 : ℚ) := by
  classical
  obtain ⟨hv, hroot⟩ := pseudo_elimOrder_valid I ε δ
  set R : ℕ → ℕ := fun t => (treeAt I ε δ t).1 with hR
  set Cv : ℕ → ℕ := fun t => I.m + (treeAt I ε δ t).2.1 with hCv
  set N := (forest I ε δ).tree.length with hN
  set base := baseLoad I ε δ (extendN (tableAsg I ε δ X).1) (balY I ε δ (tableAsg I ε δ X).1)
        (extendQ (tableAsg I ε δ X).2) with hbase
  set Tv : ℕ → ℚ := fun t => (xStar I X (treeAt I ε δ t).1 (treeAt I ε δ t).2.1 : ℚ) with hTv
  have hload : ∀ u, tLoadG R Cv N base Tv u = margin I u := by
    intro u
    unfold tLoadG
    rw [margin_split I ε δ hX u, hbase, baseLoad_tableAsg ε δ hX u]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [hR, hCv, hTv, incQ]
    split_ifs <;> ring
  have huniq := tvFin_unique (marg := margin I) hv base Tv (fun x _ => hload x.1)
  have htv : treeValues I ε δ (extendN (tableAsg I ε δ X).1) (balY I ε δ (tableAsg I ε δ X).1)
      (extendQ (tableAsg I ε δ X).2) = tvFin R Cv (margin I) base (elimOrder I ε δ) :=
    treeValues_eq_tvFin ε δ _ _ _
  have hTree : ∀ t < N, asgTree I ε δ (tableAsg I ε δ X) t = Tv t := by
    intro t ht
    unfold asgTree
    rw [htv, huniq t ht]
  refine ⟨?_, hTree⟩
  unfold asgPen penalty
  rw [htv]
  have hroots : ((roots I ε δ).map fun v =>
      |(tvFin R Cv (margin I) base (elimOrder I ε δ)).1 v - margin I v|).sum = 0 := by
    apply List.sum_eq_zero
    intro a ha
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha
    rw [tvFin_root hv base r (hroot r hr)]
    have : tLoadG R Cv N base (tvFin R Cv (margin I) base (elimOrder I ε δ)).2 r =
        tLoadG R Cv N base Tv r := by
      unfold tLoadG
      congr 1
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [← huniq t (Finset.mem_range.1 ht)]
    rw [this, hload, sub_self, abs_zero]
  have htree : ∑ t ∈ Finset.range N,
      boxDist ((tvFin R Cv (margin I) base (elimOrder I ε δ)).2 t) ((treeAt I ε δ t).2.2 : ℚ) /
        ((treeAt I ε δ t).2.2 : ℚ) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    have ht' := Finset.mem_range.1 ht
    rw [← huniq t ht']
    have hle := xStar_le_of_retained hX (treeAt_mem_retained I ht')
    have h0 : (0 : ℚ) ≤ Tv t := by simp [hTv]
    have h1 : Tv t ≤ ((treeAt I ε δ t).2.2 : ℚ) := by simp only [hTv]; exact_mod_cast hle
    unfold boxDist
    rw [if_neg (not_lt.2 h0), if_neg (not_lt.2 h1), zero_div]
  rw [hroots, htree, add_zero, mul_zero]

end tableAsg

section bij

variable (I : Instance) (ε δ : ℚ)

/-- INTERNAL: every vertex is a root or is eliminated. -/
theorem elim_cover (u : ℕ) (hu : u < I.m + I.n) (hr : u ∉ roots I ε δ) :
    u ∈ (elimOrder I ε δ).map Prod.fst := by
  classical
  obtain ⟨hv, hroot⟩ := pseudo_elimOrder_valid I ε δ
  have hK := forest_kinv I ε δ
  set l := elimOrder I ε δ with hl
  set N := (forest I ε δ).tree.length with hN
  have hlen : l.length = N := by
    have h1 : (l.map Prod.snd).toFinset = Finset.range N := by
      ext t
      simp only [List.mem_toFinset, Finset.mem_range]
      constructor
      · intro ht
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ht
        exact hv.lt x hx
      · exact hv.cover t
    have := List.toFinset_card_of_nodup hv.nodup_snd
    rw [h1, Finset.card_range, List.length_map] at this
    exact this.symm
  have hlt : ∀ x ∈ l, x.1 < I.m + I.n := by
    intro x hx
    have ht := hv.lt x hx
    have hm := forest_mem_lt I ε δ (Or.inl (eo_getD_mem (ht := ht)))
    rcases hv.inc x hx with h | h <;> rw [h] <;> simp only [treeAt] <;> omega
  have hdisj : Disjoint (roots I ε δ).toFinset (l.map Prod.fst).toFinset := by
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    exact hroot r (List.mem_toFinset.1 hr1) (List.mem_toFinset.1 hr2)
  have hcard : ((roots I ε δ).toFinset ∪ (l.map Prod.fst).toFinset).card = I.m + I.n := by
    rw [Finset.card_union_of_disjoint hdisj, List.toFinset_card_of_nodup (roots_nodup I ε δ),
      List.toFinset_card_of_nodup hv.nodup_fst, List.length_map, hlen, roots_card]
    have := hK.count
    omega
  have hsub : (roots I ε δ).toFinset ∪ (l.map Prod.fst).toFinset ⊆ Finset.range (I.m + I.n) := by
    intro w hw
    rw [Finset.mem_union, List.mem_toFinset, List.mem_toFinset] at hw
    rw [Finset.mem_range]
    rcases hw with hw | hw
    · exact ((mem_roots_iff I ε δ w).1 hw).1
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
      exact hlt x hx
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])
  have hmem : u ∈ (roots I ε δ).toFinset ∪ (l.map Prod.fst).toFinset := by
    rw [heq]; exact Finset.mem_range.2 hu
  rw [Finset.mem_union, List.mem_toFinset, List.mem_toFinset] at hmem
  exact hmem.resolve_left hr

/-- INTERNAL: the retained cells, small cells first, then tree, then free cells. -/
noncomputable def cellList : List Entry :=
  smallCells I ε δ ++ (forest I ε δ).tree ++ (forest I ε δ).free

/-- INTERNAL: the positions `(i, j)` of `cellList`. -/
noncomputable def cellPos : List (ℕ × ℕ) := (cellList I ε δ).map fun e => (e.1, e.2.1)

/-- INTERNAL: `cellList` is a rearrangement of the retained cells. -/
theorem cellList_perm : (cellList I ε δ).Perm (retained I) := by
  have h1 := List.filter_append_perm (fun e : Entry => decide (e.2.2 < WParam I ε δ)) (retained I)
  have h2 : (retained I).filter (fun e : Entry => !decide (e.2.2 < WParam I ε δ)) =
      largeCells I ε δ := by
    unfold largeCells
    exact List.filter_congr (fun e _ => by
      rcases Nat.lt_or_ge e.2.2 (WParam I ε δ) with h | h <;>
        simp [h, Nat.not_lt.2 h])
  rw [h2] at h1
  unfold cellList
  rw [List.append_assoc]
  exact (List.Perm.append_left _ ((forest_perm I ε δ).trans (sortedLarge_perm I ε δ))).trans h1

/-- INTERNAL: the retained cells are distinct. -/
theorem retained_nodup : (retained I).Nodup := by
  unfold retained
  rw [List.nodup_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · refine List.Nodup.filterMap (fun a a' b hb hb' => ?_) (List.nodup_finRange _)
    simp only [Option.mem_def] at hb hb'
    split_ifs at hb hb'
    cases hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb'
    exact Fin.ext hb'.2.1.symm
  · refine (List.nodup_finRange I.m).imp fun {i i'} hii' => ?_
    intro e he he'
    rw [List.mem_filterMap] at he he'
    obtain ⟨j, -, hj⟩ := he
    obtain ⟨j', -, hj'⟩ := he'
    split_ifs at hj hj'
    cases hj
    simp only [Option.some.injEq, Prod.mk.injEq] at hj'
    exact hii' (Fin.ext hj'.1.symm)

/-- INTERNAL: distinct retained cells have distinct positions. -/
theorem cellPos_nodup : (cellPos I ε δ).Nodup := by
  unfold cellPos
  refine List.Nodup.map_on (fun x hx y hy hxy => ?_)
    ((cellList_perm I ε δ).nodup_iff.2 (retained_nodup I))
  obtain ⟨i, j, rfl, -⟩ := mem_retained_iff I ((cellList_perm I ε δ).subset hx)
  obtain ⟨i', j', rfl, -⟩ := mem_retained_iff I ((cellList_perm I ε δ).subset hy)
  simp only [Prod.mk.injEq] at hxy
  have hi : i = i' := Fin.ext hxy.1
  have hj : j = j' := Fin.ext hxy.2
  subst hi hj; rfl

/-- INTERNAL: the length of `cellList`. -/
theorem cellList_length : (cellList I ε δ).length =
    nSmall I ε δ + (forest I ε δ).tree.length + nFree I ε δ := by
  simp [cellList, nSmall, nFree, Nat.add_assoc]

/-- INTERNAL: the `k`-th entry of `cellList` is the `k`-th small cell. -/
theorem cellList_small {k : ℕ} (hk : k < nSmall I ε δ) (h : k < (cellList I ε δ).length) :
    (cellList I ε δ)[k] = smallAt I ε δ k := by
  simp only [cellList, smallAt, nSmall] at hk ⊢
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_left hk,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]

/-- INTERNAL: the tree cells follow the small cells in `cellList`. -/
theorem cellList_tree {t : ℕ} (ht : t < (forest I ε δ).tree.length)
    (h : nSmall I ε δ + t < (cellList I ε δ).length) :
    (cellList I ε δ)[nSmall I ε δ + t] = treeAt I ε δ t := by
  simp only [cellList, treeAt, nSmall] at ht h ⊢
  rw [List.getElem_append_left (by simpa using ht), List.getElem_append_right (by omega),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
  simp

/-- INTERNAL: the free cells close `cellList`. -/
theorem cellList_free {k : ℕ} (hk : k < nFree I ε δ)
    (h : nSmall I ε δ + (forest I ε δ).tree.length + k < (cellList I ε δ).length) :
    (cellList I ε δ)[nSmall I ε δ + (forest I ε δ).tree.length + k] = freeAt I ε δ k := by
  simp only [cellList, freeAt, nSmall, nFree] at hk h ⊢
  rw [List.getElem_append_right (by simp),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  simp

/-- INTERNAL: the value an assignment gives the `k`-th cell of `cellList`
(tree values rounded down to naturals). -/
noncomputable def asgVal (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) (k : ℕ) : ℕ :=
  if k < nSmall I ε δ then extendN p.1 k
  else if k - nSmall I ε δ < (forest I ε δ).tree.length then
    ⌊asgTree I ε δ p (k - nSmall I ε δ)⌋₊
  else extendN p.2 (k - nSmall I ε δ - (forest I ε δ).tree.length)

/-- INTERNAL: the value an assignment gives the cell at position `(i, j)`
(`0` at a deleted cell). -/
noncomputable def cellVal (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) (i j : ℕ) : ℕ :=
  if (i, j) ∈ cellPos I ε δ then asgVal I ε δ p ((cellPos I ε δ).idxOf (i, j)) else 0

/-- INTERNAL: the table `X = l + (x, z)` of an assignment. -/
noncomputable def asgTable (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) :
    Fin I.m → Fin I.n → ℕ :=
  fun i j => cellLow I i j + cellVal I ε δ p i j

/-- INTERNAL: the cell value at the position of the `k`-th entry of `cellList`. -/
theorem cellVal_at (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) (k : ℕ)
    (hk : k < (cellList I ε δ).length) :
    cellVal I ε δ p ((cellList I ε δ)[k]).1 ((cellList I ε δ)[k]).2.1 = asgVal I ε δ p k := by
  have hk' : k < (cellPos I ε δ).length := by simp [cellPos, hk]
  have hpos : (cellPos I ε δ)[k] = (((cellList I ε δ)[k]).1, ((cellList I ε δ)[k]).2.1) := by
    simp [cellPos]
  unfold cellVal
  rw [← hpos, if_pos (List.getElem_mem hk'), (cellPos_nodup I ε δ).idxOf_getElem k hk']

/-- INTERNAL: the cell value of a small cell is its `x_s`. -/
theorem cellVal_small (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) {k : ℕ}
    (hk : k < nSmall I ε δ) :
    cellVal I ε δ p (smallAt I ε δ k).1 (smallAt I ε δ k).2.1 = extendN p.1 k := by
  have h : k < (cellList I ε δ).length := by rw [cellList_length]; omega
  rw [← cellList_small I ε δ hk h, cellVal_at I ε δ p k h, asgVal, if_pos hk]

/-- INTERNAL: the cell value of a tree cell is its rounded tree value. -/
theorem cellVal_tree (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) {t : ℕ}
    (ht : t < (forest I ε δ).tree.length) :
    cellVal I ε δ p (treeAt I ε δ t).1 (treeAt I ε δ t).2.1 = ⌊asgTree I ε δ p t⌋₊ := by
  have h : nSmall I ε δ + t < (cellList I ε δ).length := by rw [cellList_length]; omega
  rw [← cellList_tree I ε δ ht h, cellVal_at I ε δ p _ h, asgVal, if_neg (by omega),
    if_pos (by omega), Nat.add_sub_cancel_left]

/-- INTERNAL: the cell value of a free cell is its `z_e`. -/
theorem cellVal_free (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) {k : ℕ}
    (hk : k < nFree I ε δ) :
    cellVal I ε δ p (freeAt I ε δ k).1 (freeAt I ε δ k).2.1 = extendN p.2 k := by
  have h : nSmall I ε δ + (forest I ε δ).tree.length + k < (cellList I ε δ).length := by
    rw [cellList_length]; omega
  rw [← cellList_free I ε δ hk h, cellVal_at I ε δ p _ h, asgVal, if_neg (by omega),
    if_neg (by omega)]
  congr 1
  omega

/-- INTERNAL: a cell position in `cellPos` is the position of its own `cellList` entry,
which is the retained cell `(i, j, u_ij - l_ij)`. -/
theorem cellPos_mem (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ))
    {i : Fin I.m} {j : Fin I.n} (h : ((i : ℕ), (j : ℕ)) ∈ cellPos I ε δ) :
    ∃ k, ∃ hk : k < (cellList I ε δ).length,
      (cellList I ε δ)[k] = (i.val, j.val, cellRange I i j) ∧
      cellVal I ε δ p i j = asgVal I ε δ p k := by
  obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem h
  have hk' : k < (cellList I ε δ).length := by simpa [cellPos] using hk
  have hpos : (cellPos I ε δ)[k] = (((cellList I ε δ)[k]).1, ((cellList I ε δ)[k]).2.1) := by
    simp [cellPos]
  obtain ⟨i', j', he, -⟩ := mem_retained_iff I
    ((cellList_perm I ε δ).subset (List.getElem_mem hk'))
  rw [hpos, he] at hkeq
  simp only [Prod.mk.injEq] at hkeq
  have hi : i' = i := Fin.ext hkeq.1
  have hj : j' = j := Fin.ext hkeq.2
  subst hi hj
  refine ⟨k, hk', he, ?_⟩
  have := cellVal_at I ε δ p k hk'
  rw [he] at this
  exact this

/-- INTERNAL: deleted cells (`u_ij = l_ij`) get value `0`. -/
theorem cellVal_eq_zero (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ))
    {i : Fin I.m} {j : Fin I.n} (h : cellRange I i j = 0) : cellVal I ε δ p i j = 0 := by
  unfold cellVal
  rw [if_neg]
  intro hmem
  obtain ⟨e, he, hpos⟩ := List.mem_map.1 hmem
  obtain ⟨i', j', rfl, hpos'⟩ := mem_retained_iff I ((cellList_perm I ε δ).subset he)
  simp only [Prod.mk.injEq] at hpos
  have hi : i' = i := Fin.ext hpos.1
  have hj : j' = j := Fin.ext hpos.2
  subst hi hj
  omega

/-- INTERNAL: a cell of positive range is retained. -/
theorem mem_retained_of_pos {i : Fin I.m} {j : Fin I.n} (h : 0 < cellRange I i j) :
    ((i : ℕ), (j : ℕ), cellRange I i j) ∈ retained I := by
  unfold retained
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and]
  exact ⟨i, j, by rw [if_pos h]⟩

/-- INTERNAL: a cell of positive range has a position in `cellPos`. -/
theorem cellPos_of_pos {i : Fin I.m} {j : Fin I.n} (h : 0 < cellRange I i j) :
    ((i : ℕ), (j : ℕ)) ∈ cellPos I ε δ :=
  List.mem_map.2 ⟨_, (cellList_perm I ε δ).mem_iff.2 (mem_retained_of_pos I h), rfl⟩

variable {I} in
/-- INTERNAL: the values of the assignment of `X ∈ Ω` are `X*`. -/
theorem asgVal_tableAsg {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) (k : ℕ)
    (hk : k < (cellList I ε δ).length) :
    asgVal I ε δ (tableAsg I ε δ X) k =
      xStar I X ((cellList I ε δ)[k]).1 ((cellList I ε δ)[k]).2.1 := by
  have hlen := cellList_length I ε δ
  by_cases h1 : k < nSmall I ε δ
  · rw [asgVal, if_pos h1, cellList_small I ε δ h1 hk]
    simp [extendN, tableAsg, h1]
  by_cases h2 : k - nSmall I ε δ < (forest I ε δ).tree.length
  · obtain ⟨t, rfl⟩ : ∃ t, k = nSmall I ε δ + t := ⟨k - nSmall I ε δ, by omega⟩
    have ht : t < (forest I ε δ).tree.length := by omega
    rw [asgVal, if_neg h1, if_pos h2, Nat.add_sub_cancel_left, cellList_tree I ε δ ht hk,
      (tableAsg_spec ε δ hX).2 t ht, Nat.floor_natCast]
  · obtain ⟨k', rfl⟩ : ∃ k', k = nSmall I ε δ + (forest I ε δ).tree.length + k' :=
      ⟨k - nSmall I ε δ - (forest I ε δ).tree.length, by omega⟩
    have hk' : k' < nFree I ε δ := by omega
    rw [asgVal, if_neg h1, if_neg h2, cellList_free I ε δ hk' hk,
      show nSmall I ε δ + (forest I ε δ).tree.length + k' - nSmall I ε δ -
        (forest I ε δ).tree.length = k' by omega]
    simp [extendN, tableAsg, hk']

variable {I} in
/-- INTERNAL: the table of the assignment of `X ∈ Ω` is `X`. -/
theorem asgTable_tableAsg {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) :
    asgTable I ε δ (tableAsg I ε δ X) = X := by
  funext i j
  unfold asgTable
  by_cases hpos : 0 < cellRange I i j
  · obtain ⟨k, hk, hke, hv⟩ := cellPos_mem I ε δ (tableAsg I ε δ X) (cellPos_of_pos I ε δ hpos)
    rw [hv, asgVal_tableAsg ε δ hX k hk, hke]
    simp only [xStar, i.2, j.2, and_self, dif_pos, Fin.eta]
    have := cellLow_le hX i j
    omega
  · rw [cellVal_eq_zero I ε δ _ (by omega)]
    have h1 := cellLow_le hX i j
    have h2 := le_cellHigh hX i j
    unfold cellRange at hpos
    omega

variable {I ε δ} in
/-- INTERNAL: the non-tree load of any assignment of the box. -/
theorem baseLoad_asg {p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)}
    (hp : p ∈ asgBox I ε δ) (u : ℕ) :
    baseLoad I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2) u =
      ∑ k ∈ Finset.range (nSmall I ε δ), incQ I.m (smallAt I ε δ k) u * (extendN p.1 k : ℚ) +
        ∑ k ∈ Finset.range (nFree I ε δ), incQ I.m (freeAt I ε δ k) u * (extendN p.2 k : ℚ) := by
  unfold asgBox smallBox at hp
  simp only [Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range] at hp
  unfold baseLoad
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    have hle : extendN p.1 k ≤ (smallAt I ε δ k).2.2 := by
      have := hp.1 ⟨k, hk'⟩
      simp only [extendN, hk', dif_pos]
      unfold smallB at this
      simp only at this
      omega
    have hy : (smallAt I ε δ k).2.2 - balY I ε δ p.1 k = extendN p.1 k := by
      unfold balY smallB; omega
    rw [hy]
    unfold incQ
    split_ifs <;> ring
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    have hz : extendQ p.2 k = (extendN p.2 k : ℚ) := by
      simp [extendQ, extendN, hk']
    rw [hz]
    unfold incQ
    split_ifs <;> ring

variable {I ε δ} in
/-- INTERNAL: a zero-penalty assignment satisfies every margin equation, and its
tree values lie in their boxes. -/
theorem zeroPen_facts (hε : 0 < ε) {p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)}
    (h0 : asgPen I ε δ p = 0) :
    (∀ u < I.m + I.n, tLoadG (fun t => (treeAt I ε δ t).1) (fun t => I.m + (treeAt I ε δ t).2.1)
      (forest I ε δ).tree.length (baseLoad I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2))
      (asgTree I ε δ p) u = margin I u) ∧
    ∀ t < (forest I ε δ).tree.length,
      0 ≤ asgTree I ε δ p t ∧ asgTree I ε δ p t ≤ (treeAt I ε δ t).2.2 := by
  classical
  obtain ⟨hv, hroot⟩ := pseudo_elimOrder_valid I ε δ
  set base := baseLoad I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2) with hbase
  have htv := treeValues_eq_tvFin (I := I) ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2)
  have hA : (0 : ℚ) < AParam I ε δ := by exact_mod_cast AParam_pos I ε δ hε
  unfold asgPen penalty at h0
  set S1 := ((roots I ε δ).map fun v =>
    |(treeValues I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2)).1 v - margin I v|).sum
    with hS1
  set S2 := ∑ t ∈ Finset.range (forest I ε δ).tree.length,
    boxDist ((treeValues I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2)).2 t)
      ((treeAt I ε δ t).2.2 : ℚ) / ((treeAt I ε δ t).2.2 : ℚ) with hS2
  have hS1nn : ∀ x ∈ (roots I ε δ).map (fun v =>
      |(treeValues I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2)).1 v - margin I v|),
      0 ≤ x := by
    intro x hx
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
    exact abs_nonneg _
  have hS2nn : ∀ t ∈ Finset.range (forest I ε δ).tree.length,
      0 ≤ boxDist ((treeValues I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2)).2 t)
        ((treeAt I ε δ t).2.2 : ℚ) / ((treeAt I ε δ t).2.2 : ℚ) :=
    fun t _ => div_nonneg (boxDist_nonneg _ _) (by positivity)
  have h1 : 0 ≤ S1 := List.sum_nonneg hS1nn
  have h2 : 0 ≤ S2 := Finset.sum_nonneg hS2nn
  have hsum : S1 + S2 = 0 := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hA.ne'
    · exact h
  have hS1z : S1 = 0 := by linarith
  have hS2z : S2 = 0 := by linarith
  -- the tree values lie in their boxes
  have hbox : ∀ t < (forest I ε δ).tree.length,
      0 ≤ asgTree I ε δ p t ∧ asgTree I ε δ p t ≤ (treeAt I ε δ t).2.2 := by
    intro t ht
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hS2nn).1 hS2z t (Finset.mem_range.2 ht)
    obtain ⟨i, j, he, hpos⟩ := mem_retained_iff I (treeAt_mem_retained I ht)
    have hb : (0 : ℚ) < (treeAt I ε δ t).2.2 := by rw [he]; exact_mod_cast hpos
    rw [div_eq_zero_iff, or_iff_left hb.ne'] at hz
    unfold asgTree
    unfold boxDist at hz
    split_ifs at hz with ha hc
    · constructor <;> linarith
    · constructor <;> linarith
    · constructor <;> linarith
  refine ⟨fun u hu => ?_, hbox⟩
  have hTv : asgTree I ε δ p = (tvFin (fun t => (treeAt I ε δ t).1)
      (fun t => I.m + (treeAt I ε δ t).2.1) (margin I) base (elimOrder I ε δ)).2 := by
    funext t; unfold asgTree; rw [htv]
  rw [hTv]
  by_cases hr : u ∈ roots I ε δ
  · have hz : |(treeValues I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2)).1 u -
        margin I u| ≤ S1 :=
      List.single_le_sum hS1nn _ (List.mem_map.2 ⟨u, hr, rfl⟩)
    rw [hS1z, htv, tvFin_root hv base u (hroot u hr)] at hz
    have := abs_nonneg (tLoadG (fun t => (treeAt I ε δ t).1) (fun t => I.m + (treeAt I ε δ t).2.1)
      (forest I ε δ).tree.length base (tvFin (fun t => (treeAt I ε δ t).1)
      (fun t => I.m + (treeAt I ε δ t).2.1) (margin I) base (elimOrder I ε δ)).2 u - margin I u)
    have h00 := le_antisymm hz this
    rw [abs_eq_zero, sub_eq_zero] at h00
    exact h00
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (elim_cover I ε δ u hu hr)
    exact tvFin_nonroot hv base x hx

variable {I ε δ} in
/-- INTERNAL: for a zero-penalty assignment, the margin of every vertex is the sum
of the cell values over the retained cells incident to it. -/
theorem retained_cellVal_sum (hε : 0 < ε)
    {p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)}
    (hp : p ∈ asgBox I ε δ) (h0 : asgPen I ε δ p = 0) (u : ℕ) (hu : u < I.m + I.n) :
    ((retained I).map fun e => incQ I.m e u * (cellVal I ε δ p e.1 e.2.1 : ℚ)).sum =
      margin I u := by
  obtain ⟨hload, hbox⟩ := zeroPen_facts hε h0
  rw [← ((cellList_perm I ε δ).map _).sum_eq, ← hload u hu]
  unfold cellList tLoadG
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append,
    list_sum_range _ (0, 0, 0), list_sum_range _ (0, 0, 0), list_sum_range _ (0, 0, 0),
    baseLoad_asg hp u]
  have hs : ∑ k ∈ Finset.range (smallCells I ε δ).length, incQ I.m ((smallCells I ε δ).getD k (0, 0, 0)) u *
      (cellVal I ε δ p ((smallCells I ε δ).getD k (0, 0, 0)).1
        ((smallCells I ε δ).getD k (0, 0, 0)).2.1 : ℚ) =
      ∑ k ∈ Finset.range (nSmall I ε δ), incQ I.m (smallAt I ε δ k) u * (extendN p.1 k : ℚ) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have := cellVal_small I ε δ p (Finset.mem_range.1 hk)
    unfold smallAt at this
    rw [this]; rfl
  have hf : ∑ k ∈ Finset.range (forest I ε δ).free.length,
      incQ I.m ((forest I ε δ).free.getD k (0, 0, 0)) u *
      (cellVal I ε δ p ((forest I ε δ).free.getD k (0, 0, 0)).1
        ((forest I ε δ).free.getD k (0, 0, 0)).2.1 : ℚ) =
      ∑ k ∈ Finset.range (nFree I ε δ), incQ I.m (freeAt I ε δ k) u * (extendN p.2 k : ℚ) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have := cellVal_free I ε δ p (Finset.mem_range.1 hk)
    unfold freeAt at this
    rw [this]; rfl
  have ht : ∑ k ∈ Finset.range (forest I ε δ).tree.length,
      incQ I.m ((forest I ε δ).tree.getD k (0, 0, 0)) u *
      (cellVal I ε δ p ((forest I ε δ).tree.getD k (0, 0, 0)).1
        ((forest I ε δ).tree.getD k (0, 0, 0)).2.1 : ℚ) =
      ∑ t ∈ Finset.range (forest I ε δ).tree.length,
        ((if (treeAt I ε δ t).1 = u then asgTree I ε δ p t else 0) +
          (if I.m + (treeAt I ε δ t).2.1 = u then asgTree I ε δ p t else 0)) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' := Finset.mem_range.1 ht
    have := cellVal_tree I ε δ p ht'
    unfold treeAt at this
    rw [this]
    obtain ⟨h1, h2⟩ := hbox t ht'
    obtain ⟨z, hz⟩ := asgTree_int I ε δ p t
    have hzn : ((⌊asgTree I ε δ p t⌋₊ : ℕ) : ℚ) = asgTree I ε δ p t := by
      rw [hz] at h1 ⊢
      have hz0 : (0 : ℤ) ≤ z := by exact_mod_cast h1
      lift z to ℕ using hz0
      simp
    rw [hzn]
    unfold incQ treeAt
    split_ifs <;> ring
  rw [hs, hf, ht]
  ring

variable {I} in
/-- INTERNAL: the incidence-weighted table sum at a row vertex is the row sum. -/
theorem incQ_table_row (g : Fin I.m → Fin I.n → ℚ) (i : Fin I.m) :
    ∑ i' : Fin I.m, ∑ j : Fin I.n, incQ I.m ((i' : ℕ), (j : ℕ), 0) i * g i' j = ∑ j, g i j := by
  unfold incQ
  simp only [add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib]
  have h0 : ∑ i' : Fin I.m, ∑ j : Fin I.n, (if I.m + (j : ℕ) = i then g i' j else 0) = 0 :=
    Finset.sum_eq_zero fun i' _ => Finset.sum_eq_zero fun j _ => by
      rw [if_neg (by have := i.2; omega)]
  rw [h0, add_zero, Finset.sum_eq_single i (fun i' _ hi => Finset.sum_eq_zero fun j _ => by
    rw [if_neg (fun h => hi (Fin.ext h))]) (by simp)]
  simp

variable {I} in
/-- INTERNAL: the incidence-weighted table sum at a column vertex is the column sum. -/
theorem incQ_table_col (g : Fin I.m → Fin I.n → ℚ) (j : Fin I.n) :
    ∑ i : Fin I.m, ∑ j' : Fin I.n, incQ I.m ((i : ℕ), (j' : ℕ), 0) (I.m + j) * g i j' =
      ∑ i, g i j := by
  unfold incQ
  simp only [add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib]
  have h0 : ∑ i : Fin I.m, ∑ j' : Fin I.n, (if (i : ℕ) = I.m + j then g i j' else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j' _ => by
      rw [if_neg (by have := i.2; omega)]
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single j (fun j' _ hj => by
    rw [if_neg (fun h => hj (Fin.ext (by omega)))]) (by simp)]
  simp

variable {I ε δ} in
/-- INTERNAL: the cell values of a zero-penalty assignment have the tightened
margins. -/
theorem cellVal_margins (hε : 0 < ε)
    {p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)}
    (hp : p ∈ asgBox I ε δ) (h0 : asgPen I ε δ p = 0) :
    (∀ i : Fin I.m, ∑ j : Fin I.n, (cellVal I ε δ p i j : ℚ) = tRow I i) ∧
      ∀ j : Fin I.n, ∑ i : Fin I.m, (cellVal I ε δ p i j : ℚ) = tCol I j := by
  have key : ∀ u < I.m + I.n, margin I u = ∑ i : Fin I.m, ∑ j : Fin I.n,
      incQ I.m ((i : ℕ), (j : ℕ), 0) u * (cellVal I ε δ p i j : ℚ) := by
    intro u hu
    rw [← retained_cellVal_sum hε hp h0 u hu]
    exact retained_sum I (fun i j => incQ I.m (i, j, 0) u * (cellVal I ε δ p i j : ℚ))
      (fun i j h => by rw [cellVal_eq_zero I ε δ p h]; simp)
  constructor
  · intro i
    have := key i (by have := i.2; omega)
    rw [incQ_table_row] at this
    rw [← this]
    simp [margin, i.2]
  · intro j
    have := key (I.m + j) (by have := j.2; omega)
    rw [incQ_table_col] at this
    rw [← this]
    simp [margin]

/-- INTERNAL: `u_ij ≤ b_ij` for a feasible instance. -/
theorem cellHigh_le_b (hf : I.Omega.Nonempty) (i : Fin I.m) (j : Fin I.n) :
    cellHigh I i j ≤ I.b i j := by
  unfold cellHigh
  rw [dif_pos hf]
  obtain ⟨X, hX, hXeq⟩ := Finset.mem_image.1
    (Finset.max'_mem _ (hf.image fun X : Fin I.m → Fin I.n → ℕ => X i j))
  rw [← hXeq]
  unfold Instance.Omega at hX
  have := Fintype.mem_piFinset.1 (Finset.mem_filter.1 hX).1 i
  exact Finset.mem_range_succ_iff.1 (Fintype.mem_piFinset.1 this j)

variable {I ε δ} in
/-- INTERNAL: the values of an assignment with tree values in their boxes are
bounded by the cell ranges. -/
theorem asgVal_le {p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)}
    (hp : p ∈ asgBox I ε δ)
    (hbox : ∀ t < (forest I ε δ).tree.length, asgTree I ε δ p t ≤ (treeAt I ε δ t).2.2)
    (k : ℕ) (hk : k < (cellList I ε δ).length) :
    asgVal I ε δ p k ≤ ((cellList I ε δ)[k]).2.2 := by
  unfold asgBox smallBox freeBox at hp
  simp only [Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range] at hp
  have hlen := cellList_length I ε δ
  by_cases h1 : k < nSmall I ε δ
  · rw [asgVal, if_pos h1, cellList_small I ε δ h1 hk]
    have := hp.1 ⟨k, h1⟩
    simp only [extendN, h1, dif_pos]
    unfold smallB at this
    simp only at this
    omega
  by_cases h2 : k - nSmall I ε δ < (forest I ε δ).tree.length
  · obtain ⟨t, rfl⟩ : ∃ t, k = nSmall I ε δ + t := ⟨k - nSmall I ε δ, by omega⟩
    have ht : t < (forest I ε δ).tree.length := by omega
    rw [asgVal, if_neg h1, if_pos h2, Nat.add_sub_cancel_left, cellList_tree I ε δ ht hk]
    exact Nat.floor_le_of_le (hbox t ht)
  · obtain ⟨k', rfl⟩ : ∃ k', k = nSmall I ε δ + (forest I ε δ).tree.length + k' :=
      ⟨k - nSmall I ε δ - (forest I ε δ).tree.length, by omega⟩
    have hk' : k' < nFree I ε δ := by omega
    rw [asgVal, if_neg h1, if_neg h2, cellList_free I ε δ hk' hk,
      show nSmall I ε δ + (forest I ε δ).tree.length + k' - nSmall I ε δ -
        (forest I ε δ).tree.length = k' by omega]
    have := hp.2 ⟨k', hk'⟩
    simp only [extendN, hk', dif_pos]
    simp only at this
    omega

variable {I ε δ} in
/-- INTERNAL: the table of a zero-penalty assignment is feasible. -/
theorem asgTable_mem (hε : 0 < ε) (hf : I.Omega.Nonempty)
    {p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)}
    (hp : p ∈ asgBox I ε δ) (h0 : asgPen I ε δ p = 0) : asgTable I ε δ p ∈ I.Omega := by
  obtain ⟨X0, hX0⟩ := hf
  obtain ⟨hrow, hcol⟩ := cellVal_margins hε hp h0
  have hbox := (zeroPen_facts hε h0).2
  unfold Instance.Omega
  rw [Finset.mem_filter]
  refine ⟨?_, fun i => ?_, fun j => ?_⟩
  · simp only [Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]
    intro i j
    have hv : cellVal I ε δ p i j ≤ cellRange I i j := by
      by_cases hpos : 0 < cellRange I i j
      · obtain ⟨k, hk, hke, hv⟩ := cellPos_mem I ε δ p (cellPos_of_pos I ε δ hpos)
        rw [hv]
        have := asgVal_le hp (fun t ht => (hbox t ht).2) k hk
        rw [hke] at this
        exact this
      · rw [cellVal_eq_zero I ε δ p (by omega)]; exact Nat.zero_le _
    have := cellHigh_le_b I ⟨X0, hX0⟩ i j
    have := cellLow_le hX0 i j
    have := le_cellHigh hX0 i j
    unfold asgTable
    unfold cellRange at hv
    omega
  · have hle : ∑ j, cellLow I i j ≤ I.r i := by
      rw [← (Finset.mem_filter.1 hX0).2.1 i]
      exact Finset.sum_le_sum fun j _ => cellLow_le hX0 i j
    have h1 : ∑ j : Fin I.n, cellVal I ε δ p i j = tRow I i := by exact_mod_cast hrow i
    have h2 : tRow I i = I.r i - ∑ j, cellLow I i j := by
      unfold tRow; rw [dif_pos i.2]
    unfold asgTable
    rw [Finset.sum_add_distrib, h1, h2]
    omega
  · have hle : ∑ i, cellLow I i j ≤ I.c j := by
      rw [← (Finset.mem_filter.1 hX0).2.2 j]
      exact Finset.sum_le_sum fun i _ => cellLow_le hX0 i j
    have h1 : ∑ i : Fin I.m, cellVal I ε δ p i j = tCol I j := by exact_mod_cast hcol j
    have h2 : tCol I j = I.c j - ∑ i, cellLow I i j := by
      unfold tCol; rw [dif_pos j.2]
    unfold asgTable
    rw [Finset.sum_add_distrib, h1, h2]
    omega

/-- INTERNAL: the assignment of the table of an assignment is itself. -/
theorem tableAsg_asgTable (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) :
    tableAsg I ε δ (asgTable I ε δ p) = p := by
  have hx : ∀ i j : ℕ, i < I.m → j < I.n → xStar I (asgTable I ε δ p) i j = cellVal I ε δ p i j := by
    intro i j hi hj
    simp [xStar, hi, hj, asgTable]
  refine Prod.ext (funext fun s => ?_) (funext fun k => ?_)
  · have hm := mem_retained (smallAt_mem_retained I s.2)
    simp only [tableAsg]
    rw [hx _ _ hm.1 hm.2, cellVal_small I ε δ p s.2]
    simp [extendN]
  · have hm := mem_retained (freeAt_mem_retained I k.2)
    simp only [tableAsg]
    rw [hx _ _ hm.1 hm.2, cellVal_free I ε δ p k.2]
    simp [extendN]

end bij

/-- **Zero-penalty assignments are counted by `Z`.**  The hypothesis `0 < ε` is the
paper's standing `ε ∈ (0, 1)`; it is an auto-parameter so that callers with `hε` in
context need not pass it.  Without it the statement fails: at `ε ≤ 0` the penalty
multiplier `A` is `0`, every assignment has penalty zero, and e.g. the `2 × 3`
instance `r = (2, 1)`, `c = (1, 1, 1)`, `b ≡ 1` has `Z = 3` but `4` assignments.
PAPER: sections/integer-signatures.tex:485-493 -/
theorem zero_pen_card (I : Instance) (ε δ : ℚ) (hfeas : feasible I)
    (hε : 0 < ε := by assumption) :
    ((asgBox I ε δ).filter (fun p => asgPen I ε δ p = 0)).card = I.Z := by
  unfold Instance.Z
  symm
  refine Finset.card_nbij' (tableAsg I ε δ) (asgTable I ε δ) (fun X hX => ?_) (fun p hp => ?_)
    (fun X hX => ?_) (fun p _ => ?_)
  · exact Finset.mem_filter.2 ⟨tableAsg_mem ε δ hX, (tableAsg_spec ε δ hX).1⟩
  · obtain ⟨hp, h0⟩ := Finset.mem_filter.1 hp
    exact asgTable_mem hε hfeas hp h0
  · exact asgTable_tableAsg ε δ hX
  · exact tableAsg_asgTable I ε δ p

/-- **Endpoint attainability** for tree cells: both `0` and `b_t` are values of
`z_t` at zero-penalty assignments.
PAPER: sections/scales.tex:40-44 -/
theorem tree_endpoints (I : Instance) (ε δ : ℚ) (hfeas : feasible I) (t : ℕ)
    (ht : t < (forest I ε δ).tree.length) :
    (∃ p ∈ asgBox I ε δ, asgPen I ε δ p = 0 ∧ asgTree I ε δ p t = 0) ∧
      ∃ p ∈ asgBox I ε δ, asgPen I ε δ p = 0 ∧ asgTree I ε δ p t = (treeAt I ε δ t).2.2 := by
  obtain ⟨i, j, he, -⟩ := mem_retained_iff I (treeAt_mem_retained I ht)
  have hf : I.Omega.Nonempty := hfeas
  have himg := hf.image (fun X : Fin I.m → Fin I.n → ℕ => X i j)
  constructor
  · obtain ⟨X, hX, hXij⟩ := Finset.mem_image.1 (Finset.min'_mem _ himg)
    refine ⟨tableAsg I ε δ X, tableAsg_mem ε δ hX, (tableAsg_spec ε δ hX).1, ?_⟩
    rw [(tableAsg_spec ε δ hX).2 t ht, he]
    simp only [xStar, i.2, j.2, and_self, dif_pos, Fin.eta, hXij, cellLow, dif_pos hf]
    simp
  · obtain ⟨X, hX, hXij⟩ := Finset.mem_image.1 (Finset.max'_mem _ himg)
    refine ⟨tableAsg I ε δ X, tableAsg_mem ε δ hX, (tableAsg_spec ε δ hX).1, ?_⟩
    rw [(tableAsg_spec ε δ hX).2 t ht, he]
    simp only [xStar, i.2, j.2, and_self, dif_pos, Fin.eta, hXij, cellLow, cellRange, cellHigh,
      dif_pos hf]

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `tree_endpoints` and `zero_pen_card` (restated with `hε : 0 < ε`, auto-param; false at `ε ≤ 0`)
-/
