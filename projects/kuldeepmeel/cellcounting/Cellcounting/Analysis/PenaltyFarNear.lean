import Cellcounting.Analysis.ContaminationBoxes
import Cellcounting.Analysis.ContaminationParams

/-!
# Far and near assignments

The classification in the proof of `prop:contamination`
(`integer-signatures.tex:494-505`): an assignment with positive penalty is
either *far* (`D ≥ 4K`: a nonzero root deviation, which is a nonzero integer, or
a tree value at distance at least `γ b_t` from `[0, b_t]`) or has a *near* tree
violation `0 < dist(z_t, [0, b_t]) < γ b_t`.  Tree values are integers, every
tree cell is large (`b_t ≥ W > 0`), and there are at most `d` tree cells.
-/

namespace Cellcounting.Analysis

open Pseudocode

variable (I : Instance) (ε δ : ℚ)

/-- INTERNAL: `dist(x, [0, b]) ≥ 0`. -/
theorem boxDist_nonneg (x b : ℚ) : 0 ≤ boxDist x b := by
  unfold boxDist; split_ifs <;> linarith

/-- INTERNAL: the penalty is nonnegative.
TEXLINE: sections/scales.tex:113-126 -/
theorem asgPen_nonneg (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) :
    0 ≤ asgPen I ε δ p := by
  unfold asgPen penalty
  apply mul_nonneg (by positivity)
  apply add_nonneg
  · apply List.sum_nonneg
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨v, -, rfl⟩ := ha
    exact abs_nonneg _
  · exact Finset.sum_nonneg fun t _ => div_nonneg (boxDist_nonneg _ _) (by positivity)

/-- INTERNAL: the integers, as a subring of `ℚ`. -/
abbrev intS : Subring ℚ := (Int.castRingHom ℚ).range

/-- INTERNAL: the non-tree load of an integral assignment is an integer.
TEXLINE: sections/scales.tex:101-113 -/
theorem baseLoad_int (x y : ℕ → ℕ) (n : ℕ → ℕ) (v : ℕ) :
    baseLoad I ε δ x y (fun k => (n k : ℚ)) v ∈ intS := by
  unfold baseLoad
  refine add_mem (Subring.sum_mem _ fun k _ => add_mem ?_ ?_) (Subring.sum_mem _ fun k _ => add_mem ?_ ?_) <;>
    split_ifs <;> first | exact zero_mem _ | exact natCast_mem _ _

/-- INTERNAL: leaf elimination keeps loads and tree values integral. -/
theorem treeValues_fold_int (l : List (ℕ × ℕ)) (st : (ℕ → ℚ) × (ℕ → ℚ))
    (h1 : ∀ v, st.1 v ∈ intS) (h2 : ∀ v, st.2 v ∈ intS) :
    (∀ v, (l.foldl (fun st vt =>
      let e := treeAt I ε δ vt.2
      let ztv := margin I vt.1 - st.1 vt.1
      let other := if vt.1 = e.1 then I.m + e.2.1 else e.1
      (Function.update st.1 other (st.1 other + ztv), Function.update st.2 vt.2 ztv)) st).1 v ∈ intS) ∧
    (∀ v, (l.foldl (fun st vt =>
      let e := treeAt I ε δ vt.2
      let ztv := margin I vt.1 - st.1 vt.1
      let other := if vt.1 = e.1 then I.m + e.2.1 else e.1
      (Function.update st.1 other (st.1 other + ztv), Function.update st.2 vt.2 ztv)) st).2 v ∈ intS) := by
  induction l generalizing st with
  | nil => exact ⟨h1, h2⟩
  | cons a l ih =>
    have hm : ∀ v, margin I v ∈ intS := by
      intro v; unfold margin; split_ifs <;> exact natCast_mem _ _
    apply ih
    · intro v
      simp only
      rw [Function.update_apply]
      split_ifs <;> first | exact add_mem (h1 _) (sub_mem (hm _) (h1 _)) | exact h1 _
    · intro v
      simp only
      rw [Function.update_apply]; split_ifs
      · exact sub_mem (hm _) (h1 _)
      · exact h2 _

/-- INTERNAL: loads and tree values of an assignment are integers.
TEXLINE: sections/scales.tex:128-140 -/
theorem treeValues_int (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) :
    (∀ v, (treeValues I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2)).1 v ∈ intS) ∧
    (∀ v, (treeValues I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2)).2 v ∈ intS) := by
  have hz : extendQ p.2 = fun k => ((extendN p.2 k : ℕ) : ℚ) := by
    funext k; unfold extendQ extendN; split_ifs <;> simp
  unfold treeValues
  rw [hz]
  exact treeValues_fold_int I ε δ _ _ (fun v => baseLoad_int I ε δ _ _ _ v) (fun _ => zero_mem _)

/-- INTERNAL: tree values of integral assignments are integers (`lem:forest`).
TEXLINE: sections/scales.tex:128-140 -/
theorem asgTree_int (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) (t : ℕ) :
    ∃ k : ℤ, asgTree I ε δ p t = k := by
  obtain ⟨k, hk⟩ := (treeValues_int I ε δ p).2 t
  exact ⟨k, by rw [asgTree, ← hk]; simp⟩

/-- INTERNAL: Kruskal's fold only puts input cells in the tree, and each input
cell lands in the tree or the free list. -/
theorem kruskal_fold_tree (m : ℕ) (l : List Entry) (F : Forest) :
    (∀ e ∈ (l.foldl (kruskalStep m) F).tree, e ∈ F.tree ∨ e ∈ l) ∧
    (l.foldl (kruskalStep m) F).tree.length + (l.foldl (kruskalStep m) F).free.length =
      F.tree.length + F.free.length + l.length := by
  induction l generalizing F with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ih1, ih2⟩ := ih (kruskalStep m F a)
    refine ⟨fun e he => ?_, ?_⟩
    · rcases ih1 e he with h | h
      · unfold kruskalStep at h
        split_ifs at h
        · exact Or.inl h
        · simp only [List.mem_append, List.mem_singleton] at h
          rcases h with h | rfl
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rw [List.foldl_cons, ih2]
      unfold kruskalStep
      split_ifs <;> simp <;> omega

/-- INTERNAL: the insertion sort behind `sortedLarge` keeps membership and length. -/
theorem sortedLarge_aux (l acc : List Entry) :
    (∀ x, x ∈ l.foldl (fun acc x => acc.orderedInsert (fun a b : Entry => b.2.2 < a.2.2) x) acc ↔
      x ∈ acc ∨ x ∈ l) ∧
    (l.foldl (fun acc x => acc.orderedInsert (fun a b : Entry => b.2.2 < a.2.2) x) acc).length =
      acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ih1, ih2⟩ := ih (acc.orderedInsert (fun a b : Entry => b.2.2 < a.2.2) a)
    refine ⟨fun x => ?_, ?_⟩
    · rw [List.foldl_cons, ih1, List.mem_orderedInsert]
      simp only [List.mem_cons]; tauto
    · rw [List.foldl_cons, ih2, List.orderedInsert_length]; simp; omega

/-- INTERNAL: every tree cell is large.
TEXLINE: sections/scales.tex:88-99 -/
theorem tree_bound_ge (t : ℕ) (ht : t < (forest I ε δ).tree.length) :
    WParam I ε δ ≤ (treeAt I ε δ t).2.2 := by
  have hmem : treeAt I ε δ t ∈ (forest I ε δ).tree := by
    unfold treeAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    exact List.getElem_mem ht
  rcases (kruskal_fold_tree I.m _ _).1 _ hmem with h | h
  · simp at h
  · have h' := ((sortedLarge_aux (largeCells I ε δ) []).1 _).1 h
    simp only [List.not_mem_nil, false_or] at h'
    unfold largeCells at h'
    simpa using (List.mem_filter.1 h').2

/-- INTERNAL: there are at most `d` tree cells.
TEXLINE: sections/scales.tex:76-80 -/
theorem tree_length_le : (forest I ε δ).tree.length ≤ dParam I := by
  have h1 := (kruskal_fold_tree I.m (sortedLarge I ε δ) ⟨[], [], id⟩).2
  have h2 := (sortedLarge_aux (largeCells I ε δ) []).2
  have h3 : (largeCells I ε δ).length ≤ (retained I).length := List.length_filter_le _ _
  have h4 : (retained I).length ≤ I.m * I.n := by
    unfold retained
    rw [List.length_flatMap]
    have := List.sum_le_length_nsmul ((List.finRange I.m).map fun i =>
      ((List.finRange I.n).filterMap fun j =>
        if 0 < cellRange I i j then some (i.val, j.val, cellRange I i j) else none).length) I.n
      (by
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨i, -, rfl⟩ := hx
        exact (List.length_filterMap_le _ _).trans (by simp))
    simpa using this
  have : (forest I ε δ).tree.length ≤ (sortedLarge I ε δ).length := by
    unfold forest; simp at h1; omega
  unfold dParam; simp at h2; unfold sortedLarge at this; omega

/-- INTERNAL: an assignment with positive penalty is far or has a near tree
violation.
TEXLINE: sections/integer-signatures.tex:494-505 -/
theorem asgPen_far_or_near (hε : 0 < ε) (hε1 : ε < 1)
    (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) (hp : asgPen I ε δ p ≠ 0) :
    4 * (KParam I ε δ : ℚ) ≤ asgPen I ε δ p ∨ ∃ t < (forest I ε δ).tree.length,
      0 < boxDist (asgTree I ε δ p t) ((treeAt I ε δ t).2.2 : ℚ) ∧
        boxDist (asgTree I ε δ p t) ((treeAt I ε δ t).2.2 : ℚ) <
          γParam I ε δ * (treeAt I ε δ t).2.2 := by
  set tv := treeValues I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2) with htv
  set R := ((roots I ε δ).map fun v => |tv.1 v - margin I v|).sum with hR
  set T := ∑ t ∈ Finset.range (forest I ε δ).tree.length,
    boxDist (tv.2 t) ((treeAt I ε δ t).2.2 : ℚ) / ((treeAt I ε δ t).2.2 : ℚ) with hT
  have hpen : asgPen I ε δ p = (AParam I ε δ : ℚ) * (R + T) := rfl
  have hA : 4 * (KParam I ε δ : ℚ) ≤ AParam I ε δ * γParam I ε δ := AParam_mul_γ I ε δ hε
  have hγ1 := γParam_le_one I ε δ hε hε1
  have hγ0 := γParam_pos I ε δ hε
  have hA0 : (0 : ℚ) ≤ AParam I ε δ := by positivity
  have hRnn : 0 ≤ R := List.sum_nonneg (by
    intro a ha; simp only [List.mem_map] at ha; obtain ⟨v, -, rfl⟩ := ha; exact abs_nonneg _)
  have hTnn : 0 ≤ T :=
    Finset.sum_nonneg fun t _ => div_nonneg (boxDist_nonneg _ _) (by positivity)
  have hmarg : ∀ v, margin I v ∈ intS := by
    intro v; unfold margin; split_ifs <;> exact natCast_mem _ _
  have hRint : R ∈ intS := by
    rw [hR]
    apply Subring.list_sum_mem
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨v, -, rfl⟩ := ha
    obtain ⟨k, hk⟩ := sub_mem ((treeValues_int I ε δ p).1 v) (hmarg v)
    exact ⟨|k|, by simp only [eq_intCast] at hk ⊢; rw [← hk]; push_cast; rfl⟩
  by_cases hR0 : R = 0
  · have hT0 : T ≠ 0 := by
      intro h; apply hp; rw [hpen, hR0, h]; simp
    obtain ⟨t, ht, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT0
    rw [Finset.mem_range] at ht
    have hb : ((treeAt I ε δ t).2.2 : ℚ) ≠ 0 := by
      intro h; apply hne; rw [h, div_zero]
    have hbpos : (0 : ℚ) < (treeAt I ε δ t).2.2 := lt_of_le_of_ne (by positivity) (Ne.symm hb)
    have hd0 : boxDist (tv.2 t) ((treeAt I ε δ t).2.2 : ℚ) ≠ 0 := by
      intro h; apply hne; rw [h, zero_div]
    by_cases hnear : boxDist (tv.2 t) ((treeAt I ε δ t).2.2 : ℚ) <
        γParam I ε δ * (treeAt I ε δ t).2.2
    · exact Or.inr ⟨t, ht, lt_of_le_of_ne (boxDist_nonneg _ _) (Ne.symm hd0), hnear⟩
    · left
      push Not at hnear
      have h1 : γParam I ε δ ≤ boxDist (tv.2 t) ((treeAt I ε δ t).2.2 : ℚ) /
          ((treeAt I ε δ t).2.2 : ℚ) := by
        rw [le_div_iff₀ hbpos]; exact hnear
      have h2 : boxDist (tv.2 t) ((treeAt I ε δ t).2.2 : ℚ) / ((treeAt I ε δ t).2.2 : ℚ) ≤ T :=
        Finset.single_le_sum (f := fun t => boxDist (tv.2 t) ((treeAt I ε δ t).2.2 : ℚ) /
          ((treeAt I ε δ t).2.2 : ℚ))
          (fun t _ => div_nonneg (boxDist_nonneg _ _) (by positivity))
          (Finset.mem_range.2 ht)
      rw [hpen]
      calc 4 * (KParam I ε δ : ℚ) ≤ AParam I ε δ * γParam I ε δ := hA
        _ ≤ AParam I ε δ * (R + T) := mul_le_mul_of_nonneg_left (by linarith) hA0
  · left
    obtain ⟨k, hk⟩ := hRint
    simp only [eq_intCast] at hk
    have hk0 : k ≠ 0 := by rintro rfl; exact hR0 (by rw [← hk]; simp)
    have hkn : 0 ≤ k := by exact_mod_cast (hk ▸ hRnn : (0 : ℚ) ≤ k)
    have hR1 : 1 ≤ R := by
      rw [← hk]; exact_mod_cast (by omega : (1 : ℤ) ≤ k)
    rw [hpen]
    calc 4 * (KParam I ε δ : ℚ) ≤ AParam I ε δ * γParam I ε δ := hA
      _ ≤ AParam I ε δ * (R + T) := mul_le_mul_of_nonneg_left (by linarith) hA0

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · all five goals closed; root term integral via `treeValues_int`, far tree cell via `A γ ≥ 4K`
-/
