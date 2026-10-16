import Cellcounting.Analysis.ForestSolve

/-!
# Subtrees of a valid elimination order and their cuts

`scales.tex:136-158` (proof of `lem:forest`): for a valid elimination order `l`
(`ElimValid`), every eliminated vertex `x.1` has the parent `oth x`.  The vertices
descending to `v` form the subtree of `v`.  Two facts drive the cut argument:

* `desc_iff_of_ne`: a tree edge whose child endpoint is not `v` has both or
  neither endpoint in the subtree of `v`;
* `not_desc_oth`: the parent of `v` is not in the subtree of `v` (the order is
  acyclic: parents are eliminated after their children).

So the only tree edge leaving the subtree of an eliminated vertex `v` is its own
parent edge, and no tree edge leaves the subtree of a root.
-/

namespace Cellcounting.Analysis

variable {R Cv : ℕ → ℕ} {N : ℕ} {l : List (ℕ × ℕ)}

/-- INTERNAL: `b` is the parent of `a` in the elimination order `l`. -/
def EPar (R Cv : ℕ → ℕ) (l : List (ℕ × ℕ)) (a b : ℕ) : Prop :=
  ∃ x ∈ l, x.1 = a ∧ oth R Cv x = b

/-- INTERNAL: `a` descends to `b` (reflexively). -/
def EDesc (R Cv : ℕ → ℕ) (l : List (ℕ × ℕ)) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (EPar R Cv l)

/-- INTERNAL: an entry's parent differs from the entry's vertex. -/
theorem oth_ne_fst (hv : ElimValid R Cv N l) {x : ℕ × ℕ} (hx : x ∈ l) : oth R Cv x ≠ x.1 := by
  have hne := hv.ne _ (hv.lt x hx)
  unfold oth
  rcases hv.inc x hx with h | h <;> split_ifs <;> omega

/-- INTERNAL: an entry's parent is an endpoint of its edge. -/
theorem oth_inc (x : ℕ × ℕ) : R x.2 = oth R Cv x ∨ Cv x.2 = oth R Cv x := by
  unfold oth; split_ifs <;> simp

/-- INTERNAL: entries with the same vertex are equal. -/
theorem eq_of_fst_eq (hv : ElimValid R Cv N l) {x y : ℕ × ℕ} (hx : x ∈ l) (hy : y ∈ l)
    (h : x.1 = y.1) : x = y :=
  List.inj_on_of_nodup_map hv.nodup_fst hx hy h

/-- INTERNAL: entries with the same edge are equal. -/
theorem eq_of_snd_eq (hv : ElimValid R Cv N l) {x y : ℕ × ℕ} (hx : x ∈ l) (hy : y ∈ l)
    (h : x.2 = y.2) : x = y :=
  List.inj_on_of_nodup_map hv.nodup_snd hx hy h

/-- INTERNAL: the position of a vertex in the order (`l.length` for roots). -/
def eIdx (l : List (ℕ × ℕ)) (a : ℕ) : ℕ := (l.map Prod.fst).idxOf a

/-- INTERNAL: parents come strictly later in the order. -/
theorem eIdx_lt_of_par (hv : ElimValid R Cv N l) {a b : ℕ} (h : EPar R Cv l a b) :
    eIdx l a < eIdx l b := by
  obtain ⟨x, hx, rfl, rfl⟩ := h
  have hxa : x.1 ∈ l.map Prod.fst := List.mem_map_of_mem hx
  by_cases hb : oth R Cv x ∈ l.map Prod.fst
  · obtain ⟨y, hy, hyb⟩ := List.mem_map.1 hb
    obtain ⟨l1, l2, hl⟩ := List.append_of_mem hy
    have hxy : x.2 ≠ y.2 := by
      intro h
      have := eq_of_snd_eq hv hx hy h
      subst this
      exact oth_ne_fst hv hx hyb.symm
    have hinc : R x.2 = y.1 ∨ Cv x.2 = y.1 := by rw [hyb]; exact oth_inc x
    obtain ⟨z, hz, hzx⟩ := List.mem_map.1 (hv.child l1 y.1 y.2 l2 hl x.2 (hv.lt x hx) hinc hxy)
    have hzl : z ∈ l := by rw [hl]; exact List.mem_append_left _ hz
    have := eq_of_snd_eq hv hzl hx hzx
    subst this
    have hnd := hv.nodup_fst
    rw [hl, List.map_append, List.map_cons, List.nodup_append] at hnd
    have hy1 : y.1 ∉ l1.map Prod.fst := fun h => hnd.2.2 _ h _ List.mem_cons_self rfl
    unfold eIdx
    rw [hl, List.map_append, List.map_cons, ← hyb,
      List.idxOf_append_of_mem (List.mem_map_of_mem hz),
      List.idxOf_append_of_notMem hy1, List.idxOf_cons_self]
    have := List.idxOf_lt_length_of_mem (List.mem_map_of_mem (f := Prod.fst) hz)
    simp only [List.length_map] at this ⊢
    omega
  · unfold eIdx
    rw [List.idxOf_eq_length hb]
    exact List.idxOf_lt_length_of_mem hxa

theorem eIdx_le_of_desc (hv : ElimValid R Cv N l) {a b : ℕ} (h : EDesc R Cv l a b) :
    eIdx l a ≤ eIdx l b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact ih.trans (eIdx_lt_of_par hv hbc).le

/-- INTERNAL: the parent of an eliminated vertex is outside its subtree. -/
theorem not_desc_oth (hv : ElimValid R Cv N l) {x : ℕ × ℕ} (hx : x ∈ l) :
    ¬ EDesc R Cv l (oth R Cv x) x.1 := fun h =>
  absurd (eIdx_le_of_desc hv h) (not_le.2 (eIdx_lt_of_par hv ⟨x, hx, rfl, rfl⟩))

/-- INTERNAL: a vertex descending to `v` is `v` or eliminated. -/
theorem desc_mem (_hv : ElimValid R Cv N l) {u v : ℕ} (h : EDesc R Cv l u v) :
    u = v ∨ u ∈ l.map Prod.fst := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, ⟨x, hx, rfl, -⟩, -⟩
  · exact Or.inl rfl
  · exact Or.inr (List.mem_map_of_mem hx)

/-- INTERNAL: an entry whose vertex is not `v` has both or neither of its
vertex and parent in the subtree of `v`. -/
theorem desc_iff_of_ne (hv : ElimValid R Cv N l) {x : ℕ × ℕ} (hx : x ∈ l) {v : ℕ}
    (hxv : x.1 ≠ v) : EDesc R Cv l x.1 v ↔ EDesc R Cv l (oth R Cv x) v := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h' | ⟨c, ⟨y, hy, hyx, rfl⟩, hc⟩
    · exact absurd h' hxv
    · have := eq_of_fst_eq hv hy hx hyx
      subst this
      exact hc
  · exact Relation.ReflTransGen.head ⟨x, hx, rfl, rfl⟩

/-- **The cut of a subtree.**  For a tree edge `t'`, if the entry eliminating
through `t'` is not that of `v`, the endpoints of `t'` are both or neither in the
subtree of `v`.
TEXLINE: sections/scales.tex:136-158 -/
theorem desc_edge_iff (hv : ElimValid R Cv N l) {t' : ℕ} (ht' : t' < N) {v : ℕ}
    (hne : ∀ x ∈ l, x.2 = t' → x.1 ≠ v) :
    EDesc R Cv l (R t') v ↔ EDesc R Cv l (Cv t') v := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (hv.cover t' ht')
  have h := desc_iff_of_ne hv hx (hne x hx rfl)
  have hR := hv.ne x.2 ht'
  unfold oth at h
  rcases hv.inc x hx with hi | hi
  · rw [if_pos hi] at h; rw [← hi]; exact h
  · rw [if_neg (by rw [hi]; exact Ne.symm hR)] at h; rw [← hi]; exact h.symm

end Cellcounting.Analysis
