import Cellcounting.Analysis.PseudoElimOrderValid

/-!
# Free cells are spanned by heavier tree cells

`scales.tex:91-99, 131-133`: Kruskal processes the large cells by decreasing
bound, and a cell becomes free only when its endpoints are already joined by
tree cells processed before it.  Hence the endpoints of a free cell `e` are
joined by tree cells `t` with `b_e ≤ b_t`.  This is the path inequality of
`lem:forest` in the form the cut argument uses (`free_reach_heavy`).
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: insertion keeps a list sorted by decreasing bound. -/
theorem pairwise_orderedInsert (x : Entry) : ∀ l : List Entry,
    l.Pairwise (fun a b : Entry => b.2.2 ≤ a.2.2) →
    (l.orderedInsert (fun a b : Entry => b.2.2 < a.2.2) x).Pairwise
      (fun a b : Entry => b.2.2 ≤ a.2.2)
  | [], _ => List.pairwise_singleton _ _
  | b :: l, h => by
    rw [List.pairwise_cons] at h
    simp only [List.orderedInsert_cons]
    split_ifs with hxb
    · refine List.Pairwise.cons (fun y hy => ?_) (List.Pairwise.cons h.1 h.2)
      rcases List.mem_cons.1 hy with rfl | hy
      · exact le_of_lt hxb
      · exact (h.1 y hy).trans (le_of_lt hxb)
    · refine List.Pairwise.cons (fun y hy => ?_) (pairwise_orderedInsert x l h.2)
      rcases List.mem_cons.1 ((List.perm_orderedInsert _ x l).mem_iff.1 hy) with rfl | hy
      · exact not_lt.1 hxb
      · exact h.1 y hy

/-- INTERNAL: `sortedLarge` is sorted by decreasing bound. -/
theorem sortedLarge_pairwise (I : Instance) (ε δ : ℚ) :
    (sortedLarge I ε δ).Pairwise (fun a b : Entry => b.2.2 ≤ a.2.2) := by
  unfold sortedLarge
  have : ∀ (l acc : List Entry), acc.Pairwise (fun a b : Entry => b.2.2 ≤ a.2.2) →
      (l.foldl (fun acc x => acc.orderedInsert (fun a b : Entry => b.2.2 < a.2.2) x) acc).Pairwise
        (fun a b : Entry => b.2.2 ≤ a.2.2) := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons x l ih => intro acc h; exact ih _ (pairwise_orderedInsert x acc h)
  exact this _ [] List.Pairwise.nil

/-- INTERNAL: the generic statement for a Kruskal fold over a sorted list. -/
theorem kruskal_free_reach (m V : ℕ) (L : List Entry) (hL : ∀ e ∈ L, e.1 < V ∧ m + e.2.1 < V)
    (hs : L.Pairwise (fun a b : Entry => b.2.2 ≤ a.2.2)) :
    ∀ e ∈ (L.foldl (kruskalStep m) ⟨[], [], id⟩).free,
      EReach m ((L.foldl (kruskalStep m) ⟨[], [], id⟩).tree.filter (fun f => e.2.2 ≤ f.2.2))
        e.1 (m + e.2.1) := by
  induction L using List.reverseRecOn with
  | nil => intro e he; simp at he
  | append_singleton L e ih =>
    have hL' : ∀ e' ∈ L, e'.1 < V ∧ m + e'.2.1 < V := fun e' he' => hL e' (by simp [he'])
    have hs' := (List.pairwise_append.1 hs)
    have ih := ih hL' hs'.1
    have hK := kruskal_inv m V L hL'
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set F := L.foldl (kruskalStep m) ⟨[], [], id⟩
    unfold kruskalStep
    split_ifs with hc
    · intro e' he'
      simp only [List.mem_append, List.mem_singleton] at he'
      rcases he' with he' | rfl
      · exact ih e' he'
      · refine EReach_mono m (fun f hf => ?_) (hK.reach _ _ hc)
        have hfL : f ∈ L := hK.perm.mem_iff.1 (List.mem_append_left _ hf)
        exact List.mem_filter.2 ⟨hf, decide_eq_true (hs'.2.2 f hfL e' (by simp))⟩
    · intro e' he'
      refine EReach_mono m (fun f hf => ?_) (ih e' he')
      obtain ⟨hf1, hf2⟩ := List.mem_filter.1 hf
      exact List.mem_filter.2 ⟨List.mem_append_left _ hf1, hf2⟩

/-- **The path inequality.**  The endpoints of every free cell `e` are joined by
tree cells of bound at least `b_e`.
PAPER: sections/scales.tex:131-133 (`lem:forest`: "every tree cell `t` on the path
joining its endpoints satisfies `b_e ≤ b_t`"). -/
theorem free_reach_heavy (I : Instance) (ε δ : ℚ) (e : Entry) (he : e ∈ (forest I ε δ).free) :
    EReach I.m ((forest I ε δ).tree.filter (fun f => e.2.2 ≤ f.2.2)) e.1 (I.m + e.2.1) :=
  kruskal_free_reach I.m (I.m + I.n) (sortedLarge I ε δ)
    (fun e he => by have := mem_sortedLarge he; omega) (sortedLarge_pairwise I ε δ) e he

end Cellcounting.Analysis
