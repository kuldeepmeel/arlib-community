import Cellcounting.Analysis.ForestSolve

/-!
# The pseudocode's elimination order is valid

`scales.tex:88-99, 128-134`: Kruskal's algorithm over the large cells builds a
spanning forest of the large-cell graph whose components are the classes of
`comp`; there are exactly as many classes as `roots`; breadth-first search from
the roots then discovers every nonroot vertex exactly once, through a tree edge
whose other endpoint was discovered earlier, and uses every tree edge exactly
once.  Read newest first, this is an elimination order in which every vertex
comes after all its children (`ElimValid`).

* `kruskal_inv`: the invariants of the Kruskal fold;
* `roots_*`: the roots are one least vertex per class;
* `bfs_inv`: the invariants of the breadth-first search;
* `elimOrder_valid`: the conclusion.
-/

namespace Cellcounting.Analysis

open Pseudocode Finset

/-! ### Kruskal -/

section kruskal

variable (m : ℕ)

/-- INTERNAL: adjacency through an edge list (rows `e.1`, columns `m + e.2.1`). -/
def EAdj (T : List Entry) (u w : ℕ) : Prop :=
  ∃ e ∈ T, (e.1 = u ∧ m + e.2.1 = w) ∨ (e.1 = w ∧ m + e.2.1 = u)

/-- INTERNAL: connectivity through an edge list. -/
def EReach (T : List Entry) : ℕ → ℕ → Prop := Relation.ReflTransGen (EAdj m T)

theorem EAdj_symm (T : List Entry) {u w : ℕ} (h : EAdj m T u w) : EAdj m T w u := by
  obtain ⟨e, he, h⟩ := h
  exact ⟨e, he, h.symm⟩

theorem EReach_symm (T : List Entry) {u w : ℕ} (h : EReach m T u w) : EReach m T w u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (EAdj_symm m T hbc) ih

theorem EReach_mono {T T' : List Entry} (hT : ∀ e ∈ T, e ∈ T') {u w : ℕ}
    (h : EReach m T u w) : EReach m T' u w := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    obtain ⟨e, he, h⟩ := hbc
    exact Relation.ReflTransGen.tail ih ⟨e, hT e he, h⟩

/-- INTERNAL: the Kruskal invariants after processing a prefix `pre`. -/
structure KInv (V : ℕ) (pre : List Entry) (F : Forest) : Prop where
  reach : ∀ u w, F.comp u = F.comp w → EReach m F.tree u w
  count : F.tree.length + ((Finset.range V).image F.comp).card = V
  perm : (F.tree ++ F.free).Perm pre

theorem kruskal_inv (V : ℕ) (L : List Entry) (hL : ∀ e ∈ L, e.1 < V ∧ m + e.2.1 < V) :
    KInv m V L (L.foldl (kruskalStep m) ⟨[], [], id⟩) := by
  classical
  induction L using List.reverseRecOn with
  | nil =>
    refine ⟨fun u w h => ?_, ?_, ?_⟩
    · simp only [List.foldl_nil] at h ⊢; subst h; exact Relation.ReflTransGen.refl
    · simp
    · simp
  | append_singleton L e ih =>
    have ih := ih (fun e' he' => hL e' (by simp [he']))
    have he := hL e (by simp)
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set F := L.foldl (kruskalStep m) ⟨[], [], id⟩
    unfold kruskalStep
    split_ifs with hc
    · -- free cell
      refine ⟨ih.reach, ih.count, ?_⟩
      have := ih.perm
      simpa [← List.append_assoc] using this.append_right [e]
    · -- tree cell: merge the class of `m + e.2.1` into that of `e.1`
      set c1 := F.comp e.1
      set c2 := F.comp (m + e.2.1)
      refine ⟨fun u w h => ?_, ?_, ?_⟩
      · simp only at h ⊢
        have hsub : ∀ x ∈ F.tree, x ∈ F.tree ++ [e] := fun x hx => by simp [hx]
        have hedge : EReach m (F.tree ++ [e]) e.1 (m + e.2.1) :=
          Relation.ReflTransGen.single ⟨e, by simp, Or.inl ⟨rfl, rfl⟩⟩
        by_cases hu : F.comp u = c2 <;> by_cases hw : F.comp w = c2 <;>
          simp only [hu, hw, if_true, if_false] at h
        · exact EReach_mono m hsub (ih.reach u w (hu.trans hw.symm))
        · -- `u ∈ c2`, `w ∈ c1`
          have h1 := EReach_mono m hsub (ih.reach u (m + e.2.1) hu)
          have h2 := EReach_mono m hsub (ih.reach e.1 w h)
          exact h1.trans ((EReach_symm m _ hedge).trans h2)
        · have h1 := EReach_mono m hsub (ih.reach u e.1 h)
          have h2 := EReach_mono m hsub (ih.reach (m + e.2.1) w hw.symm)
          exact h1.trans (hedge.trans h2)
        · exact EReach_mono m hsub (ih.reach u w h)
      · simp only [List.length_append, List.length_singleton]
        have himg : (Finset.range V).image
            (fun w => if F.comp w = c2 then c1 else F.comp w) =
            ((Finset.range V).image F.comp).erase c2 := by
          ext c
          simp only [Finset.mem_image, Finset.mem_range, Finset.mem_erase]
          constructor
          · rintro ⟨w, hw, rfl⟩
            split_ifs with h
            · exact ⟨hc, e.1, he.1, rfl⟩
            · exact ⟨h, w, hw, rfl⟩
          · rintro ⟨hne, w, hw, rfl⟩
            exact ⟨w, hw, by simp [hne]⟩
        rw [himg, Finset.card_erase_of_mem (Finset.mem_image.2 ⟨m + e.2.1, Finset.mem_range.2 he.2, rfl⟩)]
        have hpos : 0 < ((Finset.range V).image F.comp).card :=
          Finset.card_pos.2 ⟨c1, Finset.mem_image.2 ⟨e.1, Finset.mem_range.2 he.1, rfl⟩⟩
        have := ih.count
        omega
      · have := ih.perm
        simp only
        have h2 : (F.tree ++ [e] ++ F.free).Perm (F.tree ++ F.free ++ [e]) := by
          simp only [List.append_assoc]
          exact List.Perm.append_left _ (List.perm_append_comm)
        exact h2.trans (this.append_right [e])

end kruskal

end Cellcounting.Analysis
