import Cellcounting.Interface.Pseudocode
import Cellcounting.Analysis.FeasibleMargin
import Cellcounting.Analysis.FreeReachHeavy
import Cellcounting.Analysis.ForestCut
import Cellcounting.Analysis.ContaminationParams

/-!
# `D ≤ H` for the pseudocode's penalty (`lem:forest`)

`Cellcounting.Analysis.pseudo_penalty_le_H`: on a feasible instance, for every
box-valid small profile `(x, y)` and every free vector in the extended box
`∏_{e ∈ F} [0, b_e + 1]`, the penalty `Pseudocode.penalty` is at most `H`.

The argument is the cut argument of `lem:forest` (`scales.tex:136-158`).  Fix
`X ∈ Ω` and the feasible table `X* = X - l` of the tightened instance
(`margin_split`).  The deviation `dev u` of vertex `u` (incident sum minus
margin) is a sum, over the cells at `u`, of their displacement from `X*`
(`dev_eq`).  For a set `S` of vertices, the signed sum `Σ_{u ∈ S} ± dev u` is a
sum over the cells leaving `S` (`signed_famQ`): cells inside `S` cancel because
every cell joins a row (`+`) to a column (`-`).

* For a tree edge `t` with child `v`, take `S` = the subtree of `v`: every vertex
  of `S` satisfies its margin equation (`tvFin_nonroot`), the only tree edge
  leaving `S` is `t` (`desc_edge_iff`, `not_desc_oth`), and a free cell leaving
  `S` has `b_e ≤ b_t` (`free_reach_heavy`).  Hence
  `|z_t - X*_t| ≤ 2 Σ_small b_s + |F| (b_t + 1) ≤ 2 d b_t`.
* For a root `r`, take `S` = the component of `r`: no tree or free cell leaves
  it, so `|δ_r| ≤ 2 Σ_small b_s ≤ 2 d W`.

Summing, `D ≤ A (2 d² W + 2 d²) ≤ 10 A d² (W + 1) = H`.  The constants are
cruder than the paper's (`|z_t - X*_t| ≤ 4 d b_t`, `Σ |δ_v| ≤ 2 d W`); only
`D ≤ H` is used downstream.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Pseudocode

/-! ### Signed sums over vertex sets -/

/-- INTERNAL: `+1` on rows, `-1` on columns. -/
def sgnQ (m u : ℕ) : ℚ := if u < m then 1 else -1

/-- INTERNAL: the load of vertex `u` from a family of cells with row endpoints
`ρ k`, column endpoints `κ k`, row contributions `a k` and column contributions
`b k`. -/
def famQ (K : ℕ) (ρ κ : ℕ → ℕ) (a b : ℕ → ℚ) (u : ℕ) : ℚ :=
  ∑ k ∈ Finset.range K, ((if ρ k = u then a k else 0) + (if κ k = u then b k else 0))

/-- INTERNAL: the contribution of one cell to a signed sum over `S`. -/
def crossTerm (S : Finset ℕ) (ρ κ : ℕ) (a b : ℚ) : ℚ :=
  (if ρ ∈ S then a else 0) - (if κ ∈ S then b else 0)

/-- INTERNAL: the signed sum over `S` of a family's loads is the sum of the
cells' contributions.
TEXLINE: sections/scales.tex:141-152 -/
theorem signed_famQ (m K : ℕ) (ρ κ : ℕ → ℕ) (a b : ℕ → ℚ) (hρ : ∀ k < K, ρ k < m)
    (hκ : ∀ k < K, m ≤ κ k) (S : Finset ℕ) :
    ∑ u ∈ S, sgnQ m u * famQ K ρ κ a b u =
      ∑ k ∈ Finset.range K, crossTerm S (ρ k) (κ k) (a k) (b k) := by
  unfold famQ
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.1 hk
  simp only [mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
  unfold crossTerm sgnQ
  have h1 := hρ k hk'
  have h2 := hκ k hk'
  simp only [if_pos h1, if_neg (not_lt.2 h2)]
  split_ifs <;> ring

theorem abs_crossTerm_le (S : Finset ℕ) (ρ κ : ℕ) (a b : ℚ) :
    |crossTerm S ρ κ a b| ≤ |a| + |b| := by
  unfold crossTerm
  split_ifs <;> simp [abs_sub _ _, abs_neg] <;>
    first | exact abs_sub _ _ | exact le_add_of_nonneg_right (abs_nonneg _) |
      exact le_add_of_nonneg_left (abs_nonneg _) | positivity

theorem crossTerm_eq_zero {S : Finset ℕ} {ρ κ : ℕ} (h : ρ ∈ S ↔ κ ∈ S) (a : ℚ) :
    crossTerm S ρ κ a a = 0 := by
  unfold crossTerm
  by_cases hρ : ρ ∈ S
  · rw [if_pos hρ, if_pos (h.1 hρ), sub_self]
  · rw [if_neg hρ, if_neg (fun h' => hρ (h.2 h')), sub_self]

theorem abs_crossTerm_same (S : Finset ℕ) (ρ κ : ℕ) (a : ℚ) : |crossTerm S ρ κ a a| ≤ |a| := by
  unfold crossTerm
  split_ifs <;> simp

/-- INTERNAL: a path that starts inside a set of vertices and ends outside it uses
an edge leaving the set. -/
theorem crossing_of_ereach (m : ℕ) (T : List Entry) (P : ℕ → Prop) {a b : ℕ}
    (h : EReach m T a b) (hab : P a ↔ ¬ P b) : ∃ f ∈ T, (P f.1 ↔ ¬ P (m + f.2.1)) := by
  induction h with
  | refl => exact absurd hab (by tauto)
  | tail _ hbc ih =>
    rename_i c d _
    by_cases hc : P a ↔ ¬ P c
    · exact ih hc
    · obtain ⟨f, hf, h⟩ := hbc
      refine ⟨f, hf, ?_⟩
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto

theorem abs_crossTerm_cross {S : Finset ℕ} {ρ κ : ℕ} (h : ρ ∈ S ↔ ¬ κ ∈ S) (a : ℚ) :
    |crossTerm S ρ κ a a| = |a| := by
  unfold crossTerm
  by_cases hρ : ρ ∈ S
  · rw [if_pos hρ, if_neg (h.1 hρ), sub_zero]
  · rw [if_neg hρ, if_pos (by tauto), zero_sub, abs_neg]

/-- INTERNAL: subtracting a common term from both contributions. -/
theorem famQ_sub (K : ℕ) (ρ κ : ℕ → ℕ) (a b c : ℕ → ℚ) (u : ℕ) :
    famQ K ρ κ (fun k => a k - c k) (fun k => b k - c k) u = famQ K ρ κ a b u -
      ∑ k ∈ Finset.range K, ((if ρ k = u then 1 else 0) + (if κ k = u then 1 else 0)) * c k := by
  unfold famQ
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> ring

/-- INTERNAL: an entry of a list at an index below its length is a member. -/
theorem getD_mem_of_lt {α : Type*} {L : List α} {k : ℕ} (d : α) (hk : k < L.length) :
    L.getD k d ∈ L := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  exact List.getElem_mem hk

/-! ### The instance's cells -/

variable (I : Instance) (ε δ : ℚ)

/-- INTERNAL: the row endpoint of tree cell `t`. -/
noncomputable def ftR (t : ℕ) : ℕ := (treeAt I ε δ t).1

/-- INTERNAL: the column endpoint of tree cell `t`. -/
noncomputable def ftC (t : ℕ) : ℕ := I.m + (treeAt I ε δ t).2.1

theorem elimValid_ft :
    ElimValid (ftR I ε δ) (ftC I ε δ) (forest I ε δ).tree.length (elimOrder I ε δ) :=
  (pseudo_elimOrder_valid I ε δ).1

theorem treeValues_eq_tvFin_ft (x y : ℕ → ℕ) (z : ℕ → ℚ) :
    treeValues I ε δ x y z = tvFin (ftR I ε δ) (ftC I ε δ) (margin I) (baseLoad I ε δ x y z)
      (elimOrder I ε δ) := rfl

theorem smallAt_mem {k : ℕ} (hk : k < nSmall I ε δ) :
    smallAt I ε δ k ∈ retained I ∧ (smallAt I ε δ k).2.2 < WParam I ε δ := by
  have h := List.mem_filter.1 (getD_mem_of_lt (L := smallCells I ε δ) (0, 0, 0) hk)
  exact ⟨h.1, of_decide_eq_true h.2⟩

theorem large_mem {e : Entry} (he : e ∈ (forest I ε δ).tree ∨ e ∈ (forest I ε δ).free) :
    e ∈ retained I ∧ WParam I ε δ ≤ e.2.2 := by
  have h1 := (forest_perm I ε δ).mem_iff.1 (List.mem_append.2 he)
  have h2 := List.mem_filter.1 ((sortedLarge_perm I ε δ).mem_iff.1 h1)
  exact ⟨h2.1, not_lt.1 (of_decide_eq_true h2.2)⟩

theorem freeAt_mem {k : ℕ} (hk : k < nFree I ε δ) : freeAt I ε δ k ∈ (forest I ε δ).free :=
  getD_mem_of_lt (L := (forest I ε δ).free) (0, 0, 0) hk

theorem treeAt_mem {t : ℕ} (ht : t < (forest I ε δ).tree.length) :
    treeAt I ε δ t ∈ (forest I ε δ).tree :=
  getD_mem_of_lt (L := (forest I ε δ).tree) (0, 0, 0) ht

theorem retained_length_le : (retained I).length ≤ I.m * I.n := by
  unfold retained
  rw [List.length_flatMap]
  have h : ∀ i ∈ List.finRange I.m, ((List.finRange I.n).filterMap fun j =>
      if 0 < cellRange I i j then some ((i : ℕ), (j : ℕ), cellRange I i j) else none).length ≤ I.n :=
    fun i _ => (List.length_filterMap_le _ _).trans (by simp)
  have := List.sum_le_card_nsmul _ I.n (by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
    exact h i hi)
  simpa using this

/-- INTERNAL: there are at most `mn` small, free and tree cells together. -/
theorem cells_count_le :
    nSmall I ε δ + nFree I ε δ + (forest I ε δ).tree.length ≤ I.m * I.n := by
  have h1 := (List.filter_append_perm (fun e : Entry => decide (e.2.2 < WParam I ε δ))
    (retained I)).length_eq
  have h2 : (retained I).filter (fun e : Entry => !decide (e.2.2 < WParam I ε δ)) =
      largeCells I ε δ := by
    unfold largeCells
    exact List.filter_congr (fun e _ => by
      rcases Nat.lt_or_ge e.2.2 (WParam I ε δ) with h | h <;> simp [h, Nat.not_lt.2 h])
  rw [h2, List.length_append] at h1
  have h3 := ((forest_perm I ε δ).trans (sortedLarge_perm I ε δ)).length_eq
  rw [List.length_append] at h3
  have h4 := retained_length_le I
  unfold nSmall nFree
  unfold smallCells at *
  omega

theorem roots_length_le : (roots I ε δ).length ≤ I.m + I.n := by
  unfold roots
  exact (List.length_filter_le _ _).trans (by simp)

theorem ftR_lt {t : ℕ} (ht : t < (forest I ε δ).tree.length) : ftR I ε δ t < I.m :=
  (forest_mem_lt I ε δ (Or.inl (treeAt_mem I ε δ ht))).1

theorem ftC_lt {t : ℕ} (ht : t < (forest I ε δ).tree.length) : ftC I ε δ t < I.m + I.n := by
  have := (forest_mem_lt I ε δ (Or.inl (treeAt_mem I ε δ ht))).2
  unfold ftC; omega

/-! ### Deviations -/

/-- INTERNAL: incident sum minus margin at `u`, for the leaf-elimination tree values. -/
noncomputable def devQ (x y : ℕ → ℕ) (z : ℕ → ℚ) (u : ℕ) : ℚ :=
  tLoadG (ftR I ε δ) (ftC I ε δ) (forest I ε δ).tree.length (baseLoad I ε δ x y z)
    (treeValues I ε δ x y z).2 u - margin I u

/-- INTERNAL: the deviation of every vertex is the sum of the displacements from
`X*` of its incident cells.
TEXLINE: sections/scales.tex:113-126 -/
theorem dev_eq {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) (x y : ℕ → ℕ) (z : ℕ → ℚ) (u : ℕ) :
    devQ I ε δ x y z u =
      famQ (nSmall I ε δ) (fun k => (smallAt I ε δ k).1) (fun k => I.m + (smallAt I ε δ k).2.1)
          (fun k => (x k : ℚ) - xStar I X (smallAt I ε δ k).1 (smallAt I ε δ k).2.1)
          (fun k => (((smallAt I ε δ k).2.2 - y k : ℕ) : ℚ) -
            xStar I X (smallAt I ε δ k).1 (smallAt I ε δ k).2.1) u +
        famQ (nFree I ε δ) (fun k => (freeAt I ε δ k).1) (fun k => I.m + (freeAt I ε δ k).2.1)
          (fun k => z k - xStar I X (freeAt I ε δ k).1 (freeAt I ε δ k).2.1)
          (fun k => z k - xStar I X (freeAt I ε δ k).1 (freeAt I ε δ k).2.1) u +
        famQ (forest I ε δ).tree.length (ftR I ε δ) (ftC I ε δ)
          (fun t => (treeValues I ε δ x y z).2 t - xStar I X (treeAt I ε δ t).1 (treeAt I ε δ t).2.1)
          (fun t => (treeValues I ε δ x y z).2 t - xStar I X (treeAt I ε δ t).1 (treeAt I ε δ t).2.1)
          u := by
  rw [famQ_sub, famQ_sub, famQ_sub]
  unfold devQ tLoadG baseLoad famQ
  rw [margin_split I ε δ hX u]
  unfold incQ ftR ftC
  ring

theorem devQ_nonroot (x y : ℕ → ℕ) (z : ℕ → ℚ) {u : ℕ} (hu : u ∈ (elimOrder I ε δ).map Prod.fst) :
    devQ I ε δ x y z u = 0 := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hu
  unfold devQ
  rw [treeValues_eq_tvFin_ft, tvFin_nonroot (elimValid_ft I ε δ) _ p hp, sub_self]

theorem devQ_root (x y : ℕ → ℕ) (z : ℕ → ℚ) {r : ℕ} (hr : r ∈ roots I ε δ) :
    (treeValues I ε δ x y z).1 r - margin I r = devQ I ε δ x y z r := by
  unfold devQ
  rw [treeValues_eq_tvFin_ft, tvFin_root (elimValid_ft I ε δ) _ r
    ((pseudo_elimOrder_valid I ε δ).2 r hr)]

/-! ### The cut argument -/

/-- INTERNAL: the displacement of small cell `k` on its row side. -/
noncomputable def smA (X : Fin I.m → Fin I.n → ℕ) (x : ℕ → ℕ) (k : ℕ) : ℚ :=
  (x k : ℚ) - xStar I X (smallAt I ε δ k).1 (smallAt I ε δ k).2.1

/-- INTERNAL: the displacement of small cell `k` on its column side. -/
noncomputable def smB (X : Fin I.m → Fin I.n → ℕ) (y : ℕ → ℕ) (k : ℕ) : ℚ :=
  (((smallAt I ε δ k).2.2 - y k : ℕ) : ℚ) - xStar I X (smallAt I ε δ k).1 (smallAt I ε δ k).2.1

/-- INTERNAL: the displacement of free cell `k`. -/
noncomputable def frC (X : Fin I.m → Fin I.n → ℕ) (z : ℕ → ℚ) (k : ℕ) : ℚ :=
  z k - xStar I X (freeAt I ε δ k).1 (freeAt I ε δ k).2.1

/-- INTERNAL: the displacement of tree cell `t`. -/
noncomputable def trD (X : Fin I.m → Fin I.n → ℕ) (x y : ℕ → ℕ) (z : ℕ → ℚ) (t : ℕ) : ℚ :=
  (treeValues I ε δ x y z).2 t - xStar I X (treeAt I ε δ t).1 (treeAt I ε δ t).2.1

/-- INTERNAL: the signed sum of deviations over `S` is a sum over the cells
leaving `S`.
TEXLINE: sections/scales.tex:141-152 -/
theorem signed_dev {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) (x y : ℕ → ℕ) (z : ℕ → ℚ)
    (S : Finset ℕ) :
    ∑ u ∈ S, sgnQ I.m u * devQ I ε δ x y z u =
      ∑ k ∈ Finset.range (nSmall I ε δ), crossTerm S (smallAt I ε δ k).1
          (I.m + (smallAt I ε δ k).2.1) (smA I ε δ X x k) (smB I ε δ X y k) +
        ∑ k ∈ Finset.range (nFree I ε δ), crossTerm S (freeAt I ε δ k).1
          (I.m + (freeAt I ε δ k).2.1) (frC I ε δ X z k) (frC I ε δ X z k) +
        ∑ t ∈ Finset.range (forest I ε δ).tree.length, crossTerm S (ftR I ε δ t) (ftC I ε δ t)
          (trD I ε δ X x y z t) (trD I ε δ X x y z t) := by
  simp only [dev_eq I ε δ hX, mul_add, Finset.sum_add_distrib]
  rw [signed_famQ I.m _ _ _ _ _ (fun k hk => (mem_retained (smallAt_mem I ε δ hk).1).1)
      (fun k _ => Nat.le_add_right _ _),
    signed_famQ I.m _ _ _ _ _ (fun k hk => (forest_mem_lt I ε δ (Or.inr (freeAt_mem I ε δ hk))).1)
      (fun k _ => Nat.le_add_right _ _),
    signed_famQ I.m _ (ftR I ε δ) (ftC I ε δ) _ _ (fun t ht => ftR_lt I ε δ ht)
      (fun t _ => Nat.le_add_right I.m _)]
  rfl

theorem small_cross_bound {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) (x y : ℕ → ℕ)
    (hxy : ∀ k < nSmall I ε δ, x k ≤ (smallAt I ε δ k).2.2 ∧ y k ≤ (smallAt I ε δ k).2.2)
    (S : Finset ℕ) :
    |∑ k ∈ Finset.range (nSmall I ε δ), crossTerm S (smallAt I ε δ k).1
          (I.m + (smallAt I ε δ k).2.1) (smA I ε δ X x k) (smB I ε δ X y k)| ≤
      2 * ∑ k ∈ Finset.range (nSmall I ε δ), ((smallAt I ε δ k).2.2 : ℚ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => (abs_crossTerm_le _ _ _ _ _).trans ?_
  have hk' := Finset.mem_range.1 hk
  have hX' : (xStar I X (smallAt I ε δ k).1 (smallAt I ε δ k).2.1 : ℚ) ≤ (smallAt I ε δ k).2.2 := by
    exact_mod_cast xStar_le_of_retained hX (smallAt_mem I ε δ hk').1
  have hX0 : (0 : ℚ) ≤ xStar I X (smallAt I ε δ k).1 (smallAt I ε δ k).2.1 := by positivity
  have hx : (x k : ℚ) ≤ (smallAt I ε δ k).2.2 := by exact_mod_cast (hxy k hk').1
  have hy : (((smallAt I ε δ k).2.2 - y k : ℕ) : ℚ) ≤ (smallAt I ε δ k).2.2 := by
    exact_mod_cast Nat.sub_le _ _
  have hx0 : (0 : ℚ) ≤ x k := by positivity
  have hy0 : (0 : ℚ) ≤ (((smallAt I ε δ k).2.2 - y k : ℕ) : ℚ) := by positivity
  unfold smA smB
  have h1 : |(x k : ℚ) - xStar I X (smallAt I ε δ k).1 (smallAt I ε δ k).2.1| ≤
      (smallAt I ε δ k).2.2 := abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : |(((smallAt I ε δ k).2.2 - y k : ℕ) : ℚ) -
      xStar I X (smallAt I ε δ k).1 (smallAt I ε δ k).2.1| ≤ (smallAt I ε δ k).2.2 :=
    abs_le.2 ⟨by linarith, by linarith⟩
  linarith

/-- INTERNAL: an edge of the forest is `tree[t']` for its index. -/
theorem treeAt_getElem {t : ℕ} (ht : t < (forest I ε δ).tree.length) :
    treeAt I ε δ t = (forest I ε δ).tree[t] := by
  unfold treeAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  rfl

/-- INTERNAL: a free cell leaving a vertex set `S` is spanned by a tree path that
leaves `S` through a tree edge `t'` of bound at least `b_e`. -/
theorem free_cross_edge {k : ℕ} (hk : k < nFree I ε δ) (S : Finset ℕ)
    (hc : (freeAt I ε δ k).1 ∈ S ↔ ¬ I.m + (freeAt I ε δ k).2.1 ∈ S) :
    ∃ t' < (forest I ε δ).tree.length, (freeAt I ε δ k).2.2 ≤ (treeAt I ε δ t').2.2 ∧
      (ftR I ε δ t' ∈ S ↔ ¬ ftC I ε δ t' ∈ S) := by
  obtain ⟨f, hf, hfc⟩ := crossing_of_ereach I.m _ (· ∈ S)
    (free_reach_heavy I ε δ _ (freeAt_mem I ε δ hk)) hc
  obtain ⟨hf1, hf2⟩ := List.mem_filter.1 hf
  obtain ⟨t', ht', rfl⟩ := List.getElem_of_mem hf1
  refine ⟨t', ht', ?_, ?_⟩
  · rw [treeAt_getElem I ε δ ht']; exact of_decide_eq_true hf2
  · unfold ftR ftC; rw [treeAt_getElem I ε δ ht']; exact hfc

/-- INTERNAL: the free-cell part of a signed sum, over a set that no tree edge
leaves except possibly `t₀`, is bounded by `|F| (b_{t₀} + 1)`. -/
theorem free_cross_bound {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) (z : ℕ → ℚ)
    (hz : ∀ k < nFree I ε δ, 0 ≤ z k ∧ z k ≤ ((freeAt I ε δ k).2.2 : ℚ) + 1)
    (S : Finset ℕ) (B : ℚ)
    (hS : ∀ t' < (forest I ε δ).tree.length, (ftR I ε δ t' ∈ S ↔ ¬ ftC I ε δ t' ∈ S) →
      ((treeAt I ε δ t').2.2 : ℚ) ≤ B) (hB : 0 ≤ B) :
    |∑ k ∈ Finset.range (nFree I ε δ), crossTerm S (freeAt I ε δ k).1
          (I.m + (freeAt I ε δ k).2.1) (frC I ε δ X z k) (frC I ε δ X z k)| ≤
      nFree I ε δ * (B + 1) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ k ∈ Finset.range (nFree I ε δ), |crossTerm S (freeAt I ε δ k).1
      (I.m + (freeAt I ε δ k).2.1) (frC I ε δ X z k) (frC I ε δ X z k)| ≤ B + 1 := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    by_cases hc : (freeAt I ε δ k).1 ∈ S ↔ I.m + (freeAt I ε δ k).2.1 ∈ S
    · rw [crossTerm_eq_zero hc, abs_zero]; linarith
    · have hc' : (freeAt I ε δ k).1 ∈ S ↔ ¬ I.m + (freeAt I ε δ k).2.1 ∈ S := by tauto
      obtain ⟨t', ht', hb, hcut⟩ := free_cross_edge I ε δ hk' S hc'
      have hbB : ((freeAt I ε δ k).2.2 : ℚ) ≤ B := (Nat.cast_le.2 hb).trans (hS t' ht' hcut)
      rw [abs_crossTerm_cross hc']
      have hX' : (xStar I X (freeAt I ε δ k).1 (freeAt I ε δ k).2.1 : ℚ) ≤ (freeAt I ε δ k).2.2 := by
        exact_mod_cast xStar_le_of_retained hX
          (large_mem I ε δ (Or.inr (freeAt_mem I ε δ hk'))).1
      have hX0 : (0 : ℚ) ≤ xStar I X (freeAt I ε δ k).1 (freeAt I ε δ k).2.1 := by positivity
      obtain ⟨hz0, hz1⟩ := hz k hk'
      unfold frC
      exact abs_le.2 ⟨by linarith, by linarith⟩
  refine (Finset.sum_le_sum this).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Tree displacement.**  `|z_t - X*_t| ≤ 2 Σ_small b_s + |F| (b_t + 1)`.
PAPER: sections/scales.tex:141-145 (`eq:forest-displacement`, first bound, in the
cruder form `≤ 2 (|small| + |F|) b_t`). -/
theorem tree_disp_bound {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) (x y : ℕ → ℕ) (z : ℕ → ℚ)
    (hxy : ∀ k < nSmall I ε δ, x k ≤ (smallAt I ε δ k).2.2 ∧ y k ≤ (smallAt I ε δ k).2.2)
    (hz : ∀ k < nFree I ε δ, 0 ≤ z k ∧ z k ≤ ((freeAt I ε δ k).2.2 : ℚ) + 1)
    {t₀ : ℕ} (ht₀ : t₀ < (forest I ε δ).tree.length) :
    |trD I ε δ X x y z t₀| ≤ 2 * ∑ k ∈ Finset.range (nSmall I ε δ), ((smallAt I ε δ k).2.2 : ℚ) +
      nFree I ε δ * (((treeAt I ε δ t₀).2.2 : ℚ) + 1) := by
  classical
  have hv := elimValid_ft I ε δ
  obtain ⟨p, hp, hpt⟩ := List.mem_map.1 (hv.cover t₀ ht₀)
  set D := EDesc (ftR I ε δ) (ftC I ε δ) (elimOrder I ε δ) with hD
  set S := (Finset.range (I.m + I.n)).filter (fun u => D u p.1) with hSdef
  have hmemS : ∀ u, u < I.m + I.n → (u ∈ S ↔ D u p.1) := fun u hu => by
    simp [hSdef, Finset.mem_filter, Finset.mem_range, hu]
  have hRS : ∀ t < (forest I ε δ).tree.length, (ftR I ε δ t ∈ S ↔ D (ftR I ε δ t) p.1) :=
    fun t ht => hmemS _ (by have := ftR_lt I ε δ ht; omega)
  have hCS : ∀ t < (forest I ε δ).tree.length, (ftC I ε δ t ∈ S ↔ D (ftC I ε δ t) p.1) :=
    fun t ht => hmemS _ (ftC_lt I ε δ ht)
  -- every vertex of the subtree satisfies its margin equation
  have hΦ : ∑ u ∈ S, sgnQ I.m u * devQ I ε δ x y z u = 0 := by
    refine Finset.sum_eq_zero fun u hu => ?_
    have hd := (Finset.mem_filter.1 hu).2
    rcases desc_mem hv hd with rfl | hm
    · rw [devQ_nonroot I ε δ x y z (List.mem_map_of_mem hp), mul_zero]
    · rw [devQ_nonroot I ε δ x y z hm, mul_zero]
  rw [signed_dev I ε δ hX] at hΦ
  -- the only tree edge leaving the subtree is `t₀`
  have hother : ∀ t < (forest I ε δ).tree.length, t ≠ t₀ →
      (ftR I ε δ t ∈ S ↔ ftC I ε δ t ∈ S) := by
    intro t ht hne
    rw [hRS t ht, hCS t ht]
    exact desc_edge_iff hv ht (fun q hq hqt hqv => hne (by
      rw [← hqt, eq_of_fst_eq hv hq hp hqv, hpt]))
  have htree : ∑ t ∈ Finset.range (forest I ε δ).tree.length, crossTerm S (ftR I ε δ t)
      (ftC I ε δ t) (trD I ε δ X x y z t) (trD I ε δ X x y z t) =
      crossTerm S (ftR I ε δ t₀) (ftC I ε δ t₀) (trD I ε δ X x y z t₀) (trD I ε δ X x y z t₀) :=
    Finset.sum_eq_single t₀ (fun t ht hne => crossTerm_eq_zero
      (hother t (Finset.mem_range.1 ht) hne) _) (fun h => absurd (Finset.mem_range.2 ht₀) h)
  have hcross : ftR I ε δ t₀ ∈ S ↔ ¬ ftC I ε δ t₀ ∈ S := by
    have hin : D p.1 p.1 := Relation.ReflTransGen.refl
    have hout := not_desc_oth hv hp
    have hne := hv.ne t₀ ht₀
    rw [hRS t₀ ht₀, hCS t₀ ht₀]
    unfold oth at hout
    rw [hpt] at hout
    rcases hv.inc p hp with h | h <;> rw [hpt] at h
    · rw [if_pos h] at hout; rw [← h]; tauto
    · rw [if_neg (by rw [h]; exact Ne.symm hne)] at hout; rw [← h]; tauto
  rw [htree] at hΦ
  have heq : |trD I ε δ X x y z t₀| = |crossTerm S (ftR I ε δ t₀) (ftC I ε δ t₀)
      (trD I ε δ X x y z t₀) (trD I ε δ X x y z t₀)| := (abs_crossTerm_cross hcross _).symm
  rw [heq, show crossTerm S (ftR I ε δ t₀) (ftC I ε δ t₀) (trD I ε δ X x y z t₀)
      (trD I ε δ X x y z t₀) = -(∑ k ∈ Finset.range (nSmall I ε δ), crossTerm S (smallAt I ε δ k).1
          (I.m + (smallAt I ε δ k).2.1) (smA I ε δ X x k) (smB I ε δ X y k) +
        ∑ k ∈ Finset.range (nFree I ε δ), crossTerm S (freeAt I ε δ k).1
          (I.m + (freeAt I ε δ k).2.1) (frC I ε δ X z k) (frC I ε δ X z k)) by linarith, abs_neg]
  refine (abs_add_le _ _).trans (add_le_add (small_cross_bound I ε δ hX x y hxy S) ?_)
  refine free_cross_bound I ε δ hX z hz S _ (fun t' ht' hc => ?_) (by positivity)
  by_cases h : t' = t₀
  · rw [h]
  · exact absurd (hother t' ht' h) (by tauto)

/-- **Root deviation.**  `|δ_r| ≤ 2 Σ_small b_s` for every root `r`.
PAPER: sections/scales.tex:141-145 (`eq:forest-displacement`, second bound). -/
theorem root_dev_bound {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) (x y : ℕ → ℕ) (z : ℕ → ℚ)
    (hxy : ∀ k < nSmall I ε δ, x k ≤ (smallAt I ε δ k).2.2 ∧ y k ≤ (smallAt I ε δ k).2.2)
    (hz : ∀ k < nFree I ε δ, 0 ≤ z k ∧ z k ≤ ((freeAt I ε δ k).2.2 : ℚ) + 1)
    {r : ℕ} (hr : r ∈ roots I ε δ) :
    |devQ I ε δ x y z r| ≤ 2 * ∑ k ∈ Finset.range (nSmall I ε δ), ((smallAt I ε δ k).2.2 : ℚ) := by
  classical
  have hv := elimValid_ft I ε δ
  have hrl := (pseudo_elimOrder_valid I ε δ).2 r hr
  have hrV := ((mem_roots_iff I ε δ r).1 hr).1
  set D := EDesc (ftR I ε δ) (ftC I ε δ) (elimOrder I ε δ) with hD
  set S := (Finset.range (I.m + I.n)).filter (fun u => D u r) with hSdef
  have hmemS : ∀ u, u < I.m + I.n → (u ∈ S ↔ D u r) := fun u hu => by
    simp [hSdef, Finset.mem_filter, Finset.mem_range, hu]
  have hrS : r ∈ S := (hmemS r hrV).2 Relation.ReflTransGen.refl
  have hΦ : ∑ u ∈ S, sgnQ I.m u * devQ I ε δ x y z u = sgnQ I.m r * devQ I ε δ x y z r := by
    refine Finset.sum_eq_single r (fun u hu hne => ?_) (fun h => absurd hrS h)
    rcases desc_mem hv (Finset.mem_filter.1 hu).2 with h | h
    · exact absurd h hne
    · rw [devQ_nonroot I ε δ x y z h, mul_zero]
  have hall : ∀ t < (forest I ε δ).tree.length, (ftR I ε δ t ∈ S ↔ ftC I ε δ t ∈ S) := by
    intro t ht
    rw [hmemS _ (by have := ftR_lt I ε δ ht; omega), hmemS _ (ftC_lt I ε δ ht)]
    exact desc_edge_iff hv ht (fun q hq _ hqr => hrl (hqr ▸ List.mem_map_of_mem hq))
  rw [signed_dev I ε δ hX] at hΦ
  have htree : ∑ t ∈ Finset.range (forest I ε δ).tree.length, crossTerm S (ftR I ε δ t)
      (ftC I ε δ t) (trD I ε δ X x y z t) (trD I ε δ X x y z t) = 0 :=
    Finset.sum_eq_zero fun t ht => crossTerm_eq_zero (hall t (Finset.mem_range.1 ht)) _
  have hfree : ∑ k ∈ Finset.range (nFree I ε δ), crossTerm S (freeAt I ε δ k).1
      (I.m + (freeAt I ε δ k).2.1) (frC I ε δ X z k) (frC I ε δ X z k) = 0 := by
    refine Finset.sum_eq_zero fun k hk => crossTerm_eq_zero ?_ _
    by_contra hc
    obtain ⟨t', ht', -, hcut⟩ := free_cross_edge I ε δ (Finset.mem_range.1 hk) S (by tauto)
    exact absurd (hall t' ht') (by tauto)
  rw [htree, hfree, add_zero, add_zero] at hΦ
  have hsgn : |sgnQ I.m r| = 1 := by unfold sgnQ; split_ifs <;> simp
  have := small_cross_bound I ε δ hX x y hxy S
  rw [hΦ, abs_mul, hsgn, one_mul] at this
  exact this

/-! ### Assembly -/

/-- INTERNAL: the distance to `[0, b]` is at most the distance to any point of it. -/
theorem boxDist_le_abs {z X b : ℚ} (h0 : 0 ≤ X) (hb : X ≤ b) : boxDist z b ≤ |z - X| := by
  unfold boxDist
  split_ifs with h1 h2
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith
  · exact abs_nonneg _

theorem WParam_pos (hε : 0 < ε) : 1 ≤ WParam I ε δ := by
  have hA := AParam_pos I ε δ hε
  have hd := dParam_ge I
  unfold WParam BParam
  have : 0 < 100 * dParam I * (16 * AParam I ε δ * dParam I ^ 2) := by positivity
  omega

/-- **`D ≤ H` throughout the extended free box.**
PAPER: sections/scales.tex:131-158 (`lem:forest`, "Consequently, throughout the
extended free box, `0 ≤ D ≤ H`"). -/
theorem pseudo_penalty_le_H (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (hfeas : feasible I)
    (x y : ℕ → ℕ) (z : ℕ → ℚ)
    (hxy : ∀ k < nSmall I ε δ, x k ≤ (smallAt I ε δ k).2.2 ∧ y k ≤ (smallAt I ε δ k).2.2)
    (hz : ∀ k < nFree I ε δ, 0 ≤ z k ∧ z k ≤ ((freeAt I ε δ k).2.2 : ℚ) + 1) :
    penalty I ε δ x y z ≤ HParam I ε δ := by
  obtain ⟨X, hX⟩ := hfeas
  set W : ℚ := (WParam I ε δ : ℚ) with hWdef
  set P : ℚ := ∑ k ∈ Finset.range (nSmall I ε δ), ((smallAt I ε δ k).2.2 : ℚ) with hPdef
  set s : ℚ := (nSmall I ε δ : ℚ)
  set f : ℚ := (nFree I ε δ : ℚ)
  set N : ℚ := ((forest I ε δ).tree.length : ℚ)
  set d : ℚ := (dParam I : ℚ)
  have hW1 : (1 : ℚ) ≤ W := by rw [hWdef]; exact_mod_cast WParam_pos I ε δ hε
  have hP0 : 0 ≤ P := by positivity
  have hPW : P ≤ s * W := by
    have := Finset.sum_le_card_nsmul (Finset.range (nSmall I ε δ))
      (fun k => ((smallAt I ε δ k).2.2 : ℚ)) W (fun k hk =>
        le_of_lt (by rw [hWdef]; exact_mod_cast (smallAt_mem I ε δ (Finset.mem_range.1 hk)).2))
    simpa [nsmul_eq_mul] using this
  -- the root part
  have hroot : ((roots I ε δ).map fun v =>
      |(treeValues I ε δ x y z).1 v - margin I v|).sum ≤ (I.m + I.n : ℚ) * (2 * P) := by
    have h1 := List.sum_le_card_nsmul ((roots I ε δ).map fun v =>
      |(treeValues I ε δ x y z).1 v - margin I v|) (2 * P) (by
        intro a ha
        obtain ⟨v, hv, rfl⟩ := List.mem_map.1 ha
        rw [devQ_root I ε δ x y z hv]
        exact root_dev_bound I ε δ hX x y z hxy hz hv)
    rw [List.length_map, nsmul_eq_mul] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact_mod_cast roots_length_le I ε δ
  -- the tree part
  have htree : ∑ t ∈ Finset.range (forest I ε δ).tree.length,
      boxDist ((treeValues I ε δ x y z).2 t) ((treeAt I ε δ t).2.2 : ℚ) /
        ((treeAt I ε δ t).2.2 : ℚ) ≤ N * (2 * s + 2 * f) := by
    have := Finset.sum_le_card_nsmul (Finset.range (forest I ε δ).tree.length)
      (fun t => boxDist ((treeValues I ε δ x y z).2 t) ((treeAt I ε δ t).2.2 : ℚ) /
        ((treeAt I ε δ t).2.2 : ℚ)) (2 * s + 2 * f) (by
        intro t ht
        have ht' := Finset.mem_range.1 ht
        have hbW : W ≤ ((treeAt I ε δ t).2.2 : ℚ) := by
          rw [hWdef]; exact_mod_cast (large_mem I ε δ (Or.inl (treeAt_mem I ε δ ht'))).2
        have hb0 : (0 : ℚ) < (treeAt I ε δ t).2.2 := by linarith
        have hX' : (xStar I X (treeAt I ε δ t).1 (treeAt I ε δ t).2.1 : ℚ) ≤
            (treeAt I ε δ t).2.2 := by
          exact_mod_cast xStar_le_of_retained hX
            (large_mem I ε δ (Or.inl (treeAt_mem I ε δ ht'))).1
        have hbd := boxDist_le_abs (z := (treeValues I ε δ x y z).2 t)
          (by positivity : (0 : ℚ) ≤ xStar I X (treeAt I ε δ t).1 (treeAt I ε δ t).2.1) hX'
        have hdisp := tree_disp_bound I ε δ hX x y z hxy hz ht'
        unfold trD at hdisp
        have hs0 : (0 : ℚ) ≤ s := by positivity
        have hf0 : (0 : ℚ) ≤ f := by positivity
        rw [div_le_iff₀ hb0]
        have e1 : 2 * P ≤ 2 * s * ((treeAt I ε δ t).2.2 : ℚ) := by nlinarith
        have e2 : f * (((treeAt I ε δ t).2.2 : ℚ) + 1) ≤ 2 * f * ((treeAt I ε δ t).2.2 : ℚ) := by
          nlinarith
        nlinarith)
    simpa [nsmul_eq_mul, N, mul_add] using this
  -- sizes
  have hcount : s + f + N ≤ (I.m * I.n : ℚ) := by simp only [s, f, N]; exact_mod_cast cells_count_le I ε δ
  have hmn : (I.m * I.n : ℚ) ≤ d := by
    simp only [d]; unfold dParam; push_cast
    have := Nat.cast_nonneg (α := ℚ) I.m; have := Nat.cast_nonneg (α := ℚ) I.n; linarith
  have hmn' : (I.m + I.n : ℚ) ≤ d := by
    simp only [d]; unfold dParam; push_cast; nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℚ) I.m)
      (Nat.cast_nonneg (α := ℚ) I.n)]
  have hs0 : (0 : ℚ) ≤ s := by positivity
  have hf0 : (0 : ℚ) ≤ f := by positivity
  have hN0 : (0 : ℚ) ≤ N := by positivity
  have hmn0 : (0 : ℚ) ≤ I.m + I.n := by positivity
  have hA : (0 : ℚ) ≤ AParam I ε δ := by positivity
  have hsum : ((roots I ε δ).map fun v =>
        |(treeValues I ε δ x y z).1 v - margin I v|).sum +
      ∑ t ∈ Finset.range (forest I ε δ).tree.length,
        boxDist ((treeValues I ε δ x y z).2 t) ((treeAt I ε δ t).2.2 : ℚ) /
          ((treeAt I ε δ t).2.2 : ℚ) ≤ 10 * d ^ 2 * (W + 1) := by
    have hsd : s ≤ d := by linarith
    have hNd : N ≤ d := by linarith
    have hsfd : s + f ≤ d := by linarith
    have e1 : (I.m + I.n : ℚ) * (2 * P) ≤ 2 * d ^ 2 * W := by
      calc (I.m + I.n : ℚ) * (2 * P) ≤ d * (2 * (s * W)) :=
            mul_le_mul hmn' (by linarith) (by positivity) (by linarith)
        _ ≤ d * (2 * (d * W)) := by
            apply mul_le_mul_of_nonneg_left _ (by linarith); nlinarith
        _ = 2 * d ^ 2 * W := by ring
    have e2 : N * (2 * s + 2 * f) ≤ 2 * d ^ 2 := by
      calc N * (2 * s + 2 * f) ≤ d * (2 * d) :=
            mul_le_mul hNd (by linarith) (by positivity) (by linarith)
        _ = 2 * d ^ 2 := by ring
    have hd0 : 0 ≤ d ^ 2 := by positivity
    nlinarith
  unfold penalty
  have hH : (HParam I ε δ : ℚ) = (AParam I ε δ : ℚ) * (10 * d ^ 2 * (W + 1)) := by
    simp only [d, W]; unfold HParam; push_cast; ring
  rw [hH]
  exact mul_le_mul_of_nonneg_left hsum hA

end Cellcounting.Analysis
