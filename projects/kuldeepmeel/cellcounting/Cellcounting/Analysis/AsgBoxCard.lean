import Cellcounting.Analysis.ContaminationBoxes
import Cellcounting.Analysis.CostScale
import Cellcounting.Analysis.ElimOrder

/-!
# The number of assignments is at most `2^K`

`eq:capacity-product` (`scales.tex:72-80`) as used in the proof of
`prop:contamination` (`integer-signatures.tex:490-493`):
`∏_{s small} (b_s + 1) ∏_{e free} (b_e + 1) ≤ 2^L ≤ 2^K`.  Tightened bounds never
exceed the input bounds, and a number with `ℓ` binary digits has at most `2^ℓ`
values between zero and itself.

The small/free bound lists are disjoint sub-selections of `retained I`, itself a
row-major listing of the cells with positive tightened range: `smallCells` and
`largeCells` partition `retained` by the `< W` test, and the forest's free edges
are a sub-multiset of `sortedLarge`, a permutation of `largeCells` (Kruskal's
invariant `KInv.perm`, `ElimOrder.lean`).  Summing `bitLen` of the tightened
bound over that selection is therefore at most summing it over every original
cell, which `inputLength` already dominates; `KParam` is linear in
`inputLength` with room to spare.

## Run record
Newest first. History, not instruction — what this file claims is above.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: every cell of `retained I` comes from a position inside the table.
TEXLINE: sections/scales.tex:24-44 -/
theorem mem_retained {I : Instance} {e : Entry} (he : e ∈ retained I) :
    e.1 < I.m ∧ e.2.1 < I.n := by
  unfold retained at he
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_finRange] at he
  obtain ⟨i, -, j, hj⟩ := he
  obtain ⟨-, hj⟩ := hj
  split_ifs at hj with hcond
  · cases hj
    exact ⟨i.2, j.2⟩

/-- INTERNAL: the tightened range never exceeds the input bound.
TEXLINE: sections/scales.tex:24-30 -/
theorem cellRange_le (I : Instance) (i : Fin I.m) (j : Fin I.n) :
    cellRange I i j ≤ I.b i j := by
  unfold cellRange cellHigh cellLow
  by_cases h : I.Omega.Nonempty
  · simp only [h, dif_pos]
    have hmem : (I.Omega.image fun X => X i j).max' (h.image _) ∈ I.Omega.image fun X => X i j :=
      Finset.max'_mem _ _
    obtain ⟨X, hX, hXeq⟩ := Finset.mem_image.1 hmem
    have hXle : X i j ≤ I.b i j := by
      unfold Instance.Omega at hX
      have := (Finset.mem_filter.1 hX).1
      have := Fintype.mem_piFinset.1 this i
      exact Finset.mem_range_succ_iff.1 (Fintype.mem_piFinset.1 this j)
    omega
  · simp [h]

/-- INTERNAL: folding `List.orderedInsert` over a list from `[]` only
rearranges it. -/
theorem foldl_orderedInsert_perm (r : Entry → Entry → Prop) [DecidableRel r] (l : List Entry) :
    ∀ (acc : List Entry), (l.foldl (fun acc x => acc.orderedInsert r x) acc).Perm (acc ++ l) := by
  induction l with
  | nil => intro acc; simp
  | cons x xs ih =>
    intro acc
    simp only [List.foldl_cons]
    have h1 := ih (acc.orderedInsert r x)
    have h2 : (acc.orderedInsert r x).Perm (x :: acc) := List.perm_orderedInsert r x acc
    have h3 : (x :: acc ++ xs).Perm (acc ++ x :: xs) := by
      simpa using List.perm_middle (a := x) (l₁ := acc) (l₂ := xs) |>.symm
    have h4 := (h2.append_right xs).trans (by simpa using h3)
    exact h1.trans h4

/-- INTERNAL: `sortedLarge` is an insertion sort of `largeCells`, hence a
permutation of it. -/
theorem sortedLarge_perm (I : Instance) (ε δ : ℚ) :
    (sortedLarge I ε δ).Perm (largeCells I ε δ) := by
  unfold sortedLarge
  simpa using foldl_orderedInsert_perm (fun a b : Entry => b.2.2 < a.2.2) (largeCells I ε δ) []

/-- INTERNAL: `largeCells` is a filter of `retained`. -/
theorem mem_largeCells {I : Instance} {ε δ : ℚ} {e : Entry} (he : e ∈ largeCells I ε δ) :
    e ∈ retained I := by
  unfold largeCells at he
  exact List.mem_of_mem_filter he

/-- INTERNAL: entries of `sortedLarge` are positions inside the table. -/
theorem mem_sortedLarge {I : Instance} {ε δ : ℚ} {e : Entry} (he : e ∈ sortedLarge I ε δ) :
    e.1 < I.m ∧ e.2.1 < I.n :=
  mem_retained (mem_largeCells ((sortedLarge_perm I ε δ).mem_iff.1 he))

/-- INTERNAL: the forest's tree and free edges together are a permutation of
`sortedLarge`, by Kruskal's fold invariant `KInv.perm`.
TEXLINE: sections/scales.tex:88-99 -/
theorem forest_perm (I : Instance) (ε δ : ℚ) :
    ((forest I ε δ).tree ++ (forest I ε δ).free).Perm (sortedLarge I ε δ) := by
  unfold forest
  exact (kruskal_inv I.m (I.m + I.n) (sortedLarge I ε δ)
    (fun e he => by
      have := mem_sortedLarge he
      omega)).perm

/-- INTERNAL: a sum over `0, …, l.length - 1` of a function read off `l` by
position is the sum over `l` itself. -/
theorem sum_range_getD_eq {α : Type*} (l : List α) (g : α → ℕ) (d : α) :
    ∑ i ∈ Finset.range l.length, g (l.getD i d) = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih, List.map_cons, List.sum_cons, add_comm]

/-- INTERNAL: a list sum splits over a boolean predicate and its negation. -/
theorem sum_filter_add_sum_filter_not {α : Type*} (l : List α) (p q : α → Bool)
    (hpq : ∀ a, q a = !p a) (g : α → ℕ) :
    ((l.filter p).map g).sum + ((l.filter q).map g).sum = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.filter_cons, List.filter_cons, hpq a]
    cases h : p a <;> simp_all [List.sum_cons] <;> omega

/-- INTERNAL: dropping the elements `filterMap` discards only decreases a
nonnegative sum, compared to the full map. -/
theorem sum_filterMap_le {B C : Type*} (lb : List B) (p : B → Prop) [DecidablePred p]
    (mapf : B → C) (g : C → ℕ) (h : B → ℕ) (hle : ∀ b, g (mapf b) ≤ h b) :
    ((lb.filterMap (fun b => if p b then some (mapf b) else none)).map g).sum ≤ (lb.map h).sum := by
  induction lb with
  | nil => simp
  | cons b l ih =>
    by_cases hp : p b
    · simp only [List.filterMap_cons, hp, if_true, List.map_cons, List.sum_cons]
      have := hle b
      omega
    · simp only [List.filterMap_cons, hp, if_false]
      have := ih
      simp only [List.map_cons, List.sum_cons]
      omega

/-- INTERNAL: a sum over a `flatMap` is bounded by summing per-outer-element
bounds on the inner sums. -/
theorem sum_flatMap_le {A B : Type*} (la : List A) (f : A → List B) (g : B → ℕ) (h : A → ℕ)
    (hb : ∀ a, ((f a).map g).sum ≤ h a) :
    ((la.flatMap f).map g).sum ≤ (la.map h).sum := by
  induction la with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    have := hb a
    omega

/-- **Capacity product** (`eq:capacity-product`): `|asgBox| ≤ 2^K`.
PAPER: sections/scales.tex:72-80 -/
theorem asgBox_card_le (I : Instance) (ε δ : ℚ) :
    (asgBox I ε δ).card ≤ 2 ^ KParam I ε δ := by
  have hcard : (asgBox I ε δ).card = (smallBox I ε δ).card * (freeBox I ε δ).card := by
    unfold asgBox; exact Finset.card_product _ _
  have hsmall : (smallBox I ε δ).card = ∏ k ∈ Finset.range (nSmall I ε δ), (smallB I ε δ k + 1) := by
    unfold smallBox
    rw [Fintype.card_piFinset]
    simp only [Finset.card_range]
    exact Fin.prod_univ_eq_prod_range (fun k => smallB I ε δ k + 1) (nSmall I ε δ)
  have hfree : (freeBox I ε δ).card
      = ∏ k ∈ Finset.range (nFree I ε δ), ((freeAt I ε δ k).2.2 + 1) := by
    unfold freeBox
    rw [Fintype.card_piFinset]
    simp only [Finset.card_range]
    exact Fin.prod_univ_eq_prod_range (fun k => (freeAt I ε δ k).2.2 + 1) (nFree I ε δ)
  have hsum_small : ∑ k ∈ Finset.range (nSmall I ε δ), bitLen (smallB I ε δ k)
      = ((smallCells I ε δ).map (fun e => bitLen e.2.2)).sum := by
    unfold nSmall smallB smallAt
    exact sum_range_getD_eq (smallCells I ε δ) (fun e => bitLen e.2.2) (0, 0, 0)
  have hsum_free : ∑ k ∈ Finset.range (nFree I ε δ), bitLen ((freeAt I ε δ k).2.2)
      = ((forest I ε δ).free.map (fun e => bitLen e.2.2)).sum := by
    unfold nFree freeAt
    exact sum_range_getD_eq (forest I ε δ).free (fun e => bitLen e.2.2) (0, 0, 0)
  have hfree_le_large : (((forest I ε δ).free.map (fun e => bitLen e.2.2))).sum
      ≤ ((largeCells I ε δ).map (fun e => bitLen e.2.2)).sum := by
    have hperm := forest_perm I ε δ
    have hpermL := sortedLarge_perm I ε δ
    have h1 : (((forest I ε δ).tree ++ (forest I ε δ).free).map (fun e => bitLen e.2.2)).sum
        = ((sortedLarge I ε δ).map (fun e => bitLen e.2.2)).sum :=
      (hperm.map (fun e => bitLen e.2.2)).sum_eq
    have h2 : ((sortedLarge I ε δ).map (fun e => bitLen e.2.2)).sum
        = ((largeCells I ε δ).map (fun e => bitLen e.2.2)).sum :=
      (hpermL.map (fun e => bitLen e.2.2)).sum_eq
    simp only [List.map_append, List.sum_append] at h1
    omega
  have hpartition : ((smallCells I ε δ).map (fun e => bitLen e.2.2)).sum
        + ((largeCells I ε δ).map (fun e => bitLen e.2.2)).sum
      = ((retained I).map (fun e => bitLen e.2.2)).sum := by
    unfold smallCells largeCells
    apply sum_filter_add_sum_filter_not
    intro a
    by_cases h : a.2.2 < WParam I ε δ <;> simp [h]
  have hretained_le : ((retained I).map (fun e => bitLen e.2.2)).sum
      ≤ ∑ i : Fin I.m, ∑ j : Fin I.n, bitLen (I.b i j) := by
    unfold retained
    have key : ((List.finRange I.m).flatMap
        (fun i => (List.finRange I.n).filterMap fun j =>
          if 0 < cellRange I i j then some (i.val, j.val, cellRange I i j) else none)
        |>.map (fun e => bitLen e.2.2)).sum
        ≤ ((List.finRange I.m).map (fun i => ∑ j : Fin I.n, bitLen (I.b i j))).sum := by
      apply sum_flatMap_le
      intro i
      have hfm := sum_filterMap_le (List.finRange I.n)
        (fun j : Fin I.n => 0 < cellRange I i j)
        (fun j : Fin I.n => ((i : ℕ), (j : ℕ), cellRange I i j))
        (fun e : Entry => bitLen e.2.2)
        (fun j : Fin I.n => bitLen (I.b i j))
        (fun j => bitLen_mono (cellRange_le I i j))
      rw [Fin.sum_univ_def]
      simpa using hfm
    rw [show (∑ i : Fin I.m, ∑ j : Fin I.n, bitLen (I.b i j))
        = ((List.finRange I.m).map (fun i => ∑ j : Fin I.n, bitLen (I.b i j))).sum from
      Fin.sum_univ_def _]
    simpa using key
  have hcellsum_le : ∑ i : Fin I.m, ∑ j : Fin I.n, bitLen (I.b i j) ≤ inputLength I ε δ := by
    unfold inputLength
    omega
  have hsum_le : ∑ k ∈ Finset.range (nSmall I ε δ), bitLen (smallB I ε δ k)
      + ∑ k ∈ Finset.range (nFree I ε δ), bitLen ((freeAt I ε δ k).2.2)
      ≤ KParam I ε δ := by
    rw [hsum_small, hsum_free]
    have : KParam I ε δ ≥ inputLength I ε δ := by unfold KParam; omega
    omega
  have hpow_small : ∏ k ∈ Finset.range (nSmall I ε δ), (smallB I ε δ k + 1)
      ≤ 2 ^ (∑ k ∈ Finset.range (nSmall I ε δ), bitLen (smallB I ε δ k)) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod (fun i _ => lt_two_pow_bitLen (smallB I ε δ i))
  have hpow_free : ∏ k ∈ Finset.range (nFree I ε δ), ((freeAt I ε δ k).2.2 + 1)
      ≤ 2 ^ (∑ k ∈ Finset.range (nFree I ε δ), bitLen ((freeAt I ε δ k).2.2)) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod (fun i _ => lt_two_pow_bitLen ((freeAt I ε δ i).2.2))
  rw [hcard, hsmall, hfree]
  calc (∏ k ∈ Finset.range (nSmall I ε δ), (smallB I ε δ k + 1))
        * ∏ k ∈ Finset.range (nFree I ε δ), ((freeAt I ε δ k).2.2 + 1)
      ≤ 2 ^ (∑ k ∈ Finset.range (nSmall I ε δ), bitLen (smallB I ε δ k))
        * 2 ^ (∑ k ∈ Finset.range (nFree I ε δ), bitLen ((freeAt I ε δ k).2.2)) :=
        Nat.mul_le_mul hpow_small hpow_free
    _ = 2 ^ (∑ k ∈ Finset.range (nSmall I ε δ), bitLen (smallB I ε δ k)
        + ∑ k ∈ Finset.range (nFree I ε δ), bitLen ((freeAt I ε δ k).2.2)) := (pow_add 2 _ _).symm
    _ ≤ 2 ^ KParam I ε δ := Nat.pow_le_pow_right (by norm_num) hsum_le

end Cellcounting.Analysis
