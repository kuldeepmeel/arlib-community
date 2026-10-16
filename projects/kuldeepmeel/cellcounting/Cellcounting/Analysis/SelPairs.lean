import Cellcounting.Analysis.ChoiceSum
import Cellcounting.Analysis.TransportDirichlet
import Cellcounting.Analysis.W0Good

/-!
# Choice sets of pairs and the classes of the paired state space

The paired ground set has the elements `2t` (row) and `2t + 1` (column) of pair `t`.
`selPairs T A` is the choice set of the pairs of `T` taking `2t` for `t ∈ A` and
`2t + 1` for `t ∈ T \ A`.  Sums over choice sets:

* `chSum_eq_sum_selPairs`: `chSum L φ = Σ_{A ⊆ L} φ(selPairs L A)` (`L` without
  repetition), so the `chSum` vocabulary of `ChoiceSum.lean` and `Finset` sums agree;
* `dm_sum_trans`: a sum over the transversals `A` is `Σ_{T ⊆ [0, p)} φ(selPairs [0, p) T)`;
* `dm_sum_four`: the transversals split by the joint choice in two pairs `i ≠ l`;
* `dm_sum_defect`: a sum over the defect class `A_il` is a sum over `A ⊆ [0, p) \ {i, l}`
  of `φ({a_l, b_l'} ∪ selPairs R A)`;
* `trMass_root_eq`, `defMass_root_eq`: at the empty assignment, `trMass φ ∅ [0, p)` and
  `defMass φ ∅ [0, p) i l` are the `φ`-masses of `A` and of `A_il`;
* `dm_kind_hole0`, `dm_kind_hole1`, `dm_kind_holet`, `dm_kind_double`: the types of the
  one-hole states of `lem:defect-mean` (fixed `a_l`, singleton slots `a_i`, `b_l'`):
  a hole at `a_i` is in `A_il`, at `b_l'` a transversal, at an ordinary pair `t` in
  `A_tl`, and a doubled pair `t` with both singletons empty is in `A_it`.
-/

namespace Cellcounting.Analysis

open Pseudocode Finset

/-- INTERNAL: the choice from the pairs of `T` taking the row element `2t` for
`t ∈ A` and the column element `2t + 1` for `t ∈ T \ A`.
TEXLINE: sections/transport.tex:100-120 -/
def selPairs (T A : Finset ℕ) : Finset ℕ :=
  A.image (fun t => 2 * t) ∪ (T \ A).image (fun t => 2 * t + 1)

/-- INTERNAL: the row element `2k` is chosen iff `k ∈ A`. -/
theorem two_mul_mem_selPairs (T A : Finset ℕ) (k : ℕ) : 2 * k ∈ selPairs T A ↔ k ∈ A := by
  simp only [selPairs, mem_union, mem_image, mem_sdiff]
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨a, -, h⟩)
    · obtain rfl : a = k := by omega
      exact ha
    · omega
  · intro h; exact Or.inl ⟨k, h, rfl⟩

/-- INTERNAL: the column element `2k + 1` is chosen iff `k ∈ T \ A`. -/
theorem two_mul_add_one_mem_selPairs (T A : Finset ℕ) (k : ℕ) :
    2 * k + 1 ∈ selPairs T A ↔ k ∈ T ∧ k ∉ A := by
  simp only [selPairs, mem_union, mem_image, mem_sdiff]
  constructor
  · rintro (⟨a, -, h⟩ | ⟨a, ha, h⟩)
    · omega
    · obtain rfl : a = k := by omega
      exact ha
  · intro h; exact Or.inr ⟨k, h, rfl⟩

/-- INTERNAL: every chosen element lies in a pair of `T` (for `A ⊆ T`). -/
theorem div_two_mem_of_mem_selPairs {T A : Finset ℕ} (hA : A ⊆ T) {x : ℕ}
    (hx : x ∈ selPairs T A) : x / 2 ∈ T := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' x
  · rw [two_mul_mem_selPairs] at hx
    rw [show 2 * k / 2 = k by omega]; exact hA hx
  · rw [two_mul_add_one_mem_selPairs] at hx
    rw [show (2 * k + 1) / 2 = k by omega]; exact hx.1

/-- INTERNAL: splitting off a pair `t ∉ T` choosing its column element. -/
theorem selPairs_insert_of_not_mem {T A : Finset ℕ} {t : ℕ} (ht : t ∉ T) (hA : A ⊆ T) :
    selPairs (insert t T) A = insert (2 * t + 1) (selPairs T A) := by
  have htA : t ∉ A := fun h => ht (hA h)
  ext x
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' x
  · rw [two_mul_mem_selPairs, mem_insert, two_mul_mem_selPairs]
    constructor
    · exact Or.inr
    · rintro (h | h)
      · omega
      · exact h
  · rw [two_mul_add_one_mem_selPairs, mem_insert, mem_insert, two_mul_add_one_mem_selPairs]
    constructor
    · rintro ⟨rfl | h, h'⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨h, h'⟩
    · rintro (h | ⟨h, h'⟩)
      · obtain rfl : k = t := by omega
        exact ⟨Or.inl rfl, htA⟩
      · exact ⟨Or.inr h, h'⟩

/-- INTERNAL: splitting off a pair `t ∉ T` choosing its row element. -/
theorem selPairs_insert_insert {T A : Finset ℕ} {t : ℕ} (ht : t ∉ T) :
    selPairs (insert t T) (insert t A) = insert (2 * t) (selPairs T A) := by
  ext x
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' x
  · rw [two_mul_mem_selPairs, mem_insert, mem_insert, two_mul_mem_selPairs]
    constructor
    · rintro (rfl | h)
      · exact Or.inl rfl
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (by omega)
      · exact Or.inr h
  · rw [two_mul_add_one_mem_selPairs, mem_insert, mem_insert, mem_insert,
      two_mul_add_one_mem_selPairs]
    constructor
    · rintro ⟨rfl | h, h'⟩
      · exact absurd (Or.inl rfl) h'
      · exact Or.inr ⟨h, fun h'' => h' (Or.inr h'')⟩
    · rintro (h | ⟨h, h'⟩)
      · omega
      · refine ⟨Or.inr h, ?_⟩
        rintro (rfl | h'')
        · exact ht h
        · exact h' h''

/-- INTERNAL: a sum over the choices from the pairs of `insert t T` splits by the
choice in the pair `t`. -/
theorem sum_powerset_insert_selPairs {T : Finset ℕ} {t : ℕ} (ht : t ∉ T)
    (φ : Finset ℕ → ℝ) :
    ∑ A ∈ (insert t T).powerset, φ (selPairs (insert t T) A) =
      ∑ A ∈ T.powerset, φ (insert (2 * t) (selPairs T A)) +
        ∑ A ∈ T.powerset, φ (insert (2 * t + 1) (selPairs T A)) := by
  rw [Finset.sum_powerset_insert ht, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun A _ => ?_
    rw [selPairs_insert_insert ht]
  · refine Finset.sum_congr rfl fun A hA => ?_
    rw [selPairs_insert_of_not_mem ht (mem_powerset.1 hA)]

/-- INTERNAL: `insert a {b} ∪ U = insert a (insert b U)`. -/
theorem dm_insert_pair_union (a b : ℕ) (U : Finset ℕ) :
    insert a ({b} : Finset ℕ) ∪ U = insert a (insert b U) := by
  rw [Finset.insert_union, Finset.insert_eq b U]

/-- INTERNAL: the transversals split by the joint choice in two distinct pairs
`i, l`, the remaining pairs `R = [0, p) \ {i, l}` being chosen by `selPairs R`.
TEXLINE: sections/transport.tex:456-458 -/
theorem dm_sum_four (p i l : ℕ) (hi : i < p) (hl : l < p) (hil : i ≠ l)
    (φ : Finset ℕ → ℝ) :
    ∑ T ∈ (range p).powerset, φ (selPairs (range p) T) =
      ∑ A ∈ (((range p).erase i).erase l).powerset,
        φ (insert (2 * i) {2 * l} ∪ selPairs (((range p).erase i).erase l) A) +
      ∑ A ∈ (((range p).erase i).erase l).powerset,
        φ (insert (2 * i) {2 * l + 1} ∪ selPairs (((range p).erase i).erase l) A) +
      ∑ A ∈ (((range p).erase i).erase l).powerset,
        φ (insert (2 * i + 1) {2 * l} ∪ selPairs (((range p).erase i).erase l) A) +
      ∑ A ∈ (((range p).erase i).erase l).powerset,
        φ (insert (2 * i + 1) {2 * l + 1} ∪ selPairs (((range p).erase i).erase l) A) := by
  set R := ((range p).erase i).erase l with hRdef
  have hlR : l ∉ R := by simp [hRdef]
  have hiR : i ∉ insert l R := by simp [hRdef, hil]
  have hR : range p = insert i (insert l R) := by
    rw [hRdef, Finset.insert_erase (by simp [hl, hil.symm]), Finset.insert_erase (by simp [hi])]
  simp only [dm_insert_pair_union]
  rw [hR, sum_powerset_insert_selPairs hiR, sum_powerset_insert_selPairs hlR (fun U => φ (insert (2 * i) U)),
    sum_powerset_insert_selPairs hlR (fun U => φ (insert (2 * i + 1) U))]
  ring

/-- INTERNAL: a sum over the transversals `A` is a sum over the choices of all pairs.
TEXLINE: sections/signatures.tex:13-41 -/
theorem dm_sum_trans (I : Instance) (ε δ : ℚ) (φ : Finset ℕ → ℝ) :
    ∑ S ∈ transStates I ε δ, φ S =
      ∑ T ∈ (range (pSmall I ε δ)).powerset, φ (selPairs (range (pSmall I ε δ)) T) := by
  classical
  have h : transStates I ε δ = (range (2 * pSmall I ε δ)).powerset.filter
      (fun S => ∀ i < pSmall I ε δ, (2 * i ∈ S ↔ 2 * i + 1 ∉ S)) := by
    unfold transStates refStates
    ext S
    simp only [mem_filter, kind_eq_transversal_iff]
  rw [h, sum_trans_eq_sum_powerset]
  rfl

/-- INTERNAL: the defect class `A_il` as `{a_l, b_l'} ∪ selPairs R A`, `A ⊆ R`.
TEXLINE: sections/signatures.tex:13-41 -/
theorem dm_w0DefEmb_eq (R A : Finset ℕ) (l al bl : ℕ)
    (hal : (al = 2 * l ∧ bl = 2 * l + 1) ∨ (al = 2 * l + 1 ∧ bl = 2 * l)) :
    w0DefEmb R l A = insert bl {al} ∪ selPairs R A := by
  ext x
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' x
  · rw [w0_two_mul_mem, mem_union, mem_insert, mem_singleton, two_mul_mem_selPairs]
    rcases hal with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · constructor
      · rintro (h | h)
        · exact Or.inl (Or.inr (by omega))
        · exact Or.inr h
      · rintro ((h | h) | h)
        · omega
        · exact Or.inl (by omega)
        · exact Or.inr h
    · constructor
      · rintro (h | h)
        · exact Or.inl (Or.inl (by omega))
        · exact Or.inr h
      · rintro ((h | h) | h)
        · exact Or.inl (by omega)
        · omega
        · exact Or.inr h
  · rw [w0_two_mul_add_one_mem, mem_union, mem_insert, mem_singleton,
      two_mul_add_one_mem_selPairs, mem_sdiff]
    rcases hal with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · constructor
      · rintro (h | h)
        · exact Or.inl (Or.inl (by omega))
        · exact Or.inr h
      · rintro ((h | h) | h)
        · exact Or.inl (by omega)
        · omega
        · exact Or.inr h
    · constructor
      · rintro (h | h)
        · exact Or.inl (Or.inr (by omega))
        · exact Or.inr h
      · rintro ((h | h) | h)
        · omega
        · exact Or.inl (by omega)
        · exact Or.inr h

open Classical in
/-- INTERNAL: a sum over the defect class `A_il` is a sum over `A ⊆ R`.
TEXLINE: sections/signatures.tex:13-41 -/
theorem dm_sum_defect (I : Instance) (ε δ : ℚ) (i l : ℕ) (hi : i < pSmall I ε δ)
    (hl : l < pSmall I ε δ) (hil : i ≠ l) (al bl : ℕ)
    (hal : (al = 2 * l ∧ bl = 2 * l + 1) ∨ (al = 2 * l + 1 ∧ bl = 2 * l))
    (φ : Finset ℕ → ℝ) :
    ∑ S ∈ (refStates I ε δ).filter (fun S => kind I ε δ S = .defect i l), φ S =
      ∑ A ∈ (((range (pSmall I ε δ)).erase i).erase l).powerset,
        φ (insert bl {al} ∪ selPairs (((range (pSmall I ε δ)).erase i).erase l) A) := by
  rw [w0_sum_defect I ε δ i l hi hl hil φ]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [dm_w0DefEmb_eq _ _ l al bl hal]


/-- INTERNAL: `chSum` over a list of pairs without repetition is a `Finset` sum over the
choice sets `selPairs`.
TEXLINE: sections/signatures.tex:96-104 -/
theorem chSum_eq_sum_selPairs {L : List ℕ} (hL : L.Nodup) (φ : Finset ℕ → ℝ) :
    chSum L φ = ∑ A ∈ L.toFinset.powerset, φ (selPairs L.toFinset A) := by
  induction L generalizing φ with
  | nil => simp [chSum_nil, selPairs]
  | cons t L ih =>
    obtain ⟨ht, hL'⟩ := List.nodup_cons.1 hL
    rw [chSum_cons, List.toFinset_cons,
      sum_powerset_insert_selPairs (by simpa using ht), ih hL', ih hL']

/-- INTERNAL: `[0, p) \ {i, l}` as the list `(range p).erase i |>.erase l`. -/
theorem dm_toFinset_erase_erase (p i l : ℕ) :
    (((List.range p).erase i).erase l).toFinset = ((range p).erase i).erase l := by
  ext k
  rw [List.mem_toFinset, ((List.nodup_range).erase i).mem_erase_iff,
    (List.nodup_range).mem_erase_iff, List.mem_range]
  simp

/-- INTERNAL: at the empty assignment, `z_∅` is the `φ`-mass of the transversals.
TEXLINE: sections/signatures.tex:303-318 -/
theorem trMass_root_eq (I : Instance) (ε δ : ℚ) (φ : Finset ℕ → ℝ) :
    trMass φ ∅ (List.range (pSmall I ε δ)) = ∑ S ∈ transStates I ε δ, φ S := by
  rw [dm_sum_trans, trMass, chSum_eq_sum_selPairs List.nodup_range, List.toFinset_range]
  simp

open Classical in
/-- INTERNAL: at the empty assignment, `c^∅_il` is the `φ`-mass of the defect class `A_il`.
TEXLINE: sections/signatures.tex:303-318 -/
theorem defMass_root_eq (I : Instance) (ε δ : ℚ) (φ : Finset ℕ → ℝ) (i l : ℕ)
    (hi : i < pSmall I ε δ) (hl : l < pSmall I ε δ) (hil : i ≠ l) :
    defMass φ ∅ (List.range (pSmall I ε δ)) i l =
      ∑ S ∈ (refStates I ε δ).filter (fun S => kind I ε δ S = .defect i l), φ S := by
  classical
  rw [dm_sum_defect I ε δ i l hi hl hil (2 * l + 1) (2 * l) (Or.inr ⟨rfl, rfl⟩), defMass,
    chSum_eq_sum_selPairs ((List.nodup_range.erase i).erase l), dm_toFinset_erase_erase]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [dm_insert_pair_union, empty_union]

/-- INTERNAL: close a pair-membership goal once the atom `h` is decided. -/
macro "dm_prop " h:ident : tactic => `(tactic| (
  simp only [$h:ident, or_true, true_or, or_false, false_or, not_true_eq_false,
    not_false_eq_true, and_false, false_and, and_true, true_and, iff_true, true_iff,
    false_iff, iff_false, not_or, not_and] at * <;> omega))

/-- INTERNAL: a state whose only empty pair is `i` and only full pair is `l` is in `A_il`.
TEXLINE: sections/signatures.tex:13-41 -/
theorem dm_kind_defect (I : Instance) (ε δ : ℚ) (S : Finset ℕ) (i l : ℕ)
    (hi : i < pSmall I ε δ) (hl : l < pSmall I ε δ)
    (hE : ∀ k < pSmall I ε δ, (2 * k ∉ S ∧ 2 * k + 1 ∉ S ↔ k = i))
    (hF : ∀ k < pSmall I ε δ, (2 * k ∈ S ∧ 2 * k + 1 ∈ S ↔ k = l)) :
    kind I ε δ S = .defect i l := by
  rw [w0_kind_eq_defect_iff]
  constructor
  · ext k
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨hk, h⟩; exact (hE k hk).1 h
    · rintro rfl; exact ⟨hi, (hE k hi).2 rfl⟩
  · ext k
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨hk, h⟩; exact (hF k hk).1 h
    · rintro rfl; exact ⟨hl, (hF k hl).2 rfl⟩

/-- INTERNAL: membership in `[0, p) \ {i, l}`. -/
theorem dm_mem_R (p i l k : ℕ) : k ∈ ((range p).erase i).erase l ↔ k ≠ l ∧ k ≠ i ∧ k < p := by
  simp

/-- INTERNAL: the states built from `selPairs R A` lie in `[0, 2p)`. -/
theorem dm_mem_refStates (I : Instance) (ε δ : ℚ) (B R A : Finset ℕ)
    (hB : ∀ x ∈ B, x < 2 * pSmall I ε δ) (hR : ∀ k ∈ R, k < pSmall I ε δ) (hA : A ⊆ R) :
    B ∪ selPairs R A ∈ refStates I ε δ := by
  simp only [refStates, mem_powerset]
  intro x hx
  rw [mem_range]
  rcases mem_union.1 hx with h | h
  · exact hB x h
  · have := hR _ (div_two_mem_of_mem_selPairs hA h)
    omega

/-- INTERNAL: a hole at `P₀ = {a_i}`: `{a_l, b_l'} ∪ selPairs R A` is in `A_il`. -/
theorem dm_kind_hole0 (I : Instance) (ε δ : ℚ) (i l : ℕ) (hi : i < pSmall I ε δ)
    (hl : l < pSmall I ε δ) (hil : i ≠ l) (al bl : ℕ)
    (hal : (al = 2 * l ∧ bl = 2 * l + 1) ∨ (al = 2 * l + 1 ∧ bl = 2 * l))
    (A : Finset ℕ) (hA : A ⊆ ((range (pSmall I ε δ)).erase i).erase l) :
    kind I ε δ (insert bl {al} ∪ selPairs (((range (pSmall I ε δ)).erase i).erase l) A) =
      .defect i l := by
  apply dm_kind_defect I ε δ _ i l hi hl
  · intro k hk
    simp only [mem_union, mem_insert, mem_singleton, two_mul_mem_selPairs,
      two_mul_add_one_mem_selPairs, dm_mem_R]
    by_cases hkA : k ∈ A
    · have := (dm_mem_R _ _ _ _).1 (hA hkA)
      dm_prop hkA
    · simp only [hkA, or_false, not_false_eq_true, and_true]
      omega
  · intro k hk
    simp only [mem_union, mem_insert, mem_singleton, two_mul_mem_selPairs,
      two_mul_add_one_mem_selPairs, dm_mem_R]
    by_cases hkA : k ∈ A
    · have := (dm_mem_R _ _ _ _).1 (hA hkA)
      dm_prop hkA
    · simp only [hkA, or_false, not_false_eq_true, and_true]
      omega

/-- INTERNAL: a hole at `P₁ = {b_l'}`: `{a_i, a_l} ∪ selPairs R A` is a transversal. -/
theorem dm_kind_hole1 (I : Instance) (ε δ : ℚ) (i l : ℕ) (hil : i ≠ l) (ai al : ℕ) (hai : ai = 2 * i ∨ ai = 2 * i + 1)
    (hal : al = 2 * l ∨ al = 2 * l + 1)
    (A : Finset ℕ) (hA : A ⊆ ((range (pSmall I ε δ)).erase i).erase l) :
    kind I ε δ (insert ai {al} ∪ selPairs (((range (pSmall I ε δ)).erase i).erase l) A) =
      .transversal := by
  rw [kind_eq_transversal_iff]
  intro k hk
  simp only [mem_union, mem_insert, mem_singleton, two_mul_mem_selPairs,
    two_mul_add_one_mem_selPairs, dm_mem_R]
  by_cases hkA : k ∈ A
  · have := (dm_mem_R _ _ _ _).1 (hA hkA)
    dm_prop hkA
  · dm_prop hkA

/-- INTERNAL: membership in `R \ {t}`. -/
theorem dm_mem_Rt (p i l t k : ℕ) :
    k ∈ (((range p).erase i).erase l).erase t ↔ k ≠ t ∧ k ≠ l ∧ k ≠ i ∧ k < p := by
  simp

/-- INTERNAL: a hole at the ordinary slot `t`: `{a_i, a_l, b_l'} ∪ selPairs (R \ {t}) A`
is in `A_tl`. -/
theorem dm_kind_holet (I : Instance) (ε δ : ℚ) (i l t : ℕ)
    (hl : l < pSmall I ε δ) (ht : t ∈ ((range (pSmall I ε δ)).erase i).erase l)
    (ai al bl : ℕ) (hai : ai = 2 * i ∨ ai = 2 * i + 1)
    (hal : (al = 2 * l ∧ bl = 2 * l + 1) ∨ (al = 2 * l + 1 ∧ bl = 2 * l))
    (A : Finset ℕ) (hA : A ⊆ (((range (pSmall I ε δ)).erase i).erase l).erase t) :
    kind I ε δ (insert ai (insert bl {al}) ∪
      selPairs ((((range (pSmall I ε δ)).erase i).erase l).erase t) A) = .defect t l := by
  have ht' := (dm_mem_R _ _ _ _).1 ht
  apply dm_kind_defect I ε δ _ t l ht'.2.2 hl
  · intro k hk
    simp only [mem_union, mem_insert, mem_singleton, two_mul_mem_selPairs,
      two_mul_add_one_mem_selPairs, dm_mem_Rt]
    by_cases hkA : k ∈ A
    · have := (dm_mem_Rt _ _ _ _ _).1 (hA hkA)
      dm_prop hkA
    · dm_prop hkA
  · intro k hk
    simp only [mem_union, mem_insert, mem_singleton, two_mul_mem_selPairs,
      two_mul_add_one_mem_selPairs, dm_mem_Rt]
    by_cases hkA : k ∈ A
    · have := (dm_mem_Rt _ _ _ _ _).1 (hA hkA)
      dm_prop hkA
    · dm_prop hkA

/-- INTERNAL: a doubled slot `t` with both singleton slots empty:
`{2t, 2t+1, a_l} ∪ selPairs (R \ {t}) A` is in `A_it`. -/
theorem dm_kind_double (I : Instance) (ε δ : ℚ) (i l t : ℕ) (hi : i < pSmall I ε δ)
    (hil : i ≠ l) (ht : t ∈ ((range (pSmall I ε δ)).erase i).erase l)
    (al : ℕ) (hal : al = 2 * l ∨ al = 2 * l + 1)
    (A : Finset ℕ) (hA : A ⊆ (((range (pSmall I ε δ)).erase i).erase l).erase t) :
    kind I ε δ (insert (2 * t) (insert (2 * t + 1) {al}) ∪
      selPairs ((((range (pSmall I ε δ)).erase i).erase l).erase t) A) = .defect i t := by
  have ht' := (dm_mem_R _ _ _ _).1 ht
  apply dm_kind_defect I ε δ _ i t hi ht'.2.2
  · intro k hk
    simp only [mem_union, mem_insert, mem_singleton, two_mul_mem_selPairs,
      two_mul_add_one_mem_selPairs, dm_mem_Rt]
    by_cases hkA : k ∈ A
    · have := (dm_mem_Rt _ _ _ _ _).1 (hA hkA)
      dm_prop hkA
    · dm_prop hkA
  · intro k hk
    simp only [mem_union, mem_insert, mem_singleton, two_mul_mem_selPairs,
      two_mul_add_one_mem_selPairs, dm_mem_Rt]
    by_cases hkA : k ∈ A
    · have := (dm_mem_Rt _ _ _ _ _).1 (hA hkA)
      dm_prop hkA
    · dm_prop hkA

end Cellcounting.Analysis
