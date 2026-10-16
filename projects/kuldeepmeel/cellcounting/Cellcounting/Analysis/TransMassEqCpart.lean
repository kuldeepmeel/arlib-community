import Cellcounting.Analysis.RefChainLaw

/-!
# The transversal mass is `C(j)` (`algorithm.tex:167`)

Grouping the transversals of the paired ground set by their small-count profile
`x` (with `y = b - x`): a profile is realized by `∏_s C(b_s, x_s)` transversals,
each of weight `h_j(x, b - x) ∏_s x_s! (b_s - x_s)! / b_s!`, so the transversal
mass `Σ_{S ∈ A} f_j(S)` is `Σ_x h_j(x, b - x) = C(j)`.
-/

namespace Cellcounting.Analysis

open Pseudocode

open Finset

/-- INTERNAL: a subset `T ⊆ [0, p)` is the same as its family of blocks
`T ∩ c⁻¹(s)`, `s < n`, when every label `i < p` has `c i < n`. -/
theorem sum_powerset_eq_sum_pi_filter (p n : ℕ) (c : ℕ → ℕ) (hc : ∀ i < p, c i < n)
    (G : (Fin n → Finset ℕ) → ℝ) :
    ∑ T ∈ (range p).powerset, G (fun s => T.filter (fun i => c i = s)) =
      ∑ F ∈ Fintype.piFinset (fun s : Fin n => ((range p).filter (fun i => c i = s)).powerset),
        G F := by
  apply Finset.sum_nbij' (fun T (s : Fin n) => T.filter (fun i => c i = s))
    (fun F => univ.biUnion F)
  · intro T hT
    simp only [Fintype.mem_piFinset, mem_powerset] at hT ⊢
    intro s
    exact filter_subset_filter _ hT
  · intro F hF
    simp only [Fintype.mem_piFinset, mem_powerset] at hF ⊢
    intro i hi
    simp only [mem_biUnion, mem_univ, true_and] at hi
    obtain ⟨s, hs⟩ := hi
    exact (mem_filter.1 (hF s hs)).1
  · intro T hT
    simp only [mem_powerset] at hT
    ext i
    simp only [mem_biUnion, mem_univ, true_and, mem_filter]
    constructor
    · rintro ⟨s, h, -⟩; exact h
    · intro h
      exact ⟨⟨c i, hc i (mem_range.1 (hT h))⟩, h, rfl⟩
  · intro F hF
    simp only [Fintype.mem_piFinset, mem_powerset] at hF
    funext s
    ext i
    simp only [mem_filter, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨⟨t, ht⟩, hcs⟩
      have := (mem_filter.1 (hF t ht)).2
      have hts : t = s := Fin.ext (by rw [← this, hcs])
      subst hts; exact ht
    · intro h
      exact ⟨⟨s, h⟩, (mem_filter.1 (hF s h)).2⟩
  · intro T _; rfl

/-- INTERNAL: summing a function of the block sizes over all block families groups
by the size vector `x`, each fibre having `∏_s C(|B_s|, x_s)` elements. -/
theorem sum_pi_powerset_card (n : ℕ) (B : Fin n → Finset ℕ) (G : (Fin n → ℕ) → ℝ) :
    ∑ F ∈ Fintype.piFinset (fun s => (B s).powerset), G (fun s => (F s).card) =
      ∑ x ∈ Fintype.piFinset (fun s => range ((B s).card + 1)),
        (∏ s, ((B s).card.choose (x s) : ℝ)) * G x := by
  have hmaps : ∀ F ∈ Fintype.piFinset (fun s => (B s).powerset),
      (fun s => (F s).card) ∈ Fintype.piFinset (fun s => range ((B s).card + 1)) := by
    intro F hF
    simp only [Fintype.mem_piFinset, mem_powerset, mem_range] at hF ⊢
    intro s
    exact Nat.lt_succ_of_le (card_le_card (hF s))
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps G]
  apply sum_congr rfl
  intro x _
  rw [sum_const, nsmul_eq_mul]
  congr 1
  have : (Fintype.piFinset (fun s => (B s).powerset)).filter
      (fun F => (fun s => (F s).card) = x) =
      Fintype.piFinset (fun s => (B s).powersetCard (x s)) := by
    ext F
    simp only [mem_filter, Fintype.mem_piFinset, mem_powerset, mem_powersetCard, funext_iff]
    constructor
    · rintro ⟨h1, h2⟩ s; exact ⟨h1 s, h2 s⟩
    · intro h; exact ⟨fun s => (h s).1, fun s => (h s).2⟩
  rw [this, Fintype.card_piFinset]
  simp [card_powersetCard]

/-- INTERNAL: the transversal of the paired ground set whose row elements are the
pairs in `T`: `{2i : i ∈ T} ∪ {2i + 1 : i < p, i ∉ T}`.
TEXLINE: sections/signatures.tex:13-41 -/
def transEmb (p : ℕ) (T : Finset ℕ) : Finset ℕ :=
  T.image (fun i => 2 * i) ∪ ((range p) \ T).image (fun i => 2 * i + 1)

/-- INTERNAL: the row element `2i` is in `transEmb p T` iff `i ∈ T`. -/
theorem two_mul_mem_transEmb (p : ℕ) (T : Finset ℕ) (i : ℕ) : 2 * i ∈ transEmb p T ↔ i ∈ T := by
  simp only [transEmb, mem_union, mem_image, mem_sdiff, mem_range]
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨a, -, h⟩)
    · have : a = i := by omega
      exact this ▸ ha
    · omega
  · intro h; exact Or.inl ⟨i, h, rfl⟩

/-- INTERNAL: the column element `2i + 1` is in `transEmb p T` iff `i < p, i ∉ T`. -/
theorem two_mul_add_one_mem_transEmb (p : ℕ) (T : Finset ℕ) (i : ℕ) :
    2 * i + 1 ∈ transEmb p T ↔ i < p ∧ i ∉ T := by
  simp only [transEmb, mem_union, mem_image, mem_sdiff, mem_range]
  constructor
  · rintro (⟨a, -, h⟩ | ⟨a, ha, h⟩)
    · omega
    · have : a = i := by omega
      exact this ▸ ha
  · intro h; exact Or.inr ⟨i, h, rfl⟩

/-- INTERNAL: transversals of `[0, 2p)` correspond to subsets of the pairs `[0, p)`. -/
theorem sum_trans_eq_sum_powerset (p : ℕ) (f : Finset ℕ → ℝ) :
    ∑ S ∈ (range (2 * p)).powerset.filter (fun S => ∀ i < p, (2 * i ∈ S ↔ 2 * i + 1 ∉ S)),
      f S = ∑ T ∈ (range p).powerset, f (transEmb p T) := by
  apply Finset.sum_nbij' (fun S => (range p).filter (fun i => 2 * i ∈ S)) (transEmb p)
  · intro S _
    simp only [mem_powerset]
    exact filter_subset _ _
  · intro T hT
    simp only [mem_powerset] at hT
    simp only [mem_filter, mem_powerset]
    refine ⟨?_, ?_⟩
    · intro e he
      simp only [transEmb, mem_union, mem_image, mem_sdiff, mem_range] at he
      rw [mem_range]
      rcases he with ⟨a, ha, rfl⟩ | ⟨a, ⟨ha, -⟩, rfl⟩
      · have := mem_range.1 (hT ha); omega
      · omega
    · intro i hi
      rw [two_mul_mem_transEmb, two_mul_add_one_mem_transEmb]
      tauto
  · intro S hS
    simp only [mem_filter, mem_powerset] at hS
    obtain ⟨hsub, htr⟩ := hS
    ext e
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' e
    · rw [two_mul_mem_transEmb, mem_filter, mem_range]
      constructor
      · exact fun h => h.2
      · intro h
        have := mem_range.1 (hsub h)
        exact ⟨by omega, h⟩
    · rw [two_mul_add_one_mem_transEmb, mem_filter, mem_range]
      constructor
      · rintro ⟨hi, h⟩
        by_contra h'; exact h ⟨hi, (htr i hi).2 h'⟩
      · intro h
        have hi : i < p := by have := mem_range.1 (hsub h); omega
        refine ⟨hi, fun ⟨_, h'⟩ => (htr i hi).1 h' h⟩
  · intro T hT
    simp only [mem_powerset] at hT
    ext i
    rw [mem_filter, two_mul_mem_transEmb, mem_range]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨mem_range.1 (hT h), h⟩
  · intro S hS
    simp only [mem_filter, mem_powerset] at hS
    congr 1
    obtain ⟨hsub, htr⟩ := hS
    ext e
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' e
    · rw [two_mul_mem_transEmb, mem_filter, mem_range]
      constructor
      · intro h
        have := mem_range.1 (hsub h)
        exact ⟨by omega, h⟩
      · exact fun h => h.2
    · rw [two_mul_add_one_mem_transEmb, mem_filter, mem_range]
      constructor
      · intro h
        have hi : i < p := by have := mem_range.1 (hsub h); omega
        refine ⟨hi, fun ⟨_, h'⟩ => (htr i hi).1 h' h⟩
      · rintro ⟨hi, h⟩
        by_contra h'; exact h ⟨hi, (htr i hi).2 h'⟩

/-- INTERNAL: the number of positions holding `s` in a list is `count s`. -/
theorem card_filter_getD_eq_count (l : List ℕ) (s : ℕ) :
    ((range l.length).filter (fun i => l.getD i 0 = s)).card = l.count s := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [card_filter, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [← card_filter, ih, List.count_cons]
    simp

/-- INTERNAL: a `List.range` sum is the matching `Finset.range` sum. -/
theorem list_range_map_sum (n : ℕ) (g : ℕ → ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ range n, g i := by
  rw [← sum_range_getD_eq (List.range n) g 0, List.length_range]
  apply sum_congr rfl
  intro i hi
  simp [List.getD_eq_getElem?_getD, mem_range.1 hi]

/-- INTERNAL: there are `p = Σ_s b_s` pair labels. -/
theorem pairCells_length (I : Instance) (ε δ : ℚ) :
    (pairCells I ε δ).length = pSmall I ε δ := by
  rw [pairCells, List.length_flatMap, pSmall]
  simp only [List.length_replicate]
  rw [← sum_range_getD_eq (smallCells I ε δ) (fun e => e.2.2) (0, 0, 0), list_range_map_sum]
  rfl

/-- INTERNAL: every pair label `i < p` belongs to a small cell `s(i) < nSmall`. -/
theorem pairCell_lt (I : Instance) (ε δ : ℚ) {i : ℕ} (hi : i < pSmall I ε δ) :
    pairCell I ε δ i < nSmall I ε δ := by
  rw [← pairCells_length] at hi
  have hmem : pairCell I ε δ i ∈ pairCells I ε δ := by
    rw [pairCell, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  rw [pairCells, List.mem_flatMap] at hmem
  obtain ⟨s, hs, hrep⟩ := hmem
  rw [List.eq_of_mem_replicate hrep]
  exact List.mem_range.1 hs

/-- INTERNAL: `smallB` vanishes past the small cells. -/
theorem smallB_eq_zero (I : Instance) (ε δ : ℚ) {s : ℕ} (hs : nSmall I ε δ ≤ s) :
    smallB I ε δ s = 0 := by
  rw [nSmall] at hs
  simp [smallB, smallAt, List.getD_eq_getElem?_getD, hs]

/-- INTERNAL: small cell `s` owns exactly `b_s` pair labels. -/
theorem smallB_eq_card (I : Instance) (ε δ : ℚ) (s : ℕ) :
    smallB I ε δ s = ((range (pSmall I ε δ)).filter (fun i => pairCell I ε δ i = s)).card := by
  have h := card_filter_getD_eq_count (pairCells I ε δ) s
  rw [pairCells_length] at h
  refine Eq.trans ?_ h.symm
  rw [pairCells, List.count_flatMap, list_range_map_sum]
  simp only [Function.comp_def, List.count_replicate, beq_iff_eq]
  rw [sum_ite_eq']
  split_ifs with h
  · rfl
  · exact smallB_eq_zero I ε δ (by simpa using h)


/-- INTERNAL: a state is a transversal iff every pair holds exactly one element.
TEXLINE: sections/signatures.tex:13-41 -/
theorem kind_eq_transversal_iff (I : Instance) (ε δ : ℚ) (S : Finset ℕ) :
    kind I ε δ S = .transversal ↔ ∀ i < pSmall I ε δ, (2 * i ∈ S ↔ 2 * i + 1 ∉ S) := by
  unfold kind
  simp only
  split_ifs with hE hF hEF
  · simp only [true_iff]
    rw [card_eq_zero, filter_eq_empty_iff] at hE hF
    intro i hi
    have h1 := hE (mem_range.2 hi)
    have h2 := hF (mem_range.2 hi)
    tauto
  · simp only [false_iff, not_forall]
    rw [card_eq_zero, filter_eq_empty_iff] at hF
    push Not at hF
    obtain ⟨i, hi, h1, h2⟩ := hF
    exact ⟨i, mem_range.1 hi, fun h => (h.1 h1) h2⟩
  · simp only [false_iff, not_forall]
    rw [card_eq_zero, filter_eq_empty_iff] at hE
    push Not at hE
    obtain ⟨i, hi, h1, h2⟩ := hE
    exact ⟨i, mem_range.1 hi, fun h => h1 (h.2 h2)⟩
  · simp only [false_iff, not_forall]
    rw [card_eq_zero, filter_eq_empty_iff] at hE
    push Not at hE
    obtain ⟨i, hi, h1, h2⟩ := hE
    exact ⟨i, mem_range.1 hi, fun h => h1 (h.2 h2)⟩

/-- INTERNAL: the small-count profile of `transEmb p T`: `x_s = |T ∩ s⁻¹(s)|`
and `y_s = b_s - x_s`.
TEXLINE: sections/signatures.tex:13-41 -/
theorem profile_transEmb (I : Instance) (ε δ : ℚ) (T : Finset ℕ)
    (hT : T ⊆ range (pSmall I ε δ)) :
    profile I ε δ (transEmb (pSmall I ε δ) T) =
      (fun s => (T.filter (fun i => pairCell I ε δ i = s)).card,
        fun s => smallB I ε δ s - (T.filter (fun i => pairCell I ε δ i = s)).card) := by
  have h1 : ∀ s, ((range (pSmall I ε δ)).filter fun i =>
      pairCell I ε δ i = s ∧ 2 * i ∈ transEmb (pSmall I ε δ) T) =
      T.filter (fun i => pairCell I ε δ i = s) := by
    intro s; ext i
    simp only [mem_filter, two_mul_mem_transEmb]
    constructor
    · rintro ⟨-, h, h'⟩; exact ⟨h', h⟩
    · rintro ⟨h', h⟩; exact ⟨hT h', h, h'⟩
  unfold profile
  refine Prod.ext (funext fun s => by simp only [h1]) (funext fun s => ?_)
  simp only
  have hsplit := card_filter_add_card_filter_not
    (s := (range (pSmall I ε δ)).filter fun i => pairCell I ε δ i = s)
    (fun i => 2 * i ∈ transEmb (pSmall I ε δ) T)
  rw [filter_filter, filter_filter] at hsplit
  have hcol : ((range (pSmall I ε δ)).filter fun i =>
      pairCell I ε δ i = s ∧ 2 * i + 1 ∈ transEmb (pSmall I ε δ) T) =
      (range (pSmall I ε δ)).filter fun i =>
        pairCell I ε δ i = s ∧ ¬ 2 * i ∈ transEmb (pSmall I ε δ) T := by
    apply filter_congr
    intro i hi
    rw [two_mul_add_one_mem_transEmb, two_mul_mem_transEmb]
    simp [mem_range.1 hi]
  rw [smallB_eq_card, ← h1 s, hcol]
  omega

/-- **The transversal mass is `C(j)`** (`algorithm.tex:167`, "The transversal mass
is `C(j)`").
PAPER: sections/algorithm.tex:167-172 -/
theorem transMass_eq_Cpart (I : Instance) (ε δ : ℚ) (j : ℕ) :
    transMass I ε δ j = Cpart I ε δ j := by
  classical
  -- the transversals are the subsets of `[0, 2p)` meeting every pair once
  have hstates : transStates I ε δ = (range (2 * pSmall I ε δ)).powerset.filter
      (fun S => ∀ i < pSmall I ε δ, (2 * i ∈ S ↔ 2 * i + 1 ∉ S)) := by
    unfold transStates refStates
    exact filter_congr fun S _ => kind_eq_transversal_iff I ε δ S
  -- `f_j` as a function of the row profile `x` (with `y = b - x`)
  set F : (ℕ → ℕ) → ℝ := fun x =>
    hWeight I ε δ j x (fun s => smallB I ε δ s - x s) *
      ∏ s ∈ range (nSmall I ε δ), (((x s).factorial : ℝ) *
        ((smallB I ε δ s - x s).factorial : ℝ) / ((smallB I ε δ s).factorial : ℝ)) with hF
  have hstep : ∀ T ∈ (range (pSmall I ε δ)).powerset,
      fWeight I ε δ j (transEmb (pSmall I ε δ) T) =
        F (extendN (fun s : Fin (nSmall I ε δ) =>
          (T.filter (fun i => pairCell I ε δ i = s)).card)) := by
    intro T hT
    rw [mem_powerset] at hT
    have hext : extendN (fun s : Fin (nSmall I ε δ) =>
        (T.filter (fun i => pairCell I ε δ i = s)).card) =
        fun s => (T.filter (fun i => pairCell I ε δ i = s)).card := by
      funext k
      unfold extendN
      split_ifs with hk
      · rfl
      · symm
        rw [card_eq_zero, filter_eq_empty_iff]
        intro i hi h
        exact hk (h ▸ pairCell_lt I ε δ (mem_range.1 (hT hi)))
    rw [hext, hF]
    unfold fWeight
    rw [profile_transEmb I ε δ T hT]
  rw [transMass, hstates, sum_trans_eq_sum_powerset, sum_congr rfl hstep]
  refine (sum_powerset_eq_sum_pi_filter (pSmall I ε δ) (nSmall I ε δ) (pairCell I ε δ)
    (fun i hi => pairCell_lt I ε δ hi) (fun Fm => F (extendN (fun s => (Fm s).card)))).trans ?_
  refine (sum_pi_powerset_card (nSmall I ε δ)
    (fun s => (range (pSmall I ε δ)).filter (fun i => pairCell I ε δ i = s))
    (fun x => F (extendN x))).trans ?_
  simp_rw [← smallB_eq_card]
  unfold Cpart smallBox
  apply sum_congr rfl
  intro x hx
  rw [hF]
  simp only
  rw [← Fin.prod_univ_eq_prod_range (fun s => ((extendN x s).factorial : ℝ) *
    ((smallB I ε δ s - extendN x s).factorial : ℝ) / ((smallB I ε δ s).factorial : ℝ))]
  have hxs : ∀ s : Fin (nSmall I ε δ), extendN x s = x s := fun s => by simp [extendN]
  simp only [hxs]
  rw [mul_left_comm, ← prod_mul_distrib, prod_eq_one, mul_one]
  intro s _
  have hle : x s ≤ smallB I ε δ s :=
    Nat.lt_succ_iff.1 (mem_range.1 (Fintype.mem_piFinset.1 hx s))
  have hc := Nat.choose_mul_factorial_mul_factorial hle
  have hpos : ((smallB I ε δ s).factorial : ℝ) ≠ 0 := by positivity
  rw [mul_div_assoc', ← mul_assoc, div_eq_one_iff_eq hpos]
  exact_mod_cast hc

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `transMass_eq_Cpart` via transversals ↔ pair subsets ↔ block families, fibres of size `∏ C(b_s, x_s)`
-/
