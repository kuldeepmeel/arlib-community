import Cellcounting.Analysis.SelPairs
import Cellcounting.Analysis.SlotTransport

/-!
# The one-hole energy of `lem:defect-mean` is at most `𝔇(g)` (`transport.tex:456-468`)

In the application of `lem:transport` in `lem:defect-mean` the fixed inclusion is
`{a_l}`, the singleton slots are `a_i` and `b_l'` (the mate of `a_l`), and the ordinary
slots are the pairs of `R = [0, p) \ {i, l}`.  A complete display is
`D_A = {a_i, b_l'} ∪ selPairs R A`, `A ⊆ R`, and its one-hole states are
`({a_l} ∪ D_A) \ {x}`: for `x = a_i` a state of `A_il`, for `x = b_l'` a transversal,
for `x` in the pair `t` a state of `A_tl`.  With the hole multipliers `defW`
(`w_il`, `1`, `w_tl`) every one-hole weight is the chain weight `λ`
(`defect_hole_state`), two one-hole states of one display are exchange neighbours, and
distinct displays have disjoint edges.  Hence the sum over displays of the clique
energies, the energy `D_sl(g)` of `slot_transport`, is at most `𝔇(g) = refDir`
(`defect_clique_le`): "all one-hole states and their exchange edges are genuine states
and edges of the chain, with the same endpoint weights.  Their energy is at most
`𝔇(g)`."
-/

namespace Cellcounting.Analysis

open Pseudocode Finset

/-- INTERNAL: the hole multipliers of `lem:defect-mean`: `w_il` at `a_i`, `1` at `b_l'`,
and `w_tl` at either element of an ordinary pair `t`.
TEXLINE: sections/transport.tex:456-466 -/
noncomputable def defW (w : ℕ → ℕ → ℚ) (i l ai bl : ℕ) (e : ℕ) : ℝ :=
  if e = ai then (w i l : ℝ) else if e = bl then 1 else (w (e / 2) l : ℝ)

/-- INTERNAL: two one-hole states of one display are exchange neighbours. -/
theorem dc_erase_exchNbr {U : Finset ℕ} {x y : ℕ} (hx : x ∈ U) (hy : y ∈ U) (hxy : x ≠ y) :
    exchNbr (U.erase x) (U.erase y) := by
  have key : ∀ x y, x ∈ U → y ∈ U → x ≠ y → U.erase x \ U.erase y = {y} := by
    intro x y hx hy hxy
    ext z
    simp only [mem_sdiff, mem_erase, mem_singleton]
    constructor
    · rintro ⟨⟨_, hz⟩, h⟩
      by_contra hzy
      exact h ⟨hzy, hz⟩
    · rintro rfl
      exact ⟨⟨fun h => hxy h.symm, hy⟩, fun h => h.1 rfl⟩
  exact ⟨by rw [key x y hx hy hxy, card_singleton],
    by rw [key y x hy hx (Ne.symm hxy), card_singleton]⟩

/-- INTERNAL: membership in a one-hole state `({a_l} ∪ D_A) \ {x}`. -/
theorem dc_mem_state (al ai bl x : ℕ) (R A : Finset ℕ) (z : ℕ) :
    z ∈ ({al} ∪ insert ai (insert bl (selPairs R A))).erase x ↔
      z ≠ x ∧ (z = al ∨ z = ai ∨ z = bl ∨ z ∈ selPairs R A) := by
  simp only [mem_erase, mem_union, mem_singleton, mem_insert]

/-- INTERNAL: every one-hole state of a display `D_A` is a state of `X` whose chain
weight is `defW x · f`.
TEXLINE: sections/transport.tex:456-468 -/
theorem defect_hole_state (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (i l : ℕ) (hi : i < pSmall I ε δ) (hl : l < pSmall I ε δ) (hil : i ≠ l)
    (ai al bl : ℕ) (hai : ai = 2 * i ∨ ai = 2 * i + 1)
    (hal : (al = 2 * l ∧ bl = 2 * l + 1) ∨ (al = 2 * l + 1 ∧ bl = 2 * l))
    (A : Finset ℕ) (hA : A ⊆ ((range (pSmall I ε δ)).erase i).erase l) (x : ℕ)
    (hx : x ∈ insert ai (insert bl (selPairs (((range (pSmall I ε δ)).erase i).erase l) A))) :
    ({al} ∪ insert ai (insert bl (selPairs (((range (pSmall I ε δ)).erase i).erase l) A))).erase x
        ∈ chainStates I ε δ ∧
      refLam I ε δ (({al} ∪ insert ai (insert bl
          (selPairs (((range (pSmall I ε δ)).erase i).erase l) A))).erase x) j w =
        defW w i l ai bl x * fWeight I ε δ j (({al} ∪ insert ai (insert bl
          (selPairs (((range (pSmall I ε δ)).erase i).erase l) A))).erase x) := by
  classical
  set p := pSmall I ε δ with hpdef
  set R := ((range p).erase i).erase l with hRdef
  set S := ({al} ∪ insert ai (insert bl (selPairs R A))).erase x with hSdef
  have hRp : ∀ k ∈ R, k < p := fun k hk => ((dm_mem_R _ _ _ _).1 hk).2.2
  have hS : S ∈ refStates I ε δ := by
    simp only [refStates, mem_powerset]
    intro z hz
    rw [hSdef, dc_mem_state] at hz
    rw [mem_range]
    rcases hz.2 with h | h | h | h
    · omega
    · omega
    · omega
    · have := hRp _ (div_two_mem_of_mem_selPairs hA h)
      omega
  have hX : ∀ k, kind I ε δ S = k → k ≠ .outside → S ∈ chainStates I ε δ := by
    intro k hk hko
    unfold chainStates
    exact mem_filter.2 ⟨hS, hk ▸ hko⟩
  by_cases hxa : x = ai
  · -- the hole `a_i`: a state of `A_il`
    rw [hxa] at hSdef
    have hk : kind I ε δ S = .defect i l := by
      apply dm_kind_defect I ε δ S i l hi hl
      · intro k hk
        simp only [hSdef, hRdef, dc_mem_state, two_mul_mem_selPairs, two_mul_add_one_mem_selPairs,
          dm_mem_R]
        by_cases hkA : k ∈ A
        · have := (dm_mem_R _ _ _ _).1 (hA hkA)
          dm_prop hkA
        · dm_prop hkA
      · intro k hk
        simp only [hSdef, hRdef, dc_mem_state, two_mul_mem_selPairs, two_mul_add_one_mem_selPairs,
          dm_mem_R]
        by_cases hkA : k ∈ A
        · have := (dm_mem_R _ _ _ _).1 (hA hkA)
          dm_prop hkA
        · dm_prop hkA
    refine ⟨hX _ hk (by simp), ?_⟩
    rw [td_refLam_eq, hk, defW, if_pos hxa]
    ring
  have hx' := (mem_insert.1 hx).resolve_left hxa
  by_cases hxb : x = bl
  · -- the hole `b_l'`: a transversal
    rw [hxb] at hSdef
    have hk : kind I ε δ S = .transversal := by
      rw [kind_eq_transversal_iff]
      intro k hk
      simp only [hSdef, hRdef, dc_mem_state, two_mul_mem_selPairs, two_mul_add_one_mem_selPairs,
        dm_mem_R]
      by_cases hkA : k ∈ A
      · have := (dm_mem_R _ _ _ _).1 (hA hkA)
        dm_prop hkA
      · dm_prop hkA
    refine ⟨hX _ hk (by simp), ?_⟩
    rw [td_refLam_eq, hk, defW, if_neg hxa, if_pos hxb]
    ring
  · have hx := (mem_insert.1 hx').resolve_left hxb
    -- an ordinary hole in the pair `t = x / 2`: a state of `A_tl`
    have ht := div_two_mem_of_mem_selPairs hA hx
    have ht' := (dm_mem_R _ _ _ _).1 ht
    have hk : kind I ε δ S = .defect (x / 2) l := by
      obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' x
      · rw [two_mul_mem_selPairs] at hx
        rw [show 2 * t / 2 = t by omega] at ht' ⊢
        apply dm_kind_defect I ε δ S t l ht'.2.2 hl
        · intro k hk
          simp only [hSdef, hRdef, dc_mem_state, two_mul_mem_selPairs, two_mul_add_one_mem_selPairs,
            dm_mem_R]
          by_cases hkA : k ∈ A
          · have := (dm_mem_R _ _ _ _).1 (hA hkA)
            dm_prop hkA
          · have hkt : k ≠ t := fun h => hkA (h ▸ hx)
            dm_prop hkA
        · intro k hk
          simp only [hSdef, hRdef, dc_mem_state, two_mul_mem_selPairs, two_mul_add_one_mem_selPairs,
            dm_mem_R]
          by_cases hkA : k ∈ A
          · have := (dm_mem_R _ _ _ _).1 (hA hkA)
            dm_prop hkA
          · have hkt : k ≠ t := fun h => hkA (h ▸ hx)
            dm_prop hkA
      · rw [two_mul_add_one_mem_selPairs] at hx
        rw [show (2 * t + 1) / 2 = t by omega] at ht' ⊢
        apply dm_kind_defect I ε δ S t l ht'.2.2 hl
        · intro k hk
          simp only [hSdef, hRdef, dc_mem_state, two_mul_mem_selPairs, two_mul_add_one_mem_selPairs,
            dm_mem_R]
          by_cases hkA : k ∈ A
          · have := (dm_mem_R _ _ _ _).1 (hA hkA)
            have hkt : k ≠ t := fun h => hx.2 (h ▸ hkA)
            dm_prop hkA
          · dm_prop hkA
        · intro k hk
          simp only [hSdef, hRdef, dc_mem_state, two_mul_mem_selPairs, two_mul_add_one_mem_selPairs,
            dm_mem_R]
          by_cases hkA : k ∈ A
          · have := (dm_mem_R _ _ _ _).1 (hA hkA)
            have hkt : k ≠ t := fun h => hx.2 (h ▸ hkA)
            dm_prop hkA
          · dm_prop hkA
    refine ⟨hX _ hk (by simp), ?_⟩
    rw [td_refLam_eq, hk, defW, if_neg hxa, if_neg hxb]
    ring

/-- **The one-hole energy is at most `𝔇(g)`** (`transport.tex:466-468`): the sum over the
complete displays `D_A` of the clique energies of their one-hole states, with the hole
multipliers `defW`, is at most `refDir`.
TEXLINE: sections/transport.tex:456-468 -/
theorem defect_clique_le (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ j w) (g : Finset ℕ → ℝ)
    (i l : ℕ) (hi : i < pSmall I ε δ) (hl : l < pSmall I ε δ) (hil : i ≠ l)
    (ai al bl : ℕ) (hai : ai = 2 * i ∨ ai = 2 * i + 1)
    (hal : (al = 2 * l ∧ bl = 2 * l + 1) ∨ (al = 2 * l + 1 ∧ bl = 2 * l)) :
    chSum (((List.range (pSmall I ε δ)).erase i).erase l)
        (fun c => cliqueEnergy (fWeight I ε δ j) g (defW w i l ai bl) {al}
          (insert ai (insert bl c))) ≤
      refDir I ε δ j w g := by
  classical
  set p := pSmall I ε δ with hpdef
  set R := ((range p).erase i).erase l with hRdef
  set X := chainStates I ε δ with hXdef
  set G : Finset ℕ × Finset ℕ → ℝ := fun q =>
    if exchNbr q.1 q.2 then
      min (refLam I ε δ q.1 j w) (refLam I ε δ q.2 j w) * (g q.1 - g q.2) ^ 2
    else 0 with hGdef
  have hG0 : ∀ q, 0 ≤ G q := by
    intro q
    simp only [hGdef]
    split
    · exact mul_nonneg (le_min (td_refLam_nonneg I ε δ j w hgood _)
        (td_refLam_nonneg I ε δ j w hgood _)) (sq_nonneg _)
    · exact le_refl 0
  set D : Finset ℕ → Finset ℕ := fun A => insert ai (insert bl (selPairs R A)) with hDdef
  set U : Finset ℕ → Finset ℕ := fun A => {al} ∪ D A with hUdef
  set e : (Σ _ : Finset ℕ, ℕ × ℕ) → Finset ℕ × Finset ℕ :=
    fun s => ((U s.1).erase s.2.1, (U s.1).erase s.2.2) with hedef
  set idx := R.powerset.sigma (fun A => (D A ×ˢ D A).filter (fun q => q.1 ≠ q.2)) with hidx
  rw [chSum_eq_sum_selPairs ((List.nodup_range.erase i).erase l), dm_toFinset_erase_erase]
  -- each clique energy is half a sum of `G` over the ordered edges of its display
  have hclique : ∀ A ∈ R.powerset,
      cliqueEnergy (fWeight I ε δ j) g (defW w i l ai bl) {al} (D A) =
        (∑ q ∈ (D A ×ˢ D A).filter (fun q => q.1 ≠ q.2), G (e ⟨A, q⟩)) / 2 := by
    intro A hA
    have hA' := mem_powerset.1 hA
    unfold cliqueEnergy
    congr 1
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
    by_cases hxy : x = y
    · simp [hxy]
    · rw [if_neg hxy, if_pos hxy]
      have hS := defect_hole_state I ε δ j w i l hi hl hil ai al bl hai hal A hA' x hx
      have hS' := defect_hole_state I ε δ j w i l hi hl hil ai al bl hai hal A hA' y hy
      have hxU : x ∈ U A := mem_union_right _ hx
      have hyU : y ∈ U A := mem_union_right _ hy
      simp only [hGdef, hedef]
      rw [if_pos (dc_erase_exchNbr hxU hyU hxy)]
      simp only [hUdef, hDdef] at hS hS' ⊢
      rw [hS.2, hS'.2]
  rw [Finset.sum_congr rfl hclique, ← Finset.sum_div]
  rw [Finset.sum_sigma' R.powerset (fun A => (D A ×ˢ D A).filter (fun q => q.1 ≠ q.2))
    (fun A q => G (e ⟨A, q⟩))]
  -- membership in the index set
  have hmem : ∀ s ∈ idx, s.1 ⊆ R ∧ s.2.1 ∈ D s.1 ∧ s.2.2 ∈ D s.1 ∧ s.2.1 ≠ s.2.2 := by
    rintro ⟨A, x, y⟩ hs
    simp only [hidx, mem_sigma, mem_powerset, mem_filter, mem_product] at hs
    exact ⟨hs.1, hs.2.1.1, hs.2.1.2, hs.2.2⟩
  -- distinct displays and distinct holes give distinct ordered edges
  have hinj : Set.InjOn e idx := by
    rintro ⟨A, x, y⟩ hs ⟨A', x', y'⟩ hs' heq
    obtain ⟨hA, hx, hy, hxy⟩ := hmem _ hs
    obtain ⟨hA', hx', hy', hxy'⟩ := hmem _ hs'
    simp only at hA hx hy hxy hA' hx' hy' hxy'
    simp only [hedef, Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have hunion : ∀ (V : Finset ℕ) (a b : ℕ), a ≠ b → V.erase a ∪ V.erase b = V := by
      intro V a b hab
      ext z
      simp only [mem_union, mem_erase]
      constructor
      · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
      · intro h
        by_cases hza : z = a
        · exact Or.inr ⟨by rw [hza]; exact hab, h⟩
        · exact Or.inl ⟨hza, h⟩
    have hU : U A = U A' := by
      rw [← hunion (U A) x y hxy, ← hunion (U A') x' y' hxy', h1, h2]
    have hAA : A = A' := by
      have key : ∀ B B', B ⊆ R → U B = U B' → ∀ t ∈ B, t ∈ B' := by
        intro B B' hB hBB t ht
        have htR := (dm_mem_R _ _ _ _).1 (hB ht)
        have h2t : 2 * t ∈ U B := by
          simp only [hUdef, hDdef, mem_union, mem_insert, two_mul_mem_selPairs]
          exact Or.inr (Or.inr (Or.inr ht))
        rw [hBB] at h2t
        simp only [hUdef, hDdef, mem_union, mem_singleton, mem_insert,
          two_mul_mem_selPairs] at h2t
        rcases h2t with h | h | h | h
        · omega
        · omega
        · omega
        · exact h
      ext t
      exact ⟨key A A' hA hU t, key A' A hA' hU.symm t⟩
    have herase : ∀ (V : Finset ℕ) (a b : ℕ), a ∈ V → b ∈ V → V.erase a = V.erase b → a = b := by
      intro V a b ha hb hab
      by_contra hne
      have : b ∈ V.erase a := mem_erase.2 ⟨Ne.symm hne, hb⟩
      rw [hab] at this
      exact (mem_erase.1 this).1 rfl
    have hxU : x ∈ U A := mem_union_right _ hx
    have hyU : y ∈ U A := mem_union_right _ hy
    have hxU' : x' ∈ U A := hU ▸ mem_union_right _ hx'
    have hyU' : y' ∈ U A := hU ▸ mem_union_right _ hy'
    rw [← hU] at h1 h2
    have hxx := herase _ _ _ hxU hxU' h1
    have hyy := herase _ _ _ hyU hyU' h2
    subst hAA hxx hyy
    rfl
  -- the ordered edges are edges of `X`
  have hsub : idx.image e ⊆ X ×ˢ X := by
    intro q hq
    obtain ⟨s, hs, rfl⟩ := mem_image.1 hq
    obtain ⟨hA, hx, hy, -⟩ := hmem s hs
    exact mem_product.2
      ⟨(defect_hole_state I ε δ j w i l hi hl hil ai al bl hai hal s.1 hA s.2.1 hx).1,
        (defect_hole_state I ε δ j w i l hi hl hil ai al bl hai hal s.1 hA s.2.2 hy).1⟩
  have hsum : ∑ s ∈ idx, G (e s) ≤ ∑ q ∈ X ×ˢ X, G q := by
    rw [← Finset.sum_image hinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => hG0 q
  have hdir : refDir I ε δ j w g = (∑ q ∈ X ×ˢ X, G q) / 2 := by
    unfold refDir
    rw [Finset.sum_product]
  rw [hdir]
  exact div_le_div_of_nonneg_right hsum (by norm_num)

end Cellcounting.Analysis
