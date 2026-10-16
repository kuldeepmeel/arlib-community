import Cellcounting.Analysis.TransportDirichlet
import Cellcounting.Analysis.RefStepReversible

/-!
# The energy is the edge energy over `2 p² Λ` (`eq:energy`, `transport.tex:70-96`)

For good multipliers (`λ ≥ 0` on `X`), `𝓔(g) = ⟨g, (I - P) g⟩_π = 𝔇(g) / (2 p² Λ)`.
Every state of `X` has `p` elements in `[0, 2p)`, so a given exchange neighbour
`S'` of `S` is proposed with probability `1/(2p²)` and accepted with probability
`min{1, λ(S')/λ(S)}`; hence `π(S) P(S, S') = min{λ(S), λ(S')}/(2 p² Λ)` for distinct
exchange neighbours and `0` for other distinct pairs.  `P(S, ·)` is supported on
`X` for `S ∈ X`, and the usual reversible identity
`⟨g, (I - P) g⟩_π = ½ Σ π(S) P(S, S') (g(S) - g(S'))²` gives the claim.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: `nthWith` returns an element of `[0, 2p)` (local copy of `nthWith_lt`, whose
module sits on a heavier import path). -/
theorem red_nthWith_lt (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (S : Finset ℕ) (v : Bool)
    (t : ℕ) : nthWith I ε δ S v t < 2 * pSmall I ε δ := by
  unfold nthWith
  rw [List.getD_eq_getElem?_getD]
  cases h : ((List.range (2 * pSmall I ε δ)).filter fun e => decide (e ∈ S) == v)[t]? with
  | none => simp; omega
  | some e =>
    simp only [Option.getD_some]
    have := List.mem_of_getElem? h
    exact List.mem_range.1 (List.mem_filter.1 this).1

/-- INTERNAL: one exact transition from a state of `X` stays in `X`.
TEXLINE: sections/transport.tex:60-69 -/
theorem red_refStep_support (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (a : ℕ)
    (w : ℕ → ℕ → ℚ) (S : Finset ℕ) (hS : S ∈ chainStates I ε δ)
    (S' : Finset ℕ) (h : S' ∈ (refStep I ε δ a w S).support) : S' ∈ chainStates I ε δ := by
  have hsub := rsr_sub_of_chain I ε δ S hS
  have hT : ∀ u1 u2, insert (nthWith I ε δ S false u2) (S.erase (nthWith I ε δ S true u1)) ⊆
      Finset.range (2 * pSmall I ε δ) := by
    intro u1 u2
    refine Finset.insert_subset (Finset.mem_range.2 (red_nthWith_lt I ε δ hp _ _ _)) ?_
    exact (Finset.erase_subset _ _).trans hsub
  unfold refStep at h
  erw [PMF.mem_support_bind_iff] at h
  obtain ⟨hold, -, h⟩ := h
  cases hold
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    erw [PMF.mem_support_bind_iff] at h
    obtain ⟨u1, -, h⟩ := h
    erw [PMF.mem_support_bind_iff] at h
    obtain ⟨u2, -, h⟩ := h
    split at h
    · rw [(PMF.mem_support_pure_iff _ _).1 h]; exact hS
    · rename_i hk
      erw [PMF.mem_support_bind_iff] at h
      obtain ⟨ok, -, h⟩ := h
      rw [(PMF.mem_support_pure_iff _ _).1 h]
      split_ifs
      · simp only [chainStates, refStates, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hT _ _, hk⟩
      · exact hS
  · simp only [↓reduceIte] at h
    rw [(PMF.mem_support_pure_iff _ _).1 h]; exact hS

/-- INTERNAL: `P(S, ·)` sums to one over `X` for `S ∈ X`.
TEXLINE: sections/transport.tex:60-69 -/
theorem red_refPk_sum_one (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (j : ℕ)
    (w : ℕ → ℕ → ℚ) (S : Finset ℕ) (hS : S ∈ chainStates I ε δ) :
    ∑ S' ∈ chainStates I ε δ, refPk I ε δ j w S S' = 1 := by
  have h1 : ∑ S' ∈ chainStates I ε δ, refStep I ε δ j w S S' = 1 := by
    refine (tsum_eq_sum (f := fun S' => refStep I ε δ j w S S') ?_).symm.trans (PMF.tsum_coe _)
    intro S' hS'
    by_contra hne
    exact hS' (red_refStep_support I ε δ hp j w S hS S' ((PMF.mem_support_iff _ _).2 hne))
  unfold refPk
  rw [← ENNReal.toReal_sum (fun S' _ => PMF.apply_ne_top _ _), h1, ENNReal.toReal_one]

open Classical in
/-- INTERNAL: exactly one exchange `(a, b) ∈ S × (R \ S)` turns `S` into an exchange neighbour
`T ⊆ R`, and none turns it into a non-neighbour.
TEXLINE: sections/transport.tex:60-69 -/
theorem red_count_exch (S T R : Finset ℕ) (hT : T ⊆ R) :
    ((S ×ˢ (R \ S)).filter fun x => insert x.2 (S.erase x.1) = T).card =
      if exchNbr S T then 1 else 0 := by
  split_ifs with h
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h.1
    obtain ⟨b, hb⟩ := Finset.card_eq_one.1 h.2
    have hA : ∀ e, (e ∈ S ∧ e ∉ T) ↔ e = a := fun e => by
      rw [← Finset.mem_sdiff, ha, Finset.mem_singleton]
    have hB : ∀ e, (e ∈ T ∧ e ∉ S) ↔ e = b := fun e => by
      rw [← Finset.mem_sdiff, hb, Finset.mem_singleton]
    rw [Finset.card_eq_one]
    refine ⟨(a, b), ?_⟩
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff, Finset.mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hx, -, hyS⟩, he⟩
      subst he
      refine ⟨(hA x).1 ⟨hx, ?_⟩, (hB y).1 ⟨Finset.mem_insert_self _ _, hyS⟩⟩
      simp only [Finset.mem_insert, Finset.mem_erase, not_or, not_and]
      exact ⟨fun hxy => hyS (hxy ▸ hx), fun h' => absurd rfl h'⟩
    · rintro ⟨rfl, rfl⟩
      obtain ⟨haS, haT⟩ := (hA x).2 rfl
      obtain ⟨hbT, hbS⟩ := (hB y).2 rfl
      refine ⟨⟨haS, hT hbT, hbS⟩, ?_⟩
      ext e
      simp only [Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨hex, heS⟩)
        · exact hbT
        · by_contra heT
          exact hex ((hA e).1 ⟨heS, heT⟩)
      · intro heT
        by_cases heS : e ∈ S
        · exact Or.inr ⟨fun hex => haT (hex ▸ heT), heS⟩
        · exact Or.inl ((hB e).1 ⟨heT, heS⟩)
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨x, y⟩ hxy he
    simp only [Finset.mem_product, Finset.mem_sdiff] at hxy
    obtain ⟨hx, -, hyS⟩ := hxy
    subst he
    refine h ⟨Finset.card_eq_one.2 ⟨x, ?_⟩, Finset.card_eq_one.2 ⟨y, ?_⟩⟩
    · ext e
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
      constructor
      · rintro ⟨heS, hne⟩
        by_contra hex
        exact hne (Or.inr ⟨hex, heS⟩)
      · rintro rfl
        exact ⟨hx, by rintro (h' | ⟨h', -⟩) <;> [exact hyS (h' ▸ hx); exact h' rfl]⟩
    · ext e
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
      constructor
      · rintro ⟨(rfl | ⟨-, heS⟩), hn⟩
        · rfl
        · exact absurd heS hn
      · rintro rfl
        exact ⟨Or.inl rfl, hyS⟩

/-- INTERNAL: for `a, b ≥ 0`, `a · clip(b/a) = min a b`.
TEXLINE: sections/transport.tex:78-84 -/
theorem red_acc_min (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * max (min 1 (b / a)) 0 = min a b := by
  rcases ha.eq_or_lt with rfl | ha
  · simp [hb]
  · rw [max_eq_left (le_min zero_le_one (div_nonneg hb ha.le)), mul_min_of_nonneg _ _ ha.le,
      mul_one, mul_div_cancel₀ _ ha.ne']

open Classical in
/-- INTERNAL: the edge weight `π(S) P(S, T) = 1[S ~ T] min{λ(S), λ(T)} / (2 p² Λ)` for distinct
`S, T ∈ X` and good multipliers.
TEXLINE: sections/transport.tex:70-96 -/
theorem red_pi_pk_ne (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (j : ℕ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) (S T : Finset ℕ)
    (hS : S ∈ chainStates I ε δ) (hT : T ∈ chainStates I ε δ) (hTS : T ≠ S) :
    refPi I ε δ j w S * refPk I ε δ j w S T =
      (if exchNbr S T then min (refLam I ε δ S j w) (refLam I ε δ T j w) else 0) /
        (2 * (pSmall I ε δ : ℝ) ^ 2 * refLamTot I ε δ j w) := by
  have hkT : kind I ε δ T ≠ .outside := by
    simp only [chainStates, Finset.mem_filter] at hT; exact hT.2
  rw [refPi, if_pos hS, rsr_refPk_ne I ε δ j w S T hTS hkT hp, rsr_count_eq I ε δ S T hS,
    red_count_exch S T _ (rsr_sub_of_chain I ε δ T hT)]
  rw [← red_acc_min _ _ (td_refLam_nonneg I ε δ j w hgood S) (td_refLam_nonneg I ε δ j w hgood T)]
  split_ifs <;> push_cast <;> ring

/-- **The energy identity** (`eq:energy`): `𝓔(g) = 𝔇(g) / (2 p² Λ)` for good multipliers.
PAPER: sections/transport.tex:86-96 -/
theorem refEnergy_eq_refDir (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (j : ℕ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) (g : Finset ℕ → ℝ) :
    refEnergy I ε δ j w g =
      refDir I ε δ j w g / (2 * (pSmall I ε δ : ℝ) ^ 2 * refLamTot I ε δ j w) := by
  classical
  set X := chainStates I ε δ
  set D := 2 * (pSmall I ε δ : ℝ) ^ 2 * refLamTot I ε δ j w
  have hE : refEnergy I ε δ j w g = ∑ S ∈ X, ∑ T ∈ X,
      refPi I ε δ j w S * refPk I ε δ j w S T * (g S * (g S - g T)) := by
    unfold refEnergy
    refine Finset.sum_congr rfl fun S hS => ?_
    have hrow : ∑ T ∈ X, refPk I ε δ j w S T = 1 := red_refPk_sum_one I ε δ hp j w S hS
    have : g S - ∑ T ∈ X, refPk I ε δ j w S T * g T =
        ∑ T ∈ X, refPk I ε δ j w S T * (g S - g T) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hrow, one_mul]
    rw [this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => by ring
  have hE' : refEnergy I ε δ j w g = ∑ S ∈ X, ∑ T ∈ X,
      refPi I ε δ j w S * refPk I ε δ j w S T * (g T * (g T - g S)) := by
    rw [hE, Finset.sum_comm]
    refine Finset.sum_congr rfl fun S hS => Finset.sum_congr rfl fun T hT => ?_
    rw [refStep_reversible I ε δ hp j w hgood T S hT hS]
  have hterm : ∀ S ∈ X, ∀ T ∈ X,
      refPi I ε δ j w S * refPk I ε δ j w S T * (g S - g T) ^ 2 =
        (if exchNbr S T then
          min (refLam I ε δ S j w) (refLam I ε δ T j w) * (g S - g T) ^ 2 else 0) / D := by
    intro S hS T hT
    by_cases hTS : T = S
    · subst hTS; simp
    · rw [red_pi_pk_ne I ε δ hp j w hgood S T hS hT hTS]
      split_ifs <;> ring
  have h2 : 2 * refEnergy I ε δ j w g = (2 * refDir I ε δ j w g) / D := by
    have : 2 * refEnergy I ε δ j w g = ∑ S ∈ X, ∑ T ∈ X,
        refPi I ε δ j w S * refPk I ε δ j w S T * (g S - g T) ^ 2 := by
      rw [two_mul]
      nth_rewrite 1 [hE]
      rw [hE', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun T _ => by ring
    rw [this, Finset.sum_congr rfl fun S hS => Finset.sum_congr rfl fun T hT => hterm S hS T hT]
    simp only [← Finset.sum_div]
    unfold refDir
    ring
  linarith [show refDir I ε δ j w g / D = (2 * refDir I ε δ j w g) / D / 2 by ring]

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `refEnergy_eq_refDir` via row sums, `refStep_reversible`, and the edge weight `red_pi_pk_ne`
-/
