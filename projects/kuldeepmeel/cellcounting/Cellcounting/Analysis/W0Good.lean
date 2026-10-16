import Cellcounting.Analysis.RefExperiment
import Cellcounting.Analysis.TransMassEqCpart

/-!
# The initial multipliers are good (`lem:initialization`)

`w^(0)_il = C(0)/c_il(0)` exactly (`algorithm.tex:94-133`): at parameter zero
`h_0 = M_f`, so `C(0) = M_f ∏_s (b_s + 1)` and `c_il(0)` is `M_f` times a product
of per-cell brackets equal to `b_s + 1`, `1`, `(b_s + 1)(b_s + 2)/6` or
`(b_s + 1)/6`.  In particular `w^(0)` satisfies `eq:good-multipliers` at `j = 0`.

The defect class `A_il` is parametrised by the subsets `T` of the remaining pairs
`R = [0, p) \ {i, l}` (`w0_sum_defect`); the sum over `T` factors over the cells
(`w0_cDef_zero`, via the block decomposition of `TransMassEqCpart`), and each cell
bracket is evaluated in closed form (`w0_bracket`).
-/

namespace Cellcounting.Analysis

open Pseudocode Finset

/-- INTERNAL: a subset `T ⊆ U` is the family of its blocks `T ∩ c⁻¹(s)`, `s < n`, when
`c` maps `U` below `n` (`sum_powerset_eq_sum_pi_filter` for a general ground set `U`). -/
theorem w0_sum_powerset_pi (U : Finset ℕ) (n : ℕ) (c : ℕ → ℕ) (hc : ∀ i ∈ U, c i < n)
    (G : (Fin n → Finset ℕ) → ℝ) :
    ∑ T ∈ U.powerset, G (fun s => T.filter (fun i => c i = s)) =
      ∑ F ∈ Fintype.piFinset (fun s : Fin n => (U.filter (fun i => c i = s)).powerset),
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
      exact ⟨⟨c i, hc i (hT h)⟩, h, rfl⟩
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

/-- INTERNAL: `S ∈ A_il` iff pair `i` is the only empty pair and `l` the only full one.
TEXLINE: sections/signatures.tex:13-41 -/
theorem w0_kind_eq_defect_iff (I : Instance) (ε δ : ℚ) (S : Finset ℕ) (i l : ℕ) :
    kind I ε δ S = .defect i l ↔
      (range (pSmall I ε δ)).filter (fun k => 2 * k ∉ S ∧ 2 * k + 1 ∉ S) = {i} ∧
      (range (pSmall I ε δ)).filter (fun k => 2 * k ∈ S ∧ 2 * k + 1 ∈ S) = {l} := by
  unfold kind
  simp only
  split_ifs with hE hF hEF
  · simp only [false_iff, not_and]
    intro h; rw [h] at hE; simp at hE
  · simp only [false_iff, not_and]
    intro h; rw [h] at hE; simp at hE
  · obtain ⟨a, ha⟩ := card_eq_one.1 hEF.1
    obtain ⟨b, hb⟩ := card_eq_one.1 hEF.2
    rw [ha, hb]
    simp [Program.Kind.defect.injEq, singleton_inj]
  · simp only [false_iff, not_and]
    intro h1 h2; rw [h1, h2] at hEF; simp at hEF

/-- INTERNAL: the defect state of `A_il` whose remaining pairs `T ⊆ R` use their row
elements: rows `T ∪ {l}`, columns `(R \ T) ∪ {l}`.
TEXLINE: sections/algorithm.tex:92-99 -/
def w0DefEmb (R : Finset ℕ) (l : ℕ) (T : Finset ℕ) : Finset ℕ :=
  (insert l T).image (fun k => 2 * k) ∪ (insert l (R \ T)).image (fun k => 2 * k + 1)

/-- INTERNAL: the row element `2k` is in `w0DefEmb R l T` iff `k = l` or `k ∈ T`. -/
theorem w0_two_mul_mem (R : Finset ℕ) (l : ℕ) (T : Finset ℕ) (k : ℕ) :
    2 * k ∈ w0DefEmb R l T ↔ k = l ∨ k ∈ T := by
  simp only [w0DefEmb, mem_union, mem_image, mem_insert]
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨a, -, h⟩)
    · obtain rfl : a = k := by omega
      exact ha
    · omega
  · intro h; exact Or.inl ⟨k, h, rfl⟩

/-- INTERNAL: the column element `2k + 1` is in `w0DefEmb R l T` iff `k = l` or
`k ∈ R \ T`. -/
theorem w0_two_mul_add_one_mem (R : Finset ℕ) (l : ℕ) (T : Finset ℕ) (k : ℕ) :
    2 * k + 1 ∈ w0DefEmb R l T ↔ k = l ∨ k ∈ R \ T := by
  simp only [w0DefEmb, mem_union, mem_image, mem_insert]
  constructor
  · rintro (⟨a, -, h⟩ | ⟨a, ha, h⟩)
    · omega
    · obtain rfl : a = k := by omega
      exact ha
  · intro h; exact Or.inr ⟨k, h, rfl⟩

open Classical in
/-- INTERNAL: the defect class `A_il` is in bijection with the subsets `T` of the
remaining pairs `R = [0, p) \ {i, l}` (the pairs using their row elements).
TEXLINE: sections/algorithm.tex:92-99 -/
theorem w0_sum_defect (I : Instance) (ε δ : ℚ) (i l : ℕ) (hi : i < pSmall I ε δ)
    (hl : l < pSmall I ε δ) (hil : i ≠ l) (f : Finset ℕ → ℝ) :
    ∑ S ∈ (refStates I ε δ).filter (fun S => kind I ε δ S = .defect i l), f S =
      ∑ T ∈ (((range (pSmall I ε δ)).erase i).erase l).powerset,
        f (w0DefEmb (((range (pSmall I ε δ)).erase i).erase l) l T) := by
  set p := pSmall I ε δ
  set R := ((range p).erase i).erase l with hR
  have hmemR : ∀ k, k ∈ R ↔ k ≠ l ∧ k ≠ i ∧ k < p := by
    intro k; simp [hR]
  have hleft : ∀ S ∈ (refStates I ε δ).filter (fun S => kind I ε δ S = .defect i l),
      w0DefEmb R l (R.filter (fun k => 2 * k ∈ S)) = S := by
    intro S hS
    simp only [mem_filter, refStates, mem_powerset] at hS
    obtain ⟨hsub, hk⟩ := hS
    rw [w0_kind_eq_defect_iff] at hk
    obtain ⟨hE, hF⟩ := hk
    have hE' : ∀ k < p, (2 * k ∉ S ∧ 2 * k + 1 ∉ S ↔ k = i) := by
      intro k hk
      have := congrArg (k ∈ ·) hE
      simpa [show k < pSmall I ε δ from hk] using this
    have hF' : ∀ k < p, (2 * k ∈ S ∧ 2 * k + 1 ∈ S ↔ k = l) := by
      intro k hk
      have := congrArg (k ∈ ·) hF
      simpa [show k < pSmall I ε δ from hk] using this
    ext e
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' e
    · rw [w0_two_mul_mem, mem_filter, hmemR]
      constructor
      · rintro (rfl | ⟨-, h⟩)
        · exact ((hF' k hl).2 rfl).1
        · exact h
      · intro h
        have hk : k < p := by have := mem_range.1 (hsub h); omega
        by_cases hkl : k = l
        · exact Or.inl hkl
        · refine Or.inr ⟨⟨hkl, fun hki => ?_, hk⟩, h⟩
          exact ((hE' k hk).2 hki).1 h
    · rw [w0_two_mul_add_one_mem, mem_sdiff, mem_filter, hmemR]
      constructor
      · rintro (rfl | ⟨⟨hkl, hki, hk⟩, h⟩)
        · exact ((hF' k hl).2 rfl).2
        · push Not at h
          have h2 := h ⟨hkl, hki, hk⟩
          by_contra h3
          exact hki ((hE' k hk).1 ⟨h2, h3⟩)
      · intro h
        have hk : k < p := by have := mem_range.1 (hsub h); omega
        by_cases hkl : k = l
        · exact Or.inl hkl
        · have hki : k ≠ i := fun hki => ((hE' k hk).2 hki).2 h
          refine Or.inr ⟨⟨hkl, hki, hk⟩, fun ⟨_, h2⟩ => hkl ((hF' k hk).1 ⟨h2, h⟩)⟩
  apply Finset.sum_nbij' (fun S => R.filter (fun k => 2 * k ∈ S)) (w0DefEmb R l)
  · intro S _
    simp only [mem_powerset]
    exact filter_subset _ _
  · intro T hT
    simp only [mem_powerset] at hT
    simp only [mem_filter, refStates, mem_powerset]
    refine ⟨?_, ?_⟩
    · intro e he
      rw [mem_range]
      simp only [w0DefEmb, mem_union, mem_image, mem_insert, mem_sdiff] at he
      rcases he with ⟨a, rfl | ha, rfl⟩ | ⟨a, rfl | ⟨ha, -⟩, rfl⟩
      · omega
      · have := (hmemR a).1 (hT ha); omega
      · omega
      · have := (hmemR a).1 ha; omega
    · rw [w0_kind_eq_defect_iff]
      constructor
      · ext k
        simp only [mem_filter, mem_range, w0_two_mul_mem, w0_two_mul_add_one_mem, mem_sdiff,
          mem_singleton]
        constructor
        · rintro ⟨hk, h1, h2⟩
          by_contra hki
          by_cases hkT : k ∈ T
          · exact h1 (Or.inr hkT)
          · exact h2 (Or.inr ⟨(hmemR k).2 ⟨fun h => h1 (Or.inl h), hki, hk⟩, hkT⟩)
        · rintro rfl
          refine ⟨hi, ?_, ?_⟩
          · rintro (h | h)
            · exact hil h
            · exact ((hmemR _).1 (hT h)).2.1 rfl
          · rintro (h | ⟨h, -⟩)
            · exact hil h
            · exact ((hmemR _).1 h).2.1 rfl
      · ext k
        simp only [mem_filter, mem_range, w0_two_mul_mem, w0_two_mul_add_one_mem, mem_sdiff,
          mem_singleton]
        constructor
        · rintro ⟨-, h1 | h1, h2 | ⟨-, h2⟩⟩
          · exact h1
          · exact h1
          · exact h2
          · exact absurd h1 h2
        · rintro rfl; exact ⟨hl, Or.inl rfl, Or.inl rfl⟩
  · exact hleft
  · intro T hT
    simp only [mem_powerset] at hT
    ext k
    rw [mem_filter, w0_two_mul_mem]
    constructor
    · rintro ⟨hkR, rfl | h⟩
      · exact absurd rfl ((hmemR _).1 hkR).1
      · exact h
    · intro h; exact ⟨hT h, Or.inr h⟩
  · intro S hS; rw [hleft S hS]

/-- INTERNAL: the small-count profile of the defect state of `T`:
`x_s = |T ∩ s⁻¹(s)| + v_s` and `y_s = |R ∩ s⁻¹(s)| - |T ∩ s⁻¹(s)| + v_s`.
TEXLINE: sections/algorithm.tex:92-99 -/
theorem w0_profile_defEmb (I : Instance) (ε δ : ℚ) (i l : ℕ) (hl : l < pSmall I ε δ)
    (T : Finset ℕ) (hT : T ⊆ ((range (pSmall I ε δ)).erase i).erase l) :
    profile I ε δ (w0DefEmb (((range (pSmall I ε δ)).erase i).erase l) l T) =
      (fun s => (T.filter (fun k => pairCell I ε δ k = s)).card +
          (if pairCell I ε δ l = s then 1 else 0),
        fun s => ((((range (pSmall I ε δ)).erase i).erase l).filter
            (fun k => pairCell I ε δ k = s)).card -
          (T.filter (fun k => pairCell I ε δ k = s)).card +
          (if pairCell I ε δ l = s then 1 else 0)) := by
  set p := pSmall I ε δ
  set R := ((range p).erase i).erase l with hR
  have hlT : l ∉ T := fun h => by have := hT h; simp [hR] at this
  have hRp : R ⊆ range p := fun k hk => by simp [hR] at hk; exact mem_range.2 hk.2.2
  unfold profile
  refine Prod.ext (funext fun s => ?_) (funext fun s => ?_)
  · simp only
    have : (range p).filter (fun k => pairCell I ε δ k = s ∧ 2 * k ∈ w0DefEmb R l T) =
        (insert l T).filter (fun k => pairCell I ε δ k = s) := by
      ext k
      simp only [mem_filter, mem_range, w0_two_mul_mem, mem_insert]
      constructor
      · rintro ⟨-, h1, h2⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩
        refine ⟨?_, h1, h2⟩
        rcases h2 with rfl | h2
        · exact hl
        · exact mem_range.1 (hRp (hT h2))
    rw [this, filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (fun h' => hlT (mem_filter.1 h').1)]
    · simp
  · simp only
    have : (range p).filter (fun k => pairCell I ε δ k = s ∧ 2 * k + 1 ∈ w0DefEmb R l T) =
        (insert l (R \ T)).filter (fun k => pairCell I ε δ k = s) := by
      ext k
      simp only [mem_filter, mem_range, w0_two_mul_add_one_mem, mem_insert]
      constructor
      · rintro ⟨-, h1, h2⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩
        refine ⟨?_, h1, h2⟩
        rcases h2 with rfl | h2
        · exact hl
        · exact mem_range.1 (hRp (mem_sdiff.1 h2).1)
    have hsd : (R \ T).filter (fun k => pairCell I ε δ k = s) =
        R.filter (fun k => pairCell I ε δ k = s) \ T.filter (fun k => pairCell I ε δ k = s) := by
      ext k; simp only [mem_filter, mem_sdiff]; tauto
    have hsub : T.filter (fun k => pairCell I ε δ k = s) ⊆
        R.filter (fun k => pairCell I ε δ k = s) := filter_subset_filter _ hT
    have hlR : l ∉ R \ T := by simp [hR]
    rw [this, filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (fun h' => hlR (mem_filter.1 h').1), hsd,
        card_sdiff_of_subset hsub]
    · rw [hsd, card_sdiff_of_subset hsub]; simp

/-- INTERNAL: `n_s + u_s + v_s = b_s`: cell `s` holds `b_s` pairs, `u_s = [s(i) = s]`
of them the hole and `v_s = [s(l) = s]` the full pair.
TEXLINE: sections/algorithm.tex:92-96 -/
theorem w0_card_block (I : Instance) (ε δ : ℚ) (i l : ℕ) (hi : i < pSmall I ε δ)
    (hl : l < pSmall I ε δ) (hil : i ≠ l) (s : ℕ) :
    ((((range (pSmall I ε δ)).erase i).erase l).filter (fun k => pairCell I ε δ k = s)).card +
      (if pairCell I ε δ i = s then 1 else 0) + (if pairCell I ε δ l = s then 1 else 0) =
      smallB I ε δ s := by
  rw [smallB_eq_card, filter_erase, filter_erase]
  set E := (range (pSmall I ε δ)).filter (fun k => pairCell I ε δ k = s)
  have hmem : ∀ k, k ∈ E ↔ k < pSmall I ε δ ∧ pairCell I ε δ k = s := by
    intro k; simp [E]
  by_cases h1 : pairCell I ε δ i = s <;> by_cases h2 : pairCell I ε δ l = s
  · have hiE : i ∈ E := (hmem i).2 ⟨hi, h1⟩
    have hlE : l ∈ E.erase i := mem_erase.2 ⟨Ne.symm hil, (hmem l).2 ⟨hl, h2⟩⟩
    rw [card_erase_of_mem hlE, card_erase_of_mem hiE]
    simp only [h1, h2, ↓reduceIte]
    have : ({i, l} : Finset ℕ) ⊆ E := by
      intro k hk; simp only [mem_insert, mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hiE
      · exact (mem_erase.1 hlE).2
    have := card_le_card this
    rw [card_pair hil] at this
    omega
  · have hiE : i ∈ E := (hmem i).2 ⟨hi, h1⟩
    have hlE : l ∉ E.erase i := fun h => h2 ((hmem l).1 (mem_erase.1 h).2).2
    rw [erase_eq_of_notMem hlE, card_erase_of_mem hiE]
    simp only [h1, h2, ↓reduceIte]
    have := card_pos.2 ⟨i, hiE⟩
    omega
  · have hiE : i ∉ E := fun h => h1 ((hmem i).1 h).2
    have hlE : l ∈ E := (hmem l).2 ⟨hl, h2⟩
    rw [erase_eq_of_notMem hiE, card_erase_of_mem hlE]
    simp only [h1, h2, ↓reduceIte]
    have := card_pos.2 ⟨l, hlE⟩
    omega
  · have hiE : i ∉ E := fun h => h1 ((hmem i).1 h).2
    have hlE : l ∉ E := fun h => h2 ((hmem l).1 h).2
    rw [erase_eq_of_notMem hiE, erase_eq_of_notMem hlE]
    simp only [h1, h2, ↓reduceIte, add_zero]

/-- INTERNAL: `h_0 = M_f` (every penalty term is `2^0`). -/
theorem w0_hWeight_zero (I : Instance) (ε δ : ℚ) (x y : ℕ → ℕ) :
    hWeight I ε δ 0 x y = (Mf I ε δ : ℝ) := by
  simp [hWeight, card_freeBox]

/-- INTERNAL: `n_s = |R ∩ s⁻¹(s)|`, `R = [0, p) \ {i, l}`: the singly occupied pairs
of cell `s` in `A_il`.
TEXLINE: sections/algorithm.tex:92-96 -/
noncomputable def w0Blk (I : Instance) (ε δ : ℚ) (i l s : ℕ) : ℕ :=
  ((((range (pSmall I ε δ)).erase i).erase l).filter (fun k => pairCell I ε δ k = s)).card

/-- INTERNAL: `v_s = [s(l) = s]`.
TEXLINE: sections/algorithm.tex:92-96 -/
noncomputable def w0V (I : Instance) (ε δ : ℚ) (l s : ℕ) : ℕ :=
  if pairCell I ε δ l = s then 1 else 0

/-- INTERNAL: `eq:alg-initial-defect`: `c_il(0) = M_f ∏_s (1/b_s!) Σ_k C(n_s,k)(k+v_s)!(n_s-k+v_s)!`.
TEXLINE: sections/algorithm.tex:100-108 -/
theorem w0_cDef_zero (I : Instance) (ε δ : ℚ) (i l : ℕ) (hi : i < pSmall I ε δ)
    (hl : l < pSmall I ε δ) (hil : i ≠ l) :
    cDef I ε δ 0 i l = (Mf I ε δ : ℝ) * ∏ s ∈ range (nSmall I ε δ),
      ∑ k ∈ range (w0Blk I ε δ i l s + 1), ((w0Blk I ε δ i l s).choose k : ℝ) *
        (((k + w0V I ε δ l s).factorial : ℝ) *
          ((w0Blk I ε δ i l s - k + w0V I ε δ l s).factorial : ℝ) /
          ((smallB I ε δ s).factorial : ℝ)) := by
  classical
  set p := pSmall I ε δ
  set R := ((range p).erase i).erase l with hR
  set φ : ℕ → ℕ → ℝ := fun s k => ((k + w0V I ε δ l s).factorial : ℝ) *
    ((w0Blk I ε δ i l s - k + w0V I ε δ l s).factorial : ℝ) /
      ((smallB I ε δ s).factorial : ℝ) with hφ
  have hc : ∀ k ∈ R, pairCell I ε δ k < nSmall I ε δ := by
    intro k hk
    simp only [hR, mem_erase, mem_range] at hk
    exact pairCell_lt I ε δ hk.2.2
  have hper : ∀ T ∈ R.powerset, fWeight I ε δ 0 (w0DefEmb R l T) =
      (Mf I ε δ : ℝ) * ∏ s : Fin (nSmall I ε δ),
        φ s (T.filter (fun k => pairCell I ε δ k = s)).card := by
    intro T hT
    rw [mem_powerset] at hT
    rw [fWeight, w0_profile_defEmb I ε δ i l hl T hT, w0_hWeight_zero,
      ← Fin.prod_univ_eq_prod_range]
    simp only [hφ, w0V, w0Blk, mul_div_assoc]
  unfold cDef
  rw [w0_sum_defect I ε δ i l hi hl hil, sum_congr rfl hper]
  have h1 := w0_sum_powerset_pi R (nSmall I ε δ) (pairCell I ε δ) hc
    (fun F => (Mf I ε δ : ℝ) * ∏ s : Fin (nSmall I ε δ), φ s (F s).card)
  simp only at h1
  rw [h1]
  have h2 := sum_pi_powerset_card (nSmall I ε δ)
    (fun s => R.filter (fun k => pairCell I ε δ k = s))
    (fun x => (Mf I ε δ : ℝ) * ∏ s : Fin (nSmall I ε δ), φ s (x s))
  simp only at h2
  rw [h2]
  have h3 : ∀ x ∈ Fintype.piFinset (fun s : Fin (nSmall I ε δ) =>
      range ((R.filter (fun k => pairCell I ε δ k = (s : ℕ))).card + 1)),
      (∏ s : Fin (nSmall I ε δ),
        (((R.filter (fun k => pairCell I ε δ k = (s : ℕ))).card.choose (x s) : ℕ) : ℝ)) *
        ((Mf I ε δ : ℝ) * ∏ s : Fin (nSmall I ε δ), φ s (x s)) =
      (Mf I ε δ : ℝ) * ∏ s : Fin (nSmall I ε δ),
        (((R.filter (fun k => pairCell I ε δ k = (s : ℕ))).card.choose (x s) : ℕ) : ℝ) *
          φ s (x s) := by
    intro x _
    rw [prod_mul_distrib]; ring
  rw [sum_congr rfl h3, ← mul_sum]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (fun s => ∑ k ∈ range (w0Blk I ε δ i l s + 1),
    ((w0Blk I ε δ i l s).choose k : ℝ) * (((k + w0V I ε δ l s).factorial : ℝ) *
      ((w0Blk I ε δ i l s - k + w0V I ε δ l s).factorial : ℝ) /
      ((smallB I ε δ s).factorial : ℝ)))]
  exact (prod_univ_sum (fun s : Fin (nSmall I ε δ) =>
    range ((R.filter (fun k => pairCell I ε δ k = (s : ℕ))).card + 1))
    (fun s k => (((R.filter (fun k => pairCell I ε δ k = (s : ℕ))).card.choose k : ℕ) : ℝ) *
      φ s k)).symm

/-- INTERNAL: `Σ_{k<m} (k + 1)(c - k)` in closed form. -/
theorem w0_sum_lin (c : ℝ) (m : ℕ) :
    ∑ k ∈ range m, ((k : ℝ) + 1) * (c - k) =
      c * (m * (m + 1) / 2) - ((m : ℝ) - 1) * m * (m + 1) / 3 := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

/-- INTERNAL: `Σ_k C(n,k) k! (n-k)! = (n + 1) n!`. -/
theorem w0_cell_sum0 (n : ℕ) :
    ∑ k ∈ range (n + 1), ((n.choose k : ℝ) * (((k + 0).factorial : ℝ) * ((n - k + 0).factorial : ℝ))) =
      (n + 1) * (n.factorial : ℝ) := by
  have : ∀ k ∈ range (n + 1), ((n.choose k : ℝ) * (((k + 0).factorial : ℝ) * ((n - k + 0).factorial : ℝ))) = n.factorial := by
    intro k hk
    have hk : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
    rw [← Nat.choose_mul_factorial_mul_factorial hk]; push_cast; simp only [add_zero]; ring
  rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul]; push_cast; ring

/-- INTERNAL: `Σ_k C(n,k) (k+1)! (n-k+1)! = n! (n+1)(n+2)(n+3)/6`. -/
theorem w0_cell_sum1 (n : ℕ) :
    ∑ k ∈ range (n + 1), ((n.choose k : ℝ) * (((k + 1).factorial : ℝ) * ((n - k + 1).factorial : ℝ))) =
      (n.factorial : ℝ) * ((n + 1) * (n + 2) * (n + 3) / 6) := by
  have : ∀ k ∈ range (n + 1), ((n.choose k : ℝ) * (((k + 1).factorial : ℝ) * ((n - k + 1).factorial : ℝ))) =
      n.factorial * (((k : ℝ) + 1) * (((n : ℝ) + 1) - k)) := by
    intro k hk
    have hk : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
    rw [← Nat.choose_mul_factorial_mul_factorial hk, Nat.factorial_succ, Nat.factorial_succ]
    push_cast [hk]; ring
  rw [sum_congr rfl this, ← mul_sum, w0_sum_lin]; push_cast; ring

/-- INTERNAL: pull the common `b!` out of a bracket sum. -/
theorem w0_cell_div (n v b : ℕ) :
    ∑ k ∈ range (n + 1), ((n.choose k : ℝ) * (((k + v).factorial : ℝ) *
      ((n - k + v).factorial : ℝ) / (b.factorial : ℝ))) =
    (∑ k ∈ range (n + 1), ((n.choose k : ℝ) * (((k + v).factorial : ℝ) *
      ((n - k + v).factorial : ℝ)))) / (b.factorial : ℝ) := by
  rw [sum_div]; exact sum_congr rfl fun k _ => by ring

/-- INTERNAL: the local bracket of `c_il(0)` divided by `b_s + 1`.
TEXLINE: sections/algorithm.tex:117-122 -/
noncomputable def w0Rho (I : Instance) (ε δ : ℚ) (i l s : ℕ) : ℝ :=
  if pairCell I ε δ i = s ∧ pairCell I ε δ l = s then 1 / 6
  else (if pairCell I ε δ i = s then 1 / ((smallB I ε δ s : ℝ) + 1) else 1) *
    (if pairCell I ε δ l = s then ((smallB I ε δ s : ℝ) + 2) / 6 else 1)

/-- INTERNAL: the local bracket of `eq:alg-initial-defect` is `b_s + 1`, `1`,
`(b_s+1)(b_s+2)/6` or `(b_s+1)/6` (neither pair, only the hole, only the full pair, both).
TEXLINE: sections/algorithm.tex:117-122 -/
theorem w0_bracket (I : Instance) (ε δ : ℚ) (i l : ℕ) (hi : i < pSmall I ε δ)
    (hl : l < pSmall I ε δ) (hil : i ≠ l) (s : ℕ) :
    ∑ k ∈ range (w0Blk I ε δ i l s + 1), ((w0Blk I ε δ i l s).choose k : ℝ) *
        (((k + w0V I ε δ l s).factorial : ℝ) *
          ((w0Blk I ε δ i l s - k + w0V I ε δ l s).factorial : ℝ) /
          ((smallB I ε δ s).factorial : ℝ)) =
      ((smallB I ε δ s : ℝ) + 1) * w0Rho I ε δ i l s := by
  have hb : w0Blk I ε δ i l s + (if pairCell I ε δ i = s then 1 else 0) +
      (if pairCell I ε δ l = s then 1 else 0) = smallB I ε δ s :=
    w0_card_block I ε δ i l hi hl hil s
  rw [w0_cell_div]
  unfold w0Rho
  unfold w0V
  generalize w0Blk I ε δ i l s = n at hb ⊢
  by_cases h1 : pairCell I ε δ i = s <;> by_cases h2 : pairCell I ε δ l = s <;>
    simp only [h1, h2, ↓reduceIte, and_self, and_true, and_false, add_zero] at hb ⊢
  · rw [← hb, w0_cell_sum1]
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · have := w0_cell_sum0 n
    simp only [add_zero] at this
    rw [this, ← hb, Nat.factorial_succ]
    push_cast
    field_simp
  · rw [← hb, w0_cell_sum1, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · have := w0_cell_sum0 n
    simp only [add_zero] at this
    rw [this, ← hb]
    field_simp

/-- INTERNAL: `c_il(0) = C(0) ∏_s ρ_s`.
TEXLINE: sections/algorithm.tex:100-122 -/
theorem w0_cDef_eq (I : Instance) (ε δ : ℚ) (i l : ℕ) (hi : i < pSmall I ε δ)
    (hl : l < pSmall I ε δ) (hil : i ≠ l) :
    cDef I ε δ 0 i l = Cpart I ε δ 0 * ∏ s ∈ range (nSmall I ε δ), w0Rho I ε δ i l s := by
  rw [w0_cDef_zero I ε δ i l hi hl hil, prod_congr rfl fun s _ => w0_bracket I ε δ i l hi hl hil s,
    prod_mul_distrib, Cpart_zero, C0]
  push_cast
  ring

/-- INTERNAL: `w^(0)_il ∏_s ρ_s = 1`, i.e. `w^(0)_il = C(0)/c_il(0)` (the equivalent
initializer).
TEXLINE: sections/algorithm.tex:122-133 -/
theorem w0_rho_prod (I : Instance) (ε δ : ℚ) (i l : ℕ) (hi : i < pSmall I ε δ)
    (hl : l < pSmall I ε δ) (hil : i ≠ l) :
    0 < ∏ s ∈ range (nSmall I ε δ), w0Rho I ε δ i l s ∧
      (∏ s ∈ range (nSmall I ε δ), w0Rho I ε δ i l s) * (w0 I ε δ i l : ℝ) = 1 := by
  have hsi := pairCell_lt I ε δ hi
  have hsl := pairCell_lt I ε δ hl
  have hw : w0 I ε δ i l = if pairCell I ε δ i = pairCell I ε δ l then 6
      else 6 * ((smallB I ε δ (pairCell I ε δ i) + 1 : ℕ) : ℚ) /
        ((smallB I ε δ (pairCell I ε δ l) + 2 : ℕ) : ℚ) := by
    simp [w0, hi, hl, hil]
  rw [hw]
  split_ifs with hs
  · have hρ : ∀ s, w0Rho I ε δ i l s = if pairCell I ε δ i = s then 1 / 6 else 1 := by
      intro s
      unfold w0Rho
      by_cases h : pairCell I ε δ i = s
      · simp [h, ← hs]
      · have h' : ¬ pairCell I ε δ l = s := hs ▸ h
        simp [h, h']
    simp only [hρ, prod_ite_eq, mem_range.2 hsi, ↓reduceIte]
    norm_num
  · have hρ : ∀ s, w0Rho I ε δ i l s =
        (if pairCell I ε δ i = s then 1 / ((smallB I ε δ s : ℝ) + 1) else 1) *
          (if pairCell I ε δ l = s then ((smallB I ε δ s : ℝ) + 2) / 6 else 1) := by
      intro s
      unfold w0Rho
      have : ¬ (pairCell I ε δ i = s ∧ pairCell I ε δ l = s) := fun h => hs (h.1.trans h.2.symm)
      simp only [this, ↓reduceIte]
    simp only [hρ, prod_mul_distrib, prod_ite_eq, mem_range.2 hsi, mem_range.2 hsl, ↓reduceIte]
    constructor
    · positivity
    · push_cast
      field_simp

/-- **Initialization is good** (`lem:initialization`): `w^(0)` satisfies
`eq:good-multipliers` at parameter `0` (with ratio exactly one).
PAPER: sections/algorithm.tex:94-133 -/
theorem w0_good (I : Instance) (ε δ : ℚ) : goodMult I ε δ 0 (w0 I ε δ) := by
  intro i hi l hl hil
  obtain ⟨hP, hPw⟩ := w0_rho_prod I ε δ i l hi hl hil
  rw [w0_cDef_eq I ε δ i l hi hl hil]
  have hC := Cpart_pos I ε δ 0
  set P := ∏ s ∈ range (nSmall I ε δ), w0Rho I ε δ i l s
  set C := Cpart I ε δ 0
  have hw : (w0 I ε δ i l : ℝ) = 1 / P := by
    field_simp; linarith
  rw [hw]
  constructor
  · rw [div_le_div_iff₀ (by positivity) hP]; nlinarith
  · rw [div_le_div_iff₀ hP (by positivity)]; nlinarith

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r6 · proved · `w0_good` from the exact identity `w^(0)_il = C(0)/c_il(0)` (`w0_rho_prod`)
-/
