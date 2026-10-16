import Cellcounting.Analysis.TransportDirichlet
import Cellcounting.Model.Prior
import Cellcounting.Analysis.SelPairs
import Cellcounting.Analysis.SlotTransport
import Cellcounting.Analysis.FWeightOmission
import Cellcounting.Analysis.DefectComparison
import Cellcounting.Analysis.DefectCliqueLe

/-!
# Defect means (`lem:defect-mean`, `transport.tex:440-506`)

For good multipliers, every real `g` on `X` and every defect type `il`, some
conditional transversal mean `g'` (the `μ`-mean of `g` on a joint choice in pairs
`i, l` of transversal mass at least `C/4`) satisfies
`(ḡ_il - g')² ≤ (C_d / C) 𝔇(g)` and `(g' - E_μ g)² ≤ 4 Var_μ(g)`, with
`C_d = 8 + 32 p q³` (`CdParam`).

The proof follows the paper.  The four joint choices `(a_i, a_l)` partition the
transversals (`dm_sum_four`), so one has mass `z ≥ C/4`.  The one-hole transport
inequality `slot_transport` is applied with the fixed inclusion `{a_l}`, singleton
slots `a_i`, `b_l'` (the mate of `a_l`) and the other pairs `R = [0, p) \ {i, l}` as
ordinary slots: a hole at `a_i` is the whole class `A_il` (`s₀ = c_il`,
`W = w_il`), a hole at `b_l'` the selected transversals (`s₁ = z`, `W = 1`), a hole at
`t` a state of type `tl` (`W = w_tl`); the doubled-slot masses are masses of states of
type `it`, so `v_t ≤ c_it` (`dm_double_le`).  The omission signature of `f_j` is
`fWeight_omission`; the one-hole energy is at most `𝔇(g)` (`defect_clique_le`); the
coefficient is at most `C_d / C` by the good-multiplier bounds and
`defect_comparison` (`eq:defect-comparison`).  The second bound is conditional
Cauchy–Schwarz on the selected class (`dm_class_le_trans`).
-/

namespace Cellcounting.Analysis

open Pseudocode Finset

/-- INTERNAL: `[0, p) \ {i, l, t}` as a list without repetition. -/
theorem dm_toFinset_erase3 (p i l t : ℕ) :
    ((((List.range p).erase i).erase l).erase t).toFinset =
      (((range p).erase i).erase l).erase t := by
  ext k
  rw [List.mem_toFinset, (((List.nodup_range).erase i).erase l).mem_erase_iff,
    ← List.mem_toFinset, dm_toFinset_erase_erase]
  simp only [mem_erase]

/-- INTERNAL: the doubled-slot mass is at most the defect mass: `v_t ≤ c_it`.
TEXLINE: sections/transport.tex:466-470 -/
theorem dm_double_le (I : Instance) (ε δ : ℚ) (j : ℕ) (i l t : ℕ) (hi : i < pSmall I ε δ)
    (hl : l < pSmall I ε δ) (hil : i ≠ l) (ht : t ∈ ((range (pSmall I ε δ)).erase i).erase l)
    (al : ℕ) (hal : al = 2 * l ∨ al = 2 * l + 1) :
    chSum ((((List.range (pSmall I ε δ)).erase i).erase l).erase t)
        (fun c => fWeight I ε δ j (insert (2 * t) (insert (2 * t + 1) ({al} ∪ c)))) ≤
      cDef I ε δ j i t := by
  classical
  rw [chSum_eq_sum_selPairs (((List.nodup_range.erase i).erase l).erase t),
    dm_toFinset_erase3]
  set R := ((range (pSmall I ε δ)).erase i).erase l with hRdef
  have ht' := (dm_mem_R _ _ _ _).1 ht
  set φ : Finset ℕ → Finset ℕ :=
    fun A => insert (2 * t) (insert (2 * t + 1) {al}) ∪ selPairs (R.erase t) A with hφ
  have hrw : ∀ A, insert (2 * t) (insert (2 * t + 1) ({al} ∪ selPairs (R.erase t) A)) = φ A := by
    intro A; simp only [hφ, insert_union]
  simp only [hrw]
  have hinj : Set.InjOn φ ((R.erase t).powerset : Set (Finset ℕ)) := by
    intro A hA A' hA' hAA
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at hA hA'
    ext k
    have h := congrArg (2 * k ∈ ·) hAA
    simp only [hφ, mem_union, mem_insert, mem_singleton, two_mul_mem_selPairs] at h
    constructor
    · intro hk
      have := (dm_mem_Rt _ _ _ _ _).1 (hA hk)
      have h' := (iff_of_eq h).1 (Or.inr hk)
      rcases h' with (h' | h' | h') | h'
      · omega
      · omega
      · omega
      · exact h'
    · intro hk
      have := (dm_mem_Rt _ _ _ _ _).1 (hA' hk)
      have h' := (iff_of_eq h).2 (Or.inr hk)
      rcases h' with (h' | h' | h') | h'
      · omega
      · omega
      · omega
      · exact h'
  unfold cDef
  rw [← Finset.sum_image (f := fWeight I ε δ j) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun S _ _ => (td_fWeight_pos I ε δ j S).le
  intro S hS
  obtain ⟨A, hA, rfl⟩ := mem_image.1 hS
  have hA := mem_powerset.1 hA
  refine mem_filter.2 ⟨dm_mem_refStates I ε δ _ _ _ ?_ ?_ hA, ?_⟩
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    omega
  · intro k hk
    exact ((dm_mem_Rt _ _ _ _ _).1 hk).2.2.2
  · exact dm_kind_double I ε δ i l t hi hil ht al hal A hA

/-- INTERNAL: the class sum of a nonnegative function over one joint choice
`(a_i, a_l)` is at most its sum over all transversals.
TEXLINE: sections/transport.tex:456-458 -/
theorem dm_class_le_trans (I : Instance) (ε δ : ℚ) (i l : ℕ) (hi : i < pSmall I ε δ)
    (hl : l < pSmall I ε δ) (hil : i ≠ l) (ai al : ℕ) (hai : ai = 2 * i ∨ ai = 2 * i + 1)
    (hal : al = 2 * l ∨ al = 2 * l + 1) (ψ : Finset ℕ → ℝ) (hψ : ∀ S, 0 ≤ ψ S) :
    ∑ A ∈ (((range (pSmall I ε δ)).erase i).erase l).powerset,
        ψ (insert ai {al} ∪ selPairs (((range (pSmall I ε δ)).erase i).erase l) A) ≤
      ∑ S ∈ transStates I ε δ, ψ S := by
  rw [dm_sum_trans, dm_sum_four _ i l hi hl hil]
  set R := ((range (pSmall I ε δ)).erase i).erase l
  have h1 := Finset.sum_nonneg fun A (_ : A ∈ R.powerset) =>
    hψ (insert (2 * i) {2 * l} ∪ selPairs R A)
  have h2 := Finset.sum_nonneg fun A (_ : A ∈ R.powerset) =>
    hψ (insert (2 * i) {2 * l + 1} ∪ selPairs R A)
  have h3 := Finset.sum_nonneg fun A (_ : A ∈ R.powerset) =>
    hψ (insert (2 * i + 1) {2 * l} ∪ selPairs R A)
  have h4 := Finset.sum_nonneg fun A (_ : A ∈ R.powerset) =>
    hψ (insert (2 * i + 1) {2 * l + 1} ∪ selPairs R A)
  rcases hai with rfl | rfl <;> rcases hal with rfl | rfl <;> linarith

/-- INTERNAL: `defect_mean` for a fixed joint choice `(a_i, a_l)` of transversal mass
at least `C/4`, with `b_l'` the mate of `a_l`.
TEXLINE: sections/transport.tex:456-506 -/
theorem dm_of_choice (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) (g : Finset ℕ → ℝ)
    (i l : ℕ) (hi : i < pSmall I ε δ) (hl : l < pSmall I ε δ) (hil : i ≠ l)
    (ai al bl : ℕ) (hai : ai = 2 * i ∨ ai = 2 * i + 1)
    (hal : (al = 2 * l ∧ bl = 2 * l + 1) ∨ (al = 2 * l + 1 ∧ bl = 2 * l))
    (hz : Cpart I ε δ j / 4 ≤ ∑ A ∈ (((range (pSmall I ε δ)).erase i).erase l).powerset,
      fWeight I ε δ j (insert ai {al} ∪ selPairs (((range (pSmall I ε δ)).erase i).erase l) A)) :
    ∃ g' : ℝ, (refDefMean I ε δ j i l g - g') ^ 2 ≤
        (CdParam I ε δ : ℝ) / Cpart I ε δ j * refDir I ε δ j w g ∧
      (g' - refMuMean I ε δ j g) ^ 2 ≤ 4 * refMuVar I ε δ j g := by
  classical
  set p := pSmall I ε δ with hpdef
  set L := ((List.range p).erase i).erase l with hLdef
  set R := ((range p).erase i).erase l with hRdef
  set f := fWeight I ε δ j with hfdef
  set C := Cpart I ε δ j with hCdef
  have hC : 0 < C := td_Cpart_pos I ε δ j
  have hf : ∀ S, 0 < f S := td_fWeight_pos I ε δ j
  have hal' : al = 2 * l ∨ al = 2 * l + 1 := by omega
  have hLnd : L.Nodup := (List.nodup_range.erase i).erase l
  have hLR : L.toFinset = R := dm_toFinset_erase_erase p i l
  have hLmem : ∀ t, t ∈ L ↔ t ≠ l ∧ t ≠ i ∧ t < p := fun t => by
    rw [← List.mem_toFinset, hLR, dm_mem_R]
  have hch : ∀ φ : Finset ℕ → ℝ, chSum L φ = ∑ A ∈ R.powerset, φ (selPairs R A) := fun φ => by
    rw [chSum_eq_sum_selPairs hLnd, hLR]
  have hRmem : ∀ k ∈ R, k < p := fun k hk => ((dm_mem_R _ _ _ _).1 hk).2.2
  set z := ∑ A ∈ R.powerset, f (insert ai {al} ∪ selPairs R A) with hzdef
  have hz0 : 0 < z := by linarith
  have hcpos : ∀ a b, a < p → b < p → a ≠ b → 0 < cDef I ε δ j a b := by
    intro a b ha hb hab
    unfold cDef
    rw [dm_sum_defect I ε δ a b ha hb hab (2 * b) (2 * b + 1) (Or.inl ⟨rfl, rfl⟩)]
    exact Finset.sum_pos (fun A _ => hf _) ⟨∅, empty_mem_powerset _⟩
  have hwpos : ∀ a b, a < p → b < p → a ≠ b → 0 < (w a b : ℝ) := by
    intro a b ha hb hab
    exact lt_of_lt_of_le (div_pos hC (mul_pos (by norm_num) (hcpos a b ha hb hab)))
      (hgood a ha b hb hab).1
  -- the selected conditional transversal mean `g'`
  have hzch : chSum L (fun c => f (insert ai ({al} ∪ c))) = z := by
    rw [hch, hzdef]
    simp only [insert_union]
  have hg'ch : chSum L (fun c => f (insert ai ({al} ∪ c)) * g (insert ai ({al} ∪ c))) =
      ∑ A ∈ R.powerset, f (insert ai {al} ∪ selPairs R A) * g (insert ai {al} ∪ selPairs R A) := by
    rw [hch]
    simp only [insert_union]
  refine ⟨chSum L (fun c => f (insert ai ({al} ∪ c)) * g (insert ai ({al} ∪ c))) /
    chSum L (fun c => f (insert ai ({al} ∪ c))), ?_, ?_⟩
  · -- the one-hole transport inequality
    have hlen : L.length + 2 = p := by
      have h1 : ((List.range p).erase i).length = p - 1 := by
        rw [List.length_erase_of_mem (List.mem_range.2 hi), List.length_range]
      have h2 : l ∈ (List.range p).erase i :=
        (List.nodup_range.mem_erase_iff).2 ⟨Ne.symm hil, List.mem_range.2 hl⟩
      rw [hLdef, List.length_erase_of_mem h2, h1]
      omega
    have hWai : defW w i l ai bl ai = (w i l : ℝ) := by rw [defW, if_pos rfl]
    have hWbl : defW w i l ai bl bl = 1 := by rw [defW, if_neg (by omega), if_pos rfl]
    have hWt : ∀ t ∈ L, defW w i l ai bl (2 * t) = (w t l : ℝ) ∧
        defW w i l ai bl (2 * t + 1) = (w t l : ℝ) := by
      intro t ht
      have := (hLmem t).1 ht
      unfold defW
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        show 2 * t / 2 = t by omega, show (2 * t + 1) / 2 = t by omega]
      exact ⟨rfl, rfl⟩
    have htr := slot_transport f g (defW w i l ai bl) {al} ai bl L hf (by omega)
      (by rw [mem_singleton]; omega) (by rw [mem_singleton]; omega) hLnd
      (by intro t ht; have := (hLmem t).1 ht; simp only [mem_singleton]; omega)
      (by intro t ht; have := (hLmem t).1 ht; omega)
      (by rw [hWai]; exact hwpos i l hi hl hil) (by rw [hWbl]; exact one_pos)
      (by
        intro t ht
        rw [(hWt t ht).1, (hWt t ht).2]
        have := (hLmem t).1 ht
        exact ⟨hwpos t l this.2.2 hl this.1, rfl⟩)
      (by
        intro D L' hL'nd hL'L hD hL'D hcard
        refine fWeight_omission hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj.le {al} D L'
          (by intro e he; rw [mem_singleton] at he; omega) ?_ ?_ hL'nd ?_ ?_ hL'D ?_
        · intro e he
          rcases hD e he with h | h | ⟨t, ht, h⟩
          · omega
          · omega
          · have := (hLmem t).1 ht; omega
        · intro t ht; exact ((hLmem t).1 (hL'L t ht)).2.2
        · rw [disjoint_singleton_left]
          intro hmem
          rcases hD al hmem with h | h | ⟨t, ht, h⟩
          · omega
          · omega
          · have := (hLmem t).1 ht; omega
        · intro t ht
          have := (hLmem t).1 (hL'L t ht)
          simp only [mem_singleton]; omega
        · rw [card_singleton]; omega)
    have hs0 : chSum L (fun c => f (insert bl ({al} ∪ c))) = cDef I ε δ j i l := by
      rw [hch]
      unfold cDef
      rw [dm_sum_defect I ε δ i l hi hl hil al bl hal]
      simp only [insert_union]
      rfl
    have hmean : refDefMean I ε δ j i l g =
        chSum L (fun c => f (insert bl ({al} ∪ c)) * g (insert bl ({al} ∪ c))) /
          chSum L (fun c => f (insert bl ({al} ∪ c))) := by
      rw [hs0]
      unfold refDefMean
      rw [dm_sum_defect I ε δ i l hi hl hil al bl hal (fun S => fWeight I ε δ j S * g S), hch]
      simp only [insert_union]
      rfl
    have hD := defect_clique_le I ε δ j w hgood g i l hi hl hil ai al bl hai hal
    rw [← hmean, hs0, hzch, hWai, hWbl, hLR] at htr
    obtain ⟨c0, hc0def⟩ : ∃ c0, cDef I ε δ j i l = c0 := ⟨_, rfl⟩
    rw [hc0def] at htr
    have hc0 : 0 < c0 := hc0def ▸ hcpos i l hi hl hil
    obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, (qParam I ε δ : ℝ) ^ 3 = Q := ⟨_, rfl⟩
    have hQ : 0 ≤ Q := hQdef ▸ pow_nonneg (Nat.cast_nonneg _) 3
    have hDir := td_refDir_nonneg I ε δ j w hgood g
    -- each ordinary slot: `v_t / w_tl ≤ c_it (4 c_tl / C) ≤ 4 q³ c_il`
    have hslot : ∀ t ∈ R,
        chSum (L.erase t) (fun c => f (insert (2 * t) (insert (2 * t + 1) ({al} ∪ c)))) /
          defW w i l ai bl (2 * t) ≤ 4 * Q * c0 := by
      intro t ht
      have ht' := (dm_mem_R _ _ _ _).1 ht
      rw [(hWt t ((hLmem t).2 ht')).1]
      have hw := hwpos t l (hRmem t ht) hl ht'.1
      have hcit := hcpos i t hi (hRmem t ht) (Ne.symm ht'.2.1)
      have hv := dm_double_le I ε δ j i l t hi hl hil ht al hal'
      have hct := hcpos t l (hRmem t ht) hl ht'.1
      have hwl : C ≤ (w t l : ℝ) * (4 * cDef I ε δ j t l) := by
        have := (hgood t (hRmem t ht) l hl ht'.1).1
        rwa [div_le_iff₀ (mul_pos (by norm_num) hct)] at this
      have hcmp := defect_comparison hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas j hj.le i t l hi
        (hRmem t ht) hl (Ne.symm ht'.2.1) ht'.1 hil
      rw [hc0def, hQdef] at hcmp
      rw [div_le_iff₀ hw]
      have h4 : 4 * (cDef I ε δ j i t * cDef I ε δ j t l) * (w t l : ℝ) ≤
          4 * (Q * C * c0) * (w t l : ℝ) := by
        have := mul_le_mul_of_nonneg_right hcmp hw.le
        nlinarith
      have h1 : cDef I ε δ j i t * C ≤
          cDef I ε δ j i t * ((w t l : ℝ) * (4 * cDef I ε δ j t l)) :=
        mul_le_mul_of_nonneg_left hwl hcit.le
      have h5 : chSum (L.erase t) (fun c => f (insert (2 * t) (insert (2 * t + 1) ({al} ∪ c)))) *
          C ≤ 4 * Q * c0 * (w t l : ℝ) * C := by
        nlinarith [mul_le_mul_of_nonneg_right hv hC.le]
      exact le_of_mul_le_mul_right h5 hC
    have hsum : ∑ t ∈ R,
        chSum (L.erase t) (fun c => f (insert (2 * t) (insert (2 * t + 1) ({al} ∪ c)))) /
          defW w i l ai bl (2 * t) ≤ p * (4 * Q * c0) := by
      refine (Finset.sum_le_sum hslot).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (mul_nonneg (by norm_num) hQ) hc0.le)
      have : R.card ≤ p := by
        calc R.card ≤ (range p).card :=
              card_le_card ((erase_subset _ _).trans (erase_subset _ _))
          _ = p := card_range p
      exact_mod_cast this
    have hS0 : 0 ≤ ∑ t ∈ R,
        chSum (L.erase t) (fun c => f (insert (2 * t) (insert (2 * t + 1) ({al} ∪ c)))) /
          defW w i l ai bl (2 * t) := by
      refine Finset.sum_nonneg fun t ht => div_nonneg ?_ ?_
      · exact chSum_nonneg (hLnd.erase t) fun c _ => (hf _).le
      · have ht' := (dm_mem_R _ _ _ _).1 ht
        rw [(hWt t ((hLmem t).2 ht')).1]
        exact (hwpos t l (hRmem t ht) hl ht'.1).le
    have hT1 : 1 / (c0 * (w i l : ℝ)) ≤ 4 / C := by
      have := (hgood i hi l hl hil).1
      rw [hc0def, div_le_iff₀ (mul_pos (by norm_num) hc0)] at this
      rw [div_le_div_iff₀ (mul_pos hc0 (hwpos i l hi hl hil)) hC]
      nlinarith
    have hT2 : 1 / (z * 1) ≤ 4 / C := by
      rw [mul_one, div_le_div_iff₀ hz0 hC]
      linarith
    have hT3 : 2 / (c0 * z) * ∑ t ∈ R,
        chSum (L.erase t) (fun c => f (insert (2 * t) (insert (2 * t + 1) ({al} ∪ c)))) /
          defW w i l ai bl (2 * t) ≤ 32 * p * Q / C := by
      calc _ ≤ 2 / (c0 * z) * (p * (4 * Q * c0)) :=
              mul_le_mul_of_nonneg_left hsum (div_nonneg (by norm_num) (mul_pos hc0 hz0).le)
        _ = 8 * p * Q / z := by field_simp; ring
        _ ≤ 32 * p * Q / C := by
            rw [div_le_div_iff₀ hz0 hC]
            have : 0 ≤ (p : ℝ) * Q := mul_nonneg (Nat.cast_nonneg _) hQ
            nlinarith
    have hcoef0 : 0 ≤ 1 / (c0 * (w i l : ℝ)) + 1 / (z * 1) + 2 / (c0 * z) * ∑ t ∈ R,
        chSum (L.erase t) (fun c => f (insert (2 * t) (insert (2 * t + 1) ({al} ∪ c)))) /
          defW w i l ai bl (2 * t) := by
      have hw := hwpos i l hi hl hil
      refine add_nonneg (add_nonneg ?_ ?_) (mul_nonneg ?_ hS0)
      · exact div_nonneg zero_le_one (mul_pos hc0 hw).le
      · exact div_nonneg zero_le_one (by rw [mul_one]; exact hz0.le)
      · exact div_nonneg (by norm_num) (mul_pos hc0 hz0).le
    have hcoef : 1 / (c0 * (w i l : ℝ)) + 1 / (z * 1) + 2 / (c0 * z) * ∑ t ∈ R,
        chSum (L.erase t) (fun c => f (insert (2 * t) (insert (2 * t + 1) ({al} ∪ c)))) /
          defW w i l ai bl (2 * t) ≤ (CdParam I ε δ : ℝ) / C := by
      have hCd : (CdParam I ε δ : ℝ) = 8 + 32 * p * Q := by
        rw [← hQdef]; unfold CdParam; push_cast; rfl
      rw [hCd]
      have : (8 + 32 * (p : ℝ) * Q) / C = 4 / C + 4 / C + 32 * p * Q / C := by ring
      rw [this]
      linarith
    rw [hzch]
    refine htr.trans ?_
    calc _ ≤ (1 / (c0 * (w i l : ℝ)) + 1 / (z * 1) + 2 / (c0 * z) * ∑ t ∈ R,
          chSum (L.erase t) (fun c => f (insert (2 * t) (insert (2 * t + 1) ({al} ∪ c)))) /
            defW w i l ai bl (2 * t)) * refDir I ε δ j w g :=
          mul_le_mul_of_nonneg_left hD hcoef0
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hDir
  · -- conditional Cauchy–Schwarz on the selected class, of `μ`-mass `z / C ≥ 1/4`
    rw [hg'ch, hzch]
    set m := refMuMean I ε δ j g with hmdef
    set V := refMuVar I ε δ j g with hVdef
    have hψ : ∀ S, 0 ≤ f S * (g S - m) ^ 2 := fun S => mul_nonneg (hf S).le (sq_nonneg _)
    have hVar : C * V = ∑ S ∈ transStates I ε δ, f S * (g S - m) ^ 2 := by
      rw [hVdef]
      unfold refMuVar
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun S hS => ?_
      unfold refMu
      rw [if_pos hS, transMass_eq_Cpart, ← hCdef, ← hmdef, ← hfdef]
      field_simp
    have hV0 : 0 ≤ V := by
      have h0 := Finset.sum_nonneg fun S (_ : S ∈ transStates I ε δ) => hψ S
      rw [← hVar] at h0
      exact nonneg_of_mul_nonneg_right (by linarith) hC
    have hcls := dm_class_le_trans I ε δ i l hi hl hil ai al hai hal'
      (fun S => f S * (g S - m) ^ 2) hψ
    rw [← hVar] at hcls
    have hdiff : (∑ A ∈ R.powerset, f (insert ai {al} ∪ selPairs R A) *
          g (insert ai {al} ∪ selPairs R A)) / z - m =
        (∑ A ∈ R.powerset, f (insert ai {al} ∪ selPairs R A) *
          (g (insert ai {al} ∪ selPairs R A) - m)) / z := by
      have hsum : ∑ A ∈ R.powerset, f (insert ai {al} ∪ selPairs R A) *
          (g (insert ai {al} ∪ selPairs R A) - m) =
          ∑ A ∈ R.powerset, f (insert ai {al} ∪ selPairs R A) *
            g (insert ai {al} ∪ selPairs R A) - m * z := by
        rw [hzdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun A _ => by ring
      rw [hsum]
      field_simp
    have hCS : (∑ A ∈ R.powerset, f (insert ai {al} ∪ selPairs R A) *
          (g (insert ai {al} ∪ selPairs R A) - m)) ^ 2 ≤
        z * ∑ A ∈ R.powerset, f (insert ai {al} ∪ selPairs R A) *
          (g (insert ai {al} ∪ selPairs R A) - m) ^ 2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun A _ => (hf _).le)
        (fun A _ => hψ _) (fun A _ => le_of_eq (by ring))
    rw [hdiff, div_pow, div_le_iff₀ (pow_pos hz0 2)]
    have h1 := mul_le_mul_of_nonneg_left hcls hz0.le
    have h2 : C * V ≤ 4 * z * V := mul_le_mul_of_nonneg_right (by linarith) hV0
    nlinarith

/-- **Defect means** (`lem:defect-mean`): for good multipliers and each defect type
`il`, a conditional transversal mean `g'` satisfies
`(ḡ_il - g')² ≤ (C_d / C) 𝔇(g)` and `(g' - E_μ g)² ≤ 4 Var_μ(g)`.
PAPER: sections/transport.tex:440-452 -/
theorem defect_mean (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) (g : Finset ℕ → ℝ)
    (i l : ℕ) (hi : i < pSmall I ε δ) (hl : l < pSmall I ε δ) (hil : i ≠ l) :
    ∃ g' : ℝ, (refDefMean I ε δ j i l g - g') ^ 2 ≤
        (CdParam I ε δ : ℝ) / Cpart I ε δ j * refDir I ε δ j w g ∧
      (g' - refMuMean I ε δ j g) ^ 2 ≤ 4 * refMuVar I ε δ j g := by
  -- of the four joint choices in pairs `i, l`, one has transversal mass at least `C/4`
  set R := ((range (pSmall I ε δ)).erase i).erase l with hRdef
  have hsplit := dm_sum_four (pSmall I ε δ) i l hi hl hil (fWeight I ε δ j)
  rw [← dm_sum_trans, ← transMass, transMass_eq_Cpart] at hsplit
  have hof := dm_of_choice hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj w hgood g i l hi hl hil
  by_cases h1 : Cpart I ε δ j / 4 ≤ ∑ A ∈ R.powerset, fWeight I ε δ j (insert (2 * i) {2 * l} ∪ selPairs R A)
  · exact hof (2 * i) (2 * l) (2 * l + 1) (Or.inl rfl) (Or.inl ⟨rfl, rfl⟩) h1
  by_cases h2 : Cpart I ε δ j / 4 ≤ ∑ A ∈ R.powerset, fWeight I ε δ j (insert (2 * i) {2 * l + 1} ∪ selPairs R A)
  · exact hof (2 * i) (2 * l + 1) (2 * l) (Or.inl rfl) (Or.inr ⟨rfl, rfl⟩) h2
  by_cases h3 : Cpart I ε δ j / 4 ≤ ∑ A ∈ R.powerset, fWeight I ε δ j (insert (2 * i + 1) {2 * l} ∪ selPairs R A)
  · exact hof (2 * i + 1) (2 * l) (2 * l + 1) (Or.inr rfl) (Or.inl ⟨rfl, rfl⟩) h3
  have h4 : Cpart I ε δ j / 4 ≤ ∑ A ∈ R.powerset, fWeight I ε δ j (insert (2 * i + 1) {2 * l + 1} ∪ selPairs R A) := by
    push Not at h1 h2 h3
    linarith
  exact hof (2 * i + 1) (2 * l + 1) (2 * l) (Or.inr rfl) (Or.inr ⟨rfl, rfl⟩) h4

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-15 · closed · `defect_mean` assembled from `slot_transport`, `fWeight_omission`
  (shared with `transversal_variance`), `defect_comparison`, `defect_clique_le`; no local `sorry`
-/
