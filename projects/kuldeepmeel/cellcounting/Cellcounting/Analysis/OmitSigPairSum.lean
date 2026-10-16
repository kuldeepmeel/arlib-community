import Cellcounting.Analysis.OmitSig
import Cellcounting.Analysis.HypCubicContract

/-!
# Summing a pair preserves the omission property (`lem:binary-contraction`)

`signatures.tex:154-196`, omission half: if `φ` has the omission property with
positivity on the `k`-subsets of `Γ` (`OmitSig φ Γ k`, `k ≥ 1`), then summing a pair
`{α, β} ⊆ Γ` at occupancy one gives a weight with the omission property with
positivity on the `(k - 1)`-subsets of `Γ \ {α, β}`.

For a display `P` of the summed weight, the three-omission weights of `φ` on
`P' = P ∪ {α, β}` form a symmetric cubic tensor whose slices are omission matrices
of `φ` (with a zero row and column at the slice index); contracting it with the
indicator of `{α, β}` and restricting to `P` gives the omission matrix of the summed
weight (`hyp_cubic_contract`).
-/

namespace Cellcounting.Analysis

open Finset

/-- INTERNAL: a matrix vanishing off the range of an injection, whose restriction
along it is `Hyp`, is `Hyp`.
TEXLINE: sections/signatures.tex:173-176 -/
theorem hyp_of_comp_inj {ι κ : Type*} [Fintype ι] [Fintype κ] {Q : ι → ι → ℝ}
    (e : κ → ι) (he : Function.Injective e) (hQ : Hyp (fun a b => Q (e a) (e b)))
    (hoff : ∀ i h, (i ∉ Set.range e ∨ h ∉ Set.range e) → Q i h = 0) : Hyp Q := by
  have hqf : ∀ u w : ι → ℝ, qf Q u w = qf (fun a b => Q (e a) (e b)) (u ∘ e) (w ∘ e) := by
    intro u w
    unfold qf
    symm
    refine Fintype.sum_of_injective e he _ _ ?_ ?_
    · intro i hi
      exact Finset.sum_eq_zero fun h _ => by rw [hoff i h (Or.inl hi)]; ring
    · intro a
      refine Fintype.sum_of_injective e he _ _ ?_ ?_
      · intro h hh; rw [hoff (e a) h (Or.inr hh)]; ring
      · intro b; rfl
  intro u w hu
  simp only [hqf] at hu ⊢
  exact hQ _ _ hu

/-- **Summing a pair at occupancy one preserves the omission property and positivity**
(`lem:binary-contraction`, omission half).
PAPER: sections/signatures.tex:154-196 -/
theorem omitSig_pairSum {φ : Finset ℕ → ℝ} {Γ : Finset ℕ} {k : ℕ} (h : OmitSig φ Γ k)
    {α β : ℕ} (hα : α ∈ Γ) (hβ : β ∈ Γ) (hαβ : α ≠ β) (hk : 1 ≤ k) :
    OmitSig (pairSum φ α β) ((Γ.erase α).erase β) (k - 1) := by
  obtain ⟨hφpos, hφsig⟩ := h
  refine ⟨fun U hU hUc => ?_, fun P hP hPc => ?_⟩
  · -- positivity
    have hαU : α ∉ U := fun hm => by simpa using hU hm
    have hβU : β ∉ U := fun hm => by simpa using hU hm
    have hUΓ : U ⊆ Γ := fun x hx => (mem_erase.1 (mem_erase.1 (hU hx)).2).2
    refine add_pos (hφpos _ ?_ ?_) (hφpos _ ?_ ?_)
    · exact insert_subset hα hUΓ
    · rw [card_insert_of_notMem hαU]; omega
    · exact insert_subset hβ hUΓ
    · rw [card_insert_of_notMem hβU]; omega
  -- the signature at a display `P` of size `k + 1`
  have hαP : α ∉ P := fun hm => by simpa using hP hm
  have hβP : β ∉ P := fun hm => by simpa using hP hm
  have hPΓ : P ⊆ Γ := fun x hx => (mem_erase.1 (mem_erase.1 (hP hx)).2).2
  set P' : Finset ℕ := insert α (insert β P) with hP'
  have hβP' : β ∉ P → insert β P ⊆ Γ := fun _ => insert_subset hβ hPΓ
  have hP'Γ : P' ⊆ Γ := insert_subset hα (hβP' hβP)
  have hαβP : α ∉ insert β P := by simp [hαβ, hαP]
  have hP'c : P'.card = k + 3 := by
    rw [hP', card_insert_of_notMem hαβP, card_insert_of_notMem hβP, hPc]; omega
  -- the cubic tensor of three-omission weights on `P'`
  set T : P' → P' → P' → ℝ := fun x y z =>
    if x ≠ y ∧ x ≠ z ∧ y ≠ z then φ (((P'.erase x).erase y).erase z) else 0 with hT
  have hcard3 : 3 ≤ Fintype.card P' := by rw [Fintype.card_coe]; omega
  have hsymm1 : ∀ x y z, T x y z = T y x z := by
    intro x y z
    simp only [hT]
    by_cases hc : x ≠ y ∧ x ≠ z ∧ y ≠ z
    · rw [if_pos hc, if_pos ⟨Ne.symm hc.1, hc.2.2, hc.2.1⟩, erase_right_comm (s := P')]
    · rw [if_neg hc, if_neg]
      exact fun h' => hc ⟨Ne.symm h'.1, h'.2.2, h'.2.1⟩
  have hsymm2 : ∀ x y z, T x y z = T x z y := by
    intro x y z
    simp only [hT]
    by_cases hc : x ≠ y ∧ x ≠ z ∧ y ≠ z
    · rw [if_pos hc, if_pos ⟨hc.2.1, hc.1, Ne.symm hc.2.2⟩, erase_right_comm]
    · rw [if_neg hc, if_neg]
      exact fun h' => hc ⟨h'.2.1, h'.1, Ne.symm h'.2.2⟩
  have hcard3erase : ∀ x y z : P', x ≠ y → x ≠ z → y ≠ z →
      (((P'.erase x).erase y).erase z).card = k := by
    intro x y z hxy hxz hyz
    have hxy' : (x : ℕ) ≠ y := fun h' => hxy (Subtype.ext h')
    have hxz' : (x : ℕ) ≠ z := fun h' => hxz (Subtype.ext h')
    have hyz' : (y : ℕ) ≠ z := fun h' => hyz (Subtype.ext h')
    rw [card_erase_of_mem, card_erase_of_mem, card_erase_of_mem x.2, hP'c]
    · simp
    · exact mem_erase.2 ⟨Ne.symm hxy', y.2⟩
    · exact mem_erase.2 ⟨Ne.symm hyz', mem_erase.2 ⟨Ne.symm hxz', z.2⟩⟩
  have hpos : ∀ x y z, x ≠ y → x ≠ z → y ≠ z → 0 < T x y z := by
    intro x y z hxy hxz hyz
    simp only [hT]
    rw [if_pos ⟨hxy, hxz, hyz⟩]
    exact hφpos _ (fun e he => hP'Γ (mem_of_mem_erase (mem_of_mem_erase (mem_of_mem_erase he))))
      (hcard3erase x y z hxy hxz hyz)
  have hzero : ∀ x y z, (x = y ∨ x = z ∨ y = z) → T x y z = 0 := by
    intro x y z hc
    simp only [hT]
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    rcases hc with hc | hc | hc
    exacts [h1 hc, h2 hc, h3 hc]
  -- every slice is an omission matrix of `φ` with a zero row and column
  have hslice : ∀ z, Hyp (T z) := by
    intro z
    have hsub : P'.erase z ⊆ Γ := (erase_subset _ _).trans hP'Γ
    have hc2 : (P'.erase z).card = k + 2 := by rw [card_erase_of_mem z.2, hP'c]; omega
    have hom := hφsig _ hsub hc2
    set e : (P'.erase z) → P' := fun a => ⟨a.1, mem_of_mem_erase a.2⟩ with he
    have heinj : Function.Injective e := by
      intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext this
    refine hyp_of_comp_inj e heinj ?_ ?_
    · have hfun : (fun a b => T z (e a) (e b)) = omMat φ (P'.erase z) := by
        funext a b
        simp only [omMat, hT, he]
        have hza : z ≠ ⟨a.1, mem_of_mem_erase a.2⟩ := by
          intro h'; have := (mem_erase.1 a.2).1; exact this (congrArg Subtype.val h').symm
        have hzb : z ≠ ⟨b.1, mem_of_mem_erase b.2⟩ := by
          intro h'; have := (mem_erase.1 b.2).1; exact this (congrArg Subtype.val h').symm
        by_cases hab : a = b
        · subst hab; simp
        · have hab' : (⟨a.1, mem_of_mem_erase a.2⟩ : P') ≠ ⟨b.1, mem_of_mem_erase b.2⟩ := by
            intro h'; exact hab (Subtype.ext (Subtype.mk.inj h'))
          rw [if_pos ⟨hza, hzb, hab'⟩, if_neg hab]
      rw [hfun]; exact hom
    · intro x y hxy
      have hz : ∀ w : P', w ∉ Set.range e → w = z := by
        intro w hw
        by_contra hwz
        exact hw ⟨⟨w.1, mem_erase.2 ⟨fun h' => hwz (Subtype.ext h'), w.2⟩⟩, rfl⟩
      rcases hxy with hx | hy
      · exact hzero z x y (Or.inl (hz x hx).symm)
      · exact hzero z x y (Or.inr (Or.inl (hz y hy).symm))
  -- contract with the indicator of `{α, β}`
  have hαm : α ∈ P' := mem_insert_self _ _
  have hβm : β ∈ P' := mem_insert_of_mem (mem_insert_self _ _)
  set α' : P' := ⟨α, hαm⟩
  set β' : P' := ⟨β, hβm⟩
  have hα'β' : α' ≠ β' := fun h' => hαβ (congrArg Subtype.val h')
  set a : P' → ℝ := fun i => if i = α' ∨ i = β' then 1 else 0 with ha
  have hM := hyp_cubic_contract hcard3 T hsymm1 hsymm2 hpos hzero hslice a
    (fun i => by simp only [ha]; split_ifs <;> norm_num)
  have hMeq : ∀ u v, ∑ i, a i * T i u v = T α' u v + T β' u v := by
    intro u v
    rw [Fintype.sum_eq_add α' β' hα'β']
    · simp [ha, hα'β', hα'β'.symm]
    · intro x hx
      simp only [ha]
      rw [if_neg (fun h' => h'.elim hx.1 hx.2), zero_mul]
  -- restrict to `P`
  set e : P → P' := fun x => ⟨x.1, mem_insert_of_mem (mem_insert_of_mem x.2)⟩ with he
  have heinj : Function.Injective e := by
    intro a b hab
    exact Subtype.ext (Subtype.mk.inj hab)
  have hR := hyp_comp_inj hM e heinj
  suffices hfun2 : omMat (pairSum φ α β) P = fun x y => ∑ i, a i * T i (e x) (e y) by
    rw [hfun2]; exact hR
  funext x y
  rw [hMeq]
  have hxα : (x : ℕ) ≠ α := fun h' => hαP (h' ▸ x.2)
  have hyα : (y : ℕ) ≠ α := fun h' => hαP (h' ▸ y.2)
  have hxβ : (x : ℕ) ≠ β := fun h' => hβP (h' ▸ x.2)
  have hyβ : (y : ℕ) ≠ β := fun h' => hβP (h' ▸ y.2)
  have hα'x : α' ≠ e x := fun h' => hxα (congrArg Subtype.val h').symm
  have hα'y : α' ≠ e y := fun h' => hyα (congrArg Subtype.val h').symm
  have hβ'x : β' ≠ e x := fun h' => hxβ (congrArg Subtype.val h').symm
  have hβ'y : β' ≠ e y := fun h' => hyβ (congrArg Subtype.val h').symm
  simp only [omMat, pairSum, hT]
  by_cases hxy : x = y
  · subst hxy; simp
  · have hexy : e x ≠ e y := fun h' => hxy (heinj h')
    have hxy' : (x : ℕ) ≠ y := fun h' => hxy (Subtype.ext h')
    rw [if_neg hxy, if_pos ⟨hα'x, hα'y, hexy⟩, if_pos ⟨hβ'x, hβ'y, hexy⟩, add_comm]
    congr 1
    · congr 1
      ext w
      simp only [P', α', e, mem_erase, mem_insert]
      constructor
      · rintro (hw | ⟨hwy, hwx, hwP⟩)
        · rw [hw]; exact ⟨fun h' => hyβ h'.symm, fun h' => hxβ h'.symm, Ne.symm hαβ, Or.inr (Or.inl rfl)⟩
        · exact ⟨hwy, hwx, fun h' => hαP (h' ▸ hwP), Or.inr (Or.inr hwP)⟩
      · rintro ⟨hwy, hwx, hwα, hw | hw | hw⟩
        · exact absurd hw hwα
        · exact Or.inl hw
        · exact Or.inr ⟨hwy, hwx, hw⟩
    · congr 1
      ext w
      simp only [P', β', e, mem_erase, mem_insert]
      constructor
      · rintro (hw | ⟨hwy, hwx, hwP⟩)
        · rw [hw]; exact ⟨fun h' => hyα h'.symm, fun h' => hxα h'.symm, hαβ, Or.inl rfl⟩
        · exact ⟨hwy, hwx, fun h' => hβP (h' ▸ hwP), Or.inr (Or.inr hwP)⟩
      · rintro ⟨hwy, hwx, hwβ, hw | hw | hw⟩
        · exact Or.inl hw
        · exact absurd hw hwβ
        · exact Or.inr ⟨hwy, hwx, hw⟩

end Cellcounting.Analysis
