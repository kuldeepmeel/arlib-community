import Cellcounting.Analysis.ChoiceSum
import Cellcounting.Analysis.CubicContraction
import Cellcounting.Model.Prior
import Cellcounting.Analysis.OmitSigPairSum
import Cellcounting.Analysis.FWeightBaseOmitSig
import Cellcounting.Analysis.HWeightAdditionHyp

/-!
# The addition signature of `f̃_j` (`lem:binary-signatures`, `signatures.tex:201-262`)

`f̃_j` has the addition property on the full `p`-subset domain of the paired ground
set `[0, 2p)`, and keeps it after fixing elements included and summing any disjoint
labeled pairs at occupancy one (`lem:binary-contraction`).  In the form used by the
defect inequalities: fix `F` included and sum the pairs of `L` at occupancy one; the
resulting weight on two further elements of `D` has a two-addition matrix
`addMat (fTilde I ε δ j) F D L` with at most one positive eigenvalue (`Hyp`).

This is the addition counterpart of `fWeight_omission`, and the proof follows the paper.

* `AddSig φ Γ k` is the addition property with positivity on the `k`-subsets of `Γ`;
  it quantifies over every index set `D` disjoint from the fixed set, so principal
  submatrices are built in.
* `addSig_pairSum` (`lem:binary-contraction`, addition half): summing a pair keeps it.
  The three-addition weights `φ(F ∪ {a, x, y})` on `D ∪ {α, β}` form a symmetric cubic
  tensor whose slices are addition matrices of `φ` (padded with a zero row and column);
  contract with the indicator of `{α, β}` (`hyp_cubic_contract`) and restrict to `D`.
* `fTilde_base_addSig` (`signatures.tex:247-262`): fix `p - 2` included elements with
  coordinate counts `r`; there are `n_u = b_u - r_u` available elements in group `u`.
  Group the available elements (`hyp_of_groups`); the ordered-copy multiplicities cancel
  the remaining-capacity factorials, leaving a positive multiple of the two-addition
  matrix of `h_j` at `r` (`hWeight_addition_hyp`, the addition half of
  `cor:hj-signatures`).
* `fTilde_addition`: induction on `L` with `addSig_pairSum`, then the test at the fixed
  set `F` and the index set `D`.
-/
namespace Cellcounting.Analysis

open Finset Pseudocode

/-- INTERNAL: the two-addition matrix `N_{xy} = G({x, y})` (zero diagonal) of
`G(U) = Σ_c f(F ∪ U ∪ c)`, the weight obtained from `f` by fixing `F` included and
summing the pairs of `L` at occupancy one.
TEXLINE: sections/signatures.tex:79-90 -/
noncomputable def addMat (f : Finset ℕ → ℝ) (F D : Finset ℕ) (L : List ℕ) :
    D → D → ℝ :=
  fun x y => if x = y then 0 else chSum L (fun c => f (insert x.1 (insert y.1 (F ∪ c))))

/-- INTERNAL: the two-addition matrix `(φ(F ∪ {x, y}))_{x ≠ y ∈ D}` of a set weight `φ`
with `F` fixed included, zero on the diagonal.
TEXLINE: sections/signatures.tex:79-90 -/
noncomputable def adMat (φ : Finset ℕ → ℝ) (F D : Finset ℕ) : D → D → ℝ :=
  fun x y => if x = y then 0 else φ (insert x.1 (insert y.1 F))

/-- INTERNAL: the addition property of `φ` on the `k`-subsets of `Γ`, with positivity:
`φ > 0` on every `k`-subset of `Γ`, and for every `k - 2` fixed included elements
`F ⊆ Γ` and every `D ⊆ Γ` disjoint from `F` the two-addition matrix on `D` has at most
one positive eigenvalue (quantifying over `D` builds in the principal submatrices).
TEXLINE: sections/signatures.tex:79-90 -/
def AddSig (φ : Finset ℕ → ℝ) (Γ : Finset ℕ) (k : ℕ) : Prop :=
  (∀ S ⊆ Γ, S.card = k → 0 < φ S) ∧
    ∀ F ⊆ Γ, ∀ D ⊆ Γ, Disjoint F D → F.card + 2 = k → Hyp (adMat φ F D)

/-- **Summing a pair at occupancy one preserves the addition property and positivity**
(`lem:binary-contraction`, addition half).
PAPER: sections/signatures.tex:154-188 -/
theorem addSig_pairSum {φ : Finset ℕ → ℝ} {Γ : Finset ℕ} {k : ℕ} (h : AddSig φ Γ k)
    {α β : ℕ} (hα : α ∈ Γ) (hβ : β ∈ Γ) (hαβ : α ≠ β) (hk : 1 ≤ k) :
    AddSig (pairSum φ α β) ((Γ.erase α).erase β) (k - 1) := by
  classical
  obtain ⟨hφpos, hφsig⟩ := h
  refine ⟨fun U hU hUc => ?_, fun F0 hF0 D hD hFD hF0c => ?_⟩
  · -- positivity
    have hαU : α ∉ U := fun hm => by simpa using hU hm
    have hβU : β ∉ U := fun hm => by simpa using hU hm
    have hUΓ : U ⊆ Γ := fun x hx => (mem_erase.1 (mem_erase.1 (hU hx)).2).2
    refine add_pos (hφpos _ ?_ ?_) (hφpos _ ?_ ?_)
    · exact insert_subset hα hUΓ
    · rw [card_insert_of_notMem hαU]; omega
    · exact insert_subset hβ hUΓ
    · rw [card_insert_of_notMem hβU]; omega
  have hαF : α ∉ F0 := fun hm => by simpa using hF0 hm
  have hβF : β ∉ F0 := fun hm => by simpa using hF0 hm
  have hαD : α ∉ D := fun hm => by simpa using hD hm
  have hβD : β ∉ D := fun hm => by simpa using hD hm
  have hFΓ : F0 ⊆ Γ := fun x hx => (mem_erase.1 (mem_erase.1 (hF0 hx)).2).2
  have hDΓ : D ⊆ Γ := fun x hx => (mem_erase.1 (mem_erase.1 (hD hx)).2).2
  -- with no index the matrix is empty
  by_cases hD0 : D = ∅
  · subst hD0
    intro u w hu
    exfalso
    have : qf (adMat (pairSum φ α β) F0 ∅) u u = 0 := by
      unfold qf
      exact Finset.sum_eq_zero fun i _ => absurd i.2 (notMem_empty _)
    linarith
  have hDc : 1 ≤ D.card := card_pos.2 (nonempty_iff_ne_empty.2 hD0)
  set P' : Finset ℕ := insert α (insert β D) with hP'
  have hP'Γ : P' ⊆ Γ := insert_subset hα (insert_subset hβ hDΓ)
  have hαβD : α ∉ insert β D := by simp [hαβ, hαD]
  have hP'c : P'.card = D.card + 2 := by
    rw [hP', card_insert_of_notMem hαβD, card_insert_of_notMem hβD]
  have hP'F : ∀ x ∈ P', x ∉ F0 := by
    intro x hx hxF
    rcases mem_insert.1 hx with h' | h'
    · exact hαF (h' ▸ hxF)
    rcases mem_insert.1 h' with h'' | h''
    · exact hβF (h'' ▸ hxF)
    · exact disjoint_left.1 hFD hxF h''
  -- the cubic tensor of three-addition weights on `P'`
  set T : P' → P' → P' → ℝ := fun x y z =>
    if x ≠ y ∧ x ≠ z ∧ y ≠ z then φ (insert x.1 (insert y.1 (insert z.1 F0))) else 0 with hT
  have hcard3 : 3 ≤ Fintype.card P' := by rw [Fintype.card_coe]; omega
  have hsymm1 : ∀ x y z, T x y z = T y x z := by
    intro x y z
    simp only [hT]
    by_cases hc : x ≠ y ∧ x ≠ z ∧ y ≠ z
    · rw [if_pos hc, if_pos ⟨Ne.symm hc.1, hc.2.2, hc.2.1⟩, insert_comm]
    · rw [if_neg hc, if_neg]
      exact fun h' => hc ⟨Ne.symm h'.1, h'.2.2, h'.2.1⟩
  have hsymm2 : ∀ x y z, T x y z = T x z y := by
    intro x y z
    simp only [hT]
    by_cases hc : x ≠ y ∧ x ≠ z ∧ y ≠ z
    · rw [if_pos hc, if_pos ⟨hc.2.1, hc.1, Ne.symm hc.2.2⟩, insert_comm y.1]
    · rw [if_neg hc, if_neg]
      exact fun h' => hc ⟨h'.2.1, h'.1, Ne.symm h'.2.2⟩
  have hpos : ∀ x y z, x ≠ y → x ≠ z → y ≠ z → 0 < T x y z := by
    intro x y z hxy hxz hyz
    have hxy' : (x : ℕ) ≠ y := fun h' => hxy (Subtype.ext h')
    have hxz' : (x : ℕ) ≠ z := fun h' => hxz (Subtype.ext h')
    have hyz' : (y : ℕ) ≠ z := fun h' => hyz (Subtype.ext h')
    simp only [hT]
    rw [if_pos ⟨hxy, hxz, hyz⟩]
    refine hφpos _ (insert_subset (hP'Γ x.2) (insert_subset (hP'Γ y.2)
      (insert_subset (hP'Γ z.2) hFΓ))) ?_
    rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem (hP'F z z.2)]
    · omega
    · simp [hyz', hP'F y y.2]
    · simp [hxy', hxz', hP'F x x.2]
  have hzero : ∀ x y z, (x = y ∨ x = z ∨ y = z) → T x y z = 0 := by
    intro x y z hc
    simp only [hT]
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    rcases hc with hc | hc | hc
    exacts [h1 hc, h2 hc, h3 hc]
  -- every slice is an addition matrix of `φ` with a zero row and column
  have hslice : ∀ z, Hyp (T z) := by
    intro z
    have hsubF : insert z.1 F0 ⊆ Γ := insert_subset (hP'Γ z.2) hFΓ
    have hsubD : P'.erase z ⊆ Γ := (erase_subset _ _).trans hP'Γ
    have hdisj : Disjoint (insert z.1 F0) (P'.erase z) := by
      rw [disjoint_insert_left]
      refine ⟨notMem_erase _ _, disjoint_left.2 fun x hxF hx => ?_⟩
      exact hP'F x (mem_of_mem_erase hx) hxF
    have hc2 : (insert z.1 F0).card + 2 = k := by
      rw [card_insert_of_notMem (hP'F z z.2)]; omega
    have hom := hφsig _ hsubF _ hsubD hdisj hc2
    set e : (P'.erase z) → P' := fun a => ⟨a.1, mem_of_mem_erase a.2⟩ with he
    have heinj : Function.Injective e := by
      intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext this
    refine hyp_of_comp_inj e heinj ?_ ?_
    · have hfun : (fun a b => T z (e a) (e b)) = adMat φ (insert z.1 F0) (P'.erase z) := by
        funext a b
        simp only [adMat, hT, he]
        have hza : z ≠ ⟨a.1, mem_of_mem_erase a.2⟩ := by
          intro h'; have := (mem_erase.1 a.2).1; exact this (congrArg Subtype.val h').symm
        have hzb : z ≠ ⟨b.1, mem_of_mem_erase b.2⟩ := by
          intro h'; have := (mem_erase.1 b.2).1; exact this (congrArg Subtype.val h').symm
        by_cases hab : a = b
        · subst hab; simp
        · have hab' : (⟨a.1, mem_of_mem_erase a.2⟩ : P') ≠ ⟨b.1, mem_of_mem_erase b.2⟩ := by
            intro h'; exact hab (Subtype.ext (Subtype.mk.inj h'))
          rw [if_pos ⟨hza, hzb, hab'⟩, if_neg hab, insert_comm z.1, insert_comm z.1]
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
  -- restrict to `D`
  set e : D → P' := fun x => ⟨x.1, mem_insert_of_mem (mem_insert_of_mem x.2)⟩ with he
  have heinj : Function.Injective e := by
    intro a b hab
    exact Subtype.ext (Subtype.mk.inj hab)
  have hR := hyp_comp_inj hM e heinj
  suffices hfun2 : adMat (pairSum φ α β) F0 D = fun x y => ∑ i, a i * T i (e x) (e y) by
    rw [hfun2]; exact hR
  funext x y
  rw [hMeq]
  have hxα : (x : ℕ) ≠ α := fun h' => hαD (h' ▸ x.2)
  have hyα : (y : ℕ) ≠ α := fun h' => hαD (h' ▸ y.2)
  have hxβ : (x : ℕ) ≠ β := fun h' => hβD (h' ▸ x.2)
  have hyβ : (y : ℕ) ≠ β := fun h' => hβD (h' ▸ y.2)
  have hα'x : α' ≠ e x := fun h' => hxα (congrArg Subtype.val h').symm
  have hα'y : α' ≠ e y := fun h' => hyα (congrArg Subtype.val h').symm
  have hβ'x : β' ≠ e x := fun h' => hxβ (congrArg Subtype.val h').symm
  have hβ'y : β' ≠ e y := fun h' => hyβ (congrArg Subtype.val h').symm
  simp only [adMat, pairSum, hT]
  by_cases hxy : x = y
  · subst hxy; simp
  · have hexy : e x ≠ e y := fun h' => hxy (heinj h')
    rw [if_neg hxy, if_pos ⟨hα'x, hα'y, hexy⟩, if_pos ⟨hβ'x, hβ'y, hexy⟩]

end Cellcounting.Analysis

namespace Cellcounting.Analysis

open Finset Pseudocode

/-- INTERNAL: the coordinate group of a label `a < 2p`: the small cell of its pair, and
whether it is the column element.
TEXLINE: sections/signatures.tex:247-252 -/
noncomputable def addGrp (I : Instance) (ε δ : ℚ) (a : ℕ) (ha : a < 2 * pSmall I ε δ) :
    Fin (nSmall I ε δ) × Bool :=
  (⟨pairCell I ε δ (a / 2), pairCell_lt I ε δ (by omega)⟩, decide (a % 2 = 1))

/-- **`f̃_j` has the addition property, with positivity, on the `p`-subsets of `[0, 2p)`**
(`lem:binary-signatures`, second assertion): fixing `p - 2` included elements with
coordinate counts `r`, the group decomposition and the multiplicity cancellation reduce
the test to the two-addition matrix of `h_j` at `r` (`hWeight_addition_hyp`).
PAPER: sections/signatures.tex:247-262 -/
theorem fTilde_base_addSig (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (j : ℕ) (hj : j ≤ HParam I ε δ) :
    AddSig (fTilde I ε δ j) (range (2 * pSmall I ε δ)) (pSmall I ε δ) := by
  classical
  refine ⟨fun S _ _ => ?_, fun F hF D hD hFD hFc => ?_⟩
  · -- positivity on every subset
    unfold fTilde
    refine mul_pos ?_ (Finset.prod_pos fun s _ => by positivity)
    exact Finset.sum_pos (fun z _ => by positivity) ⟨fun _ => 0, by simp [freeBox]⟩
  set p := pSmall I ε δ with hpdef
  set N := nSmall I ε δ with hNdef
  set P : Finset ℕ := range (2 * p) \ F with hPdef
  have hDP : D ⊆ P := fun x hx => mem_sdiff.2 ⟨hD hx, fun h => disjoint_left.1 hFD h hx⟩
  -- it suffices to treat all available elements (a principal submatrix)
  suffices hfull : Hyp (adMat (fTilde I ε δ j) F P) by
    set e : D → P := fun x => ⟨x.1, hDP x.2⟩ with he
    have heinj : Function.Injective e := fun a b hab => Subtype.ext (Subtype.mk.inj hab)
    have hR := hyp_comp_inj hfull e heinj
    convert hR using 1
    funext x y
    simp only [adMat, he]
    by_cases hxy : x = y
    · subst hxy; simp
    · have hne : (⟨x.1, hDP x.2⟩ : P) ≠ ⟨y.1, hDP y.2⟩ :=
        fun h' => hxy (Subtype.ext (Subtype.mk.inj h'))
      rw [if_neg hxy, if_neg hne]
  have hPr : ∀ z ∈ P, z < 2 * p := fun z hz => mem_range.1 (mem_sdiff.1 hz).1
  have hPF : ∀ z ∈ P, z ∉ F := fun z hz => (mem_sdiff.1 hz).2
  set g : P → Fin N × Bool := fun x => addGrp I ε δ x.1 (hPr x.1 x.2) with hg
  -- group counts of a set of labels
  set cnt : Finset ℕ → Fin N × Bool → ℕ := fun S u =>
    (S.filter fun z => pairCell I ε δ (z / 2) = u.1.1 ∧ decide (z % 2 = 1) = u.2).card
    with hcnt
  set n : Fin N × Bool → ℕ := fun u => (univ.filter fun x : P => g x = u).card with hndef
  set r : Fin N × Bool → ℕ := cnt F with hrdef
  have hgrp : ∀ a (ha : a < 2 * p) (u : Fin N × Bool), addGrp I ε δ a ha = u ↔
      pairCell I ε δ (a / 2) = u.1.1 ∧ decide (a % 2 = 1) = u.2 := by
    intro a ha u
    simp only [addGrp, Prod.ext_iff, Fin.ext_iff]
  have hn_eq : ∀ u : Fin N × Bool, n u = cnt P u := by
    intro u
    simp only [hndef, hcnt]
    refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
    · intro x hx
      exact mem_filter.2 ⟨x.2, (hgrp x.1 _ u).1 (mem_filter.1 hx).2⟩
    · intro x _ y _ h; exact Subtype.ext h
    · intro z hz
      obtain ⟨hzP, hz⟩ := mem_filter.1 hz
      exact ⟨⟨z, hzP⟩, mem_filter.2 ⟨mem_univ _, (hgrp z (hPr z hzP) u).2 hz⟩, rfl⟩
  -- inserting a label adds one to its group
  have hins : ∀ (S : Finset ℕ) (a : ℕ) (ha : a < 2 * p), a ∉ S → ∀ u,
      cnt (insert a S) u = cnt S u + if addGrp I ε δ a ha = u then 1 else 0 := by
    intro S a ha haS u
    simp only [hcnt]
    rw [filter_insert]
    by_cases h : addGrp I ε δ a ha = u
    · rw [if_pos ((hgrp a ha u).1 h), card_insert_of_notMem (fun hm => haS (mem_filter.1 hm).1),
        if_pos h]
    · rw [if_neg (fun hc => h ((hgrp a ha u).2 hc)), if_neg h, add_zero]
  have hsum : ∀ S : Finset ℕ, S ⊆ range (2 * p) → ∑ u, cnt S u = S.card := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; simp [hcnt]
    | insert a S haS ih =>
      intro hS
      have ha : a < 2 * p := mem_range.1 (hS (mem_insert_self _ _))
      rw [card_insert_of_notMem haS, ← ih ((subset_insert _ _).trans hS)]
      simp only [hins S a ha haS, sum_add_distrib, sum_ite_eq, mem_univ, if_true]
  -- the profile of a subset of `[0, 2p)` counts its labels group by group
  have hprofF : ∀ S ⊆ range (2 * p), ∀ k : ℕ,
      ((range p).filter fun i => pairCell I ε δ i = k ∧ 2 * i ∈ S).card =
      (S.filter fun z => pairCell I ε δ (z / 2) = k ∧ decide (z % 2 = 1) = false).card := by
    intro S hS k
    refine card_nbij' (fun i => 2 * i) (fun z => z / 2) ?_ ?_ ?_ ?_
    · intro i hi
      obtain ⟨_, hik, hiS⟩ := mem_filter.1 hi
      refine mem_filter.2 ⟨hiS, ?_, ?_⟩
      · show pairCell I ε δ (2 * i / 2) = k
        rw [show 2 * i / 2 = i by omega]; exact hik
      · simp
    · intro z hz
      obtain ⟨hzS, hzk, hz2⟩ := mem_filter.1 hz
      have := mem_range.1 (hS hzS)
      have hz2' : z % 2 ≠ 1 := by simpa using hz2
      refine mem_filter.2 ⟨mem_range.2 ?_, hzk, ?_⟩
      · show z / 2 < p; omega
      · show 2 * (z / 2) ∈ S; rw [show 2 * (z / 2) = z by omega]; exact hzS
    · intro i _; show 2 * i / 2 = i; omega
    · intro z hz
      have hz2' : z % 2 ≠ 1 := by simpa using (mem_filter.1 hz).2.2
      show 2 * (z / 2) = z; omega
  have hprofT : ∀ S ⊆ range (2 * p), ∀ k : ℕ,
      ((range p).filter fun i => pairCell I ε δ i = k ∧ 2 * i + 1 ∈ S).card =
      (S.filter fun z => pairCell I ε δ (z / 2) = k ∧ decide (z % 2 = 1) = true).card := by
    intro S hS k
    refine card_nbij' (fun i => 2 * i + 1) (fun z => z / 2) ?_ ?_ ?_ ?_
    · intro i hi
      obtain ⟨_, hik, hiS⟩ := mem_filter.1 hi
      refine mem_filter.2 ⟨hiS, ?_, ?_⟩
      · show pairCell I ε δ ((2 * i + 1) / 2) = k
        rw [show (2 * i + 1) / 2 = i by omega]; exact hik
      · simp only [decide_eq_true_eq]; omega
    · intro z hz
      obtain ⟨hzS, hzk, hz2⟩ := mem_filter.1 hz
      have := mem_range.1 (hS hzS)
      have hz2' : z % 2 = 1 := by simpa using hz2
      refine mem_filter.2 ⟨mem_range.2 ?_, hzk, ?_⟩
      · show z / 2 < p; omega
      · show 2 * (z / 2) + 1 ∈ S; rw [show 2 * (z / 2) + 1 = z by omega]; exact hzS
    · intro i _; show (2 * i + 1) / 2 = i; omega
    · intro z hz
      have hz2' : z % 2 = 1 := by simpa using (mem_filter.1 hz).2.2
      show 2 * (z / 2) + 1 = z; omega
  -- every group of `[0, 2p)` has `b_s` labels, split between `F` and `P`
  have hBcnt : ∀ u : Fin N × Bool, cnt (range (2 * p)) u = smallB I ε δ u.1 := by
    rintro ⟨s, b⟩
    rw [smallB_eq_card]
    cases b
    · rw [show cnt (range (2 * p)) (s, false) = _ from (hprofF _ subset_rfl s).symm]
      congr 1; ext i; simp only [mem_filter, mem_range]; constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2, by omega⟩
    · rw [show cnt (range (2 * p)) (s, true) = _ from (hprofT _ subset_rfl s).symm]
      congr 1; ext i; simp only [mem_filter, mem_range]; constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2, by omega⟩
  have hnr : ∀ u, n u + r u = smallB I ε δ u.1 := by
    intro u
    rw [hn_eq, ← hBcnt]
    simp only [hcnt, hrdef, hPdef]
    rw [← card_union_of_disjoint (disjoint_filter_filter sdiff_disjoint)]
    congr 1
    ext z
    simp only [mem_union, mem_filter, mem_sdiff]
    constructor
    · rintro (⟨⟨h1, _⟩, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2⟩
      · exact ⟨hF h1, h2⟩
    · rintro ⟨h1, h2⟩
      by_cases hz : z ∈ F
      · exact Or.inr ⟨hz, h2⟩
      · exact Or.inl ⟨⟨h1, hz⟩, h2⟩
  -- the group value: `h_j(r + e_u + e_v)` times the factorial factor
  set Nm : Fin N × Bool → Fin N × Bool → ℝ := fun u v =>
    hWeight I ε δ j (extendN fun s => addDisp r u v (s, false))
        (extendN fun s => addDisp r u v (s, true)) *
      ∏ s : Fin N, (((remDisp n u v (s, false)).factorial : ℝ) *
        ((remDisp n u v (s, true)).factorial : ℝ) / ((smallB I ε δ s).factorial : ℝ)) with hNm
  -- (a) an entry depends only on the groups of its indices
  have hentry : ∀ x y : P, x ≠ y →
      fTilde I ε δ j (insert x.1 (insert y.1 F)) = Nm (g x) (g y) := by
    intro x y hxy
    have hxy' : x.1 ≠ y.1 := fun h' => hxy (Subtype.ext h')
    have hS : insert x.1 (insert y.1 F) ⊆ range (2 * p) :=
      insert_subset (mem_range.2 (hPr _ x.2)) (insert_subset (mem_range.2 (hPr _ y.2)) hF)
    have hc : ∀ u, cnt (insert x.1 (insert y.1 F)) u = addDisp r (g x) (g y) u := by
      intro u
      rw [hins _ _ (hPr _ x.2) (by simp [hxy', hPF _ x.2]) u,
        hins _ _ (hPr _ y.2) (hPF _ y.2) u]
      simp only [addDisp, hg, hrdef]
      by_cases h1 : addGrp I ε δ x.1 (hPr x.1 x.2) = u <;>
        by_cases h2 : addGrp I ε δ y.1 (hPr y.1 y.2) = u <;>
        simp [h1, h2, eq_comm (a := u)]
    have hout : ∀ (k : ℕ) (q : ℕ → Prop) [DecidablePred q], ¬ k < N →
        ((range p).filter fun i => pairCell I ε δ i = k ∧ q i).card = 0 := by
      intro k q _ hk
      rw [card_eq_zero, filter_eq_empty_iff]
      rintro i hi ⟨hik, _⟩
      exact hk (hik ▸ pairCell_lt I ε δ (mem_range.1 hi))
    have h1 : (profile I ε δ (insert x.1 (insert y.1 F))).1 =
        extendN fun s => addDisp r (g x) (g y) (s, false) := by
      funext k
      simp only [profile, extendN]
      split_ifs with hk
      · rw [hprofF _ hS k]; exact hc (⟨k, hk⟩, false)
      · exact hout k _ hk
    have h2 : (profile I ε δ (insert x.1 (insert y.1 F))).2 =
        extendN fun s => addDisp r (g x) (g y) (s, true) := by
      funext k
      simp only [profile, extendN]
      split_ifs with hk
      · rw [hprofT _ hS k]; exact hc (⟨k, hk⟩, true)
      · exact hout k _ hk
    have hkey : ∀ w : Fin N × Bool,
        smallB I ε δ w.1 - addDisp r (g x) (g y) w = remDisp n (g x) (g y) w := by
      intro w
      have := hnr w
      simp only [addDisp, remDisp]
      split_ifs <;> omega
    rw [fTilde, h1, h2, hNm, prod_range]
    congr 1
    refine prod_congr rfl fun s _ => ?_
    have hs : (s : ℕ) < N := s.2
    have k1 := hkey (s, false)
    have k2 := hkey (s, true)
    simp only at k1 k2
    simp only [extendN, hs, dif_pos, Fin.eta]
    rw [k1, k2]
  -- (b) the fixed display `r` is box-valid of total `p - 2`
  have hbox : ∀ w, r w ≤ smallB I ε δ w.1 := fun w => by have := hnr w; omega
  have htot : ∑ w, r w + 2 = p := by
    simp only [hrdef]; rw [hsum F hF]; exact hFc
  -- (c) multiplicities cancel the factorial reductions
  set c : ℝ := (∏ w : Fin N × Bool, ((n w).factorial : ℝ)) /
      ∏ s : Fin N, ((smallB I ε δ s).factorial : ℝ) with hc
  have hcpos : 0 < c := by
    rw [hc]; positivity
  have hfact : ∀ u v, (1 ≤ n u ∧ 1 ≤ n v ∧ (u = v → 2 ≤ n u)) →
      n u * (n v - if u = v then 1 else 0) * ∏ w, (remDisp n u v w).factorial =
        ∏ w, (n w).factorial := by
    rintro u v ⟨hu, hv, huv⟩
    by_cases h : u = v
    · subst h
      have h2 := huv rfl
      rw [if_pos rfl, ← mul_prod_erase univ (fun w => (remDisp n u u w).factorial) (mem_univ u),
        ← mul_prod_erase univ (fun w => (n w).factorial) (mem_univ u)]
      have hrest : ∏ w ∈ univ.erase u, (remDisp n u u w).factorial =
          ∏ w ∈ univ.erase u, (n w).factorial :=
        prod_congr rfl fun w hw => by simp [remDisp, ne_of_mem_erase hw]
      rw [hrest, ← mul_assoc]
      congr 1
      simp only [remDisp, if_true]
      rw [mul_assoc, Nat.mul_factorial_pred (by omega : n u - 1 ≠ 0),
        Nat.mul_factorial_pred (by omega : n u ≠ 0)]
    · have hv' : v ∈ univ.erase u := mem_erase.2 ⟨Ne.symm h, mem_univ v⟩
      rw [if_neg h, Nat.sub_zero,
        ← mul_prod_erase univ (fun w => (remDisp n u v w).factorial) (mem_univ u),
        ← mul_prod_erase (univ.erase u) (fun w => (remDisp n u v w).factorial) hv',
        ← mul_prod_erase univ (fun w => (n w).factorial) (mem_univ u),
        ← mul_prod_erase (univ.erase u) (fun w => (n w).factorial) hv']
      have hrest : ∏ w ∈ (univ.erase u).erase v, (remDisp n u v w).factorial =
          ∏ w ∈ (univ.erase u).erase v, (n w).factorial :=
        prod_congr rfl fun w hw => by
          simp [remDisp, ne_of_mem_erase hw, ne_of_mem_erase (mem_of_mem_erase hw)]
      have hru : remDisp n u v u = n u - 1 := by simp [remDisp, h]
      have hrv : remDisp n u v v = n v - 1 := by simp [remDisp, Ne.symm h]
      rw [hrest, hru, hrv, ← Nat.mul_factorial_pred (by omega : n u ≠ 0),
        ← Nat.mul_factorial_pred (by omega : n v ≠ 0)]
      ring
  have hiff : ∀ u v, (1 ≤ n u ∧ 1 ≤ n v ∧ (u = v → 2 ≤ n u)) ↔
      (r u + 1 ≤ smallB I ε δ u.1 ∧ r v + 1 ≤ smallB I ε δ v.1 ∧
        (u = v → r u + 2 ≤ smallB I ε δ u.1)) := by
    intro u v
    have hu := hnr u
    have hv := hnr v
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by omega, by omega, fun he => by have := h3 he; omega⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by omega, by omega, fun he => by have := h3 he; omega⟩
  have hcancel : ∀ u v, (n u : ℝ) * ((n v : ℝ) - if u = v then 1 else 0) * Nm u v =
      c * (1 * (if r u + 1 ≤ smallB I ε δ u.1 ∧ r v + 1 ≤ smallB I ε δ v.1 ∧
          (u = v → r u + 2 ≤ smallB I ε δ u.1) then
        hWeight I ε δ j (extendN fun s => addDisp r u v (s, false))
          (extendN fun s => addDisp r u v (s, true)) else 0) * 1) := by
    intro u v
    by_cases hcond : 1 ≤ n u ∧ 1 ≤ n v ∧ (u = v → 2 ≤ n u)
    · rw [if_pos ((hiff u v).1 hcond)]
      have hk := hfact u v hcond
      have hsub : ((n v : ℝ) - if u = v then 1 else 0) =
          ((n v - if u = v then 1 else 0 : ℕ) : ℝ) := by
        split_ifs with h
        · rw [Nat.cast_sub (by omega), Nat.cast_one]
        · simp
      have hprod : ∏ s : Fin N, (((remDisp n u v (s, false)).factorial : ℝ) *
            ((remDisp n u v (s, true)).factorial : ℝ) / ((smallB I ε δ s).factorial : ℝ)) =
          (∏ w, ((remDisp n u v w).factorial : ℝ)) /
            ∏ s : Fin N, ((smallB I ε δ s).factorial : ℝ) := by
        rw [prod_div_distrib, Fintype.prod_prod_type]
        congr 1
        refine prod_congr rfl fun s _ => ?_
        rw [Fintype.prod_bool, mul_comm]
      have hk' : (n u : ℝ) * ((n v - if u = v then 1 else 0 : ℕ) : ℝ) *
          ∏ w, ((remDisp n u v w).factorial : ℝ) = ∏ w, ((n w).factorial : ℝ) := by
        exact_mod_cast hk
      simp only [hNm]
      rw [hprod, hc, hsub, ← hk']
      ring
    · have h0 : (n u : ℝ) * ((n v : ℝ) - if u = v then 1 else 0) = 0 := by
        by_cases hu : n u = 0
        · simp [hu]
        by_cases h : u = v
        · subst h
          have : n u = 1 := by
            by_contra hne
            exact hcond ⟨by omega, by omega, fun _ => by omega⟩
          simp [this]
        · have : n v = 0 := by
            by_contra hne
            exact hcond ⟨by omega, by omega, fun e => absurd e h⟩
          simp [this, h]
      rw [if_neg (fun h' => hcond ((hiff u v).2 h')), h0]; simp
  have hR := hWeight_addition_hyp hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas j hj r hbox htot
  have hM := hyp_congr hR c hcpos (fun _ => 1)
  have hNsymm : ∀ u v, Nm u v = Nm v u := by
    intro u v
    have h1 : remDisp n u v = remDisp n v u := by
      funext w; simp only [remDisp]; omega
    have h2 : addDisp r u v = addDisp r v u := by
      funext w; simp only [addDisp]; omega
    simp only [hNm, h1, h2]
  have hNdiag : ∀ u, 0 ≤ Nm u u := by
    intro u
    simp only [hNm]
    refine mul_nonneg ?_ (Finset.prod_nonneg fun s _ => by positivity)
    exact Finset.sum_nonneg fun z _ => by positivity
  have hG := hyp_of_groups g Nm hNsymm hNdiag (by
    convert hM using 1
    funext u v
    exact hcancel u v)
  convert hG using 1
  funext x y
  simp only [adMat]
  split_ifs with hxy
  · rfl
  · exact hentry x y hxy

end Cellcounting.Analysis

namespace Cellcounting.Analysis

open Finset Pseudocode

/-- **Addition signature of `f̃_j`, after fixing and pair summation**
(`lem:binary-signatures` with `lem:binary-contraction`): for `F`, `D` and the pairs of
`L` disjoint in `[0, 2p)` with `|F| + |L| + 2 = p`, the two-addition matrix of
`U ↦ Σ_c f̃_j(F ∪ U ∪ c)` on `D` has at most one positive eigenvalue.
PAPER: sections/signatures.tex:201-210 -/
theorem fTilde_addition (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j ≤ HParam I ε δ)
    (F D : Finset ℕ) (L : List ℕ)
    (hF : ∀ e ∈ F, e < 2 * pSmall I ε δ) (hD : ∀ e ∈ D, e < 2 * pSmall I ε δ)
    (hL : ∀ t ∈ L, t < pSmall I ε δ) (hLnd : L.Nodup) (hFD : Disjoint F D)
    (hLF : ∀ t ∈ L, 2 * t ∉ F ∧ 2 * t + 1 ∉ F) (hLD : ∀ t ∈ L, 2 * t ∉ D ∧ 2 * t + 1 ∉ D)
    (hcard : F.card + L.length + 2 = pSmall I ε δ) :
    Hyp (addMat (fTilde I ε δ j) F D L) := by
  classical
  set p := pSmall I ε δ with hpdef
  set f := fTilde I ε δ j with hfdef
  have hbase : AddSig f (range (2 * p)) p :=
    fTilde_base_addSig hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas j hj
  clear_value p f
  -- a nodup list of pair labels below `p` has at most `p` entries
  have hlenle : ∀ L : List ℕ, L.Nodup → (∀ t ∈ L, t < p) → L.length ≤ p := by
    intro L hnd hlt
    rw [← List.toFinset_card_of_nodup hnd]
    calc L.toFinset.card ≤ (range p).card :=
          card_le_card fun t ht => mem_range.2 (hlt t (List.mem_toFinset.1 ht))
      _ = p := card_range p
  -- summing the pairs of `L` one at a time (`lem:binary-contraction`)
  have key : ∀ L : List ℕ, L.Nodup → (∀ t ∈ L, t < p) →
      AddSig (fun U => chSum L (fun c => f (U ∪ c)))
        ((range (2 * p)).filter (fun e => e / 2 ∉ L)) (p - L.length) := by
    intro L
    induction L with
    | nil =>
      intro _ _
      have h1 : (range (2 * p)).filter (fun e => e / 2 ∉ ([] : List ℕ)) = range (2 * p) := by
        ext e; simp
      simpa [h1, chSum_nil] using hbase
    | cons t L ih =>
      intro hnd hlt
      obtain ⟨htL, hnd'⟩ := List.nodup_cons.1 hnd
      have ih' := ih hnd' fun s hs => hlt s (List.mem_cons_of_mem _ hs)
      have ht := hlt t (List.mem_cons_self ..)
      have hlen := hlenle _ hnd hlt
      simp only [List.length_cons] at hlen
      have h2t : 2 * t ∈ (range (2 * p)).filter (fun e => e / 2 ∉ L) := by
        refine mem_filter.2 ⟨mem_range.2 (by omega), ?_⟩
        rwa [show 2 * t / 2 = t by omega]
      have h2t1 : 2 * t + 1 ∈ (range (2 * p)).filter (fun e => e / 2 ∉ L) := by
        refine mem_filter.2 ⟨mem_range.2 (by omega), ?_⟩
        rwa [show (2 * t + 1) / 2 = t by omega]
      have hstep := addSig_pairSum ih' h2t h2t1 (by omega) (by omega)
      have hφ : pairSum (fun U => chSum L (fun c => f (U ∪ c))) (2 * t) (2 * t + 1) =
          fun U => chSum (t :: L) (fun c => f (U ∪ c)) := by
        funext U
        simp only [pairSum, chSum_cons]
        congr 1
        · congr 1; funext c; rw [insert_union, union_insert]
        · congr 1; funext c; rw [insert_union, union_insert]
      have hΓ : (((range (2 * p)).filter (fun e => e / 2 ∉ L)).erase (2 * t)).erase
          (2 * t + 1) = (range (2 * p)).filter (fun e => e / 2 ∉ t :: L) := by
        ext e
        simp only [mem_erase, mem_filter, mem_range, List.mem_cons, not_or]
        constructor
        · rintro ⟨h1, h2, h3, h4⟩
          exact ⟨h3, by omega, h4⟩
        · rintro ⟨h3, h5, h4⟩
          exact ⟨by omega, by omega, h3, h4⟩
      have hk : p - L.length - 1 = p - (t :: L).length := by simp only [List.length_cons]; omega
      rw [hφ, hΓ, hk] at hstep
      exact hstep
  -- the fixed set `F` and the index set `D` avoid the summed pairs
  have hsubΓ : ∀ G : Finset ℕ, (∀ e ∈ G, e < 2 * p) → (∀ t ∈ L, 2 * t ∉ G ∧ 2 * t + 1 ∉ G) →
      G ⊆ (range (2 * p)).filter (fun e => e / 2 ∉ L) := by
    intro G hG hLG e he
    refine mem_filter.2 ⟨mem_range.2 (hG e he), fun hmem => ?_⟩
    have h2 : e = 2 * (e / 2) ∨ e = 2 * (e / 2) + 1 := by omega
    rcases h2 with h2 | h2
    · exact (hLG _ hmem).1 (h2 ▸ he)
    · exact (hLG _ hmem).2 (h2 ▸ he)
  have hsig := (key L hLnd hL).2 F (hsubΓ F hF hLF) D (hsubΓ D hD hLD) hFD (by omega)
  suffices hfun : addMat f F D L = adMat (fun U => chSum L (fun c => f (U ∪ c))) F D by
    rw [hfun]; exact hsig
  funext x y
  simp only [addMat, adMat, insert_union]

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved from children · `fTilde_addition`, `fTilde_base_addSig`, `addSig_pairSum` closed;
  rests on `hWeight_addition_hyp` (open, `HWeightAdditionHyp.lean`) and `hyp_cubic_contract`
-/
