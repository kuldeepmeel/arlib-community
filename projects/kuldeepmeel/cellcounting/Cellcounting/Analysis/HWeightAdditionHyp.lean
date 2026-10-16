import Cellcounting.Analysis.Contamination
import Cellcounting.Analysis.HyperbolicForm
import Cellcounting.Analysis.HWeightRemovalHyp

/-!
# The addition signature of `h_j` (`cor:hj-signatures`, addition half)

`integer-signatures.tex:325-400`.  Each small cell `s` contributes two count
coordinates, `(s, false)` for its row view `x_s` and `(s, true)` for its column view
`y_s`.  At every box-valid display `r` (`0 ≤ r_u ≤ b_s`) of total `p - 2`, the
two-addition matrix `(h_j(r + e_u + e_v))_{u, v}`, with zero entries for invalid
additions (`r_u + 1 > b_s`, or `u = v` and `r_u + 2 > b_s`), has at most one positive
eigenvalue (`Hyp`).

The proof is the paper's (`integer-signatures.tex:394-396`): reflect every coordinate,
including the large ones summed at balance, inside the softened laminar table model
`hjModel` of the removal half (`HWeightRemovalHyp.lean`).

* `EdgeModel.refl` negates the physical intervals and the factor arguments; it again
  satisfies `Hyps` (`refl_hyps`), and its laminar weight at `w` is the original weight at
  the reflected display `mE - w` (`refl_F`): its row view of `w` is the column view of
  `mE - w` and conversely.
* Summing a set `A` of cells at balance commutes with the reflection (`refl_WA`), so the
  two-addition matrix of the balanced sum of `hjModel` at a small display `r` of total
  `p - 2` is the two-removal matrix of the balanced sum of the reflected model at
  `b - r`, of total `p + 2`.  `good_WA` for the reflected model gives `Hyp` there.
* The entries are the balanced sums of `hjModel` itself at `r + e_u + e_v`, which converge
  to `h_j` as `α ↓ 0` (`hj_tendsto`) at valid additions and vanish at invalid ones, and
  `Hyp` passes to the limit (`hyp_of_tendsto`).

`h_j` itself is *not* reflection-symmetric (a small cell loads its row with `x_s` and its
column with `b_s - y_s`), so the reflection happens inside the model, not in `h_j`.
-/

namespace Cellcounting.Analysis

open Pseudocode Finset

namespace EdgeModel

variable {C Rw Cl : Type*} [Fintype C] [DecidableEq C] [Fintype Rw] [DecidableEq Rw]
  [Fintype Cl] [DecidableEq Cl]

variable (E : EdgeModel C Rw Cl)

/-- INTERNAL: the reflected model: every coordinate and every factor argument negated,
so that its row view of `w` is the column view of `mE - w` and conversely.
TEXLINE: sections/integer-signatures.tex:394-396 -/
def refl : EdgeModel C Rw Cl where
  row := E.row
  col := E.col
  lo := fun c => -E.hi c
  hi := fun c => -E.lo c
  φR := fun r s => E.φR r (-s)
  φK := fun k s => E.φK k (-s)
  ψ := fun c s => E.ψ c (-s)

omit [Fintype C] [DecidableEq C] [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl] in
/-- INTERNAL: reflection preserves positivity, log-concavity and widths. -/
theorem refl_hyps (hE : E.Hyps) : E.refl.Hyps where
  width c := by have := hE.width c; simp only [refl]; omega
  φR_pos r s := hE.φR_pos r _
  φK_pos k s := hE.φK_pos k _
  ψ_pos c s := hE.ψ_pos c _
  φR_lc r s := by
    have := hE.φR_lc r (-s)
    simp only [refl, show -(s - 1) = -s + 1 by ring, show -(s + 1) = -s - 1 by ring]
    linarith
  φK_lc k s := by
    have := hE.φK_lc k (-s)
    simp only [refl, show -(s - 1) = -s + 1 by ring, show -(s + 1) = -s - 1 by ring]
    linarith
  ψ_lc c s := by
    have := hE.ψ_lc c (-s)
    simp only [refl, show -(s - 1) = -s + 1 by ring, show -(s + 1) = -s - 1 by ring]
    linarith

omit [Fintype C] [DecidableEq C] [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl] in
/-- INTERNAL: reflection keeps the capacities. -/
theorem refl_mE : E.refl.mE = E.mE := by
  funext p; simp only [mE, refl]; ring

omit [DecidableEq C] [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl] in
/-- INTERNAL: reflection keeps the total. -/
theorem refl_Rtot : E.refl.Rtot = E.Rtot := by
  simp only [Rtot, refl]; exact Finset.sum_congr rfl fun c _ => by ring

omit [Fintype C] [DecidableEq C] [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl] in
/-- INTERNAL: reflection keeps the widths. -/
theorem refl_width (c : C) : E.refl.hi c - E.refl.lo c = E.hi c - E.lo c := by
  simp only [refl]; ring

omit [DecidableEq C] in
/-- INTERNAL: the reflected model's two-view weight is the original two-view weight of
the negated views. -/
theorem refl_weight2 (XR XK : C → ℤ) :
    E.refl.weight2 XR XK = E.weight2 (fun c => -XR c) (fun c => -XK c) := by
  simp only [weight2, refl, Finset.sum_neg_distrib]
  rfl

omit [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl] in
/-- INTERNAL: the full sum of the capacities is twice the total. -/
theorem sum_mE : ∑ p, E.mE p = 2 * E.Rtot := by
  rw [sum_prod_bool]; simp only [mE, Rtot]; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

omit [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl] in
/-- INTERNAL: `w` is a valid full display iff its reflection `mE - w` is. -/
theorem valid_refl_iff (w : C × Bool → ℤ) :
    Valid E.mE univ E.Rtot (fun p => E.mE p - w p) ↔ Valid E.mE univ E.Rtot w := by
  have hs := E.sum_mE
  constructor
  · rintro ⟨h0, h1, _, h3⟩
    simp only at h0 h1 h3
    refine ⟨fun p => by have := h1 p (mem_univ _); omega, fun p _ => by have := h0 p; omega,
      fun p hp => absurd (mem_univ p) hp, ?_⟩
    rw [Finset.sum_sub_distrib] at h3; omega
  · rintro ⟨h0, h1, _, h3⟩
    refine ⟨fun p => by have := h1 p (mem_univ _); simp only; omega,
      fun p _ => by have := h0 p; simp only; omega, fun p hp => absurd (mem_univ p) hp, ?_⟩
    rw [Finset.sum_sub_distrib]; omega

/-- INTERNAL: the reflected laminar weight is the original weight at the reflected
display `mE - w`. -/
theorem refl_F (w : C × Bool → ℤ) : E.refl.F w = E.F (fun p => E.mE p - w p) := by
  by_cases hw : Valid E.mE univ E.Rtot w
  · have hw' : Valid E.refl.mE univ E.refl.Rtot w := by rwa [refl_mE, refl_Rtot]
    rw [E.refl.F_eq_weight2 w hw', E.F_eq_weight2 _ ((E.valid_refl_iff w).2 hw), refl_weight2]
    congr 1 <;> funext c <;> simp only [refl, mE] <;> ring
  · have hw' : ¬ Valid E.refl.mE univ E.refl.Rtot w := by rwa [refl_mE, refl_Rtot]
    have hr : ¬ Valid E.mE univ E.Rtot (fun p => E.mE p - w p) := fun h =>
      hw ((E.valid_refl_iff w).1 h)
    simp only [F, laminarWeight]
    rw [if_neg hw', if_neg hr]

/-- INTERNAL: summing the cells of `A` at balance commutes with reflection: at a display
`w` vanishing on `A`, the reflected balanced sum is the original balanced sum at the
display reflected on the active coordinates. -/
theorem refl_WA (A : Finset C) (w : C × Bool → ℤ)
    (hw : ∀ c ∈ A, w (c, true) = 0 ∧ w (c, false) = 0) :
    E.refl.WA A w = E.WA A (fun p => if p.1 ∈ A then 0 else E.mE p - w p) := by
  classical
  have hw' : ∀ c ∈ A, (fun p : C × Bool => if p.1 ∈ A then 0 else E.mE p - w p) (c, true) = 0 ∧
      (fun p : C × Bool => if p.1 ∈ A then 0 else E.mE p - w p) (c, false) = 0 := by
    intro c hc; simp [hc]
  simp only [WA]
  rw [if_pos hw, if_pos hw']
  have hbal : E.refl.bal A = E.bal A := by
    unfold bal; congr 1; funext c; rw [refl_width]
  have hshift : E.refl.shift A = E.shift A := by
    funext κ p; unfold shift; rw [refl_width]
  rw [hbal, hshift]
  refine Finset.sum_nbij' (fun κ c => if c ∈ A then E.hi c - E.lo c - κ c else κ c)
    (fun κ c => if c ∈ A then E.hi c - E.lo c - κ c else κ c) ?_ ?_ ?_ ?_ ?_
  · intro κ hκ
    simp only [bal, Fintype.mem_piFinset] at hκ ⊢
    intro c
    have := hκ c
    by_cases hc : c ∈ A
    · simp only [hc, if_true, mem_Icc] at this ⊢; omega
    · simpa [hc] using this
  · intro κ hκ
    simp only [bal, Fintype.mem_piFinset] at hκ ⊢
    intro c
    have := hκ c
    by_cases hc : c ∈ A
    · simp only [hc, if_true, mem_Icc] at this ⊢; omega
    · simpa [hc] using this
  · intro κ _; funext c; by_cases hc : c ∈ A <;> simp [hc]
  · intro κ _; funext c; by_cases hc : c ∈ A <;> simp [hc]
  · intro κ _
    rw [refl_F]
    congr 1
    funext p
    obtain ⟨c, b⟩ := p
    by_cases hc : c ∈ A
    · have := hw c hc
      cases b <;> simp [shift, hc, this, mE]
    · simp [shift, hc]

end EdgeModel

/-- INTERNAL: the display `r + e_u + e_v`.
TEXLINE: sections/integer-signatures.tex:325-332 -/
def addDisp {N : ℕ} (r : Fin N × Bool → ℕ) (u v : Fin N × Bool) : Fin N × Bool → ℕ :=
  fun w => r w + (if w = u then 1 else 0) + (if w = v then 1 else 0)

open Filter Topology in
/-- **Addition signature of `h_j`** (`cor:hj-signatures`, second assertion): at every
box-valid display `r` of total `p - 2` on the row/column views of the small cells, the
two-addition matrix of `h_j`, with zero entries for invalid additions, has at most one
positive eigenvalue.  `(s, false)` is the row view `x_s`, `(s, true)` the column view
`y_s`.
PAPER: sections/integer-signatures.tex:325-332 -/
theorem hWeight_addition_hyp (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (j : ℕ) (hj : j ≤ HParam I ε δ)
    (r : Fin (nSmall I ε δ) × Bool → ℕ) (hbox : ∀ w, r w ≤ smallB I ε δ w.1)
    (htot : ∑ w, r w + 2 = pSmall I ε δ) :
    Hyp (fun u v : Fin (nSmall I ε δ) × Bool =>
      if r u + 1 ≤ smallB I ε δ u.1 ∧ r v + 1 ≤ smallB I ε δ v.1 ∧
          (u = v → r u + 2 ≤ smallB I ε δ u.1) then
        hWeight I ε δ j (extendN fun s => addDisp r u v (s, false))
          (extendN fun s => addDisp r u v (s, true))
      else 0) := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : Fin (nSmall I ε δ) × Bool → ℕ, g = fun w => smallB I ε δ w.1 - r w :=
    ⟨_, rfl⟩
  set zs := dispZ (fun s => g (s, false)) (fun s => g (s, true)) with hzs
  have hgb : ∀ w, ((g w : ℕ) : ℤ) = smallB I ε δ w.1 - r w := by
    intro w; rw [hg]; push_cast [hbox w]; ring
  have hrtot : ∑ w, (r w : ℤ) + 2 = pSmall I ε δ := by exact_mod_cast htot
  have hpb : (pSmall I ε δ : ℤ) = ∑ s : Fin (nSmall I ε δ), (smallB I ε δ s : ℤ) := by
    exact_mod_cast pSmall_eq_sum
  have hztot : ∑ s, (((g (s, false) : ℕ) : ℤ) + ((g (s, true) : ℕ) : ℤ)) =
      (pSmall I ε δ : ℤ) + 2 := by
    simp only [hgb]
    rw [Fintype.sum_prod_type] at hrtot
    simp only [Fintype.sum_bool] at hrtot
    have : ∑ s : Fin (nSmall I ε δ), (((smallB I ε δ s : ℤ) - r (s, false)) +
        ((smallB I ε δ s : ℤ) - r (s, true))) =
        2 * ∑ s : Fin (nSmall I ε δ), (smallB I ε δ s : ℤ) -
          ∑ s, ((r (s, true) : ℤ) + r (s, false)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, ← hpb]; linarith
  have hmE : ∀ (α : ℝ) (w : Fin (nSmall I ε δ) × Bool),
      (hjModel I ε δ j α).mE (smallEmb w) = smallB I ε δ w.1 := by
    intro α w
    simp [smallEmb, EdgeModel.mE, hjModel, hjHi, hjLo, tmEntry, smallB]
  have hact : ∀ w : Fin (nSmall I ε δ) × Bool, smallEmb w ∈ EdgeModel.actS (largeSet I ε δ) := by
    intro w; simp [EdgeModel.actS, largeSet, smallEmb]
  have hgoodα : ∀ α ∈ Set.Ioo (0 : ℝ) 1, Good (hjModel I ε δ j α).mE
      (EdgeModel.actS (largeSet I ε δ)) (pSmall I ε δ)
      ((hjModel I ε δ j α).refl.WA (largeSet I ε δ)) := by
    intro α hα
    have := (hjModel I ε δ j α).refl.good_WA
      ((hjModel I ε δ j α).refl_hyps (hjModel_hyps I ε δ j hα.1 hα.2.le)) (largeSet I ε δ)
    simp only [EdgeModel.refl_width] at this
    rwa [EdgeModel.refl_mE, EdgeModel.refl_Rtot, hj_rem_total] at this
  have heq : ∀ (α : ℝ) (a b : Fin (nSmall I ε δ) × Bool),
      remMat ((hjModel I ε δ j α).refl.WA (largeSet I ε δ)) zs (smallEmb a) (smallEmb b) =
        (hjModel I ε δ j α).WA (largeSet I ε δ)
          (dispZ (fun s => addDisp r a b (s, false)) (fun s => addDisp r a b (s, true))) := by
    intro α a b
    simp only [remMat]
    rw [EdgeModel.refl_WA]
    · congr 1
      funext p
      obtain ⟨c, bb⟩ := p
      rcases c with s | c
      · have hp : ((Sum.inl s, bb) : TmCell I ε δ × Bool) = smallEmb (s, !bb) := by
          simp [smallEmb]
        have hA : (Sum.inl s : TmCell I ε δ) ∉ largeSet I ε δ := by simp [largeSet]
        simp only [hA, if_false]
        rw [hp, dispZ_emb (addDisp r a b), Pi.sub_apply, Pi.sub_apply, hzs, dispZ_emb g,
          Pi.single_apply, Pi.single_apply, hmE]
        simp only [smallEmb_inj.eq_iff]
        rw [hgb]
        unfold addDisp
        push_cast
        split_ifs <;> ring
      · have hA : (Sum.inr c : TmCell I ε δ) ∈ largeSet I ε δ := by simp [largeSet]
        simp [hA, dispZ]
    · intro c hc
      rcases c with s | c
      · simp [largeSet] at hc
      · simp [hzs, dispZ, smallEmb]
  refine hyp_of_tendsto (l := 𝓝[>] (0 : ℝ))
    (Q := fun α a b => remMat ((hjModel I ε δ j α).refl.WA (largeSet I ε δ)) zs
      (smallEmb a) (smallEmb b)) ?_ ?_
  · intro a b
    simp only [heq]
    by_cases hc : r a + 1 ≤ smallB I ε δ a.1 ∧ r b + 1 ≤ smallB I ε δ b.1 ∧
        (a = b → r a + 2 ≤ smallB I ε δ a.1)
    · simp only [if_pos hc]
      have hbox' : ∀ w, addDisp r a b w ≤ smallB I ε δ w.1 := by
        intro w
        obtain ⟨h1, h2, h3⟩ := hc
        have := hbox w
        unfold addDisp
        by_cases hwa : w = a <;> by_cases hwb : w = b
        · subst hwa; subst hwb; have := h3 rfl; simp; omega
        · subst hwa; simp [hwb]; omega
        · subst hwb; simp [hwa]; omega
        · simp [hwa, hwb]; omega
      refine hj_tendsto j _ _ (fun s => hbox' (s, false)) (fun s => hbox' (s, true)) ?_
      have h1 : ∑ s, (((addDisp r a b (s, false) : ℕ) : ℤ) +
          ((addDisp r a b (s, true) : ℕ) : ℤ)) = ∑ w, ((addDisp r a b w : ℕ) : ℤ) := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun s _ => by rw [Fintype.sum_bool]; ring
      rw [h1]
      unfold addDisp
      push_cast
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      linarith
    · simp only [if_neg hc]
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with α hα
      symm
      apply ((hjModel I ε δ j α).good_WA (hjModel_hyps I ε δ j hα.1 hα.2.le) (largeSet I ε δ)).1
      intro hv
      apply hc
      have h1 := hv.2.1 (smallEmb a) (hact a)
      have h2 := hv.2.1 (smallEmb b) (hact b)
      rw [dispZ_emb (addDisp r a b), hmE] at h1 h2
      unfold addDisp at h1 h2
      by_cases hab : a = b
      · subst hab; simp only [if_true] at h1; omega
      · rw [if_pos rfl, if_neg hab] at h1
        rw [if_neg (Ne.symm hab), if_pos rfl] at h2
        refine ⟨by omega, by omega, fun h => absurd h hab⟩
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with α hα
    exact hyp_comp_inj ((hgoodα α hα).2.2 zs (hj_valid_dispZ j α _ _
      (fun s => by rw [hg]; exact (Nat.sub_le _ _)) (fun s => by rw [hg]; exact (Nat.sub_le _ _))
      _ hztot)) smallEmb smallEmb_inj

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · `hWeight_addition_hyp` via the reflected model `EdgeModel.refl`, `refl_WA`, and the removal half's `hj_tendsto`/`hyp_of_tendsto`
* r1 · handoff rejected twice (`fta-hwadd-1`, `fta-hwadd-2`: no admission receipt); still open
* r1 · stated · child of `fTilde_addition` (via `fTilde_base_addSig`); substitution
  `x ↦ b - y` in `h_j` does not reduce it to `hWeight_removal_hyp` (`baseLoad` is not
  reflection-symmetric)
-/
