import Cellcounting.Analysis.CostScale
import Cellcounting.Model.Prior
import Cellcounting.Interface.ProgramModel
import Cellcounting.Analysis.ForestPenaltyBound

/-!
# The program's penalty satisfies `0 ≤ D ≤ H` (`lem:forest`)

`Cellcounting.Analysis.prep_penalty_bound`: on a feasible input, the context
`prepCtx I ε δ` that `Program.fpras` builds (tightened instance, small/large split,
maximum-capacity spanning forest, roots, leaf-elimination order) makes
`Program.penalty` satisfy `0 ≤ D(x, y, z) ≤ H` for every box-valid small profile
`(x, y)` and every free vector `z` in the extended box `∏_{e ∈ F} [0, b_e + 1]`.

This is what makes the bin walk and the ratio samples of the oracle polynomial:
they read `⌊aD/H⌋`-sized exponents.  It rests on the correctness of S1–S4:
the tightened instance has a feasible table `X*` (exact feasibility, i.e. the
Edmonds–Karp augmentation bound, `sections/scales.tex:12-21`, cited to
[EK1972, Theorem 1]), Kruskal produces a maximum-capacity spanning forest (the
path inequality `b_e ≤ b_t`), and `orient` lists every nonroot vertex once,
leaves before parents.

Proved here so far: the `0 ≤ D` half for any context with `A ≥ 0`
(`penalty_nonneg`); for `prepCtx`, `Aq` is `SNat.toRat` of `A`.  The `D ≤ H` half is
`lem:forest`: with a feasible table `X*` of the tightened instance, the cut identities
give `Σ_roots |δ_v| ≤ 2dW` and `|z_t - X*_t| ≤ 4 d b_t`, hence
`D ≤ A (2dW + 4d²) ≤ 10 A d² (W + 1) = H`.  The feasible `X*` exists because the
feasibility test is exact; that exactness rests on the Edmonds–Karp augmentation bound,
which the paper cites ([EK1972, Theorem 1], `sections/scales.tex:14-17`) and does not
prove, so it is a candidate `Prior` field stated about `Program.maxFlow`.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Program
open Cellcounting.Model.Operations
open Cellcounting.Interface

/-- INTERNAL: `|x|` as the program computes it is nonnegative. -/
theorem penalty_absQ_nonneg (x : SRat) : 0 ≤ (absQ x).val.get := by
  unfold absQ
  simp only [costVb, SRat.get_lit]
  split
  · rename_i h; simp only [SRat.get_sub, SRat.get_lit, SRat.val_lt] at h ⊢
    have := of_decide_eq_true h; linarith
  · rename_i h; simp only [costVp]; simp only [SRat.val_lt, SRat.get_lit] at h
    have : ¬ (x.get < 0) := fun hc => h (decide_eq_true hc)
    linarith

/-- INTERNAL: `dist(x, [0, b])` as the program computes it is nonnegative. -/
theorem penalty_distQ_nonneg (x b : SRat) : 0 ≤ (distQ x b).val.get := by
  unfold distQ
  simp only [costVb, SRat.get_lit]
  split
  · rename_i h; simp only [SRat.get_sub, SRat.get_lit, SRat.val_lt] at h ⊢
    have := of_decide_eq_true h; linarith
  · simp only [costVb]
    split
    · rename_i h; simp only [SRat.get_sub, SRat.val_lt] at h ⊢
      have := of_decide_eq_true h; linarith
    · simp only [costVp, SRat.get_lit]; exact le_refl _

/-- INTERNAL: the penalty is nonnegative for any context whose `A` is nonnegative: it is
`A` times a sum of absolute values and of distances divided by nonnegative bounds.
This is the `0 ≤ D` half of `prep_penalty_bound`.
TEXLINE: sections/scales.tex:121-126 -/
theorem penalty_nonneg (C : Ctx) (hA : 0 ≤ C.Aq.get) (x y : List SNat) (zf : List SRat) :
    0 ≤ (penalty C x y zf).val.get := by
  unfold penalty
  simp only [costVb, SRat.get_mul, SRat.get_add]
  apply mul_nonneg hA
  apply add_nonneg
  · apply foldl_val_inv (fun s : SRat => 0 ≤ s.get)
    · intro s v hs
      simp only [costVb, SRat.get_add]
      exact add_nonneg hs (penalty_absQ_nonneg _)
    · simp
  · apply repeatFor_val_inv (fun s : SRat => 0 ≤ s.get)
    · intro t s hs
      simp only [costVb, SRat.get_add, SRat.get_div, SNat.get_toRat]
      exact add_nonneg hs (div_nonneg (penalty_distQ_nonneg _ _) (by positivity))
    · simp
/-- INTERNAL: reading entry `k` of a list through a map. -/
theorem map_getD_of_map_eq {α β : Type} {f : α → β} {l : List α} {l' : List β} (h : l.map f = l')
    (d : α) (d' : β) {k : ℕ} (hk : k < l.length) : f (l.getD k d) = l'.getD k d' := by
  subst h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hk]
  rfl

/-- INTERNAL: `buildCtx_view` for `prepCtx`, the context `Program.fpras` builds. -/
theorem prepCtx_view (I : Instance) (ε δ : ℚ) (hf : Pseudocode.feasible I) :
    let C := prepCtx I ε δ
    (C.m, C.n, C.rows.map SNat.get, C.cols.map SNat.get,
      C.small.map (fun (e : Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall,
      C.free.map (fun (e : Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree,
      C.tree.map (fun (e : Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots,
      C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) =
    (I.m, I.n, (List.range I.m).map (Pseudocode.tRow I), (List.range I.n).map (Pseudocode.tCol I),
      Pseudocode.smallCells I ε δ, Pseudocode.nSmall I ε δ, (Pseudocode.forest I ε δ).free,
      Pseudocode.nFree I ε δ, (Pseudocode.forest I ε δ).tree,
      (Pseudocode.forest I ε δ).tree.length, Pseudocode.elimOrder I ε δ, Pseudocode.roots I ε δ,
      Pseudocode.Mf I ε δ, Pseudocode.dParam I, Pseudocode.BParam I ε δ, Pseudocode.HParam I ε δ,
      (Pseudocode.AParam I ε δ : ℚ), (Pseudocode.HParam I ε δ : ℚ), (Pseudocode.BParam I ε δ : ℚ)) :=
  buildCtx_view I ε δ hf

/-- **`0 ≤ D ≤ H` for the program's own context.**
PAPER: sections/scales.tex:131-158 (`lem:forest`, "Consequently, throughout the
extended free box, `0 ≤ D ≤ H`"), for the context built by S1–S4
(sections/scales.tex:8-99). -/
theorem prep_penalty_bound (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : prepFeasible I = true) :
    ∀ (x y : List SNat) (zf : List SRat), ProfileValid (prepCtx I ε δ) x y →
      FreeValid (prepCtx I ε δ) zf →
      0 ≤ (penalty (prepCtx I ε δ) x y zf).val.get ∧
        (penalty (prepCtx I ε δ) x y zf).val.get ≤ (prepCtx I ε δ).H.get := by
  intro x y zf hxy hz
  have hf : Pseudocode.feasible I := by
    have h := (output_eq_fpras I ε δ).2
    unfold prepFeasible prepR prepC prepB at hfeas
    rw [hfeas] at h
    exact of_decide_eq_true h.symm
  have hC := prepCtx_view I ε δ hf
  simp only [Prod.mk.injEq] at hC
  obtain ⟨hCm, hCn, hrows, hcols, hsmall, hnS, hfree, hnF, htree, hnT, hord, hroots, hMf, hd, hB,
    hH, hA, hHq, hBq⟩ := hC
  have hA0 : 0 ≤ (prepCtx I ε δ).Aq.get := by rw [hA]; positivity
  refine ⟨penalty_nonneg _ hA0 x y zf, ?_⟩
  have hpen := penalty_val I ε δ (prepCtx I ε δ) (by
    simp only [Prod.mk.injEq]
    exact ⟨hCm, hCn, hrows, hcols, hsmall, hnS, hfree, hnF, htree, hnT, hord, hroots, hMf, hd, hB,
      hH, hA, hHq, hBq⟩) x y zf
  rw [hpen, hH]
  have hlenS : (prepCtx I ε δ).small.length = Pseudocode.nSmall I ε δ := by
    rw [← List.length_map (f := fun (e : Entry) => (e.1, e.2.1, e.2.2.get)), hsmall]; rfl
  have hlenF : (prepCtx I ε δ).free.length = Pseudocode.nFree I ε δ := by
    rw [← List.length_map (f := fun (e : Entry) => (e.1, e.2.1, e.2.2.get)), hfree]; rfl
  refine pseudo_penalty_le_H I ε δ hε hf _ _ _ (fun k hk => ?_) (fun k hk => ?_)
  · have hb := map_getD_of_map_eq hsmall default (0, 0, 0) (k := k) (by omega)
    have := hxy k (by omega)
    have hb2 : (((prepCtx I ε δ).small.getD k default).2.2.get) = (Pseudocode.smallAt I ε δ k).2.2 := by
      unfold Pseudocode.smallAt; rw [← hb]
    rw [hb2] at this
    exact this
  · have hb := map_getD_of_map_eq hfree default (0, 0, 0) (k := k) (by omega)
    have := hz k (by omega)
    have hb2 : (((prepCtx I ε δ).free.getD k default).2.2.get) = (Pseudocode.freeAt I ε δ k).2.2 := by
      unfold Pseudocode.freeAt; rw [← hb]
    rw [hb2] at this
    exact this

end Cellcounting.Analysis
