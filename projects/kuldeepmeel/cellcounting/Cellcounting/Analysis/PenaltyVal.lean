import Cellcounting.Model.Program
import Cellcounting.Interface.Pseudocode
import Cellcounting.Interface.Encoding
import Cellcounting.Analysis.PhaseWindow
import Cellcounting.Analysis.PseudoElimOrderValid
import Cellcounting.Analysis.TighteningCount

/-!
# The program's penalty is the pseudocode penalty

`penalty_val_proof` states that `Program.penalty`, the exact-rational computation of
`D(x, y, z)` (`sections/scales.tex:113-126`), returns `Pseudocode.penalty` of the viewed
arguments when the context matches the instance.  It is the proof of
`Cellcounting.penalty_val` in `Interface/ProgramModel.lean`.

The program keeps the vertex loads in a list of length `m + n` and the tree values in a
list of length `|T|`, read through `getD`; the pseudocode keeps functions on `ℕ`.  The two
agree because every index written or read is in range: small, free and tree cells lie in
the table (`Analysis.mem_retained`, `Analysis.forest_mem_lt`), eliminated vertices and their
parent edges are in range (`Analysis.pseudo_elimOrder_valid`), and roots are vertices
(`Analysis.mem_roots_iff`).  Loop invariants are carried by `PVRep` (a list of length `N` represents a function on
indices below `N`); every lemma here, including `penalty_val_proof`, is proved.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation Cellcounting.Model.Operations

/-- INTERNAL: the program's prescribed margin of a vertex is the pseudocode margin, given
the tightened margins of the context. TEXLINE: sections/scales.tex:113-126 -/
theorem penaltyVal_getD (l : List SNat) (k : ℕ) (f : ℕ → ℕ) (hl : l.map SNat.get = (List.range k).map f)
    (hf : ∀ i, k ≤ i → f i = 0) (i : ℕ) : (l.getD i default).get = f i := by
  have hlen : l.length = k := by simpa using congrArg List.length hl
  by_cases hi : i < k
  · have := congrArg (fun l' => l'.getD i 0) hl
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi] at this
    have hil : i < l.length := by omega
    rw [List.getElem?_eq_getElem hil] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil]
    simpa using this
  · rw [hf i (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

/-- INTERNAL: the program's prescribed margin of a vertex is the pseudocode margin, given
the tightened margins of the context. TEXLINE: sections/scales.tex:113-126 -/
theorem penaltyVal_margin (I : Instance) (C : Program.Ctx) (hm : C.m = I.m)
    (hrows : C.rows.map SNat.get = (List.range I.m).map (Pseudocode.tRow I))
    (hcols : C.cols.map SNat.get = (List.range I.n).map (Pseudocode.tCol I)) (v : ℕ) :
    (Program.margin C v).val.get = Pseudocode.margin I v := by
  have hr := penaltyVal_getD C.rows I.m (Pseudocode.tRow I) hrows
    (fun i hi => by simp [Pseudocode.tRow, not_lt.2 hi])
  have hc := penaltyVal_getD C.cols I.n (Pseudocode.tCol I) hcols
    (fun i hi => by simp [Pseudocode.tCol, not_lt.2 hi])
  unfold Program.margin Pseudocode.margin
  simp only [Charged.val_bind, Interface.val_idxLt, hm]
  by_cases hv : v < I.m
  · simp only [hv, decide_true, ite_true, Charged.val_bind, Interface.SNat.get_toRat,
      Interface.val_get, hr]
  · simp only [hv, decide_false, Bool.false_eq_true, ite_false, Charged.val_bind,
      Interface.SNat.get_toRat, Interface.val_get, hc]

/-- INTERNAL: a program vector `l` of length `N` represents `f` on the indices below `N`. -/
def PVRep (N : ℕ) (l : List SRat) (f : ℕ → ℚ) : Prop :=
  l.length = N ∧ ∀ i < N, (l.getD i default).get = f i

/-- INTERNAL: representation only depends on the represented values below `N`. -/
theorem pvRep_congr {N : ℕ} {l : List SRat} {f g : ℕ → ℚ} (h : PVRep N l f)
    (hfg : ∀ i < N, f i = g i) : PVRep N l g :=
  ⟨h.1, fun i hi => (h.2 i hi).trans (hfg i hi)⟩

/-- INTERNAL: a constant vector represents the constant function. -/
theorem pvRep_replicate (N : ℕ) (z : SRat) : PVRep N (List.replicate N z) (fun _ => z.get) :=
  ⟨by simp, fun i hi => by simp [List.getD_eq_getElem?_getD, hi]⟩

/-- INTERNAL: writing an in-range entry updates the represented function. -/
theorem pvRep_set {N : ℕ} {l : List SRat} {f : ℕ → ℚ} (h : PVRep N l f) {v : ℕ} (hv : v < N)
    (a : SRat) : PVRep N (l.set v a) (Function.update f v a.get) := by
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hvi : v = i
  · subst hvi; simp [h.1, hv]
  · rw [if_neg hvi, ← List.getD_eq_getElem?_getD, h.2 i hi, Function.update_of_ne (Ne.symm hvi)]

/-- INTERNAL: `Program.addAt` at an in-range index adds to the represented value. -/
theorem pvRep_addAt {N : ℕ} {l : List SRat} {f : ℕ → ℚ} (h : PVRep N l f) {v : ℕ} (hv : v < N)
    (x : SRat) : PVRep N (Program.addAt l v x).val (Function.update f v (f v + x.get)) := by
  unfold Program.addAt
  simp only [Charged.val_bind, Interface.val_get, Interface.val_set]
  have := pvRep_set h hv (SRat.add (l.getD v default) x).val
  rwa [Interface.SRat.get_add, h.2 v hv] at this

/-- INTERNAL: reading a context cell list agrees with reading its viewed list. -/
theorem pv_entry_getD {l : List Program.Entry} {l' : List (ℕ × ℕ × ℕ)}
    (hl : l.map (fun (e : Program.Entry) => (e.1, e.2.1, e.2.2.get)) = l') (k : ℕ) :
    ((l.getD k default).1, (l.getD k default).2.1, (l.getD k default).2.2.get) = l'.getD k (0, 0, 0) := by
  rw [← hl, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[k]? <;> rfl

/-- INTERNAL: value of `Program.absQ`. -/
theorem pv_absQ_get (x : SRat) : (Program.absQ x).val.get = |x.get| := by
  unfold Program.absQ
  simp only [Charged.val_bind, Interface.SRat.val_lt, Interface.SRat.get_lit]
  by_cases hx : x.get < 0
  · simp [hx, abs_of_neg hx]
  · simp [hx, abs_of_nonneg (not_lt.1 hx)]

/-- INTERNAL: value of `Program.distQ` is `Pseudocode.boxDist`. -/
theorem pv_distQ_get (x b : SRat) : (Program.distQ x b).val.get = Pseudocode.boxDist x.get b.get := by
  unfold Program.distQ Pseudocode.boxDist
  simp only [Charged.val_bind, Interface.SRat.val_lt, Interface.SRat.get_lit]
  by_cases hx : x.get < 0
  · simp [hx]
  · by_cases hb : b.get < x.get
    · simp [hx, hb]
    · simp [hx, hb]

/-- INTERNAL: a charged fold that adds `h v` at each element computes the list sum. -/
theorem pv_fold_sum_get {ι : Type} (F : SRat → ι → Program.Prog SRat) (h : ι → ℚ) :
    ∀ (l : List ι), (∀ s, ∀ v ∈ l, (F s v).val.get = s.get + h v) →
      ∀ s, (Charged.foldl F l s).val.get = s.get + (l.map h).sum := by
  intro l
  induction l with
  | nil => intro _ s; simp
  | cons a l ih =>
    intro hF s
    rw [Charged.val_foldl_cons, ih (fun s v hv => hF s v (List.mem_cons_of_mem _ hv)),
      hF s a List.mem_cons_self, List.map_cons, List.sum_cons, add_assoc]

/-- INTERNAL: invariant for a `repeatFor` loop that adds `t r` to a represented vector. -/
theorem pvRep_repeatFor (N : ℕ) (F : ℕ → List SRat → Program.Prog (List SRat))
    (t : ℕ → ℕ → ℚ) (K : ℕ)
    (hF : ∀ r < K, ∀ acc f, PVRep N acc f → PVRep N (F r acc).val (fun v => f v + t r v))
    (acc : List SRat) (f : ℕ → ℚ) (h : PVRep N acc f) :
    PVRep N (Charged.repeatFor F K acc).val (fun v => f v + ∑ r ∈ Finset.range K, t r v) := by
  rw [val_repeatFor']
  induction K with
  | zero => exact pvRep_congr h (fun i _ => by simp)
  | succ K ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine pvRep_congr (hF K (by omega) _ _ (ih (fun r hr => hF r (by omega)))) (fun i _ => ?_)
    rw [Finset.sum_range_succ, add_assoc]

/-- INTERNAL: a list sum over `List.range` is the `Finset.range` sum. -/
theorem pv_sum_range (h : ℕ → ℚ) (n : ℕ) :
    ((List.range n).map h).sum = ∑ i ∈ Finset.range n, h i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- INTERNAL: the pair of loads and tree values is represented componentwise. -/
def PVRep2 (N T : ℕ) (st : List SRat × List SRat) (f : (ℕ → ℚ) × (ℕ → ℚ)) : Prop :=
  PVRep N st.1 f.1 ∧ PVRep T st.2 f.2

/-- INTERNAL: invariant for the leaf-elimination fold. -/
theorem pvRep2_foldl (N T : ℕ) (F : List SRat × List SRat → ℕ × ℕ → Program.Prog (List SRat × List SRat))
    (G : (ℕ → ℚ) × (ℕ → ℚ) → ℕ × ℕ → (ℕ → ℚ) × (ℕ → ℚ)) (l : List (ℕ × ℕ))
    (hF : ∀ vt ∈ l, ∀ st f, PVRep2 N T st f → PVRep2 N T (F st vt).val (G f vt)) :
    ∀ st f, PVRep2 N T st f → PVRep2 N T (Charged.foldl F l st).val (l.foldl G f) := by
  induction l with
  | nil => intro st f h; exact h
  | cons a l ih =>
    intro st f h
    rw [Charged.val_foldl_cons, List.foldl_cons]
    exact ih (fun vt hv => hF vt (List.mem_cons_of_mem _ hv)) _ _ (hF a List.mem_cons_self _ _ h)

/-- The program's deterministic exact-rational computation of the penalty agrees with the
pseudocode penalty, given a context that matches the instance.
INTERNAL: proof of `Cellcounting.penalty_val`. TEXLINE: sections/scales.tex:113-126 -/
theorem penalty_val_proof (I : Cellcounting.Instance) (ε δ : ℚ) (C : Cellcounting.Program.Ctx) (hC : (C.m, C.n, C.rows.map Cellcounting.Model.Operations.SNat.get, C.cols.map Cellcounting.Model.Operations.SNat.get, C.small.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall, C.free.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree, C.tree.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots, C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) = (I.m, I.n, (List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.smallCells I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, (Cellcounting.Pseudocode.forest I ε δ).free, Cellcounting.Pseudocode.nFree I ε δ, (Cellcounting.Pseudocode.forest I ε δ).tree, (Cellcounting.Pseudocode.forest I ε δ).tree.length, Cellcounting.Pseudocode.elimOrder I ε δ, Cellcounting.Pseudocode.roots I ε δ, Cellcounting.Pseudocode.Mf I ε δ, Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ, (Cellcounting.Pseudocode.AParam I ε δ : ℚ), (Cellcounting.Pseudocode.HParam I ε δ : ℚ), (Cellcounting.Pseudocode.BParam I ε δ : ℚ))) (x y : List Cellcounting.Model.Operations.SNat) (zf : List Cellcounting.Model.Operations.SRat) : (Cellcounting.Program.penalty C x y zf).val.get = Cellcounting.Pseudocode.penalty I ε δ (fun k => (x.getD k default).get) (fun k => (y.getD k default).get) (fun k => (zf.getD k default).get) := by
  simp only [Prod.mk.injEq] at hC
  obtain ⟨hm, hn, hrows, hcols, hsmall, hnS, hfree, hnF, htree, hnT, horder, hroots, -, -, -, -,
    hAq, -, -⟩ := hC
  have hmarg := penaltyVal_margin I C hm hrows hcols
  unfold Program.penalty
  simp only [Charged.val_bind, Interface.val_replicate]
  generalize hacc1 : (Charged.repeatFor _ C.nSmall _).val = acc1
  generalize hacc2 : (Charged.repeatFor _ C.nFree acc1).val = acc2
  generalize hst : (Charged.foldl _ C.order (acc2, _)).val = st
  generalize hrs : (Charged.foldl _ C.roots _).val = rs
  generalize hds : (Charged.repeatFor _ C.nTree _).val = ds
  simp only [Interface.SRat.get_mul, Interface.SRat.get_add]
  set X : ℕ → ℕ := fun k => (x.getD k default).get with hX
  set Y : ℕ → ℕ := fun k => (y.getD k default).get with hY
  set Z : ℕ → ℚ := fun k => (zf.getD k default).get with hZ
  -- the small-cell loop
  have h1 : PVRep (I.m + I.n) acc1 (fun v => 0 + ∑ k ∈ Finset.range (Pseudocode.nSmall I ε δ),
      ((if (Pseudocode.smallAt I ε δ k).1 = v then (X k : ℚ) else 0) +
        (if I.m + (Pseudocode.smallAt I ε δ k).2.1 = v then
          (((Pseudocode.smallAt I ε δ k).2.2 - Y k : ℕ) : ℚ) else 0))) := by
    rw [← hacc1, hnS]
    refine pvRep_repeatFor _ _ _ _ (fun r hr acc f hf => ?_) _ _ ?_
    · have hs := pv_entry_getD hsmall r
      simp only [Prod.ext_iff] at hs
      obtain ⟨hs1, hs2, hs3⟩ := hs
      have hmem : Pseudocode.smallAt I ε δ r ∈ Pseudocode.retained I := by
        have hr' : r < (Pseudocode.smallCells I ε δ).length := hr
        have : Pseudocode.smallAt I ε δ r ∈ Pseudocode.smallCells I ε δ := by
          unfold Pseudocode.smallAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr']
          exact List.getElem_mem _
        exact (List.mem_filter.1 this).1
      have hlt := mem_retained hmem
      unfold Pseudocode.smallAt at hlt ⊢
      simp only [Charged.val_bind, Interface.val_get]
      refine pvRep_congr (pvRep_addAt (pvRep_addAt hf (by omega) _) (by omega) _) (fun v hv => ?_)
      simp only [Interface.SNat.get_toRat, Interface.SNat.get_sub, hs1, hs2, hs3, hm,
        Function.update_apply, X, Y]
      split_ifs <;> subst_vars <;> first | omega | ring
    · rw [hm, hn]; exact pvRep_replicate _ _
  -- the free-cell loop
  have h2 : PVRep (I.m + I.n) acc2 (Pseudocode.baseLoad I ε δ X Y Z) := by
    rw [← hacc2, hnF]
    refine pvRep_congr (pvRep_repeatFor _ _ (fun k v =>
      (if (Pseudocode.freeAt I ε δ k).1 = v then Z k else 0) +
        (if I.m + (Pseudocode.freeAt I ε δ k).2.1 = v then Z k else 0)) _
      (fun r hr acc f hf => ?_) _ _ h1) (fun v _ => ?_)
    · have hs := pv_entry_getD hfree r
      simp only [Prod.ext_iff] at hs
      obtain ⟨hs1, hs2, -⟩ := hs
      have hlt : Pseudocode.freeAt I ε δ r ∈ (Pseudocode.forest I ε δ).free := by
        have hr' : r < (Pseudocode.forest I ε δ).free.length := hr
        unfold Pseudocode.freeAt
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr']
        exact List.getElem_mem _
      have hlt := forest_mem_lt I ε δ (Or.inr hlt)
      unfold Pseudocode.freeAt at hlt ⊢
      simp only [Charged.val_bind, Interface.val_get]
      refine pvRep_congr (pvRep_addAt (pvRep_addAt hf (by omega) _) (by omega) _) (fun v hv => ?_)
      simp only [hs1, hs2, hm, Function.update_apply, Z]
      split_ifs <;> subst_vars <;> first | omega | ring
    · simp only [Pseudocode.baseLoad, zero_add]
  -- the leaf elimination
  have hval := pseudo_elimOrder_valid I ε δ
  have hTlt : ∀ t < (Pseudocode.forest I ε δ).tree.length,
      (Pseudocode.treeAt I ε δ t).1 < I.m ∧ (Pseudocode.treeAt I ε δ t).2.1 < I.n := by
    intro t ht
    apply forest_mem_lt I ε δ
    left
    unfold Pseudocode.treeAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
    exact List.getElem_mem _
  have h3 : PVRep2 (I.m + I.n) (Pseudocode.forest I ε δ).tree.length st
      (Pseudocode.treeValues I ε δ X Y Z) := by
    rw [← hst, horder]
    unfold Pseudocode.treeValues
    refine pvRep2_foldl _ _ _ _ _ (fun vt hvt st' f hf => ?_) _ _ ⟨h2, ?_⟩
    · have ht2 := hval.1.lt vt hvt
      have hinc := hval.1.inc vt hvt
      have hb := hTlt _ ht2
      have hs := pv_entry_getD htree vt.2
      simp only [Prod.ext_iff] at hs
      obtain ⟨hs1, hs2, -⟩ := hs
      have hv1 : vt.1 < I.m + I.n := by
        unfold Pseudocode.treeAt at hinc hb; omega
      unfold Pseudocode.treeAt at hinc hb ⊢
      simp only [Charged.val_bind, Interface.val_get, Interface.val_set, Interface.val_idxEq]
      rw [hs1, hs2, hm]
      have hz : ((Program.margin C vt.1).val.sub (st'.1.getD vt.1 default)).val.get =
          Pseudocode.margin I vt.1 - f.1 vt.1 := by
        rw [Interface.SRat.get_sub, hmarg, hf.1.2 _ hv1]
      have h2' := pvRep_set hf.2 ht2 ((Program.margin C vt.1).val.sub (st'.1.getD vt.1 default)).val
      rw [hz] at h2'
      simp only [decide_eq_true_eq]
      by_cases hrow : vt.1 = ((Pseudocode.forest I ε δ).tree.getD vt.2 (0, 0, 0)).1
      · simp only [if_pos hrow, Charged.val_bind, Charged.val_pure]
        refine ⟨?_, h2'⟩
        have := pvRep_addAt hf.1 (v := I.m + ((Pseudocode.forest I ε δ).tree.getD vt.2 (0, 0, 0)).2.1)
          (by omega) ((Program.margin C vt.1).val.sub (st'.1.getD vt.1 default)).val
        rwa [hz] at this
      · simp only [if_neg hrow, Charged.val_bind, Charged.val_pure]
        refine ⟨?_, h2'⟩
        have := pvRep_addAt hf.1 (v := ((Pseudocode.forest I ε δ).tree.getD vt.2 (0, 0, 0)).1)
          (by omega) ((Program.margin C vt.1).val.sub (st'.1.getD vt.1 default)).val
        rwa [hz] at this
    · rw [hnT]; exact pvRep_congr (pvRep_replicate _ _) (fun _ _ => rfl)
  -- the root sum
  have h4 : rs.get = ((Pseudocode.roots I ε δ).map fun v =>
      |(Pseudocode.treeValues I ε δ X Y Z).1 v - Pseudocode.margin I v|).sum := by
    rw [← hrs, hroots, pv_fold_sum_get _ _ _ (fun s v hv => ?_), Interface.SRat.get_lit, zero_add]
    have hv' := ((mem_roots_iff I ε δ v).1 hv).1
    simp only [Charged.val_bind, Interface.val_get, Interface.SRat.get_add, pv_absQ_get,
      Interface.SRat.get_sub, hmarg, h3.1.2 v hv']
  -- the tree-distance sum
  have h5 : ds.get = ∑ t ∈ Finset.range (Pseudocode.forest I ε δ).tree.length,
      Pseudocode.boxDist ((Pseudocode.treeValues I ε δ X Y Z).2 t)
        ((Pseudocode.treeAt I ε δ t).2.2 : ℚ) / ((Pseudocode.treeAt I ε δ t).2.2 : ℚ) := by
    rw [← hds, hnT]
    unfold Charged.repeatFor
    rw [pv_fold_sum_get _ (fun t => Pseudocode.boxDist ((Pseudocode.treeValues I ε δ X Y Z).2 t)
        ((Pseudocode.treeAt I ε δ t).2.2 : ℚ) / ((Pseudocode.treeAt I ε δ t).2.2 : ℚ)) _
        (fun s t ht => ?_), Interface.SRat.get_lit, zero_add, pv_sum_range]
    have ht' := List.mem_range.1 ht
    have hs := pv_entry_getD htree t
    simp only [Prod.ext_iff] at hs
    obtain ⟨-, -, hs3⟩ := hs
    unfold Pseudocode.treeAt
    simp only [Charged.val_bind, Interface.val_get, Interface.SRat.get_add, pv_distQ_get,
      Interface.SRat.get_div, Interface.SNat.get_toRat, hs3, h3.2.2 t ht']
  rw [h4, h5, hAq]
  rfl

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `penalty_val_proof` via loop invariants `PVRep`/`PVRep2` over the four loops
-/
