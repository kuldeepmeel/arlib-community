import Cellcounting.Model.Program
import Cellcounting.Interface.Pseudocode
import Cellcounting.Interface.Encoding
import Cellcounting.Analysis.PhaseWindow
import Mathlib.Data.List.GetD

/-!
# The program's chain setup computes the pseudocode's chain parameters

`Cellcounting.Analysis.chainSetup_view_of`: if a context `C` and parameters `Pm` agree with
the pseudocode (the `hC`, `hPm` shapes of `Interface/ProgramModel.lean`), `pS` holds `p` and
`εS` holds `ε`, then `Program.chainSetup C Pm pS εS` returns the pseudocode's `p`, pair labels
`pairCells`, first labels `cellFirst`, bounds `smallB`, `ξ`, `k_acc`, the phase parameters
`τ, B_ret, N_av, H`, the initial multipliers `w0` (as a `p × p` table read through `getD`)
and `C0`.  Only values are stated; nothing here bounds cost.

It is proved in three pieces: `csv_lab` (the pair-label loop builds `pairCells`, the prefix
sums and the bounds), `csv_w0` (the double loop fills the table `csvW`, through the
invariant `CsvTab` and the one-entry update `csv_set2`), and `csv_c0` (the product fold).
The straight-line arithmetic is matched against `KobsParam`, `τParam`, `ηParam`,
`BretParam`, `NavParam`, `JstarParam`, `ξParam`, `kAccParam` one definition at a time.

The sealed-value lemmas `csv_vb`, `csv_na`, … restate `Charged.val_bind` and the `Encoding`
value lemmas with propositional rather than `rfl` proofs: rewriting the whole setup with the
`rfl` versions makes the kernel re-check a large definitional unfolding and time out.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Model
open Cellcounting.Model.Operations

/-- INTERNAL: `Charged.val_bind` for `Prog`, proved by the lemma (kernel-cheap under `simp`). -/
theorem csv_vb {α β : Type} (p : Program.Prog α) (f : α → Program.Prog β) :
    (p >>= f).val = (f p.val).val :=
  Charged.val_bind p f

/-- INTERNAL: `Charged.val_pure` for `Prog`, proved by the lemma. -/
theorem csv_vp {α : Type} (a : α) : (pure a : Program.Prog α).val = a :=
  Charged.val_pure a

/-- INTERNAL: value of `SNat.add`, proved propositionally (see the module note). -/
theorem csv_na (x y : SNat) : (SNat.add x y).val.get = x.get + y.get := Interface.SNat.get_add x y
/-- INTERNAL: value of `SNat.mul`, proved propositionally (see the module note). -/
theorem csv_nm (x y : SNat) : (SNat.mul x y).val.get = x.get * y.get := Interface.SNat.get_mul x y
/-- INTERNAL: value of `SNat.lit`, proved propositionally (see the module note). -/
theorem csv_nl (k : ℕ) : (SNat.lit k).val.get = k := Interface.SNat.get_lit k
/-- INTERNAL: value of `SNat.toRat`, proved propositionally (see the module note). -/
theorem csv_nq (x : SNat) : (SNat.toRat x).val.get = (x.get : ℚ) := Interface.SNat.get_toRat x
/-- INTERNAL: value of `SNat.index`, proved propositionally (see the module note). -/
theorem csv_ni (x : SNat) : (SNat.index x).val = x.get := Interface.SNat.val_index x
/-- INTERNAL: value of `SRat.div`, proved propositionally (see the module note). -/
theorem csv_qd (x y : SRat) : (SRat.div x y).val.get = x.get / y.get := Interface.SRat.get_div x y
/-- INTERNAL: value of `SRat.mul`, proved propositionally (see the module note). -/
theorem csv_qm (x y : SRat) : (SRat.mul x y).val.get = x.get * y.get := Interface.SRat.get_mul x y
/-- INTERNAL: value of `SRat.lit`, proved propositionally (see the module note). -/
theorem csv_ql (q : ℚ) : (SRat.lit q).val.get = q := Interface.SRat.get_lit q
/-- INTERNAL: value of `SRat.natCeil`, proved propositionally (see the module note). -/
theorem csv_qc (x : SRat) : (SRat.natCeil x).val.get = ⌈x.get⌉₊ := Interface.SRat.get_natCeil x
/-- INTERNAL: `Program.clog2` computes `⌈log₂ x⌉`. -/
theorem csv_clog2 (x : SNat) : (Program.clog2 x).val.get = Nat.clog 2 x.get := by
  unfold Program.clog2
  rw [csv_vb, csv_vb, ← Pseudocode.size_pred_eq_clog, Interface.SNat.get_size,
    Interface.SNat.get_sub, csv_nl]

/-- INTERNAL: `A` is a `p × p` table whose entry `(i, l)`, read through `getD`, is `g i l`. -/
def CsvTab (p : ℕ) (A : List (List SRat)) (g : ℕ → ℕ → ℚ) : Prop :=
  A.length = p ∧ (∀ row ∈ A, row.length = p) ∧
    ∀ i l, ((A.getD i []).getD l default).get = g i l

/-- INTERNAL: an invariant indexed by the step count, carried through a fold over `range n`. -/
theorem csv_fold_inv {β : Type} (f : β → ℕ → β) (P : ℕ → β → Prop) (n : ℕ) (b : β)
    (h0 : P 0 b) (hs : ∀ r < n, ∀ x, P r x → P (r + 1) (f x r)) :
    P n ((List.range n).foldl f b) := by
  suffices ∀ r ≤ n, P r ((List.range r).foldl f b) from this n le_rfl
  intro r
  induction r with
  | zero => intro _; exact h0
  | succ r ih =>
    intro hr
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact hs r (by omega) _ (ih (by omega))

/-- INTERNAL: `CsvTab` respects equality of the entry function. -/
theorem csvTab_congr {p : ℕ} {A : List (List SRat)} {g g' : ℕ → ℕ → ℚ} (h : CsvTab p A g)
    (e : g = g') : CsvTab p A g' := e ▸ h

/-- INTERNAL: `Program.set2` at an in-range entry updates that entry and keeps the shape. -/
theorem csv_set2 (p : ℕ) (A : List (List SRat)) (g : ℕ → ℕ → ℚ) (hA : CsvTab p A g)
    (i l : ℕ) (hi : i < p) (hl : l < p) (v : SRat) :
    CsvTab p (Program.set2 A i l v).val
      (fun i' l' => if i' = i ∧ l' = l then v.get else g i' l') := by
  obtain ⟨h1, h2, h3⟩ := hA
  show CsvTab p (A.set i ((A.getD i default).set l v)) _
  have hrow : (A.getD i default).length = p := by
    apply h2; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  refine ⟨by simp [h1], ?_, ?_⟩
  · intro row hrow'
    rcases List.mem_or_eq_of_mem_set hrow' with h | h
    · exact h2 row h
    · subst h; simpa using hrow
  · intro i' l'
    have := h3 i' l'
    simp only [List.getD_eq_getElem?_getD] at this hrow ⊢
    rw [← this]
    by_cases hi' : i' = i
    · subst hi'
      obtain ⟨row, hr⟩ : ∃ row, A[i']? = some row :=
        ⟨A[i'], List.getElem?_eq_getElem (by omega)⟩
      simp only [hr, Option.getD_some] at this hrow ⊢
      rw [List.getElem?_set_self (by omega), Option.getD_some]
      by_cases hl' : l' = l
      · subst hl'; simp [hrow, hl]
      · simp [hl', List.getElem?_set_ne (Ne.symm hl')]
    · simp [hi', List.getElem?_set_ne (Ne.symm hi')]

/-- INTERNAL: value of the off-cell multiplier `6 (b_i + 1)/(b_l + 2)`. -/
theorem csv_v (six : SRat) (one c2 x y : SNat) (h6 : six.get = 6) (h1 : one.get = 1)
    (h2 : c2.get = 2) :
    (SRat.div (SRat.mul six (SNat.toRat (SNat.add x one).val).val).val
      (SNat.toRat (SNat.add y c2).val).val).val.get =
      6 * (((x.get + 1 : ℕ)) : ℚ) / (((y.get + 2 : ℕ)) : ℚ) := by
  show six.get * (((x.get + one.get : ℕ)) : ℚ) / (((y.get + c2.get : ℕ)) : ℚ) = _
  rw [h6, h1, h2]

/-- INTERNAL: the initial multiplier table read from lists `pc` (pair labels) and `sb` (bounds). -/
noncomputable def csvW (p : ℕ) (pc : List ℕ) (sb : List SNat) (i l : ℕ) : ℚ :=
  if i < p ∧ l < p ∧ i ≠ l then
    if pc.getD i 0 = pc.getD l 0 then 6
    else 6 * (((sb.getD (pc.getD i 0) default).get + 1 : ℕ) : ℚ) /
      (((sb.getD (pc.getD l 0) default).get + 2 : ℕ) : ℚ)
  else 0

/-- INTERNAL: the `w^(0)` double loop of `Program.chainSetup` fills the table `csvW`.
TEXLINE: sections/algorithm.tex:36-60 -/
theorem csv_w0 (p : ℕ) (pairCell : List ℕ) (smallB : List SNat) (six zeroQ : SRat) (one c2 : SNat)
    (h6 : six.get = 6) (h0 : zeroQ.get = 0) (h1 : one.get = 1) (h2 : c2.get = 2) :
    CsvTab p (Charged.repeatFor (fun i acc =>
      Charged.repeatFor (fun l acc' => do
        let diag ← idxEq i l
        if diag then pure acc' else do
          let si ← Operations.get pairCell i
          let sl ← Operations.get pairCell l
          let same ← idxEq si sl
          if same then Program.set2 acc' i l six else do
            let bi ← Operations.get smallB si
            let bl ← Operations.get smallB sl
            let bi1 ← SNat.add bi one
            let bl2 ← SNat.add bl c2
            let bi1q ← SNat.toRat bi1
            let bl2q ← SNat.toRat bl2
            let t ← SRat.mul six bi1q
            let v ← SRat.div t bl2q
            Program.set2 acc' i l v) p acc) p (List.replicate p (List.replicate p zeroQ)) :
        Program.Prog (List (List SRat))).val (csvW p pairCell smallB) := by
  let g : ℕ → ℕ → ℕ → ℕ → ℚ := fun r c i l =>
    if i < r ∨ (i = r ∧ l < c) then csvW p pairCell smallB i l else 0
  have hinit : CsvTab p (List.replicate p (List.replicate p zeroQ)) (g 0 0) := by
    refine ⟨by simp, fun row h => by simp at h; rw [h.2]; simp, fun i l => ?_⟩
    simp only [g, Nat.not_lt_zero, false_or, false_and, if_false]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    by_cases hi : i < p <;> by_cases hl : l < p <;> simp [hi, hl, h0] <;> rfl
  have hinner : ∀ r, r < p → ∀ A, CsvTab p A (g r 0) →
      CsvTab p (Charged.repeatFor (fun l acc' => do
        let diag ← idxEq r l
        if diag then pure acc' else do
          let si ← Operations.get pairCell r
          let sl ← Operations.get pairCell l
          let same ← idxEq si sl
          if same then Program.set2 acc' r l six else do
            let bi ← Operations.get smallB si
            let bl ← Operations.get smallB sl
            let bi1 ← SNat.add bi one
            let bl2 ← SNat.add bl c2
            let bi1q ← SNat.toRat bi1
            let bl2q ← SNat.toRat bl2
            let t ← SRat.mul six bi1q
            let v ← SRat.div t bl2q
            Program.set2 acc' r l v) p A : Program.Prog (List (List SRat))).val (g r p) := by
    intro r hr A hA
    rw [val_repeatFor']
    suffices ∀ c ≤ p, CsvTab p ((List.range c).foldl (fun b l => (do
        let diag ← idxEq r l
        if diag then pure b else do
          let si ← Operations.get pairCell r
          let sl ← Operations.get pairCell l
          let same ← idxEq si sl
          if same then Program.set2 b r l six else do
            let bi ← Operations.get smallB si
            let bl ← Operations.get smallB sl
            let bi1 ← SNat.add bi one
            let bl2 ← SNat.add bl c2
            let bi1q ← SNat.toRat bi1
            let bl2q ← SNat.toRat bl2
            let t ← SRat.mul six bi1q
            let v ← SRat.div t bl2q
            Program.set2 b r l v : Program.Prog (List (List SRat))).val) A) (g r c) from this p le_rfl
    intro c
    induction c with
    | zero => intro _; exact hA
    | succ c ih =>
      intro hc
      have ih := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize (List.range c).foldl _ A = B at ih ⊢
      simp only [Charged.val_bind, Interface.val_idxEq, Interface.val_get]
      by_cases hd : r = c
      · subst hd
        simp only [decide_true, if_true, Charged.val_pure]
        convert ih using 1
        funext i l
        simp only [g, csvW]
        split_ifs <;> first | rfl | (exfalso; omega)
      · simp only [hd, decide_false, Bool.false_eq_true, if_false, Charged.val_bind,
          Interface.val_get, Interface.val_idxEq]
        have hc' : c < p := by omega
        by_cases hs : pairCell.getD r default = pairCell.getD c default
        · simp only [hs, decide_true, if_true, Charged.val_bind]
          refine csvTab_congr (csv_set2 p B (g r c) ih r c hr hc' _) ?_
          funext i l
          simp only [g, csvW, h6]
          split_ifs <;> first | rfl | (exfalso; omega) | simp_all
        · simp only [hs, decide_false, Bool.false_eq_true, if_false, Charged.val_bind,
            Interface.val_get]
          refine csvTab_congr (csv_set2 p B (g r c) ih r c hr hc' _) ?_
          funext i l
          simp only [g, csvW, csv_v six one c2 _ _ h6 h1 h2, Interface.val_get]
          split_ifs <;> first | rfl | (exfalso; omega) | simp_all
  rw [val_repeatFor']
  refine csvTab_congr (csv_fold_inv _ (fun r x => CsvTab p x (g r 0)) p _ hinit
    (fun r hr x hx => csvTab_congr (hinner r hr x hx) ?_)) ?_
  · funext i l; simp only [g, csvW]; split_ifs <;> first | rfl | (exfalso; omega) | simp_all
  · funext i l; simp only [g, csvW]; split_ifs <;> first | rfl | (exfalso; omega) | simp_all

/-- INTERNAL: the pair-label loop of `Program.chainSetup` lists cell `s` `b_s` times, stores the
prefix sums and the bounds, and accumulates `p = Σ b_s`. -/
theorem csv_lab (small : List Program.Entry) (n : ℕ) :
    (Charged.repeatFor (fun s (st : List ℕ × List ℕ × List SNat × ℕ) => do
      let e ← Operations.get small s
      let bI ← SNat.index e.2.2
      let firsts ← Operations.push st.2.1 st.2.2.2
      let bs ← Operations.push st.2.2.1 e.2.2
      let cells ← Charged.repeatFor (fun _ acc => Operations.push acc s) bI st.1
      pure (cells, firsts, bs, st.2.2.2 + bI)) n ([], [], [], 0) :
        Program.Prog (List ℕ × List ℕ × List SNat × ℕ)).val =
      ((List.range n).flatMap (fun s => List.replicate (small.getD s default).2.2.get s),
       (List.range n).map (fun s => ∑ t ∈ Finset.range s, (small.getD t default).2.2.get),
       (List.range n).map (fun s => (small.getD s default).2.2),
       ∑ t ∈ Finset.range n, (small.getD t default).2.2.get) := by
  have hp : ∀ (s b : ℕ) (l : List ℕ),
      (Charged.repeatFor (fun _ acc => Operations.push acc s) b l : Program.Prog (List ℕ)).val =
        l ++ List.replicate b s := by
    intro s b l
    rw [val_repeatFor']
    induction b with
    | zero => simp
    | succ b ih => rw [List.range_succ, List.foldl_append, ih]; simp [List.replicate_succ']
  rw [val_repeatFor']
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp [hp, Finset.sum_range_succ, List.range_succ]

/-- INTERNAL: the `C(0)` fold multiplies `M` by `Π (b + 1)`. -/
theorem csv_c0 (one : SNat) (h1 : one.get = 1) (l : List SNat) (M : SNat) :
    (Charged.foldl (fun acc (b : SNat) => do
      let b1' ← SNat.add b one
      SNat.mul acc b1') l M : Program.Prog SNat).val.get = M.get * (l.map (fun b => b.get + 1)).prod := by
  induction l generalizing M with
  | nil => simp
  | cons a l ih =>
    rw [Charged.val_foldl_cons, ih, csv_vb, csv_nm, csv_na, h1]
    simp [mul_assoc]

/-- INTERNAL: a list sum as a range sum of `getD` reads. -/
theorem csv_sum_getD (l : List Program.Entry) :
    (l.map (fun e => e.2.2.get)).sum = ∑ t ∈ Finset.range l.length, (l.getD t default).2.2.get := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']; simp [add_comm]

/-- INTERNAL: a list product over `range n` is the `Finset.range` product. -/
theorem csv_prod_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).prod = ∏ s ∈ Finset.range n, f s := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]; simp

/-- INTERNAL: interface bridge for `chainSetup_view`: the program's chain and phase parameters,
`w^(0)` and `C(0)` equal the pseudocode's values.
TEXLINE: sections/algorithm.tex:200-215, sections/algorithm.tex:385-415 -/
theorem chainSetup_view_of (I : Cellcounting.Instance) (ε δ : ℚ) (C : Cellcounting.Program.Ctx) (hC : (C.m, C.n, C.rows.map Cellcounting.Model.Operations.SNat.get, C.cols.map Cellcounting.Model.Operations.SNat.get, C.small.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall, C.free.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree, C.tree.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots, C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) = (I.m, I.n, (List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.smallCells I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, (Cellcounting.Pseudocode.forest I ε δ).free, Cellcounting.Pseudocode.nFree I ε δ, (Cellcounting.Pseudocode.forest I ε δ).tree, (Cellcounting.Pseudocode.forest I ε δ).tree.length, Cellcounting.Pseudocode.elimOrder I ε δ, Cellcounting.Pseudocode.roots I ε δ, Cellcounting.Pseudocode.Mf I ε δ, Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ, (Cellcounting.Pseudocode.AParam I ε δ : ℚ), (Cellcounting.Pseudocode.HParam I ε δ : ℚ), (Cellcounting.Pseudocode.BParam I ε δ : ℚ))) (Pm : Cellcounting.Program.Params) (hPm : (Pm.d.get, Pm.K.get, Pm.A.get, Pm.B.get, Pm.W.get, Pm.H.get) = (Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.KParam I ε δ, Cellcounting.Pseudocode.AParam I ε δ, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.WParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ)) (pS : Cellcounting.Model.Operations.SNat) (hp : pS.get = Cellcounting.Pseudocode.pSmall I ε δ) (εS : Cellcounting.Model.Operations.SRat) (hε : εS.get = ε) : let r := (Cellcounting.Program.chainSetup C Pm pS εS).val; ((r.1.p, r.1.pS.get, r.1.nsm, r.1.pairCell, r.1.cellFirst, r.1.smallB.map Cellcounting.Model.Operations.SNat.get, r.1.ξ.get, r.1.kAcc, r.1.kAccS.get), (r.2.1.τ.get, r.2.1.Bret.get, r.2.1.BretN, r.2.1.Nav.get, r.2.1.NavN, r.2.1.Hn), (fun (i l : ℕ) => ((r.2.2.1.getD i []).getD l default).get), (r.2.2.1.length, r.2.2.1.map List.length), r.2.2.2.get) = ((Cellcounting.Pseudocode.pSmall I ε δ, Cellcounting.Pseudocode.pSmall I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, Cellcounting.Pseudocode.pairCells I ε δ, (List.range (Cellcounting.Pseudocode.nSmall I ε δ)).map (Cellcounting.Pseudocode.cellFirst I ε δ), (List.range (Cellcounting.Pseudocode.nSmall I ε δ)).map (Cellcounting.Pseudocode.smallB I ε δ), Cellcounting.Pseudocode.ξParam I ε δ, Cellcounting.Pseudocode.kAccParam I ε δ, Cellcounting.Pseudocode.kAccParam I ε δ), (Cellcounting.Pseudocode.τParam I ε δ, Cellcounting.Pseudocode.BretParam I ε δ, Cellcounting.Pseudocode.BretParam I ε δ, Cellcounting.Pseudocode.NavParam I ε δ, Cellcounting.Pseudocode.NavParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ), Cellcounting.Pseudocode.w0 I ε δ, (Cellcounting.Pseudocode.pSmall I ε δ, List.replicate (Cellcounting.Pseudocode.pSmall I ε δ) (Cellcounting.Pseudocode.pSmall I ε δ)), Cellcounting.Pseudocode.C0 I ε δ)  := by
  intro r
  simp only [Prod.mk.injEq] at hC hPm
  obtain ⟨-, -, -, -, hsmall, hnS, -, -, -, -, -, -, hMf, -, -, -, -, -, -⟩ := hC
  obtain ⟨hd, hK, -, -, hW, hH⟩ := hPm
  simp only [r]
  unfold Program.chainSetup
  simp only [csv_vb, csv_vp, csv_lab]
  simp only [Prod.mk.injEq, csv_na, csv_nm, csv_nl, csv_nq, csv_ni, csv_qd, csv_qm, csv_ql, csv_qc,
    csv_clog2, hH, hW, hK, hd, hp, hε]
  -- the small cells, read through `getD`
  have hlen : C.small.length = Pseudocode.nSmall I ε δ := by
    rw [Pseudocode.nSmall, ← hsmall, List.length_map]
  have hb : ∀ s, (C.small.getD s default).2.2.get = Pseudocode.smallB I ε δ s := by
    intro s
    rw [Pseudocode.smallB, Pseudocode.smallAt, ← hsmall,
      show ((0, 0, 0) : Pseudocode.Entry) = (fun (e : Program.Entry) => (e.1, e.2.1, e.2.2.get))
        default from rfl, List.getD_map]
  have hsum : ∑ t ∈ Finset.range C.nSmall, (C.small.getD t default).2.2.get =
      Pseudocode.pSmall I ε δ := by
    rw [Pseudocode.pSmall, ← hsmall, List.map_map, hnS, ← hlen]
    exact (csv_sum_getD C.small).symm
  have hpc : (List.range C.nSmall).flatMap (fun s => List.replicate (C.small.getD s default).2.2.get s) =
      Pseudocode.pairCells I ε δ := by
    simp only [Pseudocode.pairCells, hb, hnS]
  have hsbg : ∀ k, ((List.map (fun s => (C.small.getD s default).2.2) (List.range C.nSmall)).getD k
      default).get = Pseudocode.smallB I ε δ k := by
    intro k
    rw [List.getD_eq_getElem?_getD]
    by_cases hk : k < C.nSmall
    · rw [List.getElem?_map, List.getElem?_range hk]
      simpa [List.getD_eq_getElem?_getD] using hb k
    · rw [List.getElem?_eq_none (by simpa using hk)]
      rw [hnS, Pseudocode.nSmall] at hk
      rw [Pseudocode.smallB, Pseudocode.smallAt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega)]
      rfl
  rw [hsum, hpc]
  set P := Pseudocode.pSmall I ε δ with hP
  set W := Pseudocode.WParam I ε δ with hW'
  set H := Pseudocode.HParam I ε δ with hH'
  set K := Pseudocode.KParam I ε δ with hK'
  set D := Pseudocode.dParam I with hD'
  have hKobs : 10 * (P * P * (P * P)) * (9 * (P * (1 + 8 * P * (W * W * (W * W)))) +
      2 * (8 + 32 * P * (W * W * (W * W) * (W * W)))) = Pseudocode.KobsParam I ε δ := by
    simp only [Pseudocode.KobsParam, Pseudocode.CpParam, Pseudocode.CdParam, Pseudocode.qParam]
    ring
  rw [hKobs]
  have hτ : 2 * Pseudocode.KobsParam I ε δ * (H + P + K + 5) = Pseudocode.τParam I ε δ := rfl
  rw [hτ]
  have hη : ε / ((200 * (H + 1) : ℕ) : ℚ) = Pseudocode.ηParam I ε δ := rfl
  rw [hη]
  have hBret : 2000 * (P * P) * ((H + 1) * (H + 1)) * Pseudocode.τParam I ε δ =
      Pseudocode.BretParam I ε δ := by
    simp only [Pseudocode.BretParam]; ring
  rw [hBret]
  have hNav : ⌈(((100000000 * (P * P * (P * P) * (P * P * (P * P))) * Pseudocode.KobsParam I ε δ *
      (H + 1)) : ℕ) : ℚ) / (Pseudocode.ηParam I ε δ * Pseudocode.ηParam I ε δ)⌉₊ =
      Pseudocode.NavParam I ε δ := by
    have e : 100000000 * (P * P * (P * P) * (P * P * (P * P))) * Pseudocode.KobsParam I ε δ *
        (H + 1) = 100000000 * P ^ 8 * Pseudocode.KobsParam I ε δ * (H + 1) := by ring
    rw [Pseudocode.NavParam, sq, e]
  rw [hNav]
  have hJ : 100 * (H + 1) * (Pseudocode.BretParam I ε δ + Pseudocode.NavParam I ε δ + P + D + 1) =
      Pseudocode.JstarParam I ε δ := rfl
  rw [hJ]
  have hξ : Pseudocode.ηParam I ε δ / ((1000 * Pseudocode.JstarParam I ε δ : ℕ) : ℚ) =
      Pseudocode.ξParam I ε δ := rfl
  rw [hξ]
  have hk : Nat.clog 2 ⌈1 / Pseudocode.ξParam I ε δ⌉₊ = Pseudocode.kAccParam I ε δ := by
    rw [one_div]; rfl
  rw [hk]
  have hT := csv_w0 P (Pseudocode.pairCells I ε δ)
    (List.map (fun s => (C.small.getD s default).2.2) (List.range C.nSmall)) (SRat.lit 6).val
    (SRat.lit 0).val (SNat.lit 1).val (SNat.lit 2).val (csv_ql 6) (csv_ql 0) (csv_nl 1) (csv_nl 2)
  refine ⟨⟨rfl, trivial, hnS, rfl, ?_, ?_, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩, ?_,
    ⟨hT.1, ?_⟩, ?_⟩
  · rw [← hnS]
    congr 1; funext s
    simp only [Pseudocode.cellFirst, hb]
  · rw [← hnS]
    simp only [List.map_map, Function.comp_def, hb]
  · funext i l
    refine (hT.2.2 i l).trans ?_
    simp only [csvW, Pseudocode.w0, Pseudocode.pairCell, hsbg]
    rfl
  · refine List.eq_replicate_iff.2 ⟨by rw [List.length_map]; exact hT.1, fun b hb' => ?_⟩
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hb'
    exact hT.2.1 row hrow
  · rw [csv_c0 _ (csv_nl 1), hMf, Pseudocode.C0, List.map_map, Function.comp_def]
    simp only [hb]
    rw [csv_prod_range, hnS]

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `chainSetup_view_of` with `csv_lab`, `csv_w0`, `csv_c0`; no `sorry`
-/
