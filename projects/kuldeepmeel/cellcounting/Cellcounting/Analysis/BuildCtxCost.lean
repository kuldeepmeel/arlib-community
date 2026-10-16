import Cellcounting.Analysis.CostScale
import Cellcounting.Analysis.CostLadder

/-!
# The forest construction S4 runs in polynomial bit cost, and its context is small

`Cellcounting.Analysis.buildCtx_cost`: for `m + n + 2 ≤ S`, a tightened instance
with at most `S` cells `(i, j, w)`, `i < m`, `j < n`, `bitLen w ≤ S`, margins of
binary length at most `S`, and parameters bounded by `S` (`PmSize`) with `B, H ≥ 1`,
`Program.buildCtx` (small/large split, insertion sort, Kruskal, roots, orientation,
`M_f`) costs at most `S ^ k`, the context it returns satisfies `CtxSize (S ^ k)`,
and its small cells are retained cells with bound `< W`.  The exponent is `k = 20`.

The proof walks the program stage by stage: `bc_splitCells_spec`,
`bc_sortDesc_spec` (via `bc_insertDesc_spec`), `bc_kruskal_spec` (via
`bc_relabel_spec`), `bc_rootsOf_spec`, `bc_orient_spec` (via `bc_visit_spec` and
`bc_orientInner_spec`), and `bc_Mf_spec`.  Each gives a polynomial step bound
and the value facts the next stage needs.  `bc_total_arith` and `bc_Mf_arith`
put the total under `S ^ 20`.  Every bound is a size bound only.  Nothing here
uses that Kruskal builds a spanning forest: the BFS queue counter of `orient` is
bounded by `m + n + r · nTree` after `r` rounds, not by the number of vertices.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Program
open Cellcounting.Model.Operations
open Cellcounting.Interface

/-- INTERNAL: `Program.splitCells` keeps counts equal to lengths, partitions the cells,
puts only cells with bound `< W` in the small list, and costs at most
`|cells| (B + bitLen W + |cells| + 1)` when every bound has length `≤ B`. -/
theorem bc_splitCells_spec (B : ℕ) (W : SNat) (cells : List Entry)
    (hc : ∀ e ∈ cells, bitLen e.2.2.get ≤ B) :
    (splitCells W cells).val.1.1.length = (splitCells W cells).val.1.2 ∧
    (splitCells W cells).val.1.1.length + (splitCells W cells).val.2.1.length = cells.length ∧
    (∀ e ∈ (splitCells W cells).val.1.1, e ∈ cells ∧ e.2.2.get < W.get) ∧
    (∀ e ∈ (splitCells W cells).val.2.1, e ∈ cells) ∧
    Charged.steps rate (splitCells W cells) ≤
      cells.length * (B + bitLen W.get + cells.length + 1) := by
  unfold splitCells
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := foldl_inv
    (fun (st : (List Entry × ℕ) × (List Entry × ℕ)) (e : Entry) => (do
      let isSmall ← SNat.lt e.2.2 W
      if isSmall then do
        let s ← Model.Operations.push st.1.1 e
        pure ((s, st.1.2 + 1), st.2)
      else do
        let l ← Model.Operations.push st.2.1 e
        pure (st.1, (l, st.2.2 + 1)) : Prog _))
    (fun i (st : (List Entry × ℕ) × (List Entry × ℕ)) => st.1.1.length = st.1.2 ∧
      st.1.1.length + st.2.1.length = i ∧
      (∀ e ∈ st.1.1, e ∈ cells ∧ e.2.2.get < W.get) ∧ (∀ e ∈ st.2.1, e ∈ cells))
    (B + bitLen W.get + cells.length + 1) cells 0 (([], 0), ([], 0)) (by simp)
    (by
      rintro i ⟨⟨s, ns⟩, ⟨l, nl⟩⟩ a - hi ha ⟨hs, hsl, hS, hL⟩
      have hb := hc a ha
      dsimp only at hs hsl hS hL hi ⊢
      by_cases hlt : a.2.2.get < W.get
      · simp only [Charged.steps_bind, costVb, SNat.val_lt, hlt, decide_true, ite_true,
          steps_SNat_lt, steps_push, val_push, costVp, Charged.steps_pure]
        refine ⟨⟨by simp [hs], by simp; omega, ?_, hL⟩, by omega⟩
        intro e he
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact hS e he
        · exact ⟨ha, hlt⟩
      · simp only [Charged.steps_bind, costVb, SNat.val_lt, hlt, decide_false,
          Bool.false_eq_true, ite_false,
          steps_SNat_lt, steps_push, val_push, costVp, Charged.steps_pure]
        refine ⟨⟨hs, by simp; omega, hS, ?_⟩, by omega⟩
        intro e he
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact hL e he
        · exact ha)
  exact ⟨h1, by simpa using h2, h3, h4, h5⟩

/-- INTERNAL: one insertion of `Program.insertDesc` lengthens the list by one, adds only
`x`, and costs at most `|l| (2B + 2|l| + 3) + |l| + 1`. -/
theorem bc_insertDesc_spec (B : ℕ) (l : List Entry) (x : Entry)
    (hl : ∀ y ∈ l, bitLen y.2.2.get ≤ B) (hx : bitLen x.2.2.get ≤ B) :
    (insertDesc l x).val.length = l.length + 1 ∧
    (∀ y ∈ (insertDesc l x).val, y ∈ l ∨ y = x) ∧
    Charged.steps rate (insertDesc l x) ≤ l.length * (2 * B + 2 * l.length + 3) + l.length + 1 := by
  unfold insertDesc
  obtain ⟨⟨h1, h2⟩, h3⟩ := foldl_inv
    (fun (st : List Entry × Bool) (y : Entry) => (do
      if st.2 then do
        let o ← Model.Operations.push st.1 y
        pure (o, true)
      else do
        let smaller ← SNat.lt y.2.2 x.2.2
        if smaller then do
          let o ← Model.Operations.push st.1 x
          let o' ← Model.Operations.push o y
          pure (o', true)
        else do
          let o ← Model.Operations.push st.1 y
          pure (o, false) : Prog _))
    (fun i (st : List Entry × Bool) => st.1.length = i + st.2.toNat ∧
      ∀ y ∈ st.1, y ∈ l ∨ y = x)
    (2 * B + 2 * l.length + 3) l 0 ([], false) (by simp)
    (by
      rintro i ⟨o, b⟩ y - hi hy ⟨ho, hO⟩
      have hb := hl y hy
      dsimp only at ho hO hi ⊢
      have hmem : ∀ z ∈ o ++ [y], z ∈ l ∨ z = x := by
        intro z hz
        simp only [List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | rfl
        · exact hO z hz
        · exact Or.inl hy
      cases b with
      | true =>
        simp only [ite_true, Charged.steps_bind, costVb, steps_push, val_push, costVp,
          Charged.steps_pure, Bool.toNat_true] at ho ⊢
        refine ⟨⟨by simp; omega, hmem⟩, by omega⟩
      | false =>
        simp only [Bool.false_eq_true, ite_false, Bool.toNat_false] at ho ⊢
        by_cases hlt : y.2.2.get < x.2.2.get
        · simp only [Charged.steps_bind, costVb, SNat.val_lt, hlt, decide_true, ite_true,
            steps_SNat_lt, steps_push, val_push, costVp, Charged.steps_pure, Bool.toNat_true]
          refine ⟨⟨by simp; omega, ?_⟩, by simp; omega⟩
          intro z hz
          simp only [List.mem_append, List.mem_singleton] at hz
          rcases hz with (hz | rfl) | rfl
          · exact hO z hz
          · exact Or.inr rfl
          · exact Or.inl hy
        · simp only [Charged.steps_bind, costVb, SNat.val_lt, hlt, decide_false,
            Bool.false_eq_true, ite_false,
            steps_SNat_lt, steps_push, val_push, costVp, Charged.steps_pure, Bool.toNat_false]
          refine ⟨⟨by simp; omega, hmem⟩, by omega⟩)
  simp only [Charged.steps_bind, costVb] at h1 h2 h3 ⊢
  revert h1 h2 h3
  generalize Charged.foldl _ l ([], false) = F
  intro h1 h2 h3
  rcases hF : F.val with ⟨o, b⟩
  rw [hF] at h2 h3
  dsimp only at h2 h3 ⊢
  cases b with
  | true =>
    simp only [ite_true, costVp, Charged.steps_pure, Bool.toNat_true] at h2 ⊢
    exact ⟨by omega, h3, by omega⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false, Bool.toNat_false, steps_push, val_push] at h2 ⊢
    refine ⟨by simp; omega, ?_, by omega⟩
    intro z hz
    simp only [List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact h3 z hz
    · exact Or.inr rfl

/-- INTERNAL: the insertion sort `Program.sortDesc` preserves length and membership and
costs at most `|l| (|l| (2B + 2|l| + 3) + |l| + 1)`. -/
theorem bc_sortDesc_spec (B : ℕ) (l : List Entry) (hl : ∀ y ∈ l, bitLen y.2.2.get ≤ B) :
    (sortDesc l).val.length = l.length ∧ (∀ y ∈ (sortDesc l).val, y ∈ l) ∧
    Charged.steps rate (sortDesc l) ≤
      l.length * (l.length * (2 * B + 2 * l.length + 3) + l.length + 1) := by
  unfold sortDesc
  obtain ⟨⟨h1, h2⟩, h3⟩ := foldl_inv (fun acc x => insertDesc acc x)
    (fun i (acc : List Entry) => acc.length = i ∧ ∀ y ∈ acc, y ∈ l)
    (l.length * (2 * B + 2 * l.length + 3) + l.length + 1) l 0 [] (by simp)
    (by
      rintro i acc a - hi ha ⟨hlen, hall⟩
      obtain ⟨g1, g2, g3⟩ := bc_insertDesc_spec B acc a (fun y hy => hl y (hall y hy)) (hl a ha)
      refine ⟨⟨by omega, fun y hy => (g2 y hy).elim (hall y) (fun h => h ▸ ha)⟩, ?_⟩
      have hal : acc.length ≤ l.length := by omega
      refine g3.trans ?_
      have : acc.length * (2 * B + 2 * acc.length + 3) ≤ l.length * (2 * B + 2 * l.length + 3) :=
        Nat.mul_le_mul hal (by omega)
      omega)
  exact ⟨by simpa using h1, h2, h3⟩

/-- INTERNAL: the component-relabelling loop inside `Program.kruskal` keeps every label
`≤ V` and costs at most `V (3V + bitLen cv + 3)`. -/
theorem bc_relabel_spec (V : ℕ) (cu cv : ℕ) (hcu : cu ≤ V) (comp : List ℕ)
    (hc : ∀ c ∈ comp, c ≤ V) :
    (∀ c ∈ (Charged.repeatFor (fun w comp => (do
        let cw ← Model.Operations.get comp w
        let hit ← idxEq cw cv
        if hit then Model.Operations.set comp w cu else pure comp : Prog (List ℕ))) V comp).val,
      c ≤ V) ∧
    Charged.steps rate (Charged.repeatFor (fun w comp => (do
        let cw ← Model.Operations.get comp w
        let hit ← idxEq cw cv
        if hit then Model.Operations.set comp w cu else pure comp : Prog (List ℕ))) V comp) ≤
      V * (3 * V + bitLen cv + 3) := by
  obtain ⟨h1, h2⟩ := repeatFor_inv (fun w comp => (do
        let cw ← Model.Operations.get comp w
        let hit ← idxEq cw cv
        if hit then Model.Operations.set comp w cu else pure comp : Prog (List ℕ)))
    (fun _ (comp : List ℕ) => ∀ c ∈ comp, c ≤ V) (3 * V + bitLen cv + 3) V comp hc
    (by
      intro r b hr hb
      have hcw : b.getD r default ≤ V := getD_prop (P := (· ≤ V)) b r default hb (Nat.zero_le _)
      have hbl := bitLen_le_succ (b.getD r default)
      by_cases hh : b.getD r default = cv
      · simp only [Charged.steps_bind, costVb, val_get, val_idxEq, hh, decide_true, ite_true,
          steps_get, steps_idxEq, steps_set, val_set]
        refine ⟨set_prop b r cu hb hcu, ?_⟩
        rw [hh] at hcw hbl; omega
      · simp only [Charged.steps_bind, costVb, val_get, val_idxEq, hh, decide_false,
          Bool.false_eq_true, ite_false, steps_get, steps_idxEq, costVp, Charged.steps_pure]
        exact ⟨hb, by omega⟩)
  exact ⟨h1, h2⟩

/-- INTERNAL: `Program.kruskal` splits its input into tree and free cells (counts equal
to lengths), keeps component labels `≤ m + n`, and costs a fixed polynomial in
`m + n` and `|L|`. -/
theorem bc_kruskal_spec (m n : ℕ) (L : List Entry) (hL : ∀ e ∈ L, e.1 < m ∧ e.2.1 < n) :
    (kruskal m n L).val.1.1.length = (kruskal m n L).val.1.2 ∧
    (kruskal m n L).val.2.1.1.length = (kruskal m n L).val.2.1.2 ∧
    (kruskal m n L).val.1.1.length + (kruskal m n L).val.2.1.1.length = L.length ∧
    (∀ e ∈ (kruskal m n L).val.1.1, e ∈ L) ∧ (∀ e ∈ (kruskal m n L).val.2.1.1, e ∈ L) ∧
    (∀ c ∈ (kruskal m n L).val.2.2, c ≤ m + n) ∧
    Charged.steps rate (kruskal m n L) ≤ (m + n) * (m + n) +
      L.length * ((m + n) * (4 * (m + n) + 4) + 5 * (m + n) + L.length + 5) := by
  unfold kruskal
  simp only [Charged.steps_bind, costVb]
  obtain ⟨⟨hc0, -⟩, hc0s⟩ := repeatFor_inv (fun v acc => (Model.Operations.push acc v : Prog (List ℕ)))
    (fun r (acc : List ℕ) => (∀ c ∈ acc, c ≤ m + n) ∧ acc.length = r) (m + n) (m + n) []
    (by simp)
    (by
      rintro r acc hr ⟨hacc, hlen⟩
      simp only [steps_push, val_push]
      refine ⟨⟨?_, by simp [hlen]⟩, by omega⟩
      intro c hc
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact hacc c hc
      · omega)
  generalize (Charged.repeatFor (fun v acc => (Model.Operations.push acc v : Prog (List ℕ))) (m + n) []) = C0 at hc0 hc0s ⊢
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ := foldl_inv
    (fun (st : (List Entry × ℕ) × (List Entry × ℕ) × List ℕ) (e : Entry) => (do
      let cu ← Model.Operations.get st.2.2 e.1
      let cv ← Model.Operations.get st.2.2 (m + e.2.1)
      let same ← idxEq cu cv
      if same then do
        let f ← Model.Operations.push st.2.1.1 e
        pure (st.1, (f, st.2.1.2 + 1), st.2.2)
      else do
        let t ← Model.Operations.push st.1.1 e
        let comp' ← Charged.repeatFor (fun w comp => do
          let cw ← Model.Operations.get comp w
          let hit ← idxEq cw cv
          if hit then Model.Operations.set comp w cu else pure comp) (m + n) st.2.2
        pure ((t, st.1.2 + 1), st.2.1, comp') : Prog _))
    (fun i (st : (List Entry × ℕ) × (List Entry × ℕ) × List ℕ) =>
      st.1.1.length = st.1.2 ∧ st.2.1.1.length = st.2.1.2 ∧
      st.1.1.length + st.2.1.1.length = i ∧
      (∀ e ∈ st.1.1, e ∈ L) ∧ (∀ e ∈ st.2.1.1, e ∈ L) ∧ (∀ c ∈ st.2.2, c ≤ m + n))
    ((m + n) * (4 * (m + n) + 4) + 5 * (m + n) + L.length + 5) L 0 (([], 0), ([], 0), C0.val)
    (by simpa using hc0)
    (by
      rintro i ⟨⟨t, nt⟩, ⟨f, nf⟩, comp⟩ a - hi ha ⟨ht, hf, htf, hT, hF, hC⟩
      obtain ⟨ha1, ha2⟩ := hL a ha
      dsimp only at ht hf htf hT hF hC hi ⊢
      have hcu : comp.getD a.1 default ≤ m + n :=
        getD_prop (P := (· ≤ m + n)) comp _ default hC (Nat.zero_le _)
      have hcv : comp.getD (m + a.2.1) default ≤ m + n :=
        getD_prop (P := (· ≤ m + n)) comp _ default hC (Nat.zero_le _)
      have hb1 := bitLen_le_succ (comp.getD a.1 default)
      have hb2 := bitLen_le_succ (comp.getD (m + a.2.1) default)
      have hmem : ∀ (l : List Entry), (∀ e ∈ l, e ∈ L) → ∀ e ∈ l ++ [a], e ∈ L := by
        intro l hl e he
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact hl e he
        · exact ha
      by_cases hh : comp.getD a.1 default = comp.getD (m + a.2.1) default
      · simp only [Charged.steps_bind, costVb, val_get, val_idxEq, hh, decide_true, ite_true,
          steps_get, steps_idxEq, steps_push, val_push, costVp, Charged.steps_pure]
        refine ⟨⟨ht, by simp [hf], by simp; omega, hT, hmem f hF, hC⟩, ?_⟩
        rw [hh] at hb1
        omega
      · obtain ⟨r1, r2⟩ := bc_relabel_spec (m + n) (comp.getD a.1 default)
          (comp.getD (m + a.2.1) default) hcu comp hC
        simp only [Charged.steps_bind, costVb, val_get, val_idxEq, hh, decide_false,
          Bool.false_eq_true, ite_false,
          steps_get, steps_idxEq, steps_push, val_push, costVp, Charged.steps_pure]
        refine ⟨⟨by simp [ht], hf, by simp; omega, hmem t hT, hF, r1⟩, ?_⟩
        have : (m + n) * (3 * (m + n) + bitLen (comp.getD (m + a.2.1) default) + 3) ≤
            (m + n) * (4 * (m + n) + 4) := Nat.mul_le_mul_left _ (by omega)
        omega)
  refine ⟨h1, h2, by simpa using h3, h4, h5, h6, ?_⟩
  omega

/-- INTERNAL: `Program.rootsOf` returns at most `V` roots, each `< V`, at cost
`≤ V + 1 + V (4V + 3)`. -/
theorem bc_rootsOf_spec (V : ℕ) (comp : List ℕ) (hc : ∀ c ∈ comp, c ≤ V) :
    (rootsOf V comp).val.length ≤ V ∧ (∀ v ∈ (rootsOf V comp).val, v < V) ∧
    Charged.steps rate (rootsOf V comp) ≤ V + 1 + V * (4 * V + 3) := by
  unfold rootsOf
  simp only [Charged.steps_bind, costVb, steps_replicate, val_replicate, costVp,
    Charged.steps_pure]
  obtain ⟨⟨h1, h2⟩, h3⟩ := repeatFor_inv (fun v (st : List Bool × List ℕ) => (do
      let cv ← Model.Operations.get comp v
      let s ← Model.Operations.get st.1 cv
      if s then pure st else do
        let seen ← Model.Operations.set st.1 cv true
        let rs ← Model.Operations.push st.2 v
        pure (seen, rs) : Prog _))
    (fun r (st : List Bool × List ℕ) => st.2.length ≤ r ∧ ∀ v ∈ st.2, v < r)
    (4 * V + 3) V (List.replicate V false, []) (by simp)
    (by
      rintro r ⟨seen, rs⟩ hr ⟨hl, hv⟩
      dsimp only at hl hv ⊢
      have hcv : comp.getD r default ≤ V :=
        getD_prop (P := (· ≤ V)) comp _ default hc (Nat.zero_le _)
      cases hs : seen.getD (comp.getD r default) default with
      | true =>
        simp only [Charged.steps_bind, costVb, val_get, hs, ite_true, steps_get, costVp,
          Charged.steps_pure]
        exact ⟨⟨by omega, fun v hv' => by have := hv v hv'; omega⟩, by omega⟩
      | false =>
        simp only [Charged.steps_bind, costVb, val_get, hs, Bool.false_eq_true, ite_false,
          steps_get, steps_set, steps_push, val_set, val_push, costVp, Charged.steps_pure]
        refine ⟨⟨by simp; omega, ?_⟩, by omega⟩
        intro v hv'
        simp only [List.mem_append, List.mem_singleton] at hv'
        rcases hv' with hv' | rfl
        · have := hv v hv'; omega
        · omega)
  exact ⟨h1, h2, by omega⟩

/-- INTERNAL: the size invariant of the breadth-first search of `Program.orient`:
queue counter at most `c`, at most `o` discovered pairs, queue entries and
discovered vertices at most `V`, discovered tree edges below `Nt`. -/
def BcOInv (V Nt c o : ℕ) (st : Orient) : Prop :=
  st.1.2.2 ≤ c ∧ st.2.length ≤ o ∧ (∀ u ∈ st.1.2.1, u ≤ V) ∧
    (∀ vt ∈ st.2, vt.1 ≤ V ∧ vt.2 < Nt)

/-- INTERNAL: one `Program.visit` raises the queue counter and the discovered list by at
most one each, and costs at most `2V + c + 3`. -/
theorem bc_visit_spec (V Nt c o w t : ℕ) (st : Orient) (hw : w ≤ V) (ht : t < Nt)
    (h : BcOInv V Nt c o st) :
    BcOInv V Nt (c + 1) (o + 1) (visit w t st).val ∧
      Charged.steps rate (visit w t st) ≤ 2 * V + c + 3 := by
  obtain ⟨⟨vis, q, cnt⟩, ord⟩ := st
  obtain ⟨hc, ho, hq, hord⟩ := h
  dsimp only at hc ho hq hord
  unfold visit
  cases hs : vis.getD w default with
  | true =>
    simp only [Charged.steps_bind, costVb, val_get, hs, ite_true, steps_get, costVp,
      Charged.steps_pure]
    exact ⟨⟨by dsimp only; omega, by dsimp only; omega, hq, hord⟩, by omega⟩
  | false =>
    simp only [Charged.steps_bind, costVb, val_get, hs, Bool.false_eq_true, ite_false,
      steps_get, steps_set, val_set, costVp, Charged.steps_pure]
    refine ⟨⟨by dsimp only; omega, by simp; omega, set_prop q cnt w hq hw, ?_⟩, by omega⟩
    intro vt hvt
    simp only [List.mem_cons] at hvt
    rcases hvt with rfl | hvt
    · exact ⟨hw, ht⟩
    · exact hord vt hvt

/-- INTERNAL: the scan of all tree edges at one queue vertex in `Program.orient` raises
the counter and the discovered list by at most `Nt`. -/
theorem bc_orientInner_spec (m V Nt c o u : ℕ) (tree : List Entry) (hu : u ≤ V)
    (htree : ∀ e ∈ tree, e.1 ≤ V ∧ m + e.2.1 ≤ V) (hmV : m ≤ V) (st : Orient)
    (h : BcOInv V Nt c o st) :
    BcOInv V Nt (c + Nt) (o + Nt) (Charged.repeatFor (fun t (st' : Orient) => (do
        let e ← Model.Operations.get tree t
        let atRow ← idxEq e.1 u
        if atRow then visit (m + e.2.1) t st' else do
          let atCol ← idxEq (m + e.2.1) u
          if atCol then visit e.1 t st' else pure st' : Prog Orient)) Nt st).val ∧
    Charged.steps rate (Charged.repeatFor (fun t (st' : Orient) => (do
        let e ← Model.Operations.get tree t
        let atRow ← idxEq e.1 u
        if atRow then visit (m + e.2.1) t st' else do
          let atCol ← idxEq (m + e.2.1) u
          if atCol then visit e.1 t st' else pure st' : Prog Orient)) Nt st) ≤
      Nt * (2 * Nt + 8 * V + c + 10) := by
  refine repeatFor_inv _ (fun r st => BcOInv V Nt (c + r) (o + r) st) _ Nt st (by simpa using h) ?_
  intro r st' hr hst
  have he : (tree.getD r default).1 ≤ V ∧ m + (tree.getD r default).2.1 ≤ V :=
    getD_prop (P := fun e : Entry => e.1 ≤ V ∧ m + e.2.1 ≤ V) tree r default htree
      (by change 0 ≤ V ∧ m + 0 ≤ V; omega)
  have hb1 := bitLen_le_succ (tree.getD r default).1
  have hb2 := bitLen_le_succ (m + (tree.getD r default).2.1)
  have hbu := bitLen_le_succ u
  have hmono : ∀ s, BcOInv V Nt (c + r) (o + r) s → BcOInv V Nt (c + (r + 1)) (o + (r + 1)) s := by
    rintro s ⟨a1, a2, a3, a4⟩; exact ⟨by omega, by omega, a3, a4⟩
  by_cases hrow : (tree.getD r default).1 = u
  · obtain ⟨v1, v2⟩ := bc_visit_spec V Nt (c + r) (o + r) _ r st' he.2 hr hst
    simp only [Charged.steps_bind, costVb, val_get, val_idxEq, hrow, decide_true, ite_true,
      steps_get, steps_idxEq]
    refine ⟨by simpa [Nat.add_assoc] using v1, ?_⟩
    rw [hrow] at hb1; omega
  · by_cases hcol : m + (tree.getD r default).2.1 = u
    · obtain ⟨v1, v2⟩ := bc_visit_spec V Nt (c + r) (o + r) _ r st' he.1 hr hst
      simp only [Charged.steps_bind, costVb, val_get, val_idxEq, hrow, hcol, decide_true,
        decide_false, Bool.false_eq_true, ite_false, ite_true, steps_get, steps_idxEq]
      refine ⟨by simpa [Nat.add_assoc] using v1, ?_⟩
      rw [hcol] at hb2; omega
    · simp only [Charged.steps_bind, costVb, val_get, val_idxEq, hrow, hcol,
        decide_false, Bool.false_eq_true, ite_false, steps_get, steps_idxEq, costVp,
        Charged.steps_pure]
      exact ⟨hmono _ hst, by omega⟩

/-- INTERNAL: `Program.orient` returns at most `(m + n) Nt` pairs `(vertex, edge)`, with
vertices `≤ m + n` and edges `< Nt`, at polynomial cost.  The queue counter is bounded
crudely by `m + n + r Nt` after `r` rounds; no visited-count argument is needed. -/
theorem bc_orient_spec (m n Nt : ℕ) (tree : List Entry) (roots : List ℕ)
    (htree : ∀ e ∈ tree, e.1 ≤ m + n ∧ m + e.2.1 ≤ m + n)
    (hroots : ∀ v ∈ roots, v < m + n) (hrl : roots.length ≤ m + n) :
    (orient m n tree Nt roots).val.length ≤ (m + n) * Nt ∧
    (∀ vt ∈ (orient m n tree Nt roots).val, vt.1 ≤ m + n ∧ vt.2 < Nt) ∧
    Charged.steps rate (orient m n tree Nt roots) ≤
      2 * (m + n + 1) + (m + n) * (2 * (m + n)) +
        (m + n) * (3 * (m + n) + (m + n) * Nt + 2 +
          Nt * (2 * Nt + 9 * (m + n) + (m + n) * Nt + 10)) := by
  unfold orient
  simp only [Charged.steps_bind, costVb, steps_replicate, val_replicate, costVp,
    Charged.steps_pure]
  obtain ⟨⟨r1, r2⟩, r3⟩ := foldl_inv (fun (st : List Bool × List ℕ × ℕ) v => (do
      let vis ← Model.Operations.set st.1 v true
      let q ← Model.Operations.set st.2.1 st.2.2 v
      pure (vis, q, st.2.2 + 1) : Prog _))
    (fun i (st : List Bool × List ℕ × ℕ) => st.2.2 = i ∧ ∀ u ∈ st.2.1, u ≤ m + n)
    (2 * (m + n)) roots 0 (List.replicate (m + n) false, List.replicate (m + n) 0, 0)
    (by
      refine ⟨rfl, fun u hu => ?_⟩
      simp only [List.mem_replicate] at hu; omega)
    (by
      rintro i ⟨vis, q, cnt⟩ v - hi hv ⟨hc, hq⟩
      have := hroots v hv
      dsimp only at hc hq ⊢
      simp only [Charged.steps_bind, costVb, steps_set, val_set, costVp, Charged.steps_pure]
      exact ⟨⟨by omega, set_prop q cnt v hq (by omega)⟩, by omega⟩)
  generalize (Charged.foldl _ roots _) = F0 at r1 r2 r3 ⊢
  obtain ⟨o1, o2⟩ := repeatFor_inv (fun k (st : Orient) => (do
      let live ← idxLt k st.1.2.2
      if live then do
        let u ← Model.Operations.get st.1.2.1 k
        Charged.repeatFor (fun t (st' : Orient) => do
          let e ← Model.Operations.get tree t
          let atRow ← idxEq e.1 u
          if atRow then visit (m + e.2.1) t st' else do
            let atCol ← idxEq (m + e.2.1) u
            if atCol then visit e.1 t st' else pure st') Nt st
      else pure st : Prog Orient))
    (fun r st => BcOInv (m + n) Nt (m + n + r * Nt) (r * Nt) st)
    (3 * (m + n) + (m + n) * Nt + 2 + Nt * (2 * Nt + 9 * (m + n) + (m + n) * Nt + 10))
    (m + n) (F0.val, [])
    ⟨by dsimp only; omega, by simp, r2, by simp⟩
    (by
      rintro r ⟨⟨vis, q, cnt⟩, ord⟩ hr hst
      have hst' := hst
      obtain ⟨hc, ho, hq, hord⟩ := hst
      dsimp only at hc ho hq hord ⊢
      have hrN : r * Nt ≤ (m + n) * Nt := Nat.mul_le_mul_right _ hr.le
      have hb1 := bitLen_le_succ r
      have hb2 := bitLen_le_succ cnt
      by_cases hlive : r < cnt
      · have hu : q.getD r default ≤ m + n :=
          getD_prop (P := (· ≤ m + n)) q r default hq (Nat.zero_le _)
        obtain ⟨i1, i2⟩ := bc_orientInner_spec m (m + n) Nt (m + n + r * Nt) (r * Nt)
          (q.getD r default) tree hu htree (by omega) _ hst'
        simp only [Charged.steps_bind, costVb, val_idxLt, hlive, decide_true, ite_true,
          steps_idxLt, val_get, steps_get]
        refine ⟨?_, ?_⟩
        · obtain ⟨a1, a2, a3, a4⟩ := i1
          exact ⟨by rw [Nat.succ_mul]; omega, by rw [Nat.succ_mul]; omega, a3, a4⟩
        · have : Nt * (2 * Nt + 8 * (m + n) + (m + n + r * Nt) + 10) ≤
              Nt * (2 * Nt + 9 * (m + n) + (m + n) * Nt + 10) :=
            Nat.mul_le_mul_left _ (by omega)
          generalize Nt * (2 * Nt + 9 * (m + n) + (m + n) * Nt + 10) = X at this ⊢
          generalize Nt * (2 * Nt + 8 * (m + n) + (m + n + r * Nt) + 10) = Y at this i2
          omega
      · simp only [Charged.steps_bind, costVb, val_idxLt, hlive, decide_false,
          Bool.false_eq_true, ite_false, steps_idxLt, costVp, Charged.steps_pure]
        refine ⟨⟨by dsimp only; rw [Nat.succ_mul]; omega,
          by dsimp only; rw [Nat.succ_mul]; omega, hq, hord⟩, ?_⟩
        omega)
  obtain ⟨-, a2, -, a4⟩ := o1
  refine ⟨a2, a4, ?_⟩
  have : roots.length * (2 * (m + n)) ≤ (m + n) * (2 * (m + n)) := Nat.mul_le_mul_right _ hrl
  omega

/-- INTERNAL: the fold computing `M_f = ∏ (b_e + 1)` keeps `bitLen M_f ≤ 2 + |F| (B + 2)`
and costs at most `|F| (B + 2 + (2 + |F| (B + 2)) (B + 2))`. -/
theorem bc_Mf_spec (B : ℕ) (free : List Entry) (hf : ∀ e ∈ free, bitLen e.2.2.get ≤ B)
    (one : SNat) (hone : one.get = 1) :
    bitLen (Charged.foldl (fun acc (e : Entry) => (do
        let b1 ← SNat.add e.2.2 one
        SNat.mul acc b1 : Prog SNat)) free one).val.get ≤ 2 + free.length * (B + 2) ∧
    Charged.steps rate (Charged.foldl (fun acc (e : Entry) => (do
        let b1 ← SNat.add e.2.2 one
        SNat.mul acc b1 : Prog SNat)) free one) ≤
      free.length * (B + 2 + (2 + free.length * (B + 2)) * (B + 2)) := by
  have h1 : bitLen 1 = 2 := by decide
  obtain ⟨g1, g2⟩ := foldl_inv (fun acc (e : Entry) => (do
        let b1 ← SNat.add e.2.2 one
        SNat.mul acc b1 : Prog SNat))
    (fun i (acc : SNat) => bitLen acc.get ≤ 2 + i * (B + 2))
    (B + 2 + (2 + free.length * (B + 2)) * (B + 2)) free 0 one (by simp [hone, h1])
    (by
      rintro i acc e - hi he hacc
      have hb := hf e he
      have hb1 : bitLen (e.2.2.get + 1) ≤ B + 2 := (bitLen_add_le' _ _).trans (by omega)
      simp only [Charged.steps_bind, costVb, steps_SNat_add, steps_SNat_mul, SNat.get_add,
        SNat.get_mul, hone, h1]
      refine ⟨(bitLen_mul_le _ _).trans (by rw [Nat.succ_mul]; omega), ?_⟩
      have : bitLen acc.get * bitLen (e.2.2.get + 1) ≤ (2 + free.length * (B + 2)) * (B + 2) :=
        Nat.mul_le_mul (hacc.trans (by
          have := Nat.mul_le_mul_right (B + 2) (show i ≤ free.length by omega); omega)) hb1
      omega)
  exact ⟨by simpa using g1, g2⟩

/-- INTERNAL: the total of the stage bounds of `buildCtx`, with every size
replaced by `S`, is at most `S ^ 20`. -/
theorem bc_total_arith (S : ℕ) (hS : 2 ≤ S) :
    S * (3 * S + 2) + S * (S * (4 * S + 3) + S + 1) +
      (S * S + S * (S * (4 * S + 4) + 6 * S + 5)) + (S + 1 + S * (4 * S + 3)) +
      (2 * (S + 1) + S * (2 * S) + S * (3 * S + S * S + 2 + S * (11 * S + S * S + 10))) + 2 +
      S * (S + 2 + (2 + S * (S + 2)) * (S + 2)) + 3 * (S + 1) ≤ S ^ 20 := by
  have h1 : 1 ≤ S := by omega
  have p1 : S ≤ S ^ 4 := by
    calc S = S ^ 1 := (pow_one S).symm
      _ ≤ S ^ 4 := Nat.pow_le_pow_right h1 (by norm_num)
  have p2 : S ^ 2 ≤ S ^ 4 := Nat.pow_le_pow_right h1 (by norm_num)
  have p3 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right h1 (by norm_num)
  have p0 : 1 ≤ S ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hc : 2 ^ 16 * S ^ 4 ≤ S ^ 20 := by
    rw [show S ^ 20 = S ^ 16 * S ^ 4 by ring]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hS 16)
  have : S * (3 * S + 2) + S * (S * (4 * S + 3) + S + 1) +
      (S * S + S * (S * (4 * S + 4) + 6 * S + 5)) + (S + 1 + S * (4 * S + 3)) +
      (2 * (S + 1) + S * (2 * S) + S * (3 * S + S * S + 2 + S * (11 * S + S * S + 10))) + 2 +
      S * (S + 2 + (2 + S * (S + 2)) * (S + 2)) + 3 * (S + 1) ≤ 2 ^ 16 * S ^ 4 := by
    ring_nf
    linarith
  omega

/-- INTERNAL: the bound on the length of `M_f`, in terms of `S`, is at most `S ^ 20`. -/
theorem bc_Mf_arith (S : ℕ) (hS : 2 ≤ S) : 2 + S * (S + 2) ≤ S ^ 20 := by
  have h1 : 1 ≤ S := by omega
  have p2 : S ^ 2 ≤ S ^ 4 := Nat.pow_le_pow_right h1 (by norm_num)
  have p1 : S ≤ S ^ 4 := by
    calc S = S ^ 1 := (pow_one S).symm
      _ ≤ S ^ 4 := Nat.pow_le_pow_right h1 (by norm_num)
  have p0 : 1 ≤ S ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hc : 2 ^ 4 * S ^ 4 ≤ S ^ 20 := by
    rw [show S ^ 20 = S ^ 16 * S ^ 4 by ring]
    exact Nat.mul_le_mul_right _ ((Nat.pow_le_pow_left hS 4).trans
      (Nat.pow_le_pow_right h1 (by norm_num)))
  have : 2 + S * (S + 2) ≤ 2 ^ 4 * S ^ 4 := by ring_nf; linarith
  omega

/-- INTERNAL: S4 costs a fixed power of a size bound `S`, and every size of the
context it builds is bounded by the same power.
TEXLINE: sections/scales.tex:79-99 -/
theorem buildCtx_cost : ∃ k : ℕ, ∀ (S m n : ℕ) (T : Tight) (Pm : Params),
    2 ≤ S → m + n + 2 ≤ S →
    (∀ x ∈ T.rows, bitLen x.get ≤ S) → (∀ x ∈ T.cols, bitLen x.get ≤ S) →
    T.cells.length ≤ S →
    (∀ e ∈ T.cells, e.1 < m ∧ e.2.1 < n ∧ bitLen e.2.2.get ≤ S) →
    PmSize S Pm → 1 ≤ Pm.B.get → 1 ≤ Pm.H.get →
    Charged.steps rate (buildCtx m n T Pm) ≤ S ^ k ∧
    CtxSize (S ^ k) (buildCtx m n T Pm).val ∧
    (buildCtx m n T Pm).val.small.length ≤ T.cells.length ∧
    (∀ e ∈ (buildCtx m n T Pm).val.small, e.2.2.get < Pm.W.get) := by
  refine ⟨20, ?_⟩
  intro S m n T Pm hS hmn hrows hcols hcl hcells hPm hB1 hH1
  have hSN : S ≤ S ^ 20 := pw_mono hS (pw_self le_rfl) (by norm_num)
  have hW := hPm.W_le
  obtain ⟨s1, s2, s3, s4, s5⟩ :=
    bc_splitCells_spec S Pm.W T.cells (fun e he => (hcells e he).2.2)
  unfold buildCtx
  simp only [Charged.steps_bind, costVb, costVp]
  generalize (splitCells Pm.W T.cells).val = SP at s1 s2 s3 s4 ⊢
  obtain ⟨o1, o2, o3⟩ := bc_sortDesc_spec S SP.2.1 (fun e he => (hcells e (s4 e he)).2.2)
  generalize (sortDesc SP.2.1).val = SO at o1 o2 o3 ⊢
  have hSO : ∀ e ∈ SO, e ∈ T.cells := fun e he => s4 e (o2 e he)
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := bc_kruskal_spec m n SO
    (fun e he => ⟨(hcells e (hSO e he)).1, (hcells e (hSO e he)).2.1⟩)
  generalize (kruskal m n SO).val = K at k1 k2 k3 k4 k5 k6 k7 ⊢
  obtain ⟨r1, r2, r3⟩ := bc_rootsOf_spec (m + n) K.2.2 k6
  generalize (rootsOf (m + n) K.2.2).val = R at r1 r2 r3 ⊢
  obtain ⟨t1, t2, t3⟩ := bc_orient_spec m n K.1.2 K.1.1 R
    (fun e he => by have := hcells e (hSO e (k4 e he)); omega) r2 r1
  generalize (orient m n K.1.1 K.1.2 R).val = O at t1 t2 t3 ⊢
  obtain ⟨f1, f2⟩ := bc_Mf_spec S K.2.1.1 (fun e he => (hcells e (hSO e (k5 e he))).2.2)
    (SNat.lit 1).val (by simp)
  generalize (Charged.foldl _ K.2.1.1 (SNat.lit 1).val) = MF at f1 f2 ⊢
  -- every size is at most `S`
  have hc : T.cells.length ≤ S := hcl
  have ha : SP.2.1.length ≤ S := by omega
  have hV : m + n ≤ S := by omega
  have hNt : K.1.2 ≤ S := by omega
  have hF : K.2.1.1.length ≤ S := by omega
  have hbW := bitLen_le_succ Pm.W.get
  have c1 : Charged.steps rate (splitCells Pm.W T.cells) ≤ S * (3 * S + 2) :=
    s5.trans (by
      calc T.cells.length * (S + bitLen Pm.W.get + T.cells.length + 1)
          ≤ S * (S + (S + 1) + S + 1) := by gcongr; omega
        _ = S * (3 * S + 2) := by ring)
  have c2 : Charged.steps rate (sortDesc SP.2.1) ≤ S * (S * (4 * S + 3) + S + 1) :=
    o3.trans (by
      calc SP.2.1.length * (SP.2.1.length * (2 * S + 2 * SP.2.1.length + 3) + SP.2.1.length + 1)
          ≤ S * (S * (2 * S + 2 * S + 3) + S + 1) := by gcongr
        _ = S * (S * (4 * S + 3) + S + 1) := by ring)
  have c3 : Charged.steps rate (kruskal m n SO) ≤ S * S + S * (S * (4 * S + 4) + 6 * S + 5) :=
    k7.trans (by
      calc (m + n) * (m + n) + SO.length * ((m + n) * (4 * (m + n) + 4) + 5 * (m + n) +
            SO.length + 5)
          ≤ S * S + S * (S * (4 * S + 4) + 5 * S + S + 5) := by rw [o1]; gcongr
        _ = S * S + S * (S * (4 * S + 4) + 6 * S + 5) := by ring)
  have c4 : Charged.steps rate (rootsOf (m + n) K.2.2) ≤ S + 1 + S * (4 * S + 3) :=
    r3.trans (by gcongr)
  have c5 : Charged.steps rate (orient m n K.1.1 K.1.2 R) ≤
      2 * (S + 1) + S * (2 * S) + S * (3 * S + S * S + 2 + S * (11 * S + S * S + 10)) :=
    t3.trans (by
      calc 2 * (m + n + 1) + (m + n) * (2 * (m + n)) +
            (m + n) * (3 * (m + n) + (m + n) * K.1.2 + 2 +
              K.1.2 * (2 * K.1.2 + 9 * (m + n) + (m + n) * K.1.2 + 10))
          ≤ 2 * (S + 1) + S * (2 * S) + S * (3 * S + S * S + 2 + S * (2 * S + 9 * S + S * S + 10)) := by
            gcongr
        _ = 2 * (S + 1) + S * (2 * S) + S * (3 * S + S * S + 2 + S * (11 * S + S * S + 10)) := by
            ring)
  have c6 : Charged.steps rate MF ≤ S * (S + 2 + (2 + S * (S + 2)) * (S + 2)) :=
    f2.trans (by gcongr)
  have c7 : Charged.steps rate Pm.A.toRat + Charged.steps rate Pm.H.toRat +
      Charged.steps rate Pm.B.toRat ≤ 3 * (S + 1) := by
    simp only [steps_SNat_toRat]
    have := bitLen_le_succ Pm.A.get; have := bitLen_le_succ Pm.H.get
    have := bitLen_le_succ Pm.B.get
    have := hPm.A_le; have := hPm.H_le; have := hPm.B_le
    omega
  have c8 : Charged.steps rate (SNat.lit 1) = 2 := by rw [steps_SNat_lit]; decide
  have ctot := bc_total_arith S hS
  refine ⟨?_, ?_, s2 ▸ Nat.le_add_right _ _, fun e he => (s3 e he).2⟩
  · rw [Charged.steps_pure]
    linarith
  · have hSS : S * S ≤ S ^ 20 := pw_mono hS (pw_mul (pw_self le_rfl) (pw_self le_rfl)) (by norm_num)
    have hMf : 2 + S * (S + 2) ≤ S ^ 20 := bc_Mf_arith S hS
    have hcellS : ∀ e ∈ T.cells, e.1 ≤ S ^ 20 ∧ e.2.1 ≤ S ^ 20 ∧ bitLen e.2.2.get ≤ S ^ 20 :=
      fun e he => by have := hcells e he; exact ⟨by omega, by omega, by omega⟩
    exact {
      m_le := by dsimp only; omega
      n_le := by dsimp only; omega
      rows_bits := fun x hx => (hrows x hx).trans hSN
      cols_bits := fun x hx => (hcols x hx).trans hSN
      nSmall_le := by dsimp only; linarith
      small_le := fun e he => by
        obtain ⟨he1, he2⟩ := s3 e he
        have := hcells e he1
        exact ⟨by omega, by omega, by omega⟩
      nFree_le := by dsimp only; linarith
      free_le := fun e he => hcellS e (hSO e (k5 e he))
      nTree_le := by dsimp only; linarith
      tree_le := fun e he => hcellS e (hSO e (k4 e he))
      order_length := by
        dsimp only
        exact t1.trans ((Nat.mul_le_mul hV hNt).trans hSS)
      order_le := fun vt hvt => by
        have := t2 vt hvt; exact ⟨by omega, by omega⟩
      roots_length := by dsimp only; omega
      roots_le := fun v hv => by have := r2 v hv; omega
      Mf_bits := by
        dsimp only
        refine f1.trans (le_trans ?_ hMf)
        gcongr
      d_le := by dsimp only; have := hPm.d_le; omega
      B_pos := hB1
      B_le := by dsimp only; have := hPm.B_le; omega
      H_pos := hH1
      H_le := by dsimp only; have := hPm.H_le; omega
      Aq_eq := ⟨Pm.A.get, SNat.get_toRat _, by have := hPm.A_le; omega⟩
      Hq_eq := SNat.get_toRat _
      Bq_eq := SNat.get_toRat _ }

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `buildCtx_cost` with `k = 20`, one spec lemma per stage of S4
-/
