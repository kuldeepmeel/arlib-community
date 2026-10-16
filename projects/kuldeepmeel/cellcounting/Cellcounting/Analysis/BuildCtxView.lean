import Cellcounting.Model.Program
import Cellcounting.Interface.Pseudocode
import Cellcounting.Interface.Encoding
import Cellcounting.Analysis.PhaseWindow

/-!
# The program's context builder computes the pseudocode's context

`Cellcounting.Analysis.buildCtx_view_of`: if a tightened instance `T` and parameters `Pm`
agree with the pseudocode (`tighten_view`, `params_view` shapes), then the context
`Program.buildCtx I.m I.n T Pm` agrees with the pseudocode's derived data field by field:
small cells and their count, free and tree cells of the maximum-capacity spanning forest
and their counts, the roots, the leaf-elimination order, `M_f`, and the parameters.

It is proved stage by stage, each stage a value lemma about one program routine:
`bv_splitCells` (small/large split), `bv_sortDesc` via `bv_insertDesc` (insertion sort is
`List.orderedInsert` by decreasing bound), `bv_kruskal` via `bv_kruskal_step` and
`bv_relabel` (the component list represents `Forest.comp` on vertices `< m + n`, whose
values stay `< m + n`), `bv_rootsOf`, `bv_orient` via `bv_visit` and `bv_mark` (the BFS
marks and queue represent the visited finset and queue list), and `bv_Mf`.  Only values
are stated; nothing here bounds cost.  `Interface/ProgramModel.lean` proves
`buildCtx_view` from this lemma, `tighten_view` and `params_view`.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Model.Operations

/-- INTERNAL: forget the sealing of a program cell. -/
noncomputable def bvE (e : Program.Entry) : Pseudocode.Entry := (e.1, e.2.1, e.2.2.get)

/-- INTERNAL: a relation carried through a charged fold and a pure fold in lockstep. -/
theorem bv_foldl_rel {ι β γ : Type} (R : β → γ → Prop) (f : β → ι → Program.Prog β)
    (g : γ → ι → γ) (l : List ι)
    (step : ∀ b c a, a ∈ l → R b c → R (f b a).val (g c a)) :
    ∀ b c, R b c → R (Charged.foldl f l b).val (l.foldl g c) := by
  induction l with
  | nil => intro b c h; simpa using h
  | cons a l ih =>
    intro b c h
    rw [Charged.val_foldl_cons, List.foldl_cons]
    exact ih (fun b c a ha => step b c a (List.mem_cons_of_mem _ ha)) _ _
      (step b c a (by simp) h)

/-- INTERNAL: value of the small/large split, from an arbitrary state. -/
theorem bv_split_fold (W : ℕ) (cells : List Program.Entry) :
    ∀ (s : List Program.Entry) (ns : ℕ) (l : List Program.Entry) (nl : ℕ),
    cells.foldl (fun (st : (List Program.Entry × ℕ) × (List Program.Entry × ℕ)) e =>
        if e.2.2.get < W then ((st.1.1 ++ [e], st.1.2 + 1), st.2)
        else (st.1, (st.2.1 ++ [e], st.2.2 + 1))) ((s, ns), (l, nl)) =
      ((s ++ cells.filter (fun e => decide (e.2.2.get < W)),
        ns + (cells.filter (fun e => decide (e.2.2.get < W))).length),
       (l ++ cells.filter (fun e => !decide (e.2.2.get < W)),
        nl + (cells.filter (fun e => !decide (e.2.2.get < W))).length)) := by
  induction cells with
  | nil => intro s ns l nl; simp
  | cons e cells ih =>
    intro s ns l nl
    rw [List.foldl_cons]
    by_cases h : e.2.2.get < W
    · rw [if_pos h, ih]; simp [h, List.filter_cons]; omega
    · rw [if_neg h, ih]; simp [h, List.filter_cons]; omega

/-- INTERNAL: `Program.splitCells` keeps exactly the cells of bound `< W`, in order,
counts them, and puts the rest in the large list. -/
theorem bv_splitCells (W : SNat) (cells : List Program.Entry) :
    (Program.splitCells W cells).val.1.1 = cells.filter (fun e => decide (e.2.2.get < W.get)) ∧
    (Program.splitCells W cells).val.1.2 = (Program.splitCells W cells).val.1.1.length ∧
    (Program.splitCells W cells).val.2.1 =
      cells.filter (fun e => !decide (e.2.2.get < W.get)) := by
  have h : (Program.splitCells W cells).val =
      cells.foldl (fun (st : (List Program.Entry × ℕ) × (List Program.Entry × ℕ)) e =>
        if e.2.2.get < W.get then ((st.1.1 ++ [e], st.1.2 + 1), st.2)
        else (st.1, (st.2.1 ++ [e], st.2.2 + 1))) (([], 0), ([], 0)) := by
    unfold Program.splitCells
    rw [val_foldl']
    congr 1
    funext st e
    by_cases h : e.2.2.get < W.get <;> simp [h]
  rw [h, bv_split_fold]
  simp

/-- INTERNAL: the insertion loop of `insertDesc` once `x` has been placed. -/
theorem bv_insert_done (x : Program.Entry) (l : List Program.Entry) :
    ∀ o : List Program.Entry,
    l.foldl (fun (st : List Program.Entry × Bool) y =>
        if st.2 then (st.1 ++ [y], true)
        else if y.2.2.get < x.2.2.get then (st.1 ++ [x] ++ [y], true)
        else (st.1 ++ [y], false)) (o, true) = (o ++ l, true) := by
  induction l with
  | nil => intro o; simp
  | cons y l ih =>
    intro o
    simp only [List.foldl_cons, if_true]
    rw [ih]
    simp

/-- INTERNAL: the insertion loop of `insertDesc` before `x` has been placed. -/
theorem bv_insert_open (x : Program.Entry) (l : List Program.Entry) :
    ∀ o : List Program.Entry,
    let r := l.foldl (fun (st : List Program.Entry × Bool) y =>
        if st.2 then (st.1 ++ [y], true)
        else if y.2.2.get < x.2.2.get then (st.1 ++ [x] ++ [y], true)
        else (st.1 ++ [y], false)) (o, false)
    (if r.2 then r.1 else r.1 ++ [x]) =
      o ++ l.orderedInsert (fun a b : Program.Entry => b.2.2.get < a.2.2.get) x := by
  induction l with
  | nil => intro o; simp
  | cons y l ih =>
    intro o
    by_cases h : y.2.2.get < x.2.2.get
    · simp only [List.foldl_cons, Bool.false_eq_true, if_false, if_pos h]
      rw [bv_insert_done]
      simp [List.orderedInsert_cons, h]
    · simp only [List.foldl_cons, Bool.false_eq_true, if_false, if_neg h]
      rw [ih]
      simp [List.orderedInsert_cons, h]

/-- INTERNAL: `Program.insertDesc` is `List.orderedInsert` for decreasing bound. -/
theorem bv_insertDesc (l : List Program.Entry) (x : Program.Entry) :
    (Program.insertDesc l x).val =
      l.orderedInsert (fun a b : Program.Entry => b.2.2.get < a.2.2.get) x := by
  have h := bv_insert_open x l []
  simp only [List.nil_append] at h
  rw [← h]
  unfold Program.insertDesc
  simp only [Charged.val_bind, val_foldl', apply_ite Charged.val, Charged.val_pure,
    Interface.val_push, Interface.SNat.val_lt, decide_eq_true_eq]

/-- INTERNAL: forgetting the sealing commutes with insertion by decreasing bound. -/
theorem bv_map_orderedInsert (x : Program.Entry) (l : List Program.Entry) :
    (l.orderedInsert (fun a b : Program.Entry => b.2.2.get < a.2.2.get) x).map bvE =
      (l.map bvE).orderedInsert (fun a b : Pseudocode.Entry => b.2.2 < a.2.2) (bvE x) := by
  induction l with
  | nil => simp
  | cons y l ih =>
    by_cases h : y.2.2.get < x.2.2.get
    · simp [List.orderedInsert_cons, h, bvE]
    · simp [List.orderedInsert_cons, h, bvE] at ih ⊢
      exact ih

/-- INTERNAL: `Program.sortDesc` is the pseudocode's insertion sort, after forgetting
the sealing. -/
theorem bv_sortDesc (l : List Program.Entry) :
    (Program.sortDesc l).val.map bvE =
      (l.map bvE).foldl
        (fun acc x => acc.orderedInsert (fun a b : Pseudocode.Entry => b.2.2 < a.2.2) x) [] := by
  unfold Program.sortDesc
  rw [List.foldl_map]
  exact bv_foldl_rel (fun b c => b.map bvE = c) (fun acc x => Program.insertDesc acc x)
    (fun acc x => acc.orderedInsert (fun a b : Pseudocode.Entry => b.2.2 < a.2.2) (bvE x)) l
    (fun b c a _ h => by
      show (Program.insertDesc b a).val.map bvE = _
      rw [bv_insertDesc, bv_map_orderedInsert, ← h]) [] [] rfl

/-- INTERNAL: an indexed invariant of a fold over `List.range V`. -/
theorem bv_range_foldl_inv {β : Type} (P : ℕ → β → Prop) (g : β → ℕ → β)
    (V : ℕ) (b : β) (h0 : P 0 b) (hs : ∀ k b, k < V → P k b → P (k + 1) (g b k)) :
    P V ((List.range V).foldl g b) := by
  have : ∀ k ≤ V, P k ((List.range k).foldl g b) := by
    intro k
    induction k with
    | zero => intro _; simpa using h0
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact hs k _ (by omega) (ih (by omega))
  exact this V le_rfl

/-- INTERNAL: an indexed invariant of a charged `repeatFor`. -/
theorem bv_repeatFor_inv {β : Type} (P : ℕ → β → Prop) (f : ℕ → β → Program.Prog β)
    (V : ℕ) (b : β) (h0 : P 0 b) (hs : ∀ k b, k < V → P k b → P (k + 1) (f k b).val) :
    P V (Charged.repeatFor f V b).val := by
  rw [val_repeatFor']
  exact bv_range_foldl_inv P _ V b h0 hs

/-- INTERNAL: an in-range `getD` is indexing. -/
theorem bv_getD_eq {α : Type} (l : List α) (d : α) (n : ℕ) (hn : n < l.length) :
    l.getD n d = l[n] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]

/-- INTERNAL: reading a list entry after `List.set`. -/
theorem bv_getD_set {α : Type} (l : List α) (k v : ℕ) (a d : α) (hk : k < l.length) :
    (l.set k a).getD v d = if v = k then a else l.getD v d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : k = v
  · subst h; simp [hk]
  · simp [h, Ne.symm h]

/-- INTERNAL: the component relabelling of a Kruskal step, as a pure fold. -/
theorem bv_relabel (V cu cv : ℕ) (comp : List ℕ) (hl : comp.length = V) :
    let r := (List.range V).foldl (fun b w => if b.getD w 0 = cv then b.set w cu else b) comp
    r.length = V ∧ ∀ v < V, r.getD v 0 = if comp.getD v 0 = cv then cu else comp.getD v 0 := by
  intro r
  have := bv_range_foldl_inv (fun k (b : List ℕ) => b.length = V ∧ ∀ v < V, b.getD v 0 =
      if v < k then (if comp.getD v 0 = cv then cu else comp.getD v 0) else comp.getD v 0)
    (fun b w => if b.getD w 0 = cv then b.set w cu else b) V comp ⟨hl, fun v _ => by simp⟩
    (by
      intro k b hk ⟨hbl, hb⟩
      have hbk : b.getD k 0 = comp.getD k 0 := by rw [hb k hk]; simp
      by_cases hc : comp.getD k 0 = cv
      · simp only [hbk, hc, if_true]
        refine ⟨by simp [hbl], fun v hv => ?_⟩
        rw [bv_getD_set _ _ _ _ _ (by omega)]
        by_cases hvk : v = k
        · subst hvk; simp only [lt_add_one, if_true, hc, lt_irrefl, if_false]
        · rw [if_neg hvk, hb v hv]
          by_cases hlt : v < k
          · simp [hlt, show v < k + 1 by omega]
          · simp [hlt, show ¬ v < k + 1 by omega]
      · simp only [hbk, hc, if_false]
        refine ⟨hbl, fun v hv => ?_⟩
        rw [hb v hv]
        by_cases hvk : v = k
        · subst hvk; simp only [lt_add_one, if_true, hc, lt_irrefl, if_false]
        · by_cases hlt : v < k
          · simp [hlt, show v < k + 1 by omega]
          · simp [hlt, show ¬ v < k + 1 by omega])
  refine ⟨this.1, fun v hv => ?_⟩
  rw [this.2 v hv, if_pos hv]

/-- INTERNAL: the Kruskal state of the program represents the pseudocode forest. -/
def KRel (m n : ℕ) (st : (List Program.Entry × ℕ) × (List Program.Entry × ℕ) × List ℕ)
    (F : Pseudocode.Forest) : Prop :=
  st.1.1.map bvE = F.tree ∧ st.1.2 = st.1.1.length ∧ st.2.1.1.map bvE = F.free ∧
    st.2.1.2 = st.2.1.1.length ∧ st.2.2.length = m + n ∧
    (∀ v < m + n, st.2.2.getD v 0 = F.comp v) ∧ (∀ v < m + n, F.comp v < m + n) ∧
    (∀ e ∈ st.1.1, e.1 < m ∧ e.2.1 < n)

/-- INTERNAL: one Kruskal step of the program follows `Pseudocode.kruskalStep`. -/
theorem bv_kruskal_step (m n : ℕ) (st : (List Program.Entry × ℕ) × (List Program.Entry × ℕ) × List ℕ)
    (F : Pseudocode.Forest) (e : Program.Entry) (he : e.1 < m ∧ e.2.1 < n) (h : KRel m n st F) :
    KRel m n ((fun (st : (List Program.Entry × ℕ) × (List Program.Entry × ℕ) × List ℕ)
        (e : Program.Entry) => do
      let cu ← get st.2.2 e.1
      let cv ← get st.2.2 (m + e.2.1)
      let same ← idxEq cu cv
      if same then do
        let f ← push st.2.1.1 e
        pure (st.1, (f, st.2.1.2 + 1), st.2.2)
      else do
        let t ← push st.1.1 e
        let comp' ← Charged.repeatFor (fun w comp => do
          let cw ← get comp w
          let hit ← idxEq cw cv
          if hit then set comp w cu else pure comp) (m + n) st.2.2
        pure ((t, st.1.2 + 1), st.2.1, comp') : _ → _ → Program.Prog _) st e).val
      (Pseudocode.kruskalStep m F (bvE e)) := by
  simp only [Charged.val_bind, val_repeatFor', apply_ite Charged.val, Charged.val_pure,
    Interface.val_push, Interface.val_get, Interface.val_idxEq, Interface.val_set, decide_eq_true_eq, Nat.default_eq_zero]
  obtain ⟨⟨t, nt⟩, ⟨f, nf⟩, comp⟩ := st
  unfold KRel at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  have hu : e.1 < m + n := by omega
  have hv : m + e.2.1 < m + n := by omega
  rw [h6 _ hu, h6 _ hv]
  unfold Pseudocode.kruskalStep
  simp only [bvE]
  by_cases hs : F.comp e.1 = F.comp (m + e.2.1)
  · simp only [hs, if_true]
    exact ⟨h1, h2, by simp [h3, bvE], by simp [h4], h5, h6, h7, h8⟩
  · simp only [hs, if_false]
    obtain ⟨hr1, hr2⟩ := bv_relabel (m + n) (F.comp e.1) (F.comp (m + e.2.1)) comp h5
    refine ⟨by simp [h1, bvE], by simp [h2], h3, h4, hr1, fun v hv' => ?_, fun v hv' => ?_,
      fun x hx => ?_⟩
    · rw [hr2 v hv', h6 v hv']
      by_cases hc : F.comp v = F.comp (m + e.2.1) <;> simp [hc, bvE]
    · by_cases hc : F.comp v = F.comp (m + e.2.1)
      · simp only [bvE, hc, if_true]; exact h7 _ hu
      · simp only [bvE, hc, if_false]; exact h7 _ hv'
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · exact h8 x hx
      · subst hx; exact he

/-- INTERNAL: `Program.kruskal` computes the pseudocode forest of its input, after
forgetting the sealing; component labels are kept as a list over the vertices. -/
theorem bv_kruskal (m n : ℕ) (large : List Program.Entry)
    (hl : ∀ e ∈ large, e.1 < m ∧ e.2.1 < n) :
    KRel m n (Program.kruskal m n large).val
      ((large.map bvE).foldl (Pseudocode.kruskalStep m) ⟨[], [], id⟩) := by
  have hc0 : (Charged.repeatFor (fun v (acc : List ℕ) => push acc v) (m + n) []).val =
      List.range (m + n) :=
    bv_repeatFor_inv (fun k b => b = List.range k) _ (m + n) [] rfl
      (fun k b _ hb => by subst hb; simp [List.range_succ])
  unfold Program.kruskal
  rw [Charged.val_bind, hc0, List.foldl_map]
  refine bv_foldl_rel (KRel m n) _ (fun F e => Pseudocode.kruskalStep m F (bvE e)) large
    (fun b c a ha h => bv_kruskal_step m n b c a (hl a ha) h) _ _ ?_
  unfold KRel
  refine ⟨rfl, rfl, rfl, rfl, by simp, fun v hv => ?_, fun v hv => hv, by simp⟩
  simp [List.getElem?_range hv]

/-- INTERNAL: `Program.rootsOf` lists the least vertex of every component. -/
theorem bv_rootsOf (V : ℕ) (comp : List ℕ) (c : ℕ → ℕ)
    (hc : ∀ v < V, comp.getD v 0 = c v) (hb : ∀ v < V, c v < V) :
    (Program.rootsOf V comp).val =
      (List.range V).filter (fun v => decide (∀ u < v, c u ≠ c v)) := by
  unfold Program.rootsOf
  simp only [Charged.val_bind, Charged.val_pure, Interface.val_replicate]
  refine (bv_repeatFor_inv (fun k (st : List Bool × List ℕ) => st.1.length = V ∧
      (∀ x < V, st.1.getD x false = decide (∃ u < k, c u = x)) ∧
      st.2 = (List.range k).filter (fun v => decide (∀ u < v, c u ≠ c v))) _ V _
      ⟨by simp, fun x hx => by simp [hx], by simp⟩ ?_).2.2
  rintro k ⟨seen, rs⟩ hk ⟨h1, h2, h3⟩
  simp only at h1 h2 h3
  have hck : comp.getD k default = c k := hc k hk
  simp only [Charged.val_bind, Interface.val_get, hck]
  simp only [Charged.val_pure, apply_ite Charged.val, Interface.val_get,
    Interface.val_set, Interface.val_push, Charged.val_bind, Bool.default_bool,
    h2 _ (hb k hk)]
  by_cases hex : ∃ u < k, c u = c k
  · simp only [hex, decide_true, if_true]
    refine ⟨h1, fun x hx => ?_, ?_⟩
    · rw [h2 x hx]
      congr 1
      apply propext
      constructor
      · rintro ⟨u, hu, hux⟩; exact ⟨u, by omega, hux⟩
      · rintro ⟨u, hu, hux⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | hu
        · exact ⟨u, hu, hux⟩
        · subst hu; obtain ⟨u', hu', hu'x⟩ := hex; exact ⟨u', hu', hu'x.trans hux⟩
    · rw [h3, List.range_succ, List.filter_append]
      obtain ⟨u', hu', hu'x⟩ := hex
      simp only [List.filter_cons, List.filter_nil]
      rw [if_neg]
      · simp
      · simp only [decide_eq_true_eq, not_forall]
        exact ⟨u', hu', fun h => h hu'x⟩
  · simp only [hex, decide_false, Bool.false_eq_true, if_false]
    refine ⟨by simp [h1], fun x hx => ?_, ?_⟩
    · rw [bv_getD_set _ _ _ _ _ (by rw [h1]; exact hb k hk)]
      by_cases hxk : x = c k
      · subst hxk; simp only [if_true]; symm; simp only [decide_eq_true_eq]
        exact ⟨k, by omega, rfl⟩
      · rw [if_neg hxk, h2 x hx]
        congr 1
        apply propext
        constructor
        · rintro ⟨u, hu, hux⟩; exact ⟨u, by omega, hux⟩
        · rintro ⟨u, hu, hux⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | hu
          · exact ⟨u, hu, hux⟩
          · subst hu; exact absurd hux.symm hxk
    · rw [h3, List.range_succ, List.filter_append]
      simp only [List.filter_cons, List.filter_nil]
      rw [if_pos]
      simp only [decide_eq_true_eq]
      intro u hu hcu
      exact hex ⟨u, hu, hcu⟩

/-- INTERNAL: the program's BFS marks and queue represent the visited set `S` and the
queue `Q` over vertices `< V`. -/
def ORel3 (V : ℕ) (tri : List Bool × List ℕ × ℕ) (S : Finset ℕ) (Q : List ℕ) : Prop :=
  tri.1.length = V ∧ (∀ w < V, tri.1.getD w false = decide (w ∈ S)) ∧ tri.2.1.length = V ∧
    tri.2.2 = Q.length ∧ (∀ k < Q.length, tri.2.1.getD k 0 = Q.getD k 0) ∧ Q.Nodup ∧
    Q.toFinset = S ∧ (∀ x ∈ Q, x < V)

/-- INTERNAL: marking an unvisited vertex and enqueueing it. -/
theorem bv_mark (V : ℕ) (vis : List Bool) (q : List ℕ) (ql : ℕ) (S : Finset ℕ) (Q : List ℕ)
    (w : ℕ) (h : ORel3 V (vis, q, ql) S Q) (hw : w < V) (hwS : w ∉ S) :
    ORel3 V (vis.set w true, q.set ql w, ql + 1) (insert w S) (Q ++ [w]) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only at h1 h2 h3 h4 h5
  have hwQ : w ∉ Q := fun hq => hwS (h7 ▸ List.mem_toFinset.2 hq)
  have hlt : Q.length < V := by
    have hsub : insert w S ⊆ Finset.range V := by
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · simpa using hw
      · rw [← h7, List.mem_toFinset] at hx; simpa using h8 x hx
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hwS, ← h7, List.toFinset_card_of_nodup h6,
      Finset.card_range] at this
    omega
  refine ⟨by simp [h1], fun x hx => ?_, by simp [h3], by simp [h4], fun k hk => ?_, ?_, ?_, ?_⟩
  · simp only
    rw [bv_getD_set _ _ _ _ _ (by omega)]
    by_cases hxw : x = w
    · subst hxw; simp
    · rw [if_neg hxw, h2 x hx]; simp [hxw]
  · simp only
    rw [bv_getD_set _ _ _ _ _ (by omega)]
    simp only [List.length_append, List.length_singleton] at hk
    by_cases hkq : k = ql
    · subst hkq
      rw [if_pos rfl, h4]
      simp [List.getD_eq_getElem?_getD]
    · rw [if_neg hkq, h5 k (by omega)]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
  · rw [List.nodup_append]
    refine ⟨h6, List.nodup_singleton w, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    rintro rfl
    exact hwQ ha
  · ext x; simp [← h7, or_comm]
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h8 x hx
    · exact hw

/-- INTERNAL: the program's BFS state represents the pseudocode's. -/
def ORel (V : ℕ) (st : Program.Orient) (ps : Finset ℕ × List ℕ × List (ℕ × ℕ)) : Prop :=
  st.2 = ps.2.2 ∧ ORel3 V st.1 ps.1 ps.2.1

/-- INTERNAL: `Program.visit` follows `Pseudocode.visit`. -/
theorem bv_visit (V w t : ℕ) (st : Program.Orient) (ps : Finset ℕ × List ℕ × List (ℕ × ℕ))
    (h : ORel V st ps) (hw : w < V) :
    ORel V (Program.visit w t st).val (Pseudocode.visit w t ps) := by
  obtain ⟨⟨vis, q, ql⟩, out⟩ := st
  obtain ⟨S, Q, out'⟩ := ps
  obtain ⟨ho, h3⟩ := h
  simp only at ho h3
  subst ho
  have hseen : vis.getD w false = decide (w ∈ S) := h3.2.1 w hw
  unfold Program.visit Pseudocode.visit
  simp only [Charged.val_bind, Interface.val_get, Bool.default_bool, hseen]
  by_cases hwS : w ∈ S
  · simp only [hwS, decide_true, if_true, Charged.val_pure]
    exact ⟨rfl, h3⟩
  · simp only [hwS, decide_false, Bool.false_eq_true, if_false, Charged.val_pure,
      Charged.val_bind, Interface.val_set]
    exact ⟨rfl, bv_mark V vis q ql S Q w h3 hw hwS⟩

/-- INTERNAL: the body of `Pseudocode.elimOrder`, for an arbitrary forest and roots. -/
noncomputable def bvElim (m n : ℕ) (T : List Pseudocode.Entry) (rts : List ℕ) :
    List (ℕ × ℕ) :=
  ((List.range (m + n)).foldl (fun st k =>
    match st.2.1[k]? with
    | none => st
    | some u => (List.range T.length).foldl (fun st' t =>
        let e := T.getD t (0, 0, 0)
        if e.1 = u then Pseudocode.visit (m + e.2.1) t st'
        else if m + e.2.1 = u then Pseudocode.visit e.1 t st' else st') st)
    (rts.toFinset, rts, [])).2.2

/-- INTERNAL: `Pseudocode.elimOrder` is `bvElim` of the forest and the roots. -/
theorem bv_elimOrder_eq (I : Instance) (ε δ : ℚ) :
    Pseudocode.elimOrder I ε δ =
      bvElim I.m I.n (Pseudocode.forest I ε δ).tree (Pseudocode.roots I ε δ) := rfl

/-- INTERNAL: a fold that appends each element to a duplicate-free list. -/
theorem bv_foldl_rel_nodup {β : Type} (R : β → List ℕ → Prop) (f : β → ℕ → Program.Prog β)
    (l : List ℕ) (step : ∀ b Q a, a ∈ l → a ∉ Q → R b Q → R (f b a).val (Q ++ [a])) :
    ∀ b Q, (Q ++ l).Nodup → R b Q → R (Charged.foldl f l b).val (Q ++ l) := by
  induction l with
  | nil => intro b Q _ h; simpa using h
  | cons a l ih =>
    intro b Q hnd h
    rw [Charged.val_foldl_cons]
    have haQ : a ∉ Q := by
      intro haQ
      rw [List.nodup_append] at hnd
      exact hnd.2.2 a haQ a (by simp) rfl
    have := ih (fun b Q a ha => step b Q a (List.mem_cons_of_mem _ ha)) (f b a).val (Q ++ [a])
      (by simpa using hnd) (step b Q a (by simp) haQ h)
    simpa using this

/-- INTERNAL: reading an entry through `bvE`. -/
theorem bv_getD_map (tree : List Program.Entry) (t : ℕ) (ht : t < tree.length) :
    (tree.map bvE).getD t (0, 0, 0) = bvE (tree.getD t default) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem ht]
  rfl

/-- INTERNAL: `Program.orient` computes the pseudocode's leaf-elimination order. -/
theorem bv_orient (m n : ℕ) (tree : List Program.Entry) (rts : List ℕ)
    (ht : ∀ e ∈ tree, e.1 < m ∧ e.2.1 < n) (hr : rts.Nodup) (hrb : ∀ x ∈ rts, x < m + n) :
    (Program.orient m n tree tree.length rts).val = bvElim m n (tree.map bvE) rts := by
  unfold Program.orient bvElim
  simp only [Charged.val_bind, Charged.val_pure, Interface.val_replicate]
  have hinit := bv_foldl_rel_nodup (fun tri Q => ORel3 (m + n) tri Q.toFinset Q)
    (fun (st : List Bool × List ℕ × ℕ) v => do
      let vis ← Model.Operations.set st.1 v true
      let q ← Model.Operations.set st.2.1 st.2.2 v
      pure (vis, q, st.2.2 + 1)) rts
    (fun b Q a ha haQ h => by
      obtain ⟨vis, q, ql⟩ := b
      simp only [Charged.val_bind, Charged.val_pure, Interface.val_set]
      have := bv_mark (m + n) vis q ql Q.toFinset Q a h (hrb a ha)
        (by simpa using haQ)
      have he : (Q ++ [a]).toFinset = insert a Q.toFinset := by ext x; simp [or_comm]
      rw [he]; exact this)
    (List.replicate (m + n) false, List.replicate (m + n) 0, 0) [] (by simpa using hr)
    ⟨by simp, fun w hw => by simp [hw], by simp, rfl, fun k hk => by simp at hk,
      List.nodup_nil, rfl, by simp⟩
  simp only [List.nil_append] at hinit
  unfold Charged.repeatFor
  refine (bv_foldl_rel (ORel (m + n)) _ _ (List.range (m + n)) ?_ _ _ ⟨rfl, hinit⟩).1
  rintro b ⟨S, Q, out⟩ k _ hb
  obtain ⟨⟨vis, q, ql⟩, pout⟩ := b
  have hb' := hb
  obtain ⟨ho, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hb'
  simp only at ho h1 h2 h3 h4 h5 h6 h7 h8
  subst ho h4
  simp only [Charged.val_bind, Interface.val_idxLt]
  by_cases hk : k < Q.length
  · simp only [hk, decide_true, if_true, Charged.val_bind, Interface.val_get,
      List.getElem?_eq_getElem hk]
    have hu : q.getD k default = Q[k] := by
      rw [Nat.default_eq_zero, h5 k hk, bv_getD_eq _ _ _ hk]
    rw [hu, List.length_map]
    refine bv_foldl_rel (ORel (m + n)) _ _ _ ?_ _ _ hb
    intro b' c' t ht' hb'
    have htl : t < tree.length := by simpa using ht'
    simp only [Charged.val_bind, Interface.val_get, Interface.val_idxEq]
    rw [bv_getD_map tree t htl]
    have he : (tree.getD t default).1 < m ∧ (tree.getD t default).2.1 < n :=
      ht _ (by rw [bv_getD_eq _ _ _ htl]; exact List.getElem_mem htl)
    by_cases hr1 : (tree.getD t default).1 = Q[k]
    · simp only [bvE, hr1, decide_true, if_true]
      exact bv_visit _ _ _ _ _ hb' (by omega)
    · by_cases hr2 : m + (tree.getD t default).2.1 = Q[k]
      · simp only [bvE, hr1, hr2, decide_true, decide_false, if_true, if_false,
          Bool.false_eq_true, Charged.val_bind, Interface.val_idxEq]
        exact bv_visit _ _ _ _ _ hb' (by omega)
      · simp only [bvE, hr1, hr2, decide_false, if_false, Bool.false_eq_true,
          Charged.val_bind, Interface.val_idxEq, Charged.val_pure]
        exact hb'
  · simp only [hk, decide_false, if_false, Bool.false_eq_true, Charged.val_pure,
      List.getElem?_eq_none (by omega : Q.length ≤ k)]
    exact hb

/-- INTERNAL: the `M_f` product loop of `Program.buildCtx`. -/
theorem bv_Mf (one : SNat) (h1 : one.get = 1) (free : List Program.Entry) :
    ∀ acc : SNat, (Charged.foldl (fun acc (e : Program.Entry) => do
      let b1 ← SNat.add e.2.2 one
      SNat.mul acc b1) free acc).val.get =
        acc.get * ((free.map bvE).map (fun e => e.2.2 + 1)).prod := by
  induction free with
  | nil => intro acc; simp
  | cons e free ih =>
    intro acc
    rw [Charged.val_foldl_cons, ih]
    simp only [Charged.val_bind, Interface.SNat.get_mul, Interface.SNat.get_add, h1,
      List.map_cons, List.prod_cons, bvE]
    ring

/-- INTERNAL: retained cells are in range. -/
theorem bv_retained_bounds (I : Instance) (e : Pseudocode.Entry)
    (he : e ∈ Pseudocode.retained I) : e.1 < I.m ∧ e.2.1 < I.n := by
  unfold Pseudocode.retained at he
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and] at he
  obtain ⟨i, j, hj⟩ := he
  split_ifs at hj with h
  · cases hj; exact ⟨i.isLt, j.isLt⟩

/-- INTERNAL: insertion sort by folding keeps the elements. -/
theorem bv_mem_foldl_orderedInsert (x : Pseudocode.Entry) (l : List Pseudocode.Entry) :
    ∀ acc : List Pseudocode.Entry,
    x ∈ l.foldl (fun acc y => acc.orderedInsert (fun a b : Pseudocode.Entry => b.2.2 < a.2.2) y)
      acc ↔ x ∈ l ∨ x ∈ acc := by
  induction l with
  | nil => intro acc; simp
  | cons y l ih =>
    intro acc
    rw [List.foldl_cons, ih, List.mem_orderedInsert]
    simp only [List.mem_cons]
    tauto

/-- INTERNAL: `Program.buildCtx`, run on a tightened instance and parameters that match the
pseudocode's, builds the pseudocode's context field by field.  Stage by stage:
`bv_splitCells`, `bv_sortDesc`, `bv_kruskal`, `bv_rootsOf`, `bv_orient`, `bv_Mf`.
TEXLINE: sections/scales.tex:84-99 -/
theorem buildCtx_view_of (I : Instance) (ε δ : ℚ) (T : Program.Tight) (Pm : Program.Params)
    (hT : (T.rows.map SNat.get, T.cols.map SNat.get,
      T.cells.map (fun (e : Program.Entry) => (e.1, e.2.1, e.2.2.get))) =
      ((List.range I.m).map (Pseudocode.tRow I), (List.range I.n).map (Pseudocode.tCol I),
        Pseudocode.retained I))
    (hPm : (Pm.d.get, Pm.K.get, Pm.A.get, Pm.B.get, Pm.W.get, Pm.H.get) =
      (Pseudocode.dParam I, Pseudocode.KParam I ε δ, Pseudocode.AParam I ε δ,
        Pseudocode.BParam I ε δ, Pseudocode.WParam I ε δ, Pseudocode.HParam I ε δ)) :
    let C := (Program.buildCtx I.m I.n T Pm).val
    (C.m, C.n, C.rows.map SNat.get, C.cols.map SNat.get,
      C.small.map (fun (e : Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall,
      C.free.map (fun (e : Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree,
      C.tree.map (fun (e : Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots,
      C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) =
    (I.m, I.n, (List.range I.m).map (Pseudocode.tRow I), (List.range I.n).map (Pseudocode.tCol I),
      Pseudocode.smallCells I ε δ, Pseudocode.nSmall I ε δ, (Pseudocode.forest I ε δ).free,
      Pseudocode.nFree I ε δ, (Pseudocode.forest I ε δ).tree,
      (Pseudocode.forest I ε δ).tree.length, Pseudocode.elimOrder I ε δ, Pseudocode.roots I ε δ,
      Pseudocode.Mf I ε δ, Pseudocode.dParam I, Pseudocode.BParam I ε δ, Pseudocode.HParam I ε δ,
      (Pseudocode.AParam I ε δ : ℚ), (Pseudocode.HParam I ε δ : ℚ),
      (Pseudocode.BParam I ε δ : ℚ)) := by
  intro C
  simp only [Prod.mk.injEq] at hT hPm
  obtain ⟨hrows, hcols, hcells⟩ := hT
  obtain ⟨hd, -, hA, hB, hW, hH⟩ := hPm
  change T.cells.map bvE = Pseudocode.retained I at hcells
  -- the stages, named
  set sp := (Program.splitCells Pm.W T.cells).val with hsp
  set so := (Program.sortDesc sp.2.1).val with hso
  set kr := (Program.kruskal I.m I.n so).val with hkr
  set rt := (Program.rootsOf (I.m + I.n) kr.2.2).val with hrt
  have hfields : C.small = sp.1.1 ∧ C.nSmall = sp.1.2 ∧ C.free = kr.2.1.1 ∧
      C.nFree = kr.2.1.2 ∧ C.tree = kr.1.1 ∧ C.nTree = kr.1.2 ∧ C.roots = rt ∧
      C.order = (Program.orient I.m I.n kr.1.1 kr.1.2 rt).val ∧
      C.Mf = (Charged.foldl (fun acc (e : Program.Entry) => do
        let b1 ← SNat.add e.2.2 (SNat.lit 1).val
        SNat.mul acc b1) kr.2.1.1 (SNat.lit 1).val).val ∧
      C.rows = T.rows ∧ C.cols = T.cols ∧ C.m = I.m ∧ C.n = I.n ∧ C.d = Pm.d ∧ C.B = Pm.B ∧
      C.H = Pm.H ∧ C.Aq = (SNat.toRat Pm.A).val ∧ C.Hq = (SNat.toRat Pm.H).val ∧
      C.Bq = (SNat.toRat Pm.B).val :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl⟩
  obtain ⟨fs, fns, ff, fnf, ft, fnt, frt, fod, fMf, frows, fcols, fm, fn, fd, fB, fH, fAq, fHq,
    fBq⟩ := hfields
  -- split
  obtain ⟨hs1, hs2, hs3⟩ := bv_splitCells Pm.W T.cells
  have hsmall : sp.1.1.map bvE = Pseudocode.smallCells I ε δ := by
    rw [hs1, Pseudocode.smallCells, ← hcells, List.filter_map]
    congr 1
    apply List.filter_congr
    intro e _
    by_cases h : e.2.2.get < Pseudocode.WParam I ε δ <;> simp [bvE, hW, h]
  have hlarge : sp.2.1.map bvE = Pseudocode.largeCells I ε δ := by
    rw [hs3, Pseudocode.largeCells, ← hcells, List.filter_map]
    congr 1
    apply List.filter_congr
    intro e _
    by_cases h : e.2.2.get < Pseudocode.WParam I ε δ
    · simp [bvE, hW, h, Nat.not_le.2 h]
    · simp [bvE, hW, h, Nat.not_lt.1 h]
  -- sort
  have hsorted : so.map bvE = Pseudocode.sortedLarge I ε δ := by
    rw [hso, bv_sortDesc, hlarge]; rfl
  have hsob : ∀ e ∈ so, e.1 < I.m ∧ e.2.1 < I.n := by
    intro e he
    have : bvE e ∈ Pseudocode.retained I := by
      have h1 : bvE e ∈ Pseudocode.sortedLarge I ε δ := by
        rw [← hsorted]; exact List.mem_map_of_mem he
      unfold Pseudocode.sortedLarge at h1
      rw [bv_mem_foldl_orderedInsert] at h1
      rcases h1 with h1 | h1
      · unfold Pseudocode.largeCells at h1; exact (List.mem_filter.1 h1).1
      · simp at h1
    exact bv_retained_bounds I _ this
  -- Kruskal
  have hK := bv_kruskal I.m I.n so hsob
  have hforest : Pseudocode.forest I ε δ =
      (so.map bvE).foldl (Pseudocode.kruskalStep I.m) ⟨[], [], id⟩ := by
    rw [hsorted]; rfl
  rw [← hforest] at hK
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := hK
  -- roots
  have hroots : rt = Pseudocode.roots I ε δ := by
    rw [hrt, bv_rootsOf (I.m + I.n) kr.2.2 (Pseudocode.forest I ε δ).comp k6 k7]
    rfl
  -- orientation
  have horder : (Program.orient I.m I.n kr.1.1 kr.1.2 rt).val = Pseudocode.elimOrder I ε δ := by
    rw [k2, bv_orient I.m I.n kr.1.1 rt k8 (by rw [hroots]; exact List.nodup_range.filter _)
      (by rw [hroots]; intro x hx; exact List.mem_range.1 (List.mem_filter.1 hx).1),
      bv_elimOrder_eq, k1, hroots]
  -- M_f
  have hMf : C.Mf.get = Pseudocode.Mf I ε δ := by
    rw [fMf, bv_Mf _ (by simp) kr.2.1.1, Pseudocode.Mf, k3]
    simp
  simp only [Prod.mk.injEq]
  refine ⟨fm, fn, by rw [frows, hrows], by rw [fcols, hcols], by rw [fs]; exact hsmall,
    by rw [fns, hs2, Pseudocode.nSmall, ← hsmall, List.length_map], by rw [ff]; exact k3,
    by rw [fnf, k4, Pseudocode.nFree, ← k3, List.length_map], by rw [ft]; exact k1,
    by rw [fnt, k2, ← k1, List.length_map], by rw [fod, horder], by rw [frt, hroots], hMf,
    by rw [fd, hd], by rw [fB, hB], by rw [fH, hH], by rw [fAq]; simp [hA],
    by rw [fHq]; simp [hH], by rw [fBq]; simp [hB]⟩

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `buildCtx_view_of` and every stage lemma, no `sorry`
-/
