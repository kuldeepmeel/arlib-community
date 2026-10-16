import Cellcounting.Analysis.AsgBoxCard

/-!
# The pseudocode's elimination order is valid

`scales.tex:88-99, 128-134`: breadth-first search from the roots over the
Kruskal forest discovers every nonroot vertex exactly once, through a tree edge
whose other endpoint was discovered earlier, and uses every tree edge exactly
once.  Read newest first, the discovered list is an elimination order in which
every vertex comes after all its children (`ElimValid` of `ForestSolve.lean`),
and no root is eliminated.

The first part is a generic breadth-first search over an edge list `T` with rows
`e.1 < m` and columns `m + e.2.1`; `elimOrder` is this search for the Kruskal
forest (`elimOrder_eq_eo`).  Every tree edge is used because the number of
discoveries, `V - #roots`, equals the number of tree edges (`KInv.count`).

* `eo_valid`: the generic conclusion;
* `pseudo_elimOrder_valid`: the conclusion for the pseudocode.
-/

namespace Cellcounting.Analysis

open Pseudocode Finset

/-- INTERNAL: the breadth-first state: visited set, queue, discovered pairs. -/
abbrev BState := Finset ℕ × List ℕ × List (ℕ × ℕ)

section bfs

variable (m V : ℕ) (T : List Entry) (rs : List ℕ)

/-- INTERNAL: the inner step of `elimOrder`: from `u`, look at tree edge `t`. -/
noncomputable def eoInner (u : ℕ) (st : BState) (t : ℕ) : BState :=
  let e := T.getD t (0, 0, 0)
  if e.1 = u then visit (m + e.2.1) t st else if m + e.2.1 = u then visit e.1 t st else st

/-- INTERNAL: the outer step of `elimOrder`: process the `k`-th queued vertex. -/
noncomputable def eoOuter (st : BState) (k : ℕ) : BState :=
  match st.2.1[k]? with
  | none => st
  | some u => (List.range T.length).foldl (eoInner m T u) st

/-- INTERNAL: the row endpoint of edge `t`. -/
def eoR (t : ℕ) : ℕ := (T.getD t (0, 0, 0)).1

/-- INTERNAL: the column endpoint of edge `t`. -/
def eoC (t : ℕ) : ℕ := m + (T.getD t (0, 0, 0)).2.1

/-- INTERNAL: the breadth-first invariants. -/
structure EOInv (st : BState) : Prop where
  vis : ∀ w, w ∈ st.1 ↔ w ∈ st.2.1
  queue : st.2.1 = rs ++ (st.2.2.map Prod.fst).reverse
  nodup : st.2.1.Nodup
  lt : ∀ w ∈ st.2.1, w < V
  ent : ∀ x ∈ st.2.2, x.2 < T.length ∧ (x.1 = eoR T x.2 ∨ x.1 = eoC m T x.2) ∧
    eoR T x.2 ∈ st.2.1 ∧ eoC m T x.2 ∈ st.2.1
  nodup_snd : (st.2.2.map Prod.snd).Nodup
  older : ∀ l1 x l2, st.2.2 = l1 ++ x :: l2 →
    oth (eoR T) (eoC m T) x ∈ rs ∨ oth (eoR T) (eoC m T) x ∈ l2.map Prod.fst

variable {m V T rs}

theorem eoInv_visit (st : BState) (h : EOInv m V T rs st) (w t u : ℕ) (ht : t < T.length)
    (hw : (w = eoR T t ∧ u = eoC m T t) ∨ (w = eoC m T t ∧ u = eoR T t))
    (hne : eoR T t ≠ eoC m T t) (hu : u ∈ st.2.1) (hwV : w < V) :
    EOInv m V T rs (visit w t st) ∧ (∃ s, (visit w t st).2.1 = st.2.1 ++ s) ∧
      w ∈ (visit w t st).2.1 := by
  obtain ⟨vis, Q, D⟩ := st
  unfold visit
  simp only at h hu ⊢
  split_ifs with hwv
  · exact ⟨h, ⟨[], by simp⟩, (h.vis w).1 hwv⟩
  have hwQ : w ∉ Q := fun hh => hwv ((h.vis w).2 hh)
  have hq : Q = rs ++ (D.map Prod.fst).reverse := h.queue
  have hoth : oth (eoR T) (eoC m T) (w, t) = u := by
    unfold oth
    rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp
    · simp [Ne.symm hne]
  refine ⟨⟨fun w' => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨[w], rfl⟩, by simp⟩
  · simp only [Finset.mem_insert, List.mem_append, List.mem_singleton, h.vis]; tauto
  · simp [hq]
  · exact List.nodup_append.2 ⟨h.nodup, List.nodup_singleton w, by
      intro a ha b hb; simp at hb; subst hb; rintro rfl; exact hwQ ha⟩
  · intro w' hw'
    simp only [List.mem_append, List.mem_singleton] at hw'
    rcases hw' with hw' | rfl
    · exact h.lt w' hw'
    · exact hwV
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · refine ⟨ht, ?_, ?_, ?_⟩
      · rcases hw with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
      · rcases hw with ⟨rfl, -⟩ | ⟨rfl, rfl⟩ <;> simp [hu]
      · rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, -⟩ <;> simp [hu]
    · obtain ⟨a, b, c, d⟩ := h.ent x hx
      exact ⟨a, b, List.mem_append_left _ c, List.mem_append_left _ d⟩
  · simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, h.nodup_snd⟩
    obtain ⟨x, hx, hxt⟩ := List.mem_map.1 hmem
    obtain ⟨-, -, hr, hc⟩ := h.ent x hx
    rw [hxt] at hr hc
    rcases hw with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hwQ hr
    · exact hwQ hc
  · intro l1 x l2 hl
    cases l1 with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      rw [hoth]
      have := hu
      rw [hq] at this
      simp only [List.mem_append, List.mem_reverse] at this
      exact this
    | cons y l1 =>
      simp only [List.cons_append, List.cons.injEq] at hl
      exact h.older l1 x l2 hl.2

/-- INTERNAL: `u`'s tree edges have both endpoints in the queue. -/
def EOProc (m : ℕ) (T : List Entry) (Q : List ℕ) (u : ℕ) : Prop :=
  ∀ t < T.length, (eoR T t = u ∨ eoC m T t = u) → eoR T t ∈ Q ∧ eoC m T t ∈ Q

theorem eoProc_mono {Q : List ℕ} {u : ℕ} (h : EOProc m T Q u) (s : List ℕ) :
    EOProc m T (Q ++ s) u := fun t ht hu =>
  ⟨List.mem_append_left _ (h t ht hu).1, List.mem_append_left _ (h t ht hu).2⟩

variable (hT : ∀ e ∈ T, e.1 < m ∧ m + e.2.1 < V)
include hT

omit hT in
theorem eo_getD_mem {t : ℕ} (ht : t < T.length) : T.getD t (0, 0, 0) ∈ T := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]; exact List.getElem_mem ht

theorem eoR_ne_eoC {t : ℕ} (ht : t < T.length) : eoR T t ≠ eoC m T t := by
  have := (hT _ (eo_getD_mem ht)).1
  unfold eoR eoC; omega

theorem eoInv_inner (st : BState) (h : EOInv m V T rs st) (u : ℕ) (hu : u ∈ st.2.1) (t : ℕ)
    (ht : t < T.length) :
    EOInv m V T rs (eoInner m T u st t) ∧ (∃ s, (eoInner m T u st t).2.1 = st.2.1 ++ s) ∧
      ((eoR T t = u ∨ eoC m T t = u) →
        eoR T t ∈ (eoInner m T u st t).2.1 ∧ eoC m T t ∈ (eoInner m T u st t).2.1) := by
  have he := hT _ (eo_getD_mem ht)
  have hne := eoR_ne_eoC hT ht
  unfold eoInner
  simp only
  split_ifs with h1 h2
  · obtain ⟨hI, ⟨s, hs⟩, hw⟩ := eoInv_visit st h (m + (T.getD t (0, 0, 0)).2.1) t u ht
      (Or.inr ⟨rfl, h1.symm⟩) hne hu he.2
    refine ⟨hI, ⟨s, hs⟩, fun _ => ⟨?_, hw⟩⟩
    rw [hs]; exact List.mem_append_left _ (by unfold eoR; rw [h1]; exact hu)
  · obtain ⟨hI, ⟨s, hs⟩, hw⟩ := eoInv_visit st h (T.getD t (0, 0, 0)).1 t u ht
      (Or.inl ⟨rfl, h2.symm⟩) hne hu (by omega)
    refine ⟨hI, ⟨s, hs⟩, fun _ => ⟨hw, ?_⟩⟩
    rw [hs]; exact List.mem_append_left _ (by unfold eoC; rw [h2]; exact hu)
  · refine ⟨h, ⟨[], by simp⟩, fun hh => ?_⟩
    unfold eoR eoC at hh; tauto

theorem eoInv_innerFold (u : ℕ) : ∀ j ≤ T.length, ∀ st : BState, EOInv m V T rs st →
    u ∈ st.2.1 →
    EOInv m V T rs ((List.range j).foldl (eoInner m T u) st) ∧
      (∃ s, ((List.range j).foldl (eoInner m T u) st).2.1 = st.2.1 ++ s) ∧
      ∀ t < j, (eoR T t = u ∨ eoC m T t = u) →
        eoR T t ∈ ((List.range j).foldl (eoInner m T u) st).2.1 ∧
        eoC m T t ∈ ((List.range j).foldl (eoInner m T u) st).2.1 := by
  intro j
  induction j with
  | zero => intro _ st h _; exact ⟨h, ⟨[], by simp⟩, fun t ht => absurd ht (Nat.not_lt_zero _)⟩
  | succ j ih =>
    intro hj st h hu
    obtain ⟨hI, ⟨s, hs⟩, hP⟩ := ih (by omega) st h hu
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set st1 := (List.range j).foldl (eoInner m T u) st
    have hu1 : u ∈ st1.2.1 := by rw [hs]; exact List.mem_append_left _ hu
    obtain ⟨hI2, ⟨s2, hs2⟩, hP2⟩ := eoInv_inner hT st1 hI u hu1 j (by omega)
    refine ⟨hI2, ⟨s ++ s2, by rw [hs2, hs, List.append_assoc]⟩, fun t ht htu => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · obtain ⟨a, b⟩ := hP t ht htu
      rw [hs2]; exact ⟨List.mem_append_left _ a, List.mem_append_left _ b⟩
    · exact hP2 htu

theorem eoInv_outer (k : ℕ) (st : BState) (h : EOInv m V T rs st)
    (hP : ∀ i < k, ∀ u, st.2.1[i]? = some u → EOProc m T st.2.1 u) :
    EOInv m V T rs (eoOuter m T st k) ∧
      ∀ i < k + 1, ∀ u, (eoOuter m T st k).2.1[i]? = some u →
        EOProc m T (eoOuter m T st k).2.1 u := by
  unfold eoOuter
  cases hq : st.2.1[k]? with
  | none =>
    simp only
    refine ⟨h, fun i hi u hu => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact hP i hi u hu
    · rw [hq] at hu; cases hu
  | some u =>
    simp only
    have hu : u ∈ st.2.1 := List.mem_of_getElem? hq
    have hk : k < st.2.1.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hq; cases hq
    obtain ⟨hI, ⟨s, hs⟩, hP2⟩ := eoInv_innerFold hT u T.length le_rfl st h hu
    refine ⟨hI, fun i hi u' hu' => ?_⟩
    rw [hs] at hu' ⊢
    rw [List.getElem?_append_left (by omega)] at hu'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact eoProc_mono (hP i hi u' hu') s
    · rw [hq] at hu'; cases hu'
      intro t ht htu
      have := hP2 t ht htu
      rwa [hs] at this

/-- INTERNAL: after the outer loop over `range k`, every queued vertex at an index
below `k` has been processed. -/
theorem eoInv_outerFold (st0 : BState) (h0 : EOInv m V T rs st0) : ∀ k,
    EOInv m V T rs ((List.range k).foldl (eoOuter m T) st0) ∧
      ∀ i < k, ∀ u, ((List.range k).foldl (eoOuter m T) st0).2.1[i]? = some u →
        EOProc m T ((List.range k).foldl (eoOuter m T) st0).2.1 u := by
  intro k
  induction k with
  | zero => exact ⟨h0, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact eoInv_outer hT k _ ih.1 ih.2

omit hT in
theorem nodup_length_le {Q : List ℕ} (hQ : Q.Nodup) (hlt : ∀ w ∈ Q, w < V) : Q.length ≤ V := by
  rw [← List.toFinset_card_of_nodup hQ]
  calc Q.toFinset.card ≤ (Finset.range V).card :=
        Finset.card_le_card (fun w hw => Finset.mem_range.2 (hlt w (List.mem_toFinset.1 hw)))
    _ = V := Finset.card_range V

/-- **The generic breadth-first search yields a valid elimination order.** -/
theorem eo_valid (hrs : rs.Nodup) (hrsV : ∀ r ∈ rs, r < V)
    (hreach : ∀ w < V, ∃ r ∈ rs, EReach m T r w) (hcount : T.length + rs.length = V) :
    ElimValid (eoR T) (eoC m T) T.length
        ((List.range V).foldl (eoOuter m T) (rs.toFinset, rs, [])).2.2 ∧
      ∀ r ∈ rs, r ∉ ((List.range V).foldl (eoOuter m T) (rs.toFinset, rs, [])).2.2.map Prod.fst := by
  have h0 : EOInv m V T rs (rs.toFinset, rs, []) :=
    ⟨fun w => List.mem_toFinset, by simp, hrs, hrsV, by simp, by simp,
      fun l1 x l2 h => by simp at h⟩
  obtain ⟨hI, hP⟩ := eoInv_outerFold hT (rs := rs) _ h0 V
  set st := (List.range V).foldl (eoOuter m T) (rs.toFinset, rs, [])
  have hq : st.2.1 = rs ++ (st.2.2.map Prod.fst).reverse := hI.queue
  have hlen := nodup_length_le hI.nodup hI.lt
  -- closure: every queued vertex is processed
  have hcl : ∀ u ∈ st.2.1, EOProc m T st.2.1 u := by
    intro u hu
    obtain ⟨i, hi, hiu⟩ := List.getElem_of_mem hu
    exact hP i (by omega) u (by rw [List.getElem?_eq_getElem hi, hiu])
  -- every vertex is queued
  have hall : ∀ w < V, w ∈ st.2.1 := by
    intro w hw
    obtain ⟨r, hr, hrw⟩ := hreach w hw
    have hr' : r ∈ st.2.1 := by rw [hq]; exact List.mem_append_left _ hr
    clear hw
    induction hrw with
    | refl => exact hr'
    | tail _ hbc ih =>
      obtain ⟨e, he, hbc⟩ := hbc
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he
      have hget : T.getD t (0, 0, 0) = T[t] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]; rfl
      have hP' := hcl _ ih t ht
      unfold eoR eoC at hP'
      rw [hget] at hP'
      rcases hbc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h2]; exact (hP' (Or.inl h1)).2
      · rw [← h1]; exact (hP' (Or.inr h2)).1
  -- counting
  have hQlen : st.2.1.length = V := by
    refine le_antisymm hlen ?_
    rw [← List.toFinset_card_of_nodup hI.nodup]
    calc V = (Finset.range V).card := (Finset.card_range V).symm
      _ ≤ st.2.1.toFinset.card := Finset.card_le_card (fun w hw =>
          List.mem_toFinset.2 (hall w (Finset.mem_range.1 hw)))
  have hDlen : st.2.2.length = T.length := by
    have := congrArg List.length hq
    simp only [List.length_append, List.length_reverse, List.length_map] at this
    omega
  have hnd := hI.nodup
  rw [hq, List.nodup_append] at hnd
  obtain ⟨-, hnd2, hdisj⟩ := hnd
  have hfst : (st.2.2.map Prod.fst).Nodup := List.nodup_reverse.1 hnd2
  have hcover : ∀ t < T.length, t ∈ st.2.2.map Prod.snd := by
    have hsub : (st.2.2.map Prod.snd).toFinset ⊆ Finset.range T.length := by
      intro t ht
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 ht)
      exact Finset.mem_range.2 (hI.ent x hx).1
    have hcard : (Finset.range T.length).card ≤ (st.2.2.map Prod.snd).toFinset.card := by
      rw [List.toFinset_card_of_nodup hI.nodup_snd, List.length_map, hDlen, Finset.card_range]
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    intro t ht
    have : t ∈ (st.2.2.map Prod.snd).toFinset := by rw [heq]; exact Finset.mem_range.2 ht
    exact List.mem_toFinset.1 this
  have hroot : ∀ r ∈ rs, r ∉ st.2.2.map Prod.fst := fun r hr hmem =>
    hdisj r hr r (List.mem_reverse.2 hmem) rfl
  refine ⟨⟨fun x hx => (hI.ent x hx).1, fun x hx => (hI.ent x hx).2.1,
    fun t ht => eoR_ne_eoC hT ht, hI.nodup_snd, hfst, hcover, ?_⟩, hroot⟩
  intro l1 v t l2 hl t' ht' hinc hne
  obtain ⟨x, hx, hxt⟩ := List.mem_map.1 (hcover t' ht')
  have hx' := hx
  rw [hl, List.mem_append, List.mem_cons] at hx'
  rcases hx' with hx' | rfl | hx'
  · exact List.mem_map.2 ⟨x, hx', hxt⟩
  · exact absurd hxt.symm hne
  · obtain ⟨l2a, l2b, rfl⟩ := List.append_of_mem hx'
    have hv : v ∉ (l2a ++ x :: l2b).map Prod.fst := by
      have := hfst
      rw [hl, List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at this
      exact this.2.1.1
    have hx1 : x.1 ≠ v := fun h => hv (by simp [← h])
    have hxinc := (hI.ent x hx).2.1
    have hneR := eoR_ne_eoC hT ht'
    have hoth : oth (eoR T) (eoC m T) x = v := by
      unfold oth
      subst hxt
      split_ifs with h1 <;> omega
    have hold := hI.older (l1 ++ (v, t) :: l2a) x l2b (by rw [hl]; simp)
    rw [hoth] at hold
    rcases hold with h | h
    · exact absurd (List.mem_map.2 ⟨(v, t), by rw [hl]; simp, rfl⟩) (hroot v h)
    · exact absurd (by simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]; tauto) hv

end bfs

end Cellcounting.Analysis

namespace Cellcounting.Analysis

open Pseudocode Finset

variable (I : Instance) (ε δ : ℚ)

/-- INTERNAL: `elimOrder` is the generic breadth-first search. -/
theorem elimOrder_eq_eo : elimOrder I ε δ =
    ((List.range (I.m + I.n)).foldl (eoOuter I.m (forest I ε δ).tree)
      ((roots I ε δ).toFinset, roots I ε δ, [])).2.2 := rfl

/-- INTERNAL: the Kruskal invariants of the pseudocode's forest. -/
theorem forest_kinv : KInv I.m (I.m + I.n) (sortedLarge I ε δ) (forest I ε δ) :=
  kruskal_inv I.m (I.m + I.n) (sortedLarge I ε δ) (fun e he => by
    have := mem_sortedLarge he
    omega)

/-- INTERNAL: tree and free cells lie inside the table. -/
theorem forest_mem_lt {e : Entry} (he : e ∈ (forest I ε δ).tree ∨ e ∈ (forest I ε δ).free) :
    e.1 < I.m ∧ e.2.1 < I.n :=
  mem_sortedLarge ((forest_perm I ε δ).mem_iff.1 (List.mem_append.2 he))

theorem roots_nodup : (roots I ε δ).Nodup := (List.nodup_range).filter _

theorem mem_roots_iff (r : ℕ) : r ∈ roots I ε δ ↔
    r < I.m + I.n ∧ ∀ u < r, (forest I ε δ).comp u ≠ (forest I ε δ).comp r := by
  unfold roots
  simp [List.mem_filter, List.mem_range]

/-- INTERNAL: the least vertex of the class of `w` is a root. -/
theorem exists_root (w : ℕ) (hw : w < I.m + I.n) :
    ∃ r ∈ roots I ε δ, (forest I ε δ).comp r = (forest I ε δ).comp w ∧ r ≤ w := by
  classical
  have hex : ∃ u, (forest I ε δ).comp u = (forest I ε δ).comp w := ⟨w, rfl⟩
  refine ⟨Nat.find hex, (mem_roots_iff I ε δ _).2 ⟨?_, fun u hu h => ?_⟩, Nat.find_spec hex,
    Nat.find_min' hex rfl⟩
  · exact lt_of_le_of_lt (Nat.find_min' hex rfl) hw
  · exact Nat.find_min hex hu (h.trans (Nat.find_spec hex))

theorem roots_card : (roots I ε δ).length =
    ((Finset.range (I.m + I.n)).image (forest I ε δ).comp).card := by
  classical
  rw [← List.toFinset_card_of_nodup (roots_nodup I ε δ)]
  have hinj : Set.InjOn (forest I ε δ).comp (roots I ε δ).toFinset := by
    intro r1 h1 r2 h2 h
    have h1 := (mem_roots_iff I ε δ r1).1 (List.mem_toFinset.1 h1)
    have h2 := (mem_roots_iff I ε δ r2).1 (List.mem_toFinset.1 h2)
    rcases lt_trichotomy r1 r2 with hl | hl | hl
    · exact absurd h (h2.2 r1 hl)
    · exact hl
    · exact absurd h.symm (h1.2 r2 hl)
  rw [← Finset.card_image_of_injOn hinj]
  congr 1
  ext c
  simp only [Finset.mem_image, List.mem_toFinset, Finset.mem_range]
  constructor
  · rintro ⟨r, hr, rfl⟩; exact ⟨r, ((mem_roots_iff I ε δ r).1 hr).1, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨r, hr, hc, -⟩ := exists_root I ε δ w hw
    exact ⟨r, hr, hc⟩

/-- **The elimination order is valid and eliminates no root.**
PAPER: sections/scales.tex:128-134 (leaf elimination along the forest from its
roots, `lem:forest`). -/
theorem pseudo_elimOrder_valid :
    ElimValid (fun t => (treeAt I ε δ t).1) (fun t => I.m + (treeAt I ε δ t).2.1)
        (forest I ε δ).tree.length (elimOrder I ε δ) ∧
      ∀ r ∈ roots I ε δ, r ∉ (elimOrder I ε δ).map Prod.fst := by
  have hK := forest_kinv I ε δ
  rw [elimOrder_eq_eo]
  refine eo_valid (V := I.m + I.n) (fun e he => ?_) (roots_nodup I ε δ)
    (fun r hr => ((mem_roots_iff I ε δ r).1 hr).1) (fun w hw => ?_) ?_
  · have := forest_mem_lt I ε δ (Or.inl he); omega
  · obtain ⟨r, hr, hc, -⟩ := exists_root I ε δ w hw
    exact ⟨r, hr, hK.reach r w hc⟩
  · rw [roots_card]; exact hK.count

end Cellcounting.Analysis
