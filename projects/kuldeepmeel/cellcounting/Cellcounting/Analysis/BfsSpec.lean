import Cellcounting.Analysis.FeasibleCost
import Cellcounting.Analysis.FlowNet
import Cellcounting.Analysis.NetworkVal

/-!
# What the program's breadth-first search returns

`Program.bfs V res` (`sections/scales.tex:18-19`, "each augmenting path is found by
breadth-first search") returns a parent array `par`.  `bfs_spec` gives it a level
function `lev` (the BFS depth) with the properties of `ParSpec`:

* the source is its own parent, at level `0`;
* every other reached vertex has a reached parent one level lower, along an arc of
  positive residual capacity;
* reached vertices have level `< V`;
* from a reached vertex, every positive residual arc leads to a reached vertex at most one
  level deeper.

The last property makes the parent path of every reached vertex a shortest residual path
(`lev` is at most the length of any residual path), and it makes the reached set a cut with
no residual arc leaving it.

The proof is a loop invariant (`BfsInv`) over the queue: queue entries are distinct,
reached, of nondecreasing level, spanning at most two consecutive levels beyond the
processed prefix, and every processed vertex has had all its residual arcs explored.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Program
open Cellcounting.Model.Operations

/-- INTERNAL: reading a list after overwriting one entry. -/
theorem bs_getD_set {α : Type} (l : List α) (i j : ℕ) (x d : α) :
    (l.set i x).getD j d = if i = j ∧ i < l.length then x else l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = j
  · subst h; by_cases hl : i < l.length <;> simp [hl]
  · simp [h]

/-- INTERNAL: the specification of a BFS parent array with levels `lev`.
TEXLINE: sections/scales.tex:13-19 -/
structure ParSpec (V : ℕ) (res : ℕ → ℕ → ℕ) (par : List (Option ℕ)) (lev : ℕ → ℕ) : Prop where
  len : par.length = V
  root : par.getD 0 none = some 0
  lev0 : lev 0 = 0
  parent : ∀ v u, 0 < v → v < V → par.getD v none = some u →
    u < V ∧ par.getD u none ≠ none ∧ lev v = lev u + 1 ∧ 0 < res u v
  levlt : ∀ v < V, par.getD v none ≠ none → lev v < V
  closed : ∀ v < V, par.getD v none ≠ none → ∀ w < V, 0 < res v w →
    par.getD w none ≠ none ∧ lev w ≤ lev v + 1

/-- INTERNAL: the invariant of the outer (queue) loop of `Program.bfs` after `k` rounds. -/
structure BfsInv (V : ℕ) (res : ℕ → ℕ → ℕ) (k : ℕ) (lev : ℕ → ℕ)
    (par : List (Option ℕ)) (ord : List ℕ) (cnt : ℕ) : Prop where
  plen : par.length = V
  olen : ord.length = V
  cpos : 1 ≤ cnt
  cle : cnt ≤ V
  root : par.getD 0 none = some 0
  ord0 : ord.getD 0 0 = 0
  lev0 : lev 0 = 0
  ordOK : ∀ i < cnt, ord.getD i 0 < V ∧ par.getD (ord.getD i 0) none ≠ none ∧
    lev (ord.getD i 0) ≤ i
  inj : ∀ i j, i < cnt → j < cnt → ord.getD i 0 = ord.getD j 0 → i = j
  disc : ∀ v < V, par.getD v none ≠ none → ∃ i < cnt, ord.getD i 0 = v
  parent : ∀ v u, 0 < v → v < V → par.getD v none = some u →
    u < V ∧ par.getD u none ≠ none ∧ lev v = lev u + 1 ∧ 0 < res u v
  mono : ∀ i j, i ≤ j → j < cnt → lev (ord.getD i 0) ≤ lev (ord.getD j 0)
  span : k < cnt → lev (ord.getD (cnt - 1) 0) ≤ lev (ord.getD k 0) + 1
  closed : ∀ j, j < k → j < cnt → ∀ w < V, 0 < res (ord.getD j 0) w →
    par.getD w none ≠ none ∧ lev w ≤ lev (ord.getD j 0) + 1

/-- INTERNAL: fewer than `V` vertices are queued while an unreached one remains. -/
theorem bfsInv_cnt_lt {V : ℕ} {res : ℕ → ℕ → ℕ} {k : ℕ} {lev : ℕ → ℕ}
    {par : List (Option ℕ)} {ord : List ℕ} {cnt : ℕ} (h : BfsInv V res k lev par ord cnt) (v : ℕ) (hv : v < V)
    (hnone : par.getD v none = none) : cnt < V := by
  have hcard := Finset.card_le_card_of_injOn (s := Finset.range cnt)
    (t := (Finset.range V).erase v) (fun i => ord.getD i 0)
    (fun i hi => by
      have hi' := Finset.mem_range.1 hi
      obtain ⟨h1, h2, -⟩ := h.ordOK i hi'
      refine Finset.mem_erase.2 ⟨fun e => h2 (by simp only at e; rw [e]; exact hnone), Finset.mem_range.2 h1⟩)
    (fun i hi j hj e => h.inj i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) e)
  rw [Finset.card_range, Finset.card_erase_of_mem (Finset.mem_range.2 hv), Finset.card_range]
    at hcard
  omega

/-- INTERNAL: the invariant of the inner (neighbour) loop while processing queue entry `k`,
the vertex `u`, after examining the neighbours `w < v`. -/
def BfsInner (V : ℕ) (res : ℕ → ℕ → ℕ) (k u v : ℕ) (st : List (Option ℕ) × List ℕ × ℕ) :
    Prop :=
  ∃ lev, BfsInv V res k lev st.1 st.2.1 st.2.2 ∧ k < st.2.2 ∧ st.2.1.getD k 0 = u ∧
    ∀ w < v, 0 < res u w → st.1.getD w none ≠ none ∧ lev w ≤ lev u + 1

/-- INTERNAL: examining one neighbour keeps the inner invariant. -/
theorem bfs_inner_step (V : ℕ) (res : List (List SNat)) (k u v : ℕ)
    (st : List (Option ℕ) × List ℕ × ℕ) (hv : v < V) (h : BfsInner V (capOf res) k u v st) :
    BfsInner V (capOf res) k u (v + 1)
      (fcBfsInner (res.getD u default) u (SNat.lit 0).val v st).val := by
  obtain ⟨par, ord, cnt⟩ := st
  obtain ⟨lev, hI, hk, hu, hpart⟩ := h
  dsimp only at hI hk hu hpart
  have hcap : ((res.getD u default).getD v default).get = capOf res u v := rfl
  unfold fcBfsInner
  simp only [Charged.val_bind, Cellcounting.Interface.val_get, Cellcounting.Interface.SNat.val_lt,
    Cellcounting.Interface.SNat.get_lit, hcap]
  by_cases hpos : 0 < capOf res u v
  · simp only [hpos, decide_true, if_true, Charged.val_bind, Cellcounting.Interface.val_get]
    cases hp : par.getD v default with
    | some x =>
      -- already reached: it is queued, so its level is within the span
      simp only [Charged.val_pure]
      refine ⟨lev, hI, hk, hu, fun w hw hw' => ?_⟩
      rcases Nat.lt_or_ge w v with hlt | hge
      · exact hpart w hlt hw'
      · obtain rfl : w = v := by omega
        have hd : par.getD w none ≠ none := by
          change par.getD w default ≠ none; rw [hp]; simp
        refine ⟨hd, ?_⟩
        obtain ⟨i, hi, hiw⟩ := hI.disc w hv hd
        have h1 := hI.mono i (cnt - 1) (by omega) (by omega)
        have h2 := hI.span hk
        try simp only at h1 h2
        rw [hiw] at h1; rw [hu] at h2
        omega
    | none =>
      -- newly reached: it is queued at the end, one level below `u`
      simp only [Charged.val_bind, Cellcounting.Interface.val_set, Charged.val_pure]
      have hnone : par.getD v none = none := hp
      have hlt : cnt < V := bfsInv_cnt_lt hI v hv hnone
      have hplen : par.length = V := hI.plen
      have holen : ord.length = V := hI.olen
      obtain ⟨huV, hud, hulev⟩ := hI.ordOK k hk
      try simp only at huV hud hulev
      rw [hu] at huV hud hulev
      have hvu : v ≠ u := fun e => hud (e ▸ hnone)
      -- every queued vertex differs from `v`
      have hordv : ∀ i < cnt, ord.getD i 0 ≠ v := fun i hi e =>
        (hI.ordOK i hi).2.1 (by rw [e]; exact hnone)
      have hdv : ∀ w, par.getD w none ≠ none → w ≠ v := fun w hw e => hw (e ▸ hnone)
      let lev' := Function.update lev v (lev u + 1)
      have hlev' : ∀ w, w ≠ v → lev' w = lev w := fun w hw => Function.update_of_ne hw _ _
      have hlevv : lev' v = lev u + 1 := Function.update_self _ _ _
      have hpar : ∀ w, (par.set v (some u)).getD w none =
          if w = v then some u else par.getD w none := by
        intro w; rw [bs_getD_set]; by_cases hw : w = v
        · subst hw; simp [hplen, hv]
        · simp [Ne.symm hw, hw]
      have hord : ∀ i, (ord.set cnt v).getD i 0 = if i = cnt then v else ord.getD i 0 := by
        intro i; rw [bs_getD_set]; by_cases hi : i = cnt
        · subst hi; simp [holen, hlt]
        · simp [Ne.symm hi, hi]
      have hmono_par : ∀ w, par.getD w none ≠ none → (par.set v (some u)).getD w none ≠ none := by
        intro w hw; rw [hpar]; split_ifs <;> simp_all
      have h0v : v ≠ 0 := fun e => by rw [e, hI.root] at hnone; cases hnone
      have hkc : k ≠ cnt := by omega
      refine ⟨lev', ⟨by simp [hplen], by simp [holen], by simp, by simp; omega, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp; omega, ?_, ?_⟩
      · try simp only
        rw [hpar, if_neg (Ne.symm h0v)]; exact hI.root
      · try simp only
        rw [hord, if_neg (by have := hI.cpos; omega)]; exact hI.ord0
      · rw [hlev' 0 (Ne.symm h0v)]; exact hI.lev0
      · intro i hi
        try simp only at hi ⊢
        rw [hord]
        by_cases hic : i = cnt
        · rw [if_pos hic, hpar, if_pos rfl, hlevv]
          exact ⟨hv, by simp, by omega⟩
        · rw [if_neg hic]
          obtain ⟨g1, g2, g3⟩ := hI.ordOK i (by omega)
          try simp only at g1 g2 g3
          exact ⟨g1, hmono_par _ g2, by rw [hlev' _ (hordv i (by omega))]; exact g3⟩
      · intro i j hi hj e
        try simp only at hi hj e
        rw [hord, hord] at e
        by_cases hic : i = cnt <;> by_cases hjc : j = cnt
        · omega
        · rw [if_pos hic, if_neg hjc] at e; exact absurd e.symm (hordv j (by omega))
        · rw [if_neg hic, if_pos hjc] at e; exact absurd e (hordv i (by omega))
        · rw [if_neg hic, if_neg hjc] at e; exact hI.inj i j (by omega) (by omega) e
      · intro w hw hd
        try simp only at hd ⊢
        rw [hpar] at hd
        by_cases hwv : w = v
        · exact ⟨cnt, by omega, by rw [hord, if_pos rfl, hwv]⟩
        · rw [if_neg hwv] at hd
          obtain ⟨i, hi, hiw⟩ := hI.disc w hw hd
          exact ⟨i, by (try simp only at hi ⊢); omega, by rw [hord, if_neg (by (try simp only at hi); omega)]; exact hiw⟩
      · intro w x hw0 hw hx
        try simp only at hx ⊢
        rw [hpar] at hx
        by_cases hwv : w = v
        · rw [if_pos hwv] at hx
          cases hx
          refine ⟨huV, hmono_par _ hud, ?_, ?_⟩
          · rw [hwv, hlevv, hlev' u (Ne.symm hvu)]
          · rw [hwv]; exact hpos
        · rw [if_neg hwv] at hx
          obtain ⟨g1, g2, g3, g4⟩ := hI.parent w x hw0 hw hx
          refine ⟨g1, hmono_par _ g2, ?_, g4⟩
          rw [hlev' w hwv, hlev' x (hdv x g2)]; exact g3
      · intro i j hij hj
        try simp only at hj ⊢
        rw [hord, hord]
        by_cases hjc : j = cnt
        · rw [if_pos hjc, hlevv]
          by_cases hic : i = cnt
          · rw [if_pos hic, hlevv]
          · rw [if_neg hic, hlev' _ (hordv i (by omega))]
            have h1 := hI.mono i (cnt - 1) (by omega) (by omega)
            have h2 := hI.span hk
            try simp only at h1 h2
            rw [hu] at h2
            omega
        · rw [if_neg hjc, if_neg (by omega), hlev' _ (hordv i (by omega)),
            hlev' _ (hordv j (by omega))]
          exact hI.mono i j hij (by omega)
      · intro _
        simp only
        rw [hord, hord, if_pos (by omega), if_neg hkc, hu, hlevv, hlev' u (Ne.symm hvu)]
      · intro j hj hjc w hw hpw
        try simp only at hjc hpw ⊢
        rw [hord, if_neg (by omega)] at hpw ⊢
        obtain ⟨g1, g2⟩ := hI.closed j hj (by omega) w hw hpw
        refine ⟨hmono_par _ g1, ?_⟩
        rw [hlev' w (hdv w g1), hlev' _ (hordv j (by omega))]
        exact g2
      · try simp only
        rw [hord, if_neg hkc]; exact hu
      · intro w hw hpw
        rcases Nat.lt_or_ge w v with hwlt | hwge
        · obtain ⟨g1, g2⟩ := hpart w hwlt hpw
          refine ⟨hmono_par _ g1, ?_⟩
          rw [hlev' w (hdv w g1), hlev' u (Ne.symm hvu)]
          exact g2
        · obtain rfl : w = v := by omega
          refine ⟨by rw [hpar, if_pos rfl]; simp, ?_⟩
          rw [hlevv, hlev' u (Ne.symm hvu)]
  · -- no residual arc to `v`: nothing changes
    simp only [hpos, decide_false, Bool.false_eq_true, if_false, Charged.val_pure]
    refine ⟨lev, hI, hk, hu, fun w hw hw' => ?_⟩
    rcases Nat.lt_or_ge w v with hlt | hge
    · exact hpart w hlt hw'
    · obtain rfl : w = v := by omega
      exact absurd hw' hpos

/-- INTERNAL: once queue entry `k` (if any) has had all its arcs explored, the invariant
holds after `k + 1` rounds. -/
theorem bfsInv_succ {V : ℕ} {res : ℕ → ℕ → ℕ} {k : ℕ} {lev : ℕ → ℕ} {par : List (Option ℕ)}
    {ord : List ℕ} {cnt : ℕ} (h : BfsInv V res k lev par ord cnt)
    (hk : k < cnt → ∀ w < V, 0 < res (ord.getD k 0) w →
      par.getD w none ≠ none ∧ lev w ≤ lev (ord.getD k 0) + 1) :
    BfsInv V res (k + 1) lev par ord cnt := by
  refine ⟨h.plen, h.olen, h.cpos, h.cle, h.root, h.ord0, h.lev0, h.ordOK, h.inj, h.disc,
    h.parent, h.mono, fun hk1 => ?_, fun j hj hjc => ?_⟩
  · have h1 := h.span (by omega)
    have h2 := h.mono k (k + 1) (by omega) hk1
    omega
  · rcases Nat.lt_or_ge j k with hjk | hjk
    · exact h.closed j hjk hjc
    · obtain rfl : j = k := by omega
      exact hk hjc

/-- INTERNAL: one round of the queue loop keeps the invariant. -/
theorem bfs_outer_step (V : ℕ) (res : List (List SNat)) (k : ℕ)
    (st : List (Option ℕ) × List ℕ × ℕ)
    (h : ∃ lev, BfsInv V (capOf res) k lev st.1 st.2.1 st.2.2) :
    ∃ lev, BfsInv V (capOf res) (k + 1) lev (fcBfsOuter V res (SNat.lit 0).val k st).val.1
      (fcBfsOuter V res (SNat.lit 0).val k st).val.2.1 (fcBfsOuter V res (SNat.lit 0).val k st).val.2.2 := by
  obtain ⟨lev, hI⟩ := h
  unfold fcBfsOuter
  simp only [Charged.val_bind, Cellcounting.Interface.val_idxLt, Cellcounting.Interface.val_get]
  by_cases hk : k < st.2.2
  · simp only [hk, decide_true, if_true, Charged.val_bind, Cellcounting.Interface.val_get]
    have hloop := nv_loop_inv (fcBfsInner (res.getD (st.2.1.getD k default) default)
        (st.2.1.getD k default) (SNat.lit 0).val)
      (fun v st' => BfsInner V (capOf res) k (st.2.1.getD k default) v st') V st
      ⟨lev, hI, hk, rfl, fun w hw => absurd hw (Nat.not_lt_zero w)⟩
      (fun v st' hv hP => bfs_inner_step V res k _ v st' hv hP)
    obtain ⟨lev', hI', hk', hu', hcl⟩ := hloop
    refine ⟨lev', bfsInv_succ hI' fun _ w hw hpos => ?_⟩
    rw [hu'] at hpos ⊢
    exact hcl w hw hpos
  · simp only [hk, decide_false, Bool.false_eq_true, if_false, Charged.val_pure]
    exact ⟨lev, bfsInv_succ hI fun hk' => absurd hk' hk⟩

/-- **The program's BFS.**  Its parent array, with a suitable level function, satisfies
`ParSpec`.
INTERNAL: specification of `Program.bfs`.
TEXLINE: sections/scales.tex:18-19 -/
theorem bfs_spec (V : ℕ) (res : List (List SNat)) (hV : 1 ≤ V) :
    ∃ lev, ParSpec V (capOf res) (Program.bfs V res).val lev := by
  rw [fc_bfs_eq]
  simp only [Charged.val_bind, Cellcounting.Interface.val_replicate,
    Cellcounting.Interface.val_set, Charged.val_pure]
  set par0 := (List.replicate V (none : Option ℕ)).set 0 (some 0) with hpar0
  have hpar0v : ∀ w, par0.getD w none = if w = 0 then some 0 else none := by
    intro w
    rw [hpar0, bs_getD_set]
    by_cases hw : w = 0
    · subst hw; simp only [List.length_replicate, true_and, if_true]
      rw [if_pos (by omega)]
    · simp only [Ne.symm hw, false_and, if_false, hw, List.getD_eq_getElem?_getD,
        List.getElem?_replicate]
      split_ifs <;> rfl
  have hord0 : ∀ i, (List.replicate V 0).getD i 0 = 0 := by
    intro i; simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split_ifs <;> rfl
  have hinit : BfsInv V (capOf res) 0 (fun _ => 0) par0 (List.replicate V 0) 1 := by
    refine ⟨by simp [hpar0], by simp, le_rfl, hV, by rw [hpar0v]; rfl, hord0 0, rfl,
      fun i hi => ?_, fun i j hi hj _ => by omega, fun v hv hd => ?_,
      fun v u hv0 hv hp => ?_, fun _ _ _ _ => le_rfl, fun _ => by omega,
      fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    · rw [hord0, hpar0v]; exact ⟨by omega, by simp, Nat.zero_le _⟩
    · refine ⟨0, by omega, ?_⟩
      rw [hord0]
      by_contra hne
      rw [hpar0v, if_neg (Ne.symm hne)] at hd
      exact hd rfl
    · rw [hpar0v, if_neg (by omega)] at hp; cases hp
  have hloop := nv_loop_inv (fcBfsOuter V res (SNat.lit 0).val)
    (fun k st => ∃ lev, BfsInv V (capOf res) k lev st.1 st.2.1 st.2.2) V
    (par0, List.replicate V 0, 1) ⟨_, hinit⟩
    (fun k st _ hP => bfs_outer_step V res k st hP)
  obtain ⟨lev, hI⟩ := hloop
  refine ⟨lev, hI.plen, hI.root, hI.lev0, hI.parent, fun v hv hd => ?_, fun v hv hd => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := hI.disc v hv hd
    have := (hI.ordOK i hi).2.2
    have := hI.cle
    omega
  · obtain ⟨i, hi, rfl⟩ := hI.disc v hv hd
    exact hI.closed i (by have := hI.cle; omega) hi

end Cellcounting.Analysis
