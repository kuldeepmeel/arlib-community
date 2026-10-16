import Cellcounting.Analysis.BfsSpec
import Cellcounting.Analysis.ResidualCut

/-!
# One augmentation of the program is one Edmonds–Karp step

`Program.augment V res` (`sections/scales.tex:13-20`) runs BFS, and if the sink is reached
walks the parent pointers back from the sink twice: once for the bottleneck capacity and
once to push it.

* `parPath par L v`: the parent path of `v`, `L` steps long, as a vertex list from the
  source.  Under `ParSpec` it is a simple residual path, and a shortest one
  (`parPath_spec`, `parSpec_lev_le`).
* `augment_none`: if `augment` gives up, the reached vertices form a cut containing the
  source, not the sink, with no residual arc leaving it.
* `augment_some`: otherwise the new residual matrix is the old one augmented by the
  bottleneck along a shortest simple residual path (`EKStep` data).
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Program
open Cellcounting.Model.Operations

/-- INTERNAL: the parent path of `v`, followed `L` steps, listed from its far end. -/
def parPath (par : List (Option ℕ)) : ℕ → ℕ → List ℕ
  | 0, v => [v]
  | L + 1, v =>
    match par.getD v none with
    | some u => parPath par L u ++ [v]
    | none => [v]

/-- INTERNAL: a reached vertex at level `0` is the source. -/
theorem parSpec_lev_zero {V : ℕ} {res : ℕ → ℕ → ℕ} {par : List (Option ℕ)} {lev : ℕ → ℕ}
    (hP : ParSpec V res par lev) (v : ℕ) (hv : v < V) (hd : par.getD v none ≠ none)
    (h0 : lev v = 0) : v = 0 := by
  by_contra hne
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 hd
  have := (hP.parent v u (by omega) hv hu).2.2.1
  omega

/-- INTERNAL: the parent path of a reached vertex at level `L` is a simple residual path
from the source, through reached vertices of level at most `L`, with `L` arcs. -/
theorem parPath_spec {V : ℕ} {res : ℕ → ℕ → ℕ} {par : List (Option ℕ)} {lev : ℕ → ℕ}
    (hP : ParSpec V res par lev) :
    ∀ L v, v < V → par.getD v none ≠ none → lev v = L →
      (parPath par L v).head? = some 0 ∧ (parPath par L v).getLast? = some v ∧
      (∀ x ∈ parPath par L v, x < V ∧ par.getD x none ≠ none ∧ lev x ≤ L) ∧
      (parPath par L v).IsChain (fun a b => 0 < res a b) ∧ (parPath par L v).Nodup ∧
      (parPath par L v).length = L + 1 := by
  intro L
  induction L with
  | zero =>
    intro v hv hd hl
    obtain rfl := parSpec_lev_zero hP v hv hd hl
    refine ⟨rfl, rfl, fun x hx => ?_, List.isChain_singleton _, List.nodup_singleton _, rfl⟩
    rw [List.mem_singleton.1 hx]; exact ⟨hv, hd, by omega⟩
  | succ L ih =>
    intro v hv hd hl
    have hv0 : v ≠ 0 := fun e => by rw [e, hP.lev0] at hl; omega
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 hd
    obtain ⟨huV, hud, hlev, hpos⟩ := hP.parent v u (by omega) hv hu
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := ih u huV hud (by omega)
    simp only [parPath, hu]
    have hne : parPath par L u ≠ [] := by intro e; rw [e] at g1; cases g1
    have hvnot : v ∉ parPath par L u := fun hm => by have := (g3 v hm).2.2; omega
    refine ⟨?_, by simp, fun x hx => ?_, ?_, ?_, by simp [g6]⟩
    · rw [List.head?_append, g1]; rfl
    · rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨a, b, c⟩ := g3 x hx; exact ⟨a, b, by omega⟩
      · rw [List.mem_singleton.1 hx]; exact ⟨hv, hd, by omega⟩
    · refine List.isChain_append.2 ⟨g4, List.isChain_singleton _, fun x hx y hy => ?_⟩
      rw [g2] at hx; cases hx
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      rw [← hy]; exact hpos
    · exact List.nodup_append.2 ⟨g5, List.nodup_singleton _, fun a ha b hb e => by
        rw [List.mem_singleton.1 hb] at e; exact hvnot (e ▸ ha)⟩

/-- INTERNAL: a residual path from a reached vertex ends at a reached vertex, at most one
level deeper per arc. -/
theorem parSpec_walk {V : ℕ} {res : ℕ → ℕ → ℕ} {par : List (Option ℕ)} {lev : ℕ → ℕ}
    (hP : ParSpec V res par lev) :
    ∀ (q : List ℕ) (y : ℕ), y < V → par.getD y none ≠ none → (∀ x ∈ q, x < V) →
      (y :: q).IsChain (fun a b => 0 < res a b) →
      ∀ z, (y :: q).getLast? = some z → par.getD z none ≠ none ∧ lev z ≤ lev y + q.length := by
  intro q
  induction q with
  | nil =>
    intro y _ hy _ _ z hz
    simp only [List.getLast?_singleton, Option.some.injEq] at hz
    subst hz; exact ⟨hy, by simp⟩
  | cons x q ih =>
    intro y hyV hy hq hc z hz
    obtain ⟨hpos, hc'⟩ := List.isChain_cons_cons.1 hc
    have hxV := hq x List.mem_cons_self
    obtain ⟨hxd, hxl⟩ := hP.closed y hyV hy x hxV hpos
    have hz' : (x :: q).getLast? = some z := by
      rw [List.getLast?_cons_cons] at hz; exact hz
    obtain ⟨g1, g2⟩ := ih x hxV hxd (fun w hw => hq w (List.mem_cons_of_mem _ hw)) hc' z hz'
    exact ⟨g1, by simp only [List.length_cons]; omega⟩

/-- INTERNAL: every residual path from the source to `t` has more than `lev t` vertices,
so the parent path is a shortest one. -/
theorem parSpec_lev_le {V : ℕ} {res : ℕ → ℕ → ℕ} {par : List (Option ℕ)} {lev : ℕ → ℕ}
    (hP : ParSpec V res par lev) (hV : 1 ≤ V) (q : List ℕ) (t : ℕ)
    (hh : q.head? = some 0) (hl : q.getLast? = some t) (hlt : ∀ x ∈ q, x < V)
    (hc : q.IsChain (fun a b => 0 < res a b)) :
    par.getD t none ≠ none ∧ lev t + 1 ≤ q.length := by
  obtain ⟨y, q', rfl⟩ : ∃ y q', q = y :: q' := by
    cases q with
    | nil => cases hh
    | cons y q' => exact ⟨y, q', rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at hh
  subst hh
  obtain ⟨g1, g2⟩ := parSpec_walk hP q' 0 (by omega) (by rw [hP.root]; simp)
    (fun x hx => hlt x (List.mem_cons_of_mem _ hx)) hc t hl
  rw [hP.lev0] at g2
  exact ⟨g1, by simp only [List.length_cons]; omega⟩

/-- INTERNAL: the arcs of a path extended by one vertex. -/
theorem arcs_snoc : ∀ (p : List ℕ) (u v : ℕ), p.getLast? = some u →
    (p ++ [v]).zip (p ++ [v]).tail = p.zip p.tail ++ [(u, v)]
  | [], _, _, h => by cases h
  | [x], u, v, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h; rfl
  | x :: y :: t, u, v, h => by
    rw [List.getLast?_cons_cons] at h
    have ih := arcs_snoc (y :: t) u v h
    simp only [List.cons_append, List.tail_cons, List.zip_cons_cons] at ih ⊢
    rw [ih]

/-- INTERNAL: pushing along a path extended by the arc `(u, v)` is pushing on that arc and
then along the path. -/
theorem pushAlong_snoc (M : ℕ → ℕ → ℕ) (p : List ℕ) (u v a : ℕ) (hl : p.getLast? = some u)
    (hv : v ∉ p) (ha : a ≤ M u v) :
    pushAlong (fun x y => if x = v ∧ y = u then M v u + a else
      if x = u ∧ y = v then M u v - a else M x y) p a = pushAlong M (p ++ [v]) a := by
  have huv : u ≠ v := fun e => hv (e ▸ List.mem_of_getLast? hl)
  have hcnt1 : ∀ y, (p.zip p.tail).count (v, y) = 0 := fun y =>
    List.count_eq_zero.2 fun hm => hv (List.of_mem_zip hm).1
  have hcnt2 : ∀ x, (p.zip p.tail).count (x, v) = 0 := fun x =>
    List.count_eq_zero.2 fun hm => hv (List.mem_of_mem_tail (List.of_mem_zip hm).2)
  funext x y
  unfold pushAlong
  rw [arcs_snoc p u v hl, List.count_append, List.count_append]
  simp only [List.count_singleton, beq_iff_eq, Prod.mk.injEq]
  by_cases h1 : x = v ∧ y = u
  · obtain ⟨rfl, rfl⟩ := h1
    simp [hcnt1, hcnt2, huv, Ne.symm huv]
  · by_cases h2 : x = u ∧ y = v
    · obtain ⟨rfl, rfl⟩ := h2
      simp [hcnt1, hcnt2, huv, Ne.symm huv]
    · rw [if_neg h1, if_neg h2]
      have n1 : ¬ (u = y ∧ v = x) := fun h => h1 ⟨h.2.symm, h.1.symm⟩
      have n2 : ¬ (u = x ∧ v = y) := fun h => h2 ⟨h.1.symm, h.2.symm⟩
      simp only [n1, n2, if_false, add_zero]

/-- INTERNAL: a `repeatFor` whose body ignores the round index is an iterate. -/
theorem repeatFor_iterate {β : Type} (f : ℕ → β → Prog β) (hf : ∀ i s, f i s = f 0 s)
    (n : ℕ) (b : β) :
    (Charged.repeatFor f n b).val = (fun s => (f 0 s).val)^[n] b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [nv_repeatFor_succ, ih, Function.iterate_succ_apply', hf]

/-- INTERNAL: reading a matrix entry. -/
theorem get2_val {α : Type} [Inhabited α] (M : List (List α)) (u v : ℕ) :
    (Program.get2 M u v).val = (M.getD u default).getD v default := by
  simp [Program.get2]

/-- INTERNAL: one step of the bottleneck walk at the source. -/
theorem bnStep_src (res : List (List SNat)) (par : List (Option ℕ)) (o : Option SNat) :
    (fcBnStep res par 0 (0, o)).val = (0, o) := by
  simp [fcBnStep]

/-- INTERNAL: one step of the bottleneck walk away from the source. -/
theorem bnStep_par (res : List (List SNat)) (par : List (Option ℕ)) (v u : ℕ) (b : SNat)
    (hv : v ≠ 0) (hu : par.getD v none = some u) :
    (fcBnStep res par 0 (v, some b)).val =
      (u, some (if capOf res u v < b.get then (Program.get2 res u v).val else b)) := by
  have hu' : par.getD v default = some u := hu
  simp only [fcBnStep, Charged.val_bind, Cellcounting.Interface.val_idxEq, hv, decide_false,
    Bool.false_eq_true, if_false, Cellcounting.Interface.val_get, hu',
    Cellcounting.Interface.SNat.val_lt]
  have hc : (Program.get2 res u v).val.get = capOf res u v := by rw [get2_val]; rfl
  by_cases h : capOf res u v < b.get <;> simp [h, hc]

/-- INTERNAL: the bottleneck walk from a reached vertex returns the minimum of its starting
value and the residual capacities along the parent path. -/
theorem bn_walk {V : ℕ} {res : List (List SNat)} {par : List (Option ℕ)} {lev : ℕ → ℕ}
    (hP : ParSpec V (capOf res) par lev) :
    ∀ L v (b : SNat) n, v < V → par.getD v none ≠ none → lev v = L → L ≤ n →
      ((fun s => (fcBnStep res par 0 s).val)^[n] (v, some b)).1 = 0 ∧
      ∃ b', ((fun s => (fcBnStep res par 0 s).val)^[n] (v, some b)).2 = some b' ∧
        b'.get ≤ b.get ∧
        (∀ e ∈ (parPath par L v).zip (parPath par L v).tail, b'.get ≤ capOf res e.1 e.2) ∧
        (b'.get = b.get ∨
          ∃ e ∈ (parPath par L v).zip (parPath par L v).tail, capOf res e.1 e.2 = b'.get) := by
  intro L
  induction L with
  | zero =>
    intro v b n hv hd hl _
    obtain rfl := parSpec_lev_zero hP v hv hd hl
    rw [Function.iterate_fixed (bnStep_src res par (some b))]
    exact ⟨rfl, b, rfl, le_rfl, by simp [parPath], Or.inl rfl⟩
  | succ L ih =>
    intro v b n hv hd hl hn
    have hv0 : v ≠ 0 := fun e => by rw [e, hP.lev0] at hl; omega
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 hd
    obtain ⟨huV, hud, hlev, hpos⟩ := hP.parent v u (by omega) hv hu
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Function.iterate_succ_apply, bnStep_par res par v u b hv0 hu]
    set b1 := if capOf res u v < b.get then (Program.get2 res u v).val else b with hb1
    have hb1v : b1.get = min (capOf res u v) b.get := by
      rw [hb1]; split_ifs with h
      · rw [get2_val]; exact (min_eq_left h.le).symm
      · exact (min_eq_right (by omega)).symm
    obtain ⟨g0, b', g1, g2, g3, g4⟩ := ih u b1 n' huV hud (by omega) (by omega)
    have hlast : (parPath par L u).getLast? = some u :=
      (parPath_spec hP L u huV hud (by omega)).2.1
    have harcs : (parPath par (L + 1) v).zip (parPath par (L + 1) v).tail =
        (parPath par L u).zip (parPath par L u).tail ++ [(u, v)] := by
      simp only [parPath, hu]; exact arcs_snoc _ u v hlast
    refine ⟨g0, b', g1, by omega, fun e he => ?_, ?_⟩
    · rw [harcs] at he
      rcases List.mem_append.1 he with he | he
      · exact g3 e he
      · rw [List.mem_singleton.1 he]; simp only; omega
    · rw [harcs]
      rcases g4 with h | ⟨e, he, hee⟩
      · rw [h, hb1v]
        by_cases hm : capOf res u v ≤ b.get
        · exact Or.inr ⟨(u, v), by simp, (min_eq_left hm).symm⟩
        · exact Or.inl (min_eq_right (by omega))
      · exact Or.inr ⟨e, List.mem_append_left _ he, hee⟩

/-- INTERNAL: one step of the push walk at the source. -/
theorem pushStep_src (par : List (Option ℕ)) (bn : SNat) (M : List (List SNat)) :
    (fcPushStep par bn 0 (0, M)).val = (0, M) := by
  simp [fcPushStep]

/-- INTERNAL: one step of the push walk away from the source moves `bn` units across the
arc from the parent. -/
theorem pushStep_par {V : ℕ} (par : List (Option ℕ)) (bn : SNat) (M : List (List SNat))
    (v u : ℕ) (hM : SqShape V M) (hvV : v < V) (huV : u < V) (huv : u ≠ v) (hv : v ≠ 0)
    (hu : par.getD v none = some u) :
    (fcPushStep par bn 0 (v, M)).val.1 = u ∧ SqShape V (fcPushStep par bn 0 (v, M)).val.2 ∧
      capOf (fcPushStep par bn 0 (v, M)).val.2 = fun x y =>
        if x = v ∧ y = u then capOf M v u + bn.get else
          if x = u ∧ y = v then capOf M u v - bn.get else capOf M x y := by
  have hu' : par.getD v default = some u := hu
  simp only [fcPushStep, Charged.val_bind, Cellcounting.Interface.val_idxEq, hv, decide_false,
    Bool.false_eq_true, if_false, Cellcounting.Interface.val_get, hu', Charged.val_pure]
  set fwd := (Program.get2 M u v).val
  have hfwd : fwd.get = capOf M u v := by simp only [fwd]; rw [get2_val]; rfl
  obtain ⟨hs1, hc1⟩ := set2_sq V M u v (SNat.sub fwd bn).val hM huV hvV
  set M1 := (Program.set2 M u v (SNat.sub fwd bn).val).val
  set bwd := (Program.get2 M1 v u).val
  have hbwd : bwd.get = capOf M v u := by
    simp only [bwd]; rw [get2_val]
    show capOf M1 v u = capOf M v u
    rw [hc1]; simp [Ne.symm huv]
  obtain ⟨hs2, hc2⟩ := set2_sq V M1 v u (SNat.add bwd bn).val hs1 hvV huV
  refine ⟨by first | rfl | trivial, hs2, ?_⟩
  rw [hc2, hc1]
  funext x y
  simp only [Cellcounting.Interface.SNat.get_add, Cellcounting.Interface.SNat.get_sub, hfwd, hbwd]

/-- INTERNAL: the push walk from a reached vertex augments along its parent path. -/
theorem push_walk {V : ℕ} {res : List (List SNat)} {par : List (Option ℕ)} {lev : ℕ → ℕ}
    (hP : ParSpec V (capOf res) par lev) (bn : SNat) :
    ∀ L v (M : List (List SNat)) n, SqShape V M → v < V → par.getD v none ≠ none →
      lev v = L → L ≤ n →
      (∀ e ∈ (parPath par L v).zip (parPath par L v).tail, bn.get ≤ capOf M e.1 e.2) →
      ((fun s => (fcPushStep par bn 0 s).val)^[n] (v, M)).1 = 0 ∧
      SqShape V ((fun s => (fcPushStep par bn 0 s).val)^[n] (v, M)).2 ∧
      capOf ((fun s => (fcPushStep par bn 0 s).val)^[n] (v, M)).2 =
        pushAlong (capOf M) (parPath par L v) bn.get := by
  intro L
  induction L with
  | zero =>
    intro v M n hM hv hd hl _ _
    obtain rfl := parSpec_lev_zero hP v hv hd hl
    rw [Function.iterate_fixed (pushStep_src par bn M)]
    refine ⟨rfl, hM, ?_⟩
    funext x y; simp [pushAlong, parPath]
  | succ L ih =>
    intro v M n hM hv hd hl hn hbn
    have hv0 : v ≠ 0 := fun e => by rw [e, hP.lev0] at hl; omega
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 hd
    obtain ⟨huV, hud, hlev, -⟩ := hP.parent v u (by omega) hv hu
    obtain ⟨g1, g2, g3, -, -, -⟩ := parPath_spec hP L u huV hud (by omega)
    have hvnot : v ∉ parPath par L u := fun hm => by have := (g3 v hm).2.2; omega
    have huv : u ≠ v := fun e => hvnot (e ▸ List.mem_of_getLast? g2)
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have harcs : (parPath par (L + 1) v).zip (parPath par (L + 1) v).tail =
        (parPath par L u).zip (parPath par L u).tail ++ [(u, v)] := by
      simp only [parPath, hu]; exact arcs_snoc _ u v g2
    rw [harcs] at hbn
    obtain ⟨s1, s2, s3⟩ := pushStep_par par bn M v u hM hv huV huv hv0 hu
    rw [Function.iterate_succ_apply]
    set st := (fcPushStep par bn 0 (v, M)).val with hst
    obtain ⟨st1, st2⟩ := st
    simp only at s1 s2 s3
    subst s1
    obtain ⟨h1, h2, h3⟩ := ih st1 st2 n' s2 huV hud (by omega) (by omega) (fun e he => by
      rw [s3]
      have hx := (List.of_mem_zip he).1
      have hy := List.mem_of_mem_tail (List.of_mem_zip he).2
      have e1 : ¬ (e.1 = v ∧ e.2 = st1) := fun h => hvnot (h.1 ▸ hx)
      have e2 : ¬ (e.1 = st1 ∧ e.2 = v) := fun h => hvnot (h.2 ▸ hy)
      simp only [e1, e2, if_false]
      exact hbn e (List.mem_append_left _ he))
    refine ⟨h1, h2, ?_⟩
    rw [h3, s3]
    have hsnoc := pushAlong_snoc (capOf M) (parPath par L st1) st1 v bn.get g2 hvnot
      (hbn (st1, v) (by simp))
    simp only [parPath, hu]
    exact hsnoc

/-- INTERNAL: the first step of the bottleneck walk, from the sink with no value yet. -/
theorem bnStep_first (res : List (List SNat)) (par : List (Option ℕ)) (v u : ℕ)
    (hv : v ≠ 0) (hu : par.getD v none = some u) :
    (fcBnStep res par 0 (v, none)).val = (u, some (Program.get2 res u v).val) := by
  have hu' : par.getD v default = some u := hu
  simp only [fcBnStep, Charged.val_bind, Cellcounting.Interface.val_idxEq, hv, decide_false,
    Bool.false_eq_true, if_false, Cellcounting.Interface.val_get, hu', Charged.val_pure]

/-- INTERNAL: when `augment` finds no path, the vertices BFS reached form a cut with no
residual arc leaving it.
TEXLINE: sections/scales.tex:13-20 -/
theorem augment_none (V : ℕ) (res : List (List SNat)) (hV : 2 ≤ V)
    (h : (Program.augment V res).val = none) :
    ∃ S : Finset ℕ, S ⊆ Finset.range V ∧ 0 ∈ S ∧ V - 1 ∉ S ∧
      ∀ u ∈ S, ∀ w ∈ Finset.range V \ S, capOf res u w = 0 := by
  obtain ⟨lev, hP⟩ := bfs_spec V res (by omega)
  set par := (Program.bfs V res).val with hpar
  have hsink : par.getD (V - 1) none = none := by
    unfold Program.augment at h
    simp only [Charged.val_bind, Cellcounting.Interface.val_get] at h
    rw [← hpar] at h
    cases hpt : par.getD (V - 1) default with
    | none => rfl
    | some w => rw [hpt] at h; simp at h
  refine ⟨(Finset.range V).filter (fun v => par.getD v none ≠ none), Finset.filter_subset _ _,
    Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), by rw [hP.root]; simp⟩,
    fun hm => (Finset.mem_filter.1 hm).2 hsink, fun u hu w hw => ?_⟩
  obtain ⟨huV, hud⟩ := Finset.mem_filter.1 hu
  obtain ⟨hwV, hwS⟩ := Finset.mem_sdiff.1 hw
  by_contra hne
  exact hwS (Finset.mem_filter.2 ⟨hwV,
    (hP.closed u (Finset.mem_range.1 huV) hud w (Finset.mem_range.1 hwV) (by omega)).1⟩)

/-- INTERNAL: when `augment` succeeds it is one Edmonds–Karp step: it augments by the
bottleneck capacity along a shortest simple residual path.
TEXLINE: sections/scales.tex:13-20 -/
theorem augment_some (V : ℕ) (res : List (List SNat)) (hV : 2 ≤ V) (hsh : SqShape V res)
    (res' : List (List SNat)) (bn : SNat) (h : (Program.augment V res).val = some (res', bn)) :
    SqShape V res' ∧ ∃ p : List ℕ, IsResPath V (capOf res) p ∧ p.Nodup ∧
      (∀ q, IsResPath V (capOf res) q → p.length ≤ q.length) ∧
      (∀ e ∈ p.zip p.tail, bn.get ≤ capOf res e.1 e.2) ∧
      (∃ e ∈ p.zip p.tail, capOf res e.1 e.2 = bn.get) ∧
      capOf res' = pushAlong (capOf res) p bn.get := by
  obtain ⟨lev, hP⟩ := bfs_spec V res (by omega)
  set par := (Program.bfs V res).val with hpar
  unfold Program.augment at h
  simp only [Charged.val_bind, Cellcounting.Interface.val_get] at h
  rw [← hpar] at h
  cases hpt : par.getD (V - 1) default with
  | none => rw [hpt] at h; simp at h
  | some w =>
    rw [hpt] at h
    simp only [Charged.val_bind, Charged.val_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hres', hbn⟩ := h
    rw [hbn] at hres'
    have hd : par.getD (V - 1) none ≠ none := by
      change par.getD (V - 1) default ≠ none; rw [hpt]; simp
    have ht0 : V - 1 ≠ 0 := by omega
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 hd
    obtain ⟨huV, hud, hlev, hpos⟩ := hP.parent (V - 1) u (by omega) (by omega) hu
    set L := lev u with hL
    have hLV : lev (V - 1) < V := hP.levlt (V - 1) (by omega) hd
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := parPath_spec hP (L + 1) (V - 1) (by omega) hd hlev
    obtain ⟨-, q2, -, -, -, -⟩ := parPath_spec hP L u huV hud rfl
    have harcs : (parPath par (L + 1) (V - 1)).zip (parPath par (L + 1) (V - 1)).tail =
        (parPath par L u).zip (parPath par L u).tail ++ [(u, V - 1)] := by
      simp only [parPath, hu]; exact arcs_snoc _ u (V - 1) q2
    -- the bottleneck
    have hbnv : ∃ b', (Charged.repeatFor (fcBnStep res par) V (V - 1, none)).val.2 = some b' ∧
        (∀ e ∈ (parPath par (L + 1) (V - 1)).zip (parPath par (L + 1) (V - 1)).tail,
          b'.get ≤ capOf res e.1 e.2) ∧
        (∃ e ∈ (parPath par (L + 1) (V - 1)).zip (parPath par (L + 1) (V - 1)).tail,
          capOf res e.1 e.2 = b'.get) := by
      rw [repeatFor_iterate _ (fun _ _ => rfl)]
      obtain ⟨V', hV'⟩ : ∃ V', V = V' + 1 := ⟨V - 1, by omega⟩
      rw [hV', Function.iterate_succ_apply, ← hV', bnStep_first res par (V - 1) u ht0 hu]
      obtain ⟨-, b', g1, g2, g3, g4⟩ := bn_walk hP L u (Program.get2 res u (V - 1)).val V'
        huV hud rfl (by omega)
      have hcuv : (Program.get2 res u (V - 1)).val.get = capOf res u (V - 1) := by
        rw [get2_val]; rfl
      rw [harcs]
      refine ⟨b', g1, fun e he => ?_, ?_⟩
      · rcases List.mem_append.1 he with he | he
        · exact g3 e he
        · rw [List.mem_singleton.1 he]; simp only; omega
      · rcases g4 with g | ⟨e, he, hee⟩
        · exact ⟨(u, V - 1), by simp, by simp only; omega⟩
        · exact ⟨e, List.mem_append_left _ he, hee⟩
    obtain ⟨b', hb'1, hb'2, hb'3⟩ := hbnv
    have hbnb : bn = b' := by
      rw [← hbn, fc_bottleneck_eq]
      simp only [Charged.val_bind]
      rw [hb'1]; rfl
    subst hbnb
    -- the push
    obtain ⟨-, w2, w3⟩ := push_walk hP bn (L + 1) (V - 1) res V hsh (by omega) hd hlev
      (by omega) hb'2
    have hpush : (Program.pushFlow V res par bn).val =
        ((fun s => (fcPushStep par bn 0 s).val)^[V] (V - 1, res)).2 := by
      rw [fc_pushFlow_eq]
      simp only [Charged.val_bind, Charged.val_pure]
      rw [repeatFor_iterate _ (fun _ _ => rfl)]
    rw [← hres', hpush]
    refine ⟨w2, parPath par (L + 1) (V - 1), ⟨p1, p2, fun x hx => (p3 x hx).1, p4⟩, p5,
      fun q hq => ?_, hb'2, hb'3, w3⟩
    obtain ⟨qh, ql, qlt, qc⟩ := hq
    have := (parSpec_lev_le hP (by omega) q (V - 1) qh ql qlt qc).2
    rw [p6]; omega

end Cellcounting.Analysis
