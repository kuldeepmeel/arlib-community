import Cellcounting.Analysis.CostScale
import Cellcounting.Analysis.CostLadder

/-!
# The feasibility test S1 runs in polynomial bit cost

`Cellcounting.Analysis.feasible_cost`: on a network with `m + n + 2 ≤ S` vertices
whose margins and capacities have binary length at most `S`, the feasibility test
`Program.feasible` (equal-totals test, then at most `V³` Edmonds–Karp
augmentations) costs at most `S ^ 32` bit operations.

This is a statement about cost only; correctness of the test is not needed, and
neither is the shape of the BFS tree.  `bottleneck` returns a residual entry or `0`;
each of the at most `V` steps of `pushFlow` subtracts it from one entry and adds it to
another, so one step at most doubles the matrix bound (`fc_pushStep`), and one
augmentation multiplies it by at most `2 ^ V`.  After `t ≤ V³` augmentations every
residual entry, and the flow value, is below `2 ^ (S + V t)` (`fc_maxFlow`), so every
comparison and addition has length at most `S + V⁴ + 1`.  Each round then costs at
most `32 T⁴` with `T = S + V⁴` (`fc_round_arith`): BFS is `V × V` neighbour steps with
queue indices `≤ V²` (`fc_bfs`), and the path walks are `V` steps (`fc_bottleneck`,
`fc_pushFlow`).  The equal-totals sums are below `2 ^ (2S)` (`fc_sumN`) and building
the network costs `≤ 64 V³` (`fc_network`).

The loop bodies of `bfs`, `bottleneck`, `pushFlow` and `maxFlow` are restated here
verbatim (`fcBfsInner`, `fcBfsOuter`, `fcBnStep`, `fcPushStep`, `fcMfStep`) with
definitional equations, so that the loop lemmas of `CostScale` see one stable term.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Program
open Cellcounting.Model.Operations
open Cellcounting.Interface

/-- INTERNAL: every entry of a capacity/residual matrix is below `2 ^ e`. -/
def FeasMatLt (e : ℕ) (M : List (List SNat)) : Prop := ∀ row ∈ M, ∀ x ∈ row, x.get < 2 ^ e

/-- INTERNAL: every parent recorded by the breadth-first search is a vertex `< V`. -/
def FeasParOK (V : ℕ) (par : List (Option ℕ)) : Prop := ∀ o ∈ par, ∀ u, o = some u → u < V

/-- INTERNAL: price of a matrix read. -/
theorem fc_get2_steps {α : Type} [Inhabited α] (M : List (List α)) (u v : ℕ) :
    Charged.steps rate (get2 M u v) = (u + 1) + (v + 1) := by
  unfold get2; simp only [Charged.steps_bind, steps_get]

/-- INTERNAL: price of a matrix write. -/
theorem fc_set2_steps {α : Type} (M : List (List α)) (u v : ℕ) (a : α) :
    Charged.steps rate (set2 M u v a) = (u + 1) + (v + 1) + (u + 1) := by
  unfold set2; simp only [Charged.steps_bind, steps_get, steps_set]; omega

/-- INTERNAL: a matrix read returns an entry below the matrix bound (or the default `0`). -/
theorem fc_get2_lt {e : ℕ} {M : List (List SNat)} (h : FeasMatLt e M) (u v : ℕ) :
    (get2 M u v).val.get < 2 ^ e := by
  unfold get2; simp only [costVb, val_get]
  exact getD_prop (P := fun x : SNat => x.get < 2 ^ e) _ _ _
    (getD_prop (P := fun row : List SNat => ∀ x ∈ row, x.get < 2 ^ e) _ _ _ h (fun x hx => by cases hx))
    (by simp)

/-- INTERNAL: writing an entry below the bound keeps the matrix bound. -/
theorem fc_set2_lt {e : ℕ} {M : List (List SNat)} (h : FeasMatLt e M) (u v : ℕ) (a : SNat)
    (ha : a.get < 2 ^ e) : FeasMatLt e (set2 M u v a).val := by
  unfold set2; simp only [costVb, val_get, val_set]
  exact set_prop (P := fun row : List SNat => ∀ x ∈ row, x.get < 2 ^ e) _ _ _ h
    (set_prop (P := fun x : SNat => x.get < 2 ^ e) _ _ _
      (getD_prop (P := fun row : List SNat => ∀ x ∈ row, x.get < 2 ^ e) _ _ _ h (fun x hx => by cases hx)) ha)

/-- INTERNAL: the matrix bound is monotone in the exponent. -/
theorem fc_matLt_mono {e e' : ℕ} {M : List (List SNat)} (h : FeasMatLt e M) (he : e ≤ e') :
    FeasMatLt e' M := fun row hr x hx =>
  (h row hr x hx).trans_le (Nat.pow_le_pow_right (by norm_num) he)

/-- INTERNAL: a number below `2 ^ e` has length at most `e + 1`. -/
theorem fc_bitLen_lt {x e : ℕ} (h : x < 2 ^ e) : bitLen x ≤ e + 1 := bitLen_le_of_lt_two_pow h

/-- INTERNAL: `sumN` of entries below `2 ^ e` over a list of length `≤ N` is below `2 ^ (e + N)` and costs at most `1 + N (2e + N + 2)`. -/
theorem fc_sumN (e N : ℕ) (l : List SNat) (hl : ∀ x ∈ l, x.get < 2 ^ e) (hN : l.length ≤ N) :
    (sumN l).val.get < 2 ^ (e + N) ∧
      Charged.steps rate (sumN l) ≤ 1 + N * (2 * e + N + 2) := by
  unfold sumN
  simp only [Charged.steps_bind, costVb, steps_SNat_lit]
  obtain ⟨h1, h2⟩ := foldl_inv (fun (acc : SNat) (x : SNat) => SNat.add acc x)
    (fun i (acc : SNat) => acc.get < 2 ^ (e + i)) (2 * e + N + 2) l 0 (SNat.lit 0).val
    (by simp)
    (by
      rintro i acc a - hi ha hP
      simp only [steps_SNat_add, SNat.get_add]
      have hx := hl a ha
      have h2 : 2 ^ e ≤ 2 ^ (e + i) := Nat.pow_le_pow_right (by norm_num) (by omega)
      refine ⟨?_, ?_⟩
      · rw [show e + (i + 1) = (e + i) + 1 by omega, pow_succ]; omega
      · have := fc_bitLen_lt hP; have := fc_bitLen_lt hx; simp at hi; omega)
  refine ⟨?_, ?_⟩
  · simp only [zero_add] at h1
    exact h1.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  · have : l.length * (2 * e + N + 2) ≤ N * (2 * e + N + 2) := Nat.mul_le_mul_right _ hN
    have h0 : bitLen 0 = 1 := by simp [bitLen]
    omega

/-- INTERNAL: the arithmetic closing `fc_network`. -/
theorem fc_network_arith (m n : ℕ) :
    1 + (m + n + 2 + 1) + (m + n + 2 + 1) + m * (2 * m + 5) +
      m * (m + 1 + n * (3 * m + 2 * n + 7)) + n * (3 * m + 4 * n + 7) ≤ 64 * (m + n + 2) ^ 3 := by
  have hm : m ≤ m + n + 2 := by omega
  have hn : n ≤ m + n + 2 := by omega
  have h2 : 2 ≤ m + n + 2 := by omega
  generalize m + n + 2 = V at hm hn h2 ⊢
  have a1 : m * (2 * m + 5) ≤ V * (7 * V) := Nat.mul_le_mul hm (by omega)
  have a2 : n * (3 * m + 2 * n + 7) ≤ V * (12 * V) := Nat.mul_le_mul hn (by omega)
  have a3 : m * (m + 1 + n * (3 * m + 2 * n + 7)) ≤ V * (2 * V + V * (12 * V)) :=
    Nat.mul_le_mul hm (by nlinarith)
  have a4 : n * (3 * m + 4 * n + 7) ≤ V * (14 * V) := Nat.mul_le_mul hn (by omega)
  have b1 : 2 * V ≤ V * V := Nat.mul_le_mul_right V h2
  have b2 : 2 * (V * V) ≤ V * V * V := by
    rw [Nat.mul_comm (V * V) V]; exact Nat.mul_le_mul_right _ h2
  have e1 : V * (7 * V) = 7 * (V * V) := by ring
  have e2 : V * (14 * V) = 14 * (V * V) := by ring
  have e3 : V * (2 * V + V * (12 * V)) = 2 * (V * V) + 12 * (V * V * V) := by ring
  have e4 : V ^ 3 = V * V * V := by ring
  rw [e4]; omega

/-- INTERNAL: the capacity matrix of `network` keeps the input bound `2 ^ e` and costs at most `64 (m + n + 2)³`. -/
theorem fc_network (e m n : ℕ) (r c : List SNat) (b : List (List SNat))
    (hr : ∀ x ∈ r, x.get < 2 ^ e) (hc : ∀ x ∈ c, x.get < 2 ^ e)
    (hb : ∀ row ∈ b, ∀ x ∈ row, x.get < 2 ^ e) :
    FeasMatLt e (network m n r c b).val ∧
      Charged.steps rate (network m n r c b) ≤ 64 * (m + n + 2) ^ 3 := by
  unfold network
  simp only [Charged.steps_bind, costVb, steps_SNat_lit, steps_replicate, val_replicate]
  have hz : FeasMatLt e (List.replicate (m + n + 2) (List.replicate (m + n + 2) (SNat.lit 0).val)) := by
    intro row hrow x hx
    obtain rfl := List.eq_of_mem_replicate hrow
    obtain rfl := List.eq_of_mem_replicate hx
    simp
  obtain ⟨h1v, h1s⟩ := repeatFor_inv (fun i (cap : List (List SNat)) => (do
      let ri ← Model.Operations.get r i
      set2 cap 0 (1 + i) ri : Prog (List (List SNat))))
    (fun _ cap => FeasMatLt e cap) (2 * m + 5) m _ hz (by
      intro i cap hi hP
      simp only [Charged.steps_bind, costVb, steps_get, val_get, fc_set2_steps]
      refine ⟨fc_set2_lt hP _ _ _ (getD_prop _ _ _ hr (by simp)), by omega⟩)
  obtain ⟨h2v, h2s⟩ := repeatFor_inv (fun i (cap : List (List SNat)) => (do
      let bi ← Model.Operations.get b i
      Charged.repeatFor (fun j cap' => do
        let bij ← Model.Operations.get bi j
        set2 cap' (1 + i) (1 + m + j) bij) n cap : Prog (List (List SNat))))
    (fun _ cap => FeasMatLt e cap) (m + 1 + n * (3 * m + 2 * n + 7)) m _ h1v (by
      intro i cap hi hP
      simp only [Charged.steps_bind, costVb, steps_get, val_get]
      have hbi : ∀ x ∈ b.getD i default, x.get < 2 ^ e :=
        getD_prop (P := fun row : List SNat => ∀ x ∈ row, x.get < 2 ^ e) _ _ _ hb
          (fun x hx => by cases hx)
      obtain ⟨hv, hs⟩ := repeatFor_inv (fun j (cap' : List (List SNat)) => (do
          let bij ← Model.Operations.get (b.getD i default) j
          set2 cap' (1 + i) (1 + m + j) bij : Prog (List (List SNat))))
        (fun _ cap => FeasMatLt e cap) (3 * m + 2 * n + 7) n _ hP (by
          intro j cap' hj hP'
          simp only [Charged.steps_bind, costVb, steps_get, val_get, fc_set2_steps]
          refine ⟨fc_set2_lt hP' _ _ _ (getD_prop _ _ _ hbi (by simp)), by omega⟩)
      exact ⟨hv, by omega⟩)
  obtain ⟨h3v, h3s⟩ := repeatFor_inv (fun j (cap : List (List SNat)) => (do
      let cj ← Model.Operations.get c j
      set2 cap (1 + m + j) (m + n + 1) cj : Prog (List (List SNat))))
    (fun _ cap => FeasMatLt e cap) (3 * m + 4 * n + 7) n _ h2v (by
      intro j cap hj hP
      simp only [Charged.steps_bind, costVb, steps_get, val_get, fc_set2_steps]
      refine ⟨fc_set2_lt hP _ _ _ (getD_prop _ _ _ hc (by simp)), by omega⟩)
  refine ⟨h3v, ?_⟩
  have h0 : bitLen 0 = 1 := by simp [bitLen]
  have := fc_network_arith m n
  omega

/-- INTERNAL: the inner (neighbour) loop body of `Program.bfs`, verbatim, so that loop lemmas see one stable term. -/
def fcBfsInner (row : List SNat) (u : ℕ) (zero : SNat) (v : ℕ)
    (st' : List (Option ℕ) × List ℕ × ℕ) : Prog (List (Option ℕ) × List ℕ × ℕ) := do
  let cap ← Model.Operations.get row v
  let pos ← SNat.lt zero cap
  if pos then do
    let pv ← Model.Operations.get st'.1 v
    match pv with
    | some _ => pure st'
    | none => do
      let par' ← Model.Operations.set st'.1 v (some u)
      let ord' ← Model.Operations.set st'.2.1 st'.2.2 v
      pure (par', ord', st'.2.2 + 1)
  else pure st'

/-- INTERNAL: one neighbour step of `bfs`: the queue tail grows by at most one, parents and queue entries stay `< V`, and the price is linear. -/
theorem fc_bfsInner (V e t u : ℕ) (row : List SNat) (zero : SNat) (v : ℕ)
    (st : List (Option ℕ) × List ℕ × ℕ) (hrow : ∀ x ∈ row, x.get < 2 ^ e) (hz : zero.get = 0)
    (hu : u < V) (hv : v < V) (ht : st.2.2 ≤ t) (hP : FeasParOK V st.1) (hO : ∀ x ∈ st.2.1, x < V) :
    (fcBfsInner row u zero v st).val.2.2 ≤ t + 1 ∧ FeasParOK V (fcBfsInner row u zero v st).val.1 ∧
      (∀ x ∈ (fcBfsInner row u zero v st).val.2.1, x < V) ∧
      Charged.steps rate (fcBfsInner row u zero v st) ≤ 3 * V + e + t + 3 := by
  have hcap : bitLen ((row.getD v default).get) ≤ e + 1 :=
    bitLen_le_of_lt_two_pow (getD_prop (P := fun x : SNat => x.get < 2 ^ e) _ _ _ hrow (by simp))
  have h0 : bitLen zero.get = 1 := by rw [hz]; simp [bitLen]
  unfold fcBfsInner
  simp only [Charged.steps_bind, costVb, steps_get, val_get, steps_SNat_lt, SNat.val_lt]
  by_cases hpos : zero.get < (row.getD v default).get
  · simp only [hpos, decide_true, ite_true, Charged.steps_bind, costVb, steps_get, val_get]
    cases hpv : st.1.getD v default with
    | some w =>
      simp only [costVp, Charged.steps_pure]
      exact ⟨by omega, hP, hO, by omega⟩
    | none =>
      simp only [Charged.steps_bind, costVb, steps_set, val_set, costVp, Charged.steps_pure]
      refine ⟨by omega, ?_, ?_, by omega⟩
      · exact set_prop (P := fun o : Option ℕ => ∀ w, o = some w → w < V) _ _ _ hP
          (by rintro w ⟨⟩; exact hu)
      · exact set_prop (P := fun x : ℕ => x < V) _ _ _ hO hv
  · simp only [hpos, decide_false, Bool.false_eq_true, ite_false, costVp, Charged.steps_pure]
    exact ⟨by omega, hP, hO, by omega⟩

/-- INTERNAL: the outer (queue) loop body of `Program.bfs`, verbatim. -/
def fcBfsOuter (V : ℕ) (res : List (List SNat)) (zero : SNat) (k : ℕ)
    (st : List (Option ℕ) × List ℕ × ℕ) : Prog (List (Option ℕ) × List ℕ × ℕ) := do
  let live ← idxLt k st.2.2
  if live then do
    let u ← Model.Operations.get st.2.1 k
    let row ← Model.Operations.get res u
    Charged.repeatFor (fcBfsInner row u zero) V st
  else pure st

/-- INTERNAL: the queue-tail bound `1 + kV + v ≤ V²` for `k, v < V`. -/
theorem fc_bfs_tail {V k v : ℕ} (hk : k < V) (hv : v < V) : 1 + k * V + v ≤ V * V := by
  have : (k + 1) * V ≤ V * V := Nat.mul_le_mul_right V hk
  rw [Nat.succ_mul] at this; omega

/-- INTERNAL: one queue step of `bfs`: the tail stays `≤ 1 + (k+1)V`, invariants are kept, and the price is polynomial in `V` and `e`. -/
theorem fc_bfsOuter (V e k : ℕ) (res : List (List SNat)) (zero : SNat)
    (st : List (Option ℕ) × List ℕ × ℕ) (hres : FeasMatLt e res) (hz : zero.get = 0)
    (hk : k < V) (ht : st.2.2 ≤ 1 + k * V) (hP : FeasParOK V st.1) (hO : ∀ x ∈ st.2.1, x < V) :
    (fcBfsOuter V res zero k st).val.2.2 ≤ 1 + (k + 1) * V ∧
      FeasParOK V (fcBfsOuter V res zero k st).val.1 ∧
      (∀ x ∈ (fcBfsOuter V res zero k st).val.2.1, x < V) ∧
      Charged.steps rate (fcBfsOuter V res zero k st) ≤
        3 * V + V * V + 1 + V * (3 * V + e + V * V + 3) := by
  have htV : st.2.2 ≤ V * V := by have := fc_bfs_tail hk (Nat.zero_lt_of_lt hk); omega
  have hb1 := bitLen_le_succ k
  have hb2 := bitLen_le_succ st.2.2
  unfold fcBfsOuter
  simp only [Charged.steps_bind, costVb, steps_idxLt, val_idxLt]
  by_cases hlive : k < st.2.2
  · simp only [hlive, decide_true, ite_true, Charged.steps_bind, costVb, steps_get, val_get]
    have hu : st.2.1.getD k default < V :=
      getD_prop (P := fun x : ℕ => x < V) _ _ _ hO (Nat.zero_lt_of_lt hk)
    have hrow : ∀ x ∈ res.getD (st.2.1.getD k default) default, x.get < 2 ^ e :=
      getD_prop (P := fun row : List SNat => ∀ x ∈ row, x.get < 2 ^ e) _ _ _ hres
        (fun x hx => by cases hx)
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := repeatFor_inv
      (fcBfsInner (res.getD (st.2.1.getD k default) default) (st.2.1.getD k default) zero)
      (fun v (st' : List (Option ℕ) × List ℕ × ℕ) =>
        st'.2.2 ≤ 1 + k * V + v ∧ FeasParOK V st'.1 ∧ ∀ x ∈ st'.2.1, x < V)
      (3 * V + e + V * V + 3) V st ⟨by omega, hP, hO⟩ (by
        rintro v st' hv ⟨h1, h2, h3⟩
        obtain ⟨g1, g2, g3, g4⟩ := fc_bfsInner V e (1 + k * V + v) _ _ _ v st' hrow hz hu hv h1 h2 h3
        have := fc_bfs_tail hk hv
        exact ⟨⟨by omega, g2, g3⟩, by omega⟩)
    refine ⟨by rw [Nat.succ_mul]; omega, h2, h3, ?_⟩
    have : V * (3 * V + e + V * V + 3) = V * (3 * V + e + V * V + 3) := rfl
    omega
  · simp only [hlive, decide_false, Bool.false_eq_true, ite_false, costVp, Charged.steps_pure]
    refine ⟨by rw [Nat.succ_mul]; omega, hP, hO, by omega⟩

/-- INTERNAL: `Program.bfs` in terms of `fcBfsOuter` (definitional). -/
theorem fc_bfs_eq (V : ℕ) (res : List (List SNat)) : bfs V res = (do
    let zero ← SNat.lit 0
    let par0 ← Model.Operations.replicate V (none : Option ℕ)
    let par ← Model.Operations.set par0 0 (some 0)
    let ord ← Model.Operations.replicate V 0
    let st ← Charged.repeatFor (fcBfsOuter V res zero) V (par, ord, 1)
    pure st.1) := rfl

/-- INTERNAL: `bfs` on a residual matrix with entries `< 2 ^ e` returns parents `< V` at polynomial price. -/
theorem fc_bfs (V e : ℕ) (res : List (List SNat)) (hV : 1 ≤ V) (hres : FeasMatLt e res) :
    FeasParOK V (bfs V res).val ∧
      Charged.steps rate (bfs V res) ≤
        2 * V + 4 + V * (3 * V + V * V + 1 + V * (3 * V + e + V * V + 3)) := by
  rw [fc_bfs_eq]
  simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SNat_lit,
    steps_replicate, val_replicate, steps_set, val_set]
  have hP0 : FeasParOK V ((List.replicate V (none : Option ℕ)).set 0 (some 0)) :=
    set_prop (P := fun o : Option ℕ => ∀ w, o = some w → w < V) _ _ _
      (by intro o ho w hw; rw [List.eq_of_mem_replicate ho] at hw; cases hw)
      (by rintro w ⟨⟩; omega)
  have hO0 : ∀ x ∈ List.replicate V 0, x < V := by
    intro x hx; rw [List.eq_of_mem_replicate hx]; omega
  obtain ⟨⟨-, h2, -⟩, h4⟩ := repeatFor_inv (fcBfsOuter V res (SNat.lit 0).val)
    (fun k (st : List (Option ℕ) × List ℕ × ℕ) =>
      st.2.2 ≤ 1 + k * V ∧ FeasParOK V st.1 ∧ ∀ x ∈ st.2.1, x < V)
    (3 * V + V * V + 1 + V * (3 * V + e + V * V + 3)) V
      ((List.replicate V (none : Option ℕ)).set 0 (some 0), List.replicate V 0, 1) ⟨by simp, hP0, hO0⟩ (by
      rintro k st hk ⟨h1, h2, h3⟩
      obtain ⟨g1, g2, g3, g4⟩ := fc_bfsOuter V e k res (SNat.lit 0).val st hres (by simp) hk h1 h2 h3
      exact ⟨⟨g1, g2, g3⟩, g4⟩)
  refine ⟨h2, ?_⟩
  have h0 : bitLen 0 = 1 := by simp [bitLen]
  omega

/-- INTERNAL: the loop body of `Program.bottleneck`, verbatim. -/
def fcBnStep (res : List (List SNat)) (par : List (Option ℕ)) (_i : ℕ) (st : ℕ × Option SNat) :
    Prog (ℕ × Option SNat) := do
  let atSrc ← idxEq st.1 0
  if atSrc then pure st else do
    let pu ← Model.Operations.get par st.1
    match pu with
    | none => pure st
    | some u => do
      let cuv ← get2 res u st.1
      match st.2 with
      | none => pure (u, some cuv)
      | some bn => do
        let smaller ← SNat.lt cuv bn
        if smaller then pure (u, some cuv) else pure (u, some bn)

/-- INTERNAL: `Program.bottleneck` in terms of `fcBnStep` (definitional). -/
theorem fc_bottleneck_eq (V : ℕ) (res : List (List SNat)) (par : List (Option ℕ)) :
    bottleneck V res par = (do
      let st ← Charged.repeatFor (fcBnStep res par) V (V - 1, none)
      match st.2 with
      | none => SNat.lit 0
      | some bn => pure bn) := rfl

/-- INTERNAL: one step of `bottleneck`: the position stays `< V`, the running minimum stays `< 2 ^ e`. -/
theorem fc_bnStep (V e i : ℕ) (res : List (List SNat)) (par : List (Option ℕ)) (st : ℕ × Option SNat)
    (hres : FeasMatLt e res) (hpar : FeasParOK V par) (h1 : st.1 < V)
    (h2 : ∀ bn, st.2 = some bn → bn.get < 2 ^ e) :
    (fcBnStep res par i st).val.1 < V ∧
      (∀ bn, (fcBnStep res par i st).val.2 = some bn → bn.get < 2 ^ e) ∧
      Charged.steps rate (fcBnStep res par i st) ≤ 4 * V + 2 * e + 3 := by
  have hb1 := bitLen_le_succ st.1
  have h0 : bitLen 0 = 1 := by simp [bitLen]
  unfold fcBnStep
  simp only [Charged.steps_bind, costVb, steps_idxEq, val_idxEq]
  by_cases hs : st.1 = 0
  · simp only [hs, decide_true, ite_true, costVp, Charged.steps_pure]
    exact ⟨by omega, h2, by omega⟩
  · simp only [hs, decide_false, Bool.false_eq_true, ite_false, Charged.steps_bind, costVb,
      steps_get, val_get]
    cases hpu : par.getD st.1 default with
    | none =>
      simp only [costVp, Charged.steps_pure]
      exact ⟨h1, h2, by omega⟩
    | some u =>
      have hu : u < V := getD_prop (P := fun o : Option ℕ => ∀ w, o = some w → w < V) _ _ _
        hpar (by rintro w ⟨⟩) u hpu
      have hc := fc_get2_lt hres u st.1
      have hcb := bitLen_le_of_lt_two_pow hc
      simp only [Charged.steps_bind, costVb, fc_get2_steps]
      cases hst : st.2 with
      | none =>
        simp only [costVp, Charged.steps_pure]
        refine ⟨hu, ?_, by omega⟩
        rintro bn ⟨⟩; exact hc
      | some bn =>
        have hbn := h2 bn hst
        have hbb := bitLen_le_of_lt_two_pow hbn
        simp only [Charged.steps_bind, costVb, steps_SNat_lt]
        split
        · simp only [costVp, Charged.steps_pure]
          refine ⟨hu, ?_, by omega⟩
          rintro b ⟨⟩; exact hc
        · simp only [costVp, Charged.steps_pure]
          refine ⟨hu, ?_, by omega⟩
          rintro b ⟨⟩; exact hbn

/-- INTERNAL: the bottleneck is below `2 ^ e` and costs at most `1 + V (4V + 2e + 3)`. -/
theorem fc_bottleneck (V e : ℕ) (res : List (List SNat)) (par : List (Option ℕ)) (hV : 1 ≤ V)
    (hres : FeasMatLt e res) (hpar : FeasParOK V par) :
    (bottleneck V res par).val.get < 2 ^ e ∧
      Charged.steps rate (bottleneck V res par) ≤ 1 + V * (4 * V + 2 * e + 3) := by
  rw [fc_bottleneck_eq]
  obtain ⟨⟨-, h2⟩, h3⟩ := repeatFor_inv (fcBnStep res par)
    (fun _ (st : ℕ × Option SNat) => st.1 < V ∧ ∀ bn, st.2 = some bn → bn.get < 2 ^ e)
    (4 * V + 2 * e + 3) V (V - 1, none) ⟨by simp; omega, by simp⟩ (by
      rintro i st - ⟨h1, h2⟩
      obtain ⟨g1, g2, g3⟩ := fc_bnStep V e i res par st hres hpar h1 h2
      exact ⟨⟨g1, g2⟩, g3⟩)
  simp only [Charged.steps_bind, costVb]
  cases hst : (Charged.repeatFor (fcBnStep res par) V (V - 1, none)).val.2 with
  | none =>
    simp only [steps_SNat_lit, SNat.get_lit]
    have h0 : bitLen 0 = 1 := by simp [bitLen]
    exact ⟨by positivity, by omega⟩
  | some bn =>
    simp only [costVp, Charged.steps_pure]
    exact ⟨h2 bn hst, by omega⟩

/-- INTERNAL: the loop body of `Program.pushFlow`, verbatim. -/
def fcPushStep (par : List (Option ℕ)) (bn : SNat) (_i : ℕ) (st : ℕ × List (List SNat)) :
    Prog (ℕ × List (List SNat)) := do
  let atSrc ← idxEq st.1 0
  if atSrc then pure st else do
    let pu ← Model.Operations.get par st.1
    match pu with
    | none => pure st
    | some u => do
      let fwd ← get2 st.2 u st.1
      let fwd' ← SNat.sub fwd bn
      let res1 ← set2 st.2 u st.1 fwd'
      let bwd ← get2 res1 st.1 u
      let bwd' ← SNat.add bwd bn
      let res2 ← set2 res1 st.1 u bwd'
      pure (u, res2)

/-- INTERNAL: `Program.pushFlow` in terms of `fcPushStep` (definitional). -/
theorem fc_pushFlow_eq (V : ℕ) (res : List (List SNat)) (par : List (Option ℕ)) (bn : SNat) :
    pushFlow V res par bn = (do
      let st ← Charged.repeatFor (fcPushStep par bn) V (V - 1, res)
      pure st.2) := rfl

/-- INTERNAL: one step of `pushFlow` at most doubles the matrix bound (subtract `bn`, add `bn < 2 ^ e`). -/
theorem fc_pushStep (V e i : ℕ) (par : List (Option ℕ)) (bn : SNat) (st : ℕ × List (List SNat))
    (hbn : bn.get < 2 ^ e) (hpar : FeasParOK V par) (h1 : st.1 < V) (h2 : FeasMatLt (e + i) st.2) :
    (fcPushStep par bn i st).val.1 < V ∧ FeasMatLt (e + i + 1) (fcPushStep par bn i st).val.2 ∧
      Charged.steps rate (fcPushStep par bn i st) ≤ 12 * V + 2 * (e + i) + 2 * e + 5 := by
  have hb1 := bitLen_le_succ st.1
  have h0 : bitLen 0 = 1 := by simp [bitLen]
  have hbb := bitLen_le_of_lt_two_pow hbn
  have hpow : 2 ^ e ≤ 2 ^ (e + i) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow2 : 2 ^ (e + i + 1) = 2 ^ (e + i) + 2 ^ (e + i) := by rw [pow_succ]; ring
  unfold fcPushStep
  simp only [Charged.steps_bind, costVb, steps_idxEq, val_idxEq]
  by_cases hs : st.1 = 0
  · simp only [hs, decide_true, ite_true, costVp, Charged.steps_pure]
    exact ⟨by omega, fc_matLt_mono h2 (by omega), by omega⟩
  · simp only [hs, decide_false, Bool.false_eq_true, ite_false, Charged.steps_bind, costVb,
      steps_get, val_get]
    cases hpu : par.getD st.1 default with
    | none =>
      simp only [costVp, Charged.steps_pure]
      exact ⟨h1, fc_matLt_mono h2 (by omega), by omega⟩
    | some u =>
      have hu : u < V := getD_prop (P := fun o : Option ℕ => ∀ w, o = some w → w < V) _ _ _
        hpar (by rintro w ⟨⟩) u hpu
      have hf := fc_get2_lt h2 u st.1
      have hfb := bitLen_le_of_lt_two_pow hf
      have hr1 : FeasMatLt (e + i) (set2 st.2 u st.1 ((get2 st.2 u st.1).val.sub bn).val).val :=
        fc_set2_lt h2 _ _ _ (by rw [SNat.get_sub]; omega)
      have hw := fc_get2_lt hr1 st.1 u
      have hwb := bitLen_le_of_lt_two_pow hw
      simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, fc_get2_steps,
        fc_set2_steps, steps_SNat_sub, steps_SNat_add]
      refine ⟨hu, fc_set2_lt (fc_matLt_mono hr1 (by omega)) _ _ _
        (by rw [SNat.get_add]; omega), by omega⟩

/-- INTERNAL: `pushFlow` with `bn < 2 ^ e` maps entries `< 2 ^ e` to entries `< 2 ^ (e + V)`, at price `≤ V (14V + 4e + 5)`. -/
theorem fc_pushFlow (V e : ℕ) (res : List (List SNat)) (par : List (Option ℕ)) (bn : SNat)
    (hV : 1 ≤ V) (hbn : bn.get < 2 ^ e) (hres : FeasMatLt e res) (hpar : FeasParOK V par) :
    FeasMatLt (e + V) (pushFlow V res par bn).val ∧
      Charged.steps rate (pushFlow V res par bn) ≤ V * (14 * V + 4 * e + 5) := by
  rw [fc_pushFlow_eq]
  obtain ⟨⟨-, h2⟩, h3⟩ := repeatFor_inv (fcPushStep par bn)
    (fun i (st : ℕ × List (List SNat)) => st.1 < V ∧ FeasMatLt (e + i) st.2)
    (14 * V + 4 * e + 5) V (V - 1, res) ⟨by simp; omega, by simpa using hres⟩ (by
      rintro i st hi ⟨h1, h2⟩
      obtain ⟨g1, g2, g3⟩ := fc_pushStep V e i par bn st hbn hpar h1 h2
      exact ⟨⟨g1, by simpa [Nat.add_assoc] using g2⟩, by omega⟩)
  simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure]
  exact ⟨h2, by omega⟩

/-- INTERNAL: the arithmetic bounding one Edmonds–Karp round by `32 T⁴`. -/
theorem fc_round_arith (V e T : ℕ) (hV : V ≤ T) (he : e + V ≤ T) (hT : 2 ≤ T) :
    (2 * V + 4 + V * (3 * V + V * V + 1 + V * (3 * V + e + V * V + 3))) + V +
      (1 + V * (4 * V + 2 * e + 3)) + V * (14 * V + 4 * e + 5) + 2 * (e + V + 1) ≤
      32 * T ^ 4 := by
  have he' : e ≤ T := by omega
  calc (2 * V + 4 + V * (3 * V + V * V + 1 + V * (3 * V + e + V * V + 3))) + V +
      (1 + V * (4 * V + 2 * e + 3)) + V * (14 * V + 4 * e + 5) + 2 * (e + V + 1)
      ≤ (2 * T + 4 + T * (3 * T + T * T + 1 + T * (3 * T + T + T * T + 3))) + T +
      (1 + T * (4 * T + 2 * T + 3)) + T * (14 * T + 4 * T + 5) + 2 * (T + T + 1) := by
        gcongr
    _ ≤ 32 * T ^ 4 := by nlinarith [pow_pos (show 0 < T by omega) 3]

/-- INTERNAL: one augmentation: the new residual matrix is below `2 ^ (e + V)`, the bottleneck below `2 ^ e`; polynomial price. -/
theorem fc_augment (V e : ℕ) (res : List (List SNat)) (hV : 1 ≤ V) (hres : FeasMatLt e res) :
    (∀ res' bn, (augment V res).val = some (res', bn) → FeasMatLt (e + V) res' ∧ bn.get < 2 ^ e) ∧
      Charged.steps rate (augment V res) ≤
        (2 * V + 4 + V * (3 * V + V * V + 1 + V * (3 * V + e + V * V + 3))) + V +
          (1 + V * (4 * V + 2 * e + 3)) + V * (14 * V + 4 * e + 5) := by
  obtain ⟨hp, hbs⟩ := fc_bfs V e res hV hres
  unfold augment
  simp only [Charged.steps_bind, costVb, steps_get, val_get]
  cases hpt : (bfs V res).val.getD (V - 1) default with
  | none =>
    simp only [costVp, Charged.steps_pure]
    refine ⟨by rintro _ _ ⟨⟩, by omega⟩
  | some w =>
    obtain ⟨hb1, hb2⟩ := fc_bottleneck V e res _ hV hres hp
    obtain ⟨hq1, hq2⟩ := fc_pushFlow V e res _ _ hV hb1 hres hp
    simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure]
    refine ⟨?_, by omega⟩
    rintro res' bn h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hq1, hb1⟩

/-- INTERNAL: the loop body of `Program.maxFlow`, verbatim. -/
def fcMfStep (V : ℕ) (_t : ℕ) (st : List (List SNat) × SNat) :
    Prog (Option (List (List SNat) × SNat)) := do
  let a ← augment V st.1
  match a with
  | none => pure none
  | some (res', bn) => do
    let f ← SNat.add st.2 bn
    pure (some (res', f))

/-- INTERNAL: `Program.maxFlow` in terms of `fcMfStep` (definitional). -/
theorem fc_maxFlow_eq (V : ℕ) (cap : List (List SNat)) : maxFlow V cap = (do
    let z ← SNat.lit 0
    let st ← Charged.repeatWhile (fcMfStep V) (V * V * V) (cap, z)
    pure st.2) := rfl

/-- INTERNAL: `maxFlow` on capacities `< 2 ^ e`: after `t` augmentations entries and flow are `< 2 ^ (e + V t)`, so the value is `< 2 ^ (e + V⁴)` and the price is at most `1 + V³ · 32 (e + V⁴)⁴`. -/
theorem fc_maxFlow (V e : ℕ) (cap : List (List SNat)) (hV : 1 ≤ V) (hT : 2 ≤ e + V * (V * V * V))
    (hcap : FeasMatLt e cap) :
    (maxFlow V cap).val.get < 2 ^ (e + V * (V * V * V)) ∧
      Charged.steps rate (maxFlow V cap) ≤
        1 + V * V * V * (32 * (e + V * (V * V * V)) ^ 4) := by
  rw [fc_maxFlow_eq]
  have hVT : V ≤ e + V * (V * V * V) := by
    have : V * 1 ≤ V * (V * V * V) := Nat.mul_le_mul_left V (Nat.one_le_iff_ne_zero.mpr
      (by positivity))
    omega
  obtain ⟨⟨r, hr, h1, h2⟩, h3⟩ := repeatWhile_inv (fcMfStep V)
    (fun t (st : List (List SNat) × SNat) =>
      FeasMatLt (e + V * t) st.1 ∧ st.2.get < 2 ^ (e + V * t))
    (32 * (e + V * (V * V * V)) ^ 4) (V * V * V) (cap, (SNat.lit 0).val)
    ⟨by simpa using hcap, by simp⟩ (by
      rintro t st ht ⟨g1, g2⟩
      have hle : V * (t + 1) ≤ V * (V * V * V) := Nat.mul_le_mul_left V ht
      rw [Nat.mul_succ] at hle
      obtain ⟨a1, a2⟩ := fc_augment V (e + V * t) st.1 hV g1
      have ar := fc_round_arith V (e + V * t) (e + V * (V * V * V)) hVT (by omega) hT
      have hb := bitLen_le_of_lt_two_pow g2
      unfold fcMfStep
      simp only [Charged.steps_bind, costVb]
      cases ha : (augment V st.1).val with
      | none =>
        simp only [costVp, Charged.steps_pure]
        refine ⟨by omega, by rintro _ ⟨⟩⟩
      | some p =>
        obtain ⟨res', bn⟩ := p
        obtain ⟨b1, b2⟩ := a1 res' bn ha
        have hbb := bitLen_le_of_lt_two_pow b2
        simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SNat_add]
        refine ⟨by omega, ?_⟩
        rintro b' hb'
        simp only [Option.some.injEq] at hb'
        subst hb'
        refine ⟨by simpa [Nat.mul_succ, Nat.add_assoc] using b1, ?_⟩
        simp only [SNat.get_add]
        have hp1 : 2 ^ (e + V * t) ≤ 2 ^ (e + V * t + 1) / 2 := by
          rw [pow_succ]; simp
        have hp2 : 2 ^ (e + V * t + 1) ≤ 2 ^ (e + V * (t + 1)) :=
          Nat.pow_le_pow_right (by norm_num) (by rw [Nat.mul_succ]; omega)
        have hp3 : 2 ^ (e + V * t + 1) = 2 ^ (e + V * t) + 2 ^ (e + V * t) := by
          rw [pow_succ]; ring
        omega)
  simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SNat_lit]
  have h0 : bitLen 0 = 1 := by simp [bitLen]
  refine ⟨h2.trans_le (Nat.pow_le_pow_right (by norm_num) ?_), by omega⟩
  have := Nat.mul_le_mul_left V hr
  omega

/-- INTERNAL: the arithmetic closing `feasible_cost` with exponent `32`. -/
theorem fc_final_arith (S V : ℕ) (hS : 2 ≤ S) (hV : V ≤ S) :
    (1 + S * (2 * S + S + 2)) + (1 + S * (2 * S + S + 2)) + ((S + S + 1) + (S + S + 1)) +
      64 * V ^ 3 + (1 + V * V * V * (32 * (S + V * (V * V * V)) ^ 4)) +
      ((S + V * (V * V * V) + 1) + (S + S + 1)) ≤ S ^ 32 := by
  have hS1 : 1 ≤ S := by omega
  -- every summand is at most `S ^ 28`
  have hSS : S ≤ S * S := Nat.le_mul_of_pos_left S (by omega)
  have p2 : S ^ 2 = S * S := by ring
  have hX2 : S ^ 2 ≤ S ^ 28 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h4 : S + S * (S * S * S) ≤ S ^ 5 := by
    have a : S ≤ S * (S * S * S) := Nat.le_mul_of_pos_right S (by positivity)
    have b : 2 * (S * (S * S * S)) ≤ S * (S * (S * S * S)) := Nat.mul_le_mul_right _ hS
    have c : S ^ 5 = S * (S * (S * S * S)) := by ring
    omega
  have hVV : V * (V * V * V) ≤ S * (S * S * S) := by gcongr
  have t1 : 1 + S * (2 * S + S + 2) ≤ 6 * S ^ 2 := by nlinarith
  have t2 : 64 * V ^ 3 ≤ S ^ 28 := by
    calc 64 * V ^ 3 ≤ S ^ 6 * S ^ 3 := by
          gcongr
          exact (show 64 = 2 ^ 6 by norm_num) ▸ Nat.pow_le_pow_left hS 6
      _ = S ^ 9 := by ring
      _ ≤ S ^ 28 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have t3 : V * V * V * (32 * (S + V * (V * V * V)) ^ 4) ≤ S ^ 28 := by
    calc V * V * V * (32 * (S + V * (V * V * V)) ^ 4)
        ≤ S * S * S * (S ^ 5 * (S ^ 5) ^ 4) := by
          gcongr
          · exact (show 32 = 2 ^ 5 by norm_num) ▸ Nat.pow_le_pow_left hS 5
          · omega
      _ = S ^ 28 := by ring
  have t4 : S + V * (V * V * V) + 1 ≤ S ^ 28 := by
    have : S ^ 5 ≤ S ^ 27 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have : S ^ 28 = S * S ^ 27 := by ring
    have : 2 * S ^ 27 ≤ S * S ^ 27 := Nat.mul_le_mul_right _ hS
    have : 1 ≤ S ^ 27 := Nat.one_le_pow _ _ (by omega)
    omega
  have t5 : 8 * S ^ 28 ≤ S ^ 32 := by
    calc 8 * S ^ 28 ≤ S ^ 3 * S ^ 28 := by
          gcongr; exact (show 8 = 2 ^ 3 by norm_num) ▸ Nat.pow_le_pow_left hS 3
      _ = S ^ 31 := by ring
      _ ≤ S ^ 32 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have t6 : 8 * S ^ 2 ≤ S ^ 28 := by
    calc 8 * S ^ 2 ≤ S ^ 3 * S ^ 2 := by
          gcongr; exact (show 8 = 2 ^ 3 by norm_num) ▸ Nat.pow_le_pow_left hS 3
      _ = S ^ 5 := by ring
      _ ≤ S ^ 28 := Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

/-- INTERNAL: the feasibility test costs a fixed power of a size bound `S` on the
dimensions, the list lengths and the binary lengths of all margins and capacities.
TEXLINE: sections/scales.tex:8-24 -/
theorem feasible_cost : ∃ k : ℕ, ∀ (S m n : ℕ) (r c : List SNat) (b : List (List SNat)),
    2 ≤ S → m + n + 2 ≤ S → r.length ≤ S → c.length ≤ S →
    (∀ x ∈ r, bitLen x.get ≤ S) → (∀ x ∈ c, bitLen x.get ≤ S) →
    (∀ row ∈ b, ∀ x ∈ row, bitLen x.get ≤ S) →
    Charged.steps rate (feasible m n r c b) ≤ S ^ k := by
  refine ⟨32, ?_⟩
  intro S m n r c b hS hmn hrl hcl hrb hcb hbb
  have hlt : ∀ x : SNat, bitLen x.get ≤ S → x.get < 2 ^ S := fun x h =>
    (lt_two_pow_bitLen x.get).trans_le (Nat.pow_le_pow_right (by norm_num) h)
  have hr : ∀ x ∈ r, x.get < 2 ^ S := fun x hx => hlt x (hrb x hx)
  have hc : ∀ x ∈ c, x.get < 2 ^ S := fun x hx => hlt x (hcb x hx)
  have hb : ∀ row ∈ b, ∀ x ∈ row, x.get < 2 ^ S := fun row hrow x hx => hlt x (hbb row hrow x hx)
  obtain ⟨sr1, sr2⟩ := fc_sumN S S r hr hrl
  obtain ⟨sc1, sc2⟩ := fc_sumN S S c hc hcl
  have bsr := bitLen_le_of_lt_two_pow sr1
  have bsc := bitLen_le_of_lt_two_pow sc1
  obtain ⟨nw1, nw2⟩ := fc_network S m n r c b hr hc hb
  obtain ⟨mf1, mf2⟩ := fc_maxFlow (m + n + 2) S _ (by omega) (by omega) nw1
  have bf := bitLen_le_of_lt_two_pow mf1
  have ar := fc_final_arith S (m + n + 2) hS hmn
  unfold feasible
  simp only [Charged.steps_bind, steps_SNat_eq, SNat.val_eq]
  by_cases he : (sumN r).val.get = (sumN c).val.get
  · simp only [he, decide_true, ite_true, Charged.steps_bind, steps_SNat_eq]
    omega
  · simp only [he, decide_false, Bool.false_eq_true, ite_false, Charged.steps_pure]
    omega

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `feasible_cost` with `k = 32`, via `fc_sumN`, `fc_network`, `fc_maxFlow`
  (matrix bound `2 ^ (S + V t)` after `t` augmentations)
-/
