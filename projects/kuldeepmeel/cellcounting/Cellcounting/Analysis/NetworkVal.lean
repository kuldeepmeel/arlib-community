import Cellcounting.Analysis.FlowNet
import Cellcounting.Analysis.PhaseWindow

/-!
# The program builds the paper's feasibility network

`network_val`: `Program.network m n r c b` is an `(m + n + 2) × (m + n + 2)` matrix
whose entries are `netCap m n r c b` (`Analysis/FlowNet.lean`), the capacities of
`sections/scales.tex:8-11`, with the margins and bounds read through `getD`.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Model.Operations

/-- INTERNAL: a `V × V` matrix. -/
def SqShape (V : ℕ) (M : List (List SNat)) : Prop :=
  M.length = V ∧ ∀ row ∈ M, row.length = V

/-- INTERNAL: overwriting an in-range entry keeps the shape and changes that entry only. -/
theorem set2_sq (V : ℕ) (M : List (List SNat)) (u v : ℕ) (a : SNat) (h : SqShape V M)
    (hu : u < V) (hv : v < V) :
    SqShape V (Program.set2 M u v a).val ∧
      capOf (Program.set2 M u v a).val =
        fun x y => if x = u ∧ y = v then a.get else capOf M x y := by
  have e : (Program.set2 M u v a).val = M.set u ((M.getD u []).set v a) := by
    simp [Program.set2]; rfl
  have hu' : u < M.length := h.1 ▸ hu
  have hrow : (M.getD u []).length = V := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu', Option.getD_some]
    exact h.2 _ (List.getElem_mem _)
  rw [e]
  refine ⟨⟨by rw [List.length_set]; exact h.1, fun row hr => ?_⟩, ?_⟩
  · rcases List.mem_or_eq_of_mem_set hr with hm | rfl
    · exact h.2 row hm
    · rw [List.length_set, hrow]
  · funext x y
    simp only [capOf, List.getD_eq_getElem?_getD, List.getElem?_set]
    by_cases hx : x = u
    · subst hx
      by_cases hy : y = v
      · subst hy
        have hl : y < (M[x]'hu').length := by
          have := h.2 _ (List.getElem_mem hu'); omega
        simp [hu', List.getElem?_set_self hl]
      · simp [hu', Ne.symm hy, hy]
    · simp [hx, Ne.symm hx]

/-- INTERNAL: one more round of a charged loop, on values. -/
theorem nv_repeatFor_succ {β : Type} (F : ℕ → β → Program.Prog β) (k : ℕ) (b : β) :
    (Charged.repeatFor F (k + 1) b).val = (F k (Charged.repeatFor F k b).val).val := by
  rw [val_repeatFor', val_repeatFor', List.range_succ, List.foldl_append]
  rfl

/-- INTERNAL: a round-indexed invariant of a charged `repeatFor` loop, on values. -/
theorem nv_loop_inv {β : Type} (F : ℕ → β → Program.Prog β) (P : ℕ → β → Prop) (n : ℕ)
    (b : β) (h0 : P 0 b) (hs : ∀ k x, k < n → P k x → P (k + 1) (F k x).val) :
    P n (Charged.repeatFor F n b).val := by
  suffices ∀ k, k ≤ n → P k (Charged.repeatFor F k b).val from this n le_rfl
  intro k
  induction k with
  | zero => intro _; simpa [val_repeatFor'] using h0
  | succ k ih =>
    intro hk
    rw [nv_repeatFor_succ]
    exact hs k _ (by omega) (ih (by omega))

/-- The program's network matrix has the paper's capacities.
INTERNAL: transcription check of `Program.network` against `sections/scales.tex:8-11`.
TEXLINE: sections/scales.tex:8-11 -/
theorem network_val (m n : ℕ) (r c : List SNat) (b : List (List SNat)) :
    SqShape (m + n + 2) (Program.network m n r c b).val ∧
      capOf (Program.network m n r c b).val =
        netCap m n (fun i => (r.getD i default).get) (fun j => (c.getD j default).get)
          (fun i j => ((b.getD i []).getD j default).get) := by
  set R : ℕ → ℕ := fun i => (r.getD i default).get
  set Cc : ℕ → ℕ := fun j => (c.getD j default).get
  set B : ℕ → ℕ → ℕ := fun i j => ((b.getD i []).getD j default).get
  set V := m + n + 2 with hVdef
  let G1 : ℕ → ℕ → ℕ := fun x y => if x = 0 ∧ 1 ≤ y ∧ y ≤ m then R (y - 1) else 0
  let G2 : ℕ → ℕ → ℕ := fun x y =>
    if 1 ≤ x ∧ x ≤ m ∧ m + 1 ≤ y ∧ y ≤ m + n then B (x - 1) (y - 1 - m) else G1 x y
  unfold Program.network
  simp only [Charged.val_bind, Cellcounting.Interface.val_replicate]
  -- the zero matrix
  have h0 : SqShape V (List.replicate V (List.replicate V (SNat.lit 0).val)) ∧
      capOf (List.replicate V (List.replicate V (SNat.lit 0).val)) = fun _ _ => 0 := by
    refine ⟨⟨by simp, fun row hr => by rw [(List.mem_replicate.1 hr).2]; simp⟩, ?_⟩
    funext x y
    simp only [capOf, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> simp [List.getElem?_replicate] <;> split_ifs <;> rfl
  -- source arcs
  have h1 := nv_loop_inv (fun i cap => do
      let ri ← Model.Operations.get r i
      Program.set2 cap 0 (1 + i) ri)
    (fun k M => SqShape V M ∧ capOf M = fun x y => if x = 0 ∧ 1 ≤ y ∧ y ≤ k then R (y - 1) else 0)
    m _ ⟨h0.1, by rw [h0.2]; funext x y; split_ifs <;> first | rfl | omega⟩ (fun k M hk hM => by
      simp only [Charged.val_bind, Cellcounting.Interface.val_get]
      obtain ⟨hs, hc⟩ := set2_sq V M 0 (1 + k) (r.getD k default) hM.1 (by omega) (by omega)
      refine ⟨hs, ?_⟩
      rw [hc, hM.2]
      funext x y
      dsimp only
      split_ifs <;> first | rfl | omega | (simp only [R]; congr <;> omega))
  -- row-to-column arcs
  have h2 := nv_loop_inv (fun i cap => do
      let bi ← Model.Operations.get b i
      Charged.repeatFor (fun j cap' => do
          let bij ← Model.Operations.get bi j
          Program.set2 cap' (1 + i) (1 + m + j) bij) n cap)
    (fun k M => SqShape V M ∧ capOf M = fun x y =>
      if 1 ≤ x ∧ x ≤ k ∧ m + 1 ≤ y ∧ y ≤ m + n then B (x - 1) (y - 1 - m) else G1 x y)
    m _ ⟨h1.1, by rw [h1.2]; funext x y; dsimp only [G1]; split_ifs <;> first | rfl | omega⟩
    (fun k M hk hM => by
      simp only [Charged.val_bind, Cellcounting.Interface.val_get]
      have hin := nv_loop_inv (fun j cap' => do
          let bij ← Model.Operations.get (b.getD k default) j
          Program.set2 cap' (1 + k) (1 + m + j) bij)
        (fun l M' => SqShape V M' ∧ capOf M' = fun x y =>
          if x = 1 + k ∧ m + 1 ≤ y ∧ y ≤ m + l then B k (y - 1 - m) else capOf M x y)
        n M ⟨hM.1, by funext x y; split_ifs <;> first | rfl | omega⟩
        (fun l M' hl hM' => by
          simp only [Charged.val_bind, Cellcounting.Interface.val_get]
          obtain ⟨hs, hc⟩ := set2_sq V M' (1 + k) (1 + m + l)
            ((b.getD k default).getD l default) hM'.1 (by omega) (by omega)
          refine ⟨hs, ?_⟩
          rw [hc, hM'.2]
          funext x y
          dsimp only
          split_ifs <;> first | rfl | omega | (simp only [B]; congr <;> omega))
      refine ⟨hin.1, ?_⟩
      rw [hin.2, hM.2]
      funext x y; dsimp only
      split_ifs <;> first | rfl | omega | (simp only [B]; congr <;> omega))
  -- column-to-sink arcs
  have h3 := nv_loop_inv (fun j cap => do
      let cj ← Model.Operations.get c j
      Program.set2 cap (1 + m + j) (m + n + 1) cj)
    (fun k M => SqShape V M ∧ capOf M = fun x y =>
      if m + 1 ≤ x ∧ x ≤ m + k ∧ y = m + n + 1 then Cc (x - 1 - m) else G2 x y)
    n _ ⟨h2.1, by rw [h2.2]; funext x y; dsimp only [G2]; split_ifs <;> first | rfl | omega⟩
    (fun k M hk hM => by
      simp only [Charged.val_bind, Cellcounting.Interface.val_get]
      obtain ⟨hs, hc⟩ := set2_sq V M (1 + m + k) (m + n + 1) (c.getD k default) hM.1
        (by omega) (by omega)
      refine ⟨hs, ?_⟩
      rw [hc, hM.2]
      funext x y
      dsimp only
      split_ifs <;> first | rfl | omega | (simp only [Cc]; congr <;> omega))
  refine ⟨h3.1, ?_⟩
  rw [h3.2]
  funext x y
  simp only [netCap, G2, G1]
  split_ifs <;> first | rfl | omega

end Cellcounting.Analysis
