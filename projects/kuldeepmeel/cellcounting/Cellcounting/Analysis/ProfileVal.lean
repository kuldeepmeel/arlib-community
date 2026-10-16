import Cellcounting.Analysis.KindVal
import Cellcounting.Analysis.ChainSize

/-!
# The program's small-count profile is the pseudocode `profile`

INTERNAL bridge for `Interface/ProgramModel.lean` (the observation and transition rungs).
`Program.profile K S` scans the `p` pairs once, adding one to `x_{s(i)}` when the row
element `2i` is present and to `y_{s(i)}` when the column element `2i + 1` is.  With the
chain fields `p`, `#small` and `s(·)` of the instance, `profile_val` says the two count
lists, read as functions, are `Pseudocode.profile` of the state viewed as a finset
(`stateView`).  The one fact about the instance used is that every pair label `i < p`
belongs to a small cell `s(i) < #small` (`pv_pairCell_lt`), so that no increment falls
off the end of a count list.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Cellcounting.Program Cellcounting.Model Cellcounting.Model.Operations Arlib.Computation
open Cellcounting.Interface

/-- INTERNAL: there are `p = Σ_s b_s` pair labels. -/
theorem pv_pairCells_length (I : Instance) (ε δ : ℚ) :
    (Pseudocode.pairCells I ε δ).length = Pseudocode.pSmall I ε δ := by
  rw [Pseudocode.pairCells, List.length_flatMap, Pseudocode.pSmall]
  simp only [List.length_replicate]
  congr 1
  apply List.ext_getElem
  · simp [Pseudocode.nSmall]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, Pseudocode.smallB, Pseudocode.smallAt]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h2)]
    rfl

/-- INTERNAL: every pair label `i < p` belongs to a small cell `s(i) < #small`. -/
theorem pv_pairCell_lt (I : Instance) (ε δ : ℚ) {i : ℕ} (hi : i < Pseudocode.pSmall I ε δ) :
    Pseudocode.pairCell I ε δ i < Pseudocode.nSmall I ε δ := by
  rw [← pv_pairCells_length] at hi
  have hmem : Pseudocode.pairCell I ε δ i ∈ Pseudocode.pairCells I ε δ := by
    rw [Pseudocode.pairCell, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  rw [Pseudocode.pairCells, List.mem_flatMap] at hmem
  obtain ⟨s, hs, hrep⟩ := hmem
  rw [List.eq_of_mem_replicate hrep]
  exact List.mem_range.1 hs

/-- INTERNAL: pairs among the first `r` with label `s` whose element `2i + c` is present. -/
noncomputable def pairsWith (K : Chain) (S : List Bool) (c r s : ℕ) : Finset ℕ :=
  (Finset.range r).filter fun i => K.pairCell.getD i default = s ∧ S.getD (2 * i + c) false = true

/-- INTERNAL: the profile scan after `r` pairs, as counts. -/
def ProfInv (K : Chain) (S : List Bool) (r : ℕ) (st : List SNat × List SNat) : Prop :=
  st.1.length = K.nsm ∧ st.2.length = K.nsm ∧
    ∀ s, (st.1.getD s default).get = (pairsWith K S 0 r s).card ∧
      (st.2.getD s default).get = (pairsWith K S 1 r s).card

/-- INTERNAL: adding pair `r` to the counts. -/
theorem pairsWith_succ (K : Chain) (S : List Bool) (c r s : ℕ) :
    (pairsWith K S c (r + 1) s).card = (pairsWith K S c r s).card +
      if K.pairCell.getD r default = s ∧ S.getD (2 * r + c) false = true then 1 else 0 := by
  unfold pairsWith
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

/-- INTERNAL: one in-range increment of a count list. -/
theorem incr_view (l : List SNat) (s₀ s : ℕ) (h : s₀ < l.length) :
    ((l.set s₀ (SNat.add (l.getD s₀ default) (SNat.lit 1).val).val).getD s default).get =
      (l.getD s default).get + if s₀ = s then 1 else 0 := by
  rw [getD_set_get _ _ _ _ h]
  split_ifs with h1 h2 h2
  · subst h1; simp
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

/-- INTERNAL: one round of the profile scan adds pair `r` to the exact counts. -/
theorem pv_step (K : Chain) (S : List Bool) (hlt : ∀ i < K.p, K.pairCell.getD i default < K.nsm)
    (r : ℕ) (hr : r < K.p) (st : List SNat × List SNat) (h : ProfInv K S r st) :
    ProfInv K S (r + 1) ((do
    let s ← Operations.get K.pairCell r
    let rowIn ← Operations.get S (2 * r)
    let colIn ← Operations.get S (2 * r + 1)
    let x ← if rowIn then do
        let a ← Operations.get st.1 s
        let a' ← SNat.add a (SNat.lit 1).val
        Operations.set st.1 s a'
      else pure st.1
    let y ← if colIn then do
        let a ← Operations.get st.2 s
        let a' ← SNat.add a (SNat.lit 1).val
        Operations.set st.2 s a'
      else pure st.2
    pure (x, y) : Prog (List SNat × List SNat))).val := by
  obtain ⟨x, y⟩ := st
  obtain ⟨hx, hy, hc⟩ := h
  have hlt₀ := hlt r hr
  simp only [costVb, val_get]
  have hps := fun c s => pairsWith_succ K S c r s
  generalize K.pairCell.getD r default = s₀ at hlt₀ hps
  rcases Bool.eq_false_or_eq_true (S.getD (2 * r) default) with h1 | h1 <;>
  rcases Bool.eq_false_or_eq_true (S.getD (2 * r + 1) default) with h2 | h2 <;>
    simp only [ProfInv, h1, h2, Bool.false_eq_true, ↓reduceIte, costVb, costVp, val_get, val_set,
      List.length_set, hx, hy] <;>
    refine ⟨trivial, trivial, fun s => ?_⟩ <;>
    simp only [incr_view _ _ _ (hx ▸ hlt₀), incr_view _ _ _ (hy ▸ hlt₀), hps, (hc s).1, (hc s).2] <;>
    simp_all

/-- INTERNAL: an indexed invariant preserved by every round of `repeatFor` holds at its end
(values only). -/
theorem pv_fold_inv {β : Type} (f : ℕ → β → Prog β) (P : ℕ → β → Prop) (n : ℕ) (b : β)
    (hb : P 0 b) (h : ∀ r b, r < n → P r b → P (r + 1) (f r b).val) :
    P n (Charged.repeatFor f n b).val := by
  rw [val_repeatFor']
  suffices H : ∀ m ≤ n, P m ((List.range m).foldl (fun b r => (f r b).val) b) from H n le_rfl
  intro m hm
  induction m with
  | zero => exact hb
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact h m _ (by omega) (ih (by omega))

/-- INTERNAL: **the program's profile is the pseudocode profile** of the viewed state.
TEXLINE: sections/signatures.tex:13-41 -/
theorem profile_val (I : Instance) (ε δ : ℚ) (K : Chain) (hp : K.p = Pseudocode.pSmall I ε δ)
    (hnsm : K.nsm = Pseudocode.nSmall I ε δ) (hpc : K.pairCell = Pseudocode.pairCells I ε δ)
    (S : List Bool) :
    (fun k => ((Program.profile K S).val.1.getD k default).get) =
        (Pseudocode.profile I ε δ (stateView (Pseudocode.pSmall I ε δ) S)).1 ∧
      (fun k => ((Program.profile K S).val.2.getD k default).get) =
        (Pseudocode.profile I ε δ (stateView (Pseudocode.pSmall I ε δ) S)).2 := by
  have hlt : ∀ i < K.p, K.pairCell.getD i default < K.nsm := fun i hi => by
    rw [hpc, hnsm]; exact pv_pairCell_lt I ε δ (hp ▸ hi)
  have hinv : ProfInv K S K.p (Program.profile K S).val := by
    have h0 : ProfInv K S 0 (List.replicate K.nsm (SNat.lit 0).val,
        List.replicate K.nsm (SNat.lit 0).val) := by
      have hz := fun s => getD_pred_of_forall (fun x : SNat => x.get = 0)
        (List.replicate K.nsm (SNat.lit 0).val) s (by simp) (by simp)
      exact ⟨by simp, by simp, fun s => ⟨by rw [hz]; rfl, by rw [hz]; rfl⟩⟩
    exact pv_fold_inv _ (ProfInv K S) K.p _ h0 (fun r b hr hb => pv_step K S hlt r hr b hb)
  have hcard : ∀ c, c < 2 → ∀ s, (pairsWith K S c K.p s).card =
      ((Finset.range (Pseudocode.pSmall I ε δ)).filter fun i =>
        Pseudocode.pairCell I ε δ i = s ∧ 2 * i + c ∈ stateView (Pseudocode.pSmall I ε δ) S).card := by
    intro c hc s
    unfold pairsWith
    rw [hp]
    congr 1
    apply Finset.filter_congr
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [stateView, Finset.mem_filter, Finset.mem_range, hpc, Pseudocode.pairCell]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega, h2⟩
    · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
  refine ⟨funext fun s => ?_, funext fun s => ?_⟩
  · rw [(hinv.2.2 s).1, hcard 0 (by norm_num)]; rfl
  · rw [(hinv.2.2 s).2, hcard 1 (by norm_num)]; rfl

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `profile_val` by an exact-count fold invariant (`ProfInv`, `pv_step`, `pv_fold_inv`)
-/
