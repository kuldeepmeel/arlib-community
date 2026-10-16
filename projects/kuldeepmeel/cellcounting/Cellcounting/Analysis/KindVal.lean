import Cellcounting.Interface.Encoding
import Cellcounting.Interface.Pseudocode
import Cellcounting.Analysis.PhaseWindow

/-!
# The program's state classifier is the pseudocode `kind`

INTERNAL bridge for `Interface/ProgramModel.lean` (the observation and transition rungs).
`Program.kind K S` scans the `p` pairs of a `2p`-bit state once, counting empty and full
pairs and remembering the last of each.  `kind_val` says that, with `K.p = p`, this is
exactly `Pseudocode.kind` of the state read as the finset of its set bits below `2p`.
The scan after `k` pairs holds the card and the `sup` of the empty (full) pairs among the
first `k` (`kindScan_eq`); the final case split is then the same on both sides.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Cellcounting.Program Cellcounting.Model Cellcounting.Model.Operations Arlib.Computation

/-- INTERNAL: the state `S` as the finset of its set bits below `2p`.
TEXLINE: sections/signatures.tex:13-41 -/
noncomputable def stateView (p : ℕ) (S : List Bool) : Finset ℕ :=
  (Finset.range (2 * p)).filter (fun e => S.getD e false = true)

/-- INTERNAL: the per-pair body of the scan inside `Program.kind`, verbatim. -/
def kindBody (S : List Bool) : ℕ → (ℕ × ℕ) × (ℕ × ℕ) → Prog ((ℕ × ℕ) × (ℕ × ℕ)) :=
  fun i st => do
    let rowIn ← Operations.get S (2 * i)
    let colIn ← Operations.get S (2 * i + 1)
    if rowIn then
      if colIn then pure (st.1, (st.2.1 + 1, i)) else pure st
    else
      if colIn then pure st else pure ((st.1.1 + 1, i), st.2)

/-- INTERNAL: empty pairs among the first `k`. -/
noncomputable def emptyPairs (S : List Bool) (k : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun i => S.getD (2 * i) false = false ∧ S.getD (2 * i + 1) false = false

/-- INTERNAL: full pairs among the first `k`. -/
noncomputable def fullPairs (S : List Bool) (k : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun i => S.getD (2 * i) false = true ∧ S.getD (2 * i + 1) false = true

/-- INTERNAL: inserting a new maximum. -/
theorem sup_insert_top (E : Finset ℕ) (k : ℕ) (h : ∀ i ∈ E, i < k) :
    (insert k E).sup id = k := by
  rw [Finset.sup_insert]
  apply le_antisymm
  · exact sup_le le_rfl (Finset.sup_le fun i hi => (h i hi).le)
  · exact le_sup_left

/-- INTERNAL: the scan after `k` pairs holds the card and the `sup` of the empty and of the
full pairs among them. -/
theorem kindScan_eq (S : List Bool) (k : ℕ) :
    (List.range k).foldl (fun b r => (kindBody S r b).val) ((0, 0), (0, 0)) =
      (((emptyPairs S k).card, (emptyPairs S k).sup id),
        ((fullPairs S k).card, (fullPairs S k).sup id)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    have hE : emptyPairs S (k + 1) = if S.getD (2 * k) false = false ∧ S.getD (2 * k + 1) false = false
        then insert k (emptyPairs S k) else emptyPairs S k := by
      unfold emptyPairs; rw [Finset.range_add_one, Finset.filter_insert]
    have hF : fullPairs S (k + 1) = if S.getD (2 * k) false = true ∧ S.getD (2 * k + 1) false = true
        then insert k (fullPairs S k) else fullPairs S k := by
      unfold fullPairs; rw [Finset.range_add_one, Finset.filter_insert]
    have hEk : k ∉ emptyPairs S k := by simp [emptyPairs]
    have hFk : k ∉ fullPairs S k := by simp [fullPairs]
    have hElt : ∀ i ∈ emptyPairs S k, i < k := fun i hi => by
      simp only [emptyPairs, Finset.mem_filter, Finset.mem_range] at hi; exact hi.1
    have hFlt : ∀ i ∈ fullPairs S k, i < k := fun i hi => by
      simp only [fullPairs, Finset.mem_filter, Finset.mem_range] at hi; exact hi.1
    rw [hE, hF]
    have hv : ∀ st : (ℕ × ℕ) × (ℕ × ℕ), (kindBody S k st).val =
        if S.getD (2 * k) false then
          (if S.getD (2 * k + 1) false then (st.1, (st.2.1 + 1, k)) else st)
        else (if S.getD (2 * k + 1) false then st else ((st.1.1 + 1, k), st.2)) := by
      intro st
      simp only [kindBody, Charged.val_bind, Cellcounting.Interface.val_get]
      change Charged.val (if S.getD (2 * k) false = true then
        (if S.getD (2 * k + 1) false = true then pure (st.1, (st.2.1 + 1, k)) else pure st)
        else (if S.getD (2 * k + 1) false = true then pure st else pure ((st.1.1 + 1, k), st.2))) = _
      cases S.getD (2 * k) false <;> cases S.getD (2 * k + 1) false <;> rfl
    rw [hv]
    rcases Bool.eq_false_or_eq_true (S.getD (2 * k) false) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (S.getD (2 * k + 1) false) with h2 | h2 <;>
      simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true, and_true, and_false,
        Bool.true_eq_false, Finset.card_insert_of_notMem hEk,
        Finset.card_insert_of_notMem hFk, sup_insert_top _ _ hElt, sup_insert_top _ _ hFlt]

/-- INTERNAL: **the program's classifier is the pseudocode `kind`** of the viewed state.
TEXLINE: sections/signatures.tex:13-41 -/
theorem kind_val (I : Instance) (ε δ : ℚ) (K : Chain) (hp : K.p = Pseudocode.pSmall I ε δ)
    (S : List Bool) :
    (Program.kind K S).val = Pseudocode.kind I ε δ (stateView (Pseudocode.pSmall I ε δ) S) := by
  have hscan : (Charged.repeatFor (kindBody S) K.p ((0, 0), (0, 0))).val =
      (((emptyPairs S K.p).card, (emptyPairs S K.p).sup id),
        ((fullPairs S K.p).card, (fullPairs S K.p).sup id)) := by
    rw [val_repeatFor']; exact kindScan_eq S K.p
  have hk : (Program.kind K S).val =
      (do
        let st ← Charged.repeatFor (kindBody S) K.p ((0, 0), (0, 0))
        let e0 ← idxEq st.1.1 0
        let f0 ← idxEq st.2.1 0
        if e0 then
          if f0 then pure Kind.transversal else pure Kind.outside
        else do
          let e1 ← idxEq st.1.1 1
          let f1 ← idxEq st.2.1 1
          if e1 then
            if f1 then pure (Kind.defect st.1.2 st.2.2) else pure Kind.outside
          else pure Kind.outside : Prog Kind).val := rfl
  have hmem : ∀ i < K.p, ∀ b : Bool, (2 * i + (if b then 1 else 0) ∈ stateView (Pseudocode.pSmall I ε δ) S ↔
      S.getD (2 * i + (if b then 1 else 0)) false = true) := by
    intro i hi b
    simp only [stateView, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro h; refine ⟨?_, h⟩; cases b <;> simp <;> omega
  have hE : ((Finset.range (Pseudocode.pSmall I ε δ)).filter fun i =>
      2 * i ∉ stateView (Pseudocode.pSmall I ε δ) S ∧ 2 * i + 1 ∉ stateView (Pseudocode.pSmall I ε δ) S) =
      emptyPairs S K.p := by
    rw [emptyPairs, hp]
    refine Finset.filter_congr fun i hi => ?_
    rw [Finset.mem_range, ← hp] at hi
    have h0 := hmem i hi false
    have h1 := hmem i hi true
    simp only [Bool.false_eq_true, ite_false, add_zero, ite_true] at h0 h1
    rw [h0, h1]; simp
  have hF : ((Finset.range (Pseudocode.pSmall I ε δ)).filter fun i =>
      2 * i ∈ stateView (Pseudocode.pSmall I ε δ) S ∧ 2 * i + 1 ∈ stateView (Pseudocode.pSmall I ε δ) S) =
      fullPairs S K.p := by
    rw [fullPairs, hp]
    refine Finset.filter_congr fun i hi => ?_
    rw [Finset.mem_range, ← hp] at hi
    have h0 := hmem i hi false
    have h1 := hmem i hi true
    simp only [Bool.false_eq_true, ite_false, add_zero, ite_true] at h0 h1
    rw [h0, h1]
  rw [hk, Pseudocode.kind]
  simp only [hE, hF, Charged.val_bind, hscan, Cellcounting.Interface.val_idxEq]
  by_cases a : (emptyPairs S K.p).card = 0 <;> by_cases b : (fullPairs S K.p).card = 0 <;>
    by_cases c : (emptyPairs S K.p).card = 1 <;> by_cases d : (fullPairs S K.p).card = 1 <;>
    simp [a, b, c, d]

end Cellcounting.Analysis
