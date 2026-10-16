import Cellcounting.Analysis.FlowNet
import Cellcounting.Analysis.EdmondsKarpBound
import Cellcounting.Analysis.AugmentSpec

/-!
# The program's `maxFlow` computes a maximum flow value

`sections/scales.tex:13-22`: `Program.maxFlow V cap` runs at most `V³` augmentations,
each along a breadth-first (hence shortest) residual path by its bottleneck capacity.

`maxFlow_correct`: on a `V × V` capacity matrix with `V ≥ 2`, the returned number is
the value of an integral flow, and no flow has larger value.

The proof is a loop invariant (`MfInv`) over the `repeatWhile` rounds: the residual matrix
is `cap` minus a net flow of the accumulated value (`ResInv`, `Analysis/ResidualCut.lean`),
and the residual matrices so far form a run of Edmonds–Karp steps (`EKStep`).  Each
successful `augment` is such a step (`augment_some`, `Analysis/AugmentSpec.lean`: BFS parent
paths are shortest simple residual paths, `bottleneck` is their minimum and `pushFlow` is
`pushAlong`).  By `edmondsKarp_bound` the loop cannot run out of rounds while a path
remains, so it ends with `augment` returning `none`; the vertices BFS reached are then a cut
with no residual arc leaving it (`augment_none`), and `resInv_cut` bounds every flow.
`resInv_flow` turns the final net flow into an integral flow of the returned value.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Cellcounting.Model.Operations

open Arlib.Computation

/-- INTERNAL: one round of an early-exit fold, on values. -/
theorem mf_foldlWhile_cons {β : Type} (g : β → ℕ → Program.Prog (Option β)) (i : ℕ)
    (xs : List ℕ) (a : β) :
    (Charged.foldlWhile g (i :: xs) a).val =
      match (g a i).val with
      | none => a
      | some a' => (Charged.foldlWhile g xs a').val := by
  cases h : (g a i).val <;> simp [Charged.foldlWhile, Charged.val, h] at h ⊢ <;> simp [h]

/-- INTERNAL: a round-indexed invariant of an early-exit loop, together with the reason it
stopped: either every round ran, or the round after the last one declined. -/
theorem mf_repeatWhile_inv {β : Type} (f : ℕ → β → Program.Prog (Option β)) (P : ℕ → β → Prop)
    (n : ℕ) (b : β) (h0 : P 0 b)
    (hs : ∀ r b, r < n → P r b → ∀ b', (f r b).val = some b' → P (r + 1) b') :
    ∃ r ≤ n, P r (Charged.repeatWhile f n b).val ∧
      (r < n → (f r (Charged.repeatWhile f n b).val).val = none) := by
  have key : ∀ k s b, s + k = n → P s b →
      ∃ r, s ≤ r ∧ r ≤ n ∧ P r (Charged.foldlWhile (fun b r => f r b) (List.range' s k) b).val ∧
        (r < n → (f r (Charged.foldlWhile (fun b r => f r b) (List.range' s k) b).val).val = none) := by
    intro k
    induction k with
    | zero =>
      intro s b hs hb
      exact ⟨s, le_rfl, by omega, by simpa using hb, fun h => by omega⟩
    | succ k ih =>
      intro s b hsk hb
      rw [List.range'_succ, mf_foldlWhile_cons]
      cases hv : (f s b).val with
      | none => exact ⟨s, le_rfl, by omega, hb, fun _ => hv⟩
      | some b' =>
        obtain ⟨r, h1, h2, h3, h4⟩ := ih (s + 1) b' (by omega) (hs s b (by omega) hb b' hv)
        exact ⟨r, by omega, h2, h3, h4⟩
  obtain ⟨r, -, h2, h3, h4⟩ := key n 0 b (by omega) h0
  refine ⟨r, h2, ?_, ?_⟩
  · simpa [Charged.repeatWhile, List.range_eq_range'] using h3
  · simpa [Charged.repeatWhile, List.range_eq_range'] using h4

/-- INTERNAL: the invariant of the augmentation loop after `r` augmentations: a `V × V`
residual matrix, the residual invariant at the accumulated value, and a run of `r`
Edmonds–Karp steps from the capacities to the current residuals. -/
def MfInv (V : ℕ) (cap : List (List SNat)) (r : ℕ) (st : List (List SNat) × SNat) : Prop :=
  SqShape V st.1 ∧ (∃ g, ResInv V (capOf cap) (capOf st.1) g st.2.get) ∧
    ∃ seq : ℕ → ℕ → ℕ → ℕ, seq 0 = capOf cap ∧ seq r = capOf st.1 ∧
      ∀ k < r, EKStep V (seq k) (seq (k + 1))

/-- INTERNAL: a successful augmentation keeps the loop invariant. -/
theorem mfInv_step (V : ℕ) (cap : List (List SNat)) (hV : 2 ≤ V) (r : ℕ)
    (st st' : List (List SNat) × SNat) (h : MfInv V cap r st)
    (hst : (Cellcounting.Analysis.fcMfStep V r st).val = some st') : MfInv V cap (r + 1) st' := by
  obtain ⟨hsh, ⟨g, hg⟩, seq, hs0, hsr, hseq⟩ := h
  unfold Cellcounting.Analysis.fcMfStep at hst
  simp only [Charged.val_bind] at hst
  cases ha : (Program.augment V st.1).val with
  | none => rw [ha] at hst; simp at hst
  | some a =>
    obtain ⟨res', bn⟩ := a
    rw [ha] at hst
    simp only [Charged.val_bind, Charged.val_pure, Option.some.injEq] at hst
    subst hst
    obtain ⟨hsh', p, hp, hnd, hshort, hle, hatt, hpush⟩ := augment_some V st.1 hV hsh res' bn ha
    have hinv := resInv_push hg hV p hp hnd bn.get hle
    rw [← hpush] at hinv
    refine ⟨hsh', ⟨_, by simpa only [Cellcounting.Interface.SNat.get_add] using hinv⟩,
      fun k => if k ≤ r then seq k else capOf res', by simp [hs0], by simp, fun k hk => ?_⟩
    · by_cases hkr : k + 1 ≤ r
      · simp only [if_pos hkr, if_pos (show k ≤ r by omega)]
        exact hseq k (by omega)
      · obtain rfl : k = r := by omega
        simp only [le_refl, if_true, show ¬ (k + 1 ≤ k) by omega, if_false, hsr]
        exact ⟨p, hp, hshort, bn.get, hle, hatt, hpush⟩

/-- The program's Edmonds–Karp loop returns the maximum flow value: some flow attains
it, and every flow is bounded by it.
PAPER: sections/scales.tex:13-22 -/
theorem maxFlow_correct (V : ℕ) (cap : List (List SNat)) (hV : 2 ≤ V)
    (hlen : cap.length = V) (hrow : ∀ row ∈ cap, row.length = V) :
    (∃ f, IsFlow V (capOf cap) f ∧
        flowValue V f = ((Program.maxFlow V cap).val.get : ℤ)) ∧
      ∀ g, IsFlow V (capOf cap) g → flowValue V g ≤ ((Program.maxFlow V cap).val.get : ℤ) := by
  have hval : (Program.maxFlow V cap).val =
      (Charged.repeatWhile (fcMfStep V) (V * V * V) (cap, (SNat.lit 0).val)).val.2 := by
    rw [fc_maxFlow_eq]; simp only [Charged.val_bind, Charged.val_pure]
  rw [hval]
  set fin := (Charged.repeatWhile (fcMfStep V) (V * V * V) (cap, (SNat.lit 0).val)).val with hfin
  obtain ⟨r, hr, ⟨hsh, ⟨g, hg⟩, seq, hs0, hsr, hseq⟩, hstop⟩ :=
    mf_repeatWhile_inv (fcMfStep V) (MfInv V cap) (V * V * V) (cap, (SNat.lit 0).val)
      ⟨⟨hlen, hrow⟩, ⟨_, by simpa using resInv_init V (capOf cap)⟩, fun _ => capOf cap, rfl, rfl,
        fun k hk => absurd hk (Nat.not_lt_zero k)⟩
      (fun r st _ h st' hst => mfInv_step V cap hV r st st' h hst)
  rw [← hfin] at hstop
  -- the loop stopped because no augmenting path is left
  have hnone : (Program.augment V fin.1).val = none := by
    cases ha : (Program.augment V fin.1).val with
    | none => rfl
    | some a =>
      exfalso
      obtain ⟨res', bn⟩ := a
      rcases Nat.lt_or_ge r (V * V * V) with hlt | hge
      · have := hstop hlt
        unfold fcMfStep at this
        simp only [Charged.val_bind, ha] at this
        simp at this
      · obtain ⟨-, p, hp, -, hshort, hle, hatt, hpush⟩ := augment_some V fin.1 hV hsh res' bn ha
        have hEK := edmondsKarp_bound V hV (r + 1)
          (fun k => if k ≤ r then seq k else capOf res') (fun k hk => by
            by_cases hkr : k + 1 ≤ r
            · simp only [if_pos hkr, if_pos (show k ≤ r by omega)]
              exact hseq k (by omega)
            · obtain rfl : k = r := by omega
              simp only [le_refl, if_true, show ¬ (k + 1 ≤ k) by omega, if_false, hsr]
              exact ⟨p, hp, hshort, bn.get, hle, hatt, hpush⟩)
        have : V ^ 3 = V * V * V := by ring
        omega
  obtain ⟨S, hS, h0, ht, hcl⟩ := augment_none V fin.1 hV hnone
  exact ⟨resInv_flow hg, fun h hh => resInv_cut hg S hS h0 ht hcl h hh⟩

end Cellcounting.Analysis
