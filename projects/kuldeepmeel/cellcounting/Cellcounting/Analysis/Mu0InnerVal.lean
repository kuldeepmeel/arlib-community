import Cellcounting.Analysis.RefMu0Law
import Cellcounting.Analysis.ChainSize
import Cellcounting.Analysis.PhaseWindow

/-!
# The deterministic unranking loop inside `Program.mu0` matches `Pseudocode.unrank`

INTERNAL infrastructure for `Interface/ProgramModel.lean`'s `mu0_tape`. No paper claim is
stated here: this file is the bridge obligation flagged at `Interface/Pseudocode.lean:111-114`
("`C(n, k)` is `Nat.choose`. The program's product formula `Program.binom n k` equals it for
`k ≤ n`. Inside `mu0` this is always the case, by the unranking invariant `remaining ≤
positions left`. That invariant is internal to the bridge proof of `mu0`, not a hypothesis.").

`innerStep` is a verbatim copy of the per-position closure inside `Program.mu0`
(`Model/Program.lean`, the body of its inner `Charged.repeatFor`), named so the two
occurrences this file and `ProgramModel.lean` both need can be stated once and unified by
`rfl`.  `unrankStep` is the same copy of the closure inside `Pseudocode.unrank`
(`Interface/Pseudocode.lean`), so that `unrank_eq_fold` holds by `rfl`.

`binom_val` is the flagged bridge fact itself: `Program.binom n k` computes `Nat.choose
n.get k.get` whenever `k.get ≤ n.get` (by the standard recurrence `add_one_mul_choose_eq`,
tracked through the accumulator one division at a time).

`mu0Inner_main` is the joint induction carrying both sides of the unranking loop in
lockstep for `n` steps, `n ≤ b.get`: the two numeric fields agree with `unrankStep`'s own
fold, every already-decided bit matches `unrankStep`'s accumulated set, and the invariant
`remaining ≤ positions left` needed for the next `binom` call persists.  `mu0Inner_eq`
specializes it to the full `b.get` steps and rewrites the pseudocode side to
`Pseudocode.unrank` by `unrank_eq_fold`.  `mu0Inner_untouched` and `mu0Inner_length` are the
two routine facts about the loop used throughout: it never touches a position outside its
own cell's range, and it never changes the length of the state list.

`dyadicDraw_lt` is the companion fact `mu0_tape` needs before it can even state the
`binom`/`unrank` preconditions: the program's dyadic draw returns a value strictly below
its parameter `M`, on every tape, whenever `M.get` is positive.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Cellcounting Cellcounting.Program Cellcounting.Model Cellcounting.Model.Operations
open Arlib.Computation Cellcounting.Interface

/-- INTERNAL: a verbatim copy of the per-position closure inside `Program.mu0`'s inner loop
(`Model/Program.lean`), so it can be named once and reused by `rfl` at the call site. -/
noncomputable def innerStep (b : SNat) (first : ℕ) :
    ℕ → List Bool × SNat × SNat → Prog (List Bool × SNat × SNat) :=
  fun t st' => do
    let lbl := first + t
    let remaining ← SNat.lt (SNat.lit 0).val st'.2.1
    if remaining then do
      let tS ← SNat.lit (t + 1)
      let rest ← SNat.sub b tS
      let k1 ← SNat.sub st'.2.1 (SNat.lit 1).val
      let c ← binom rest k1
      let incl ← SNat.lt st'.2.2 c
      if incl then do
        let S ← Operations.set st'.1 (2 * lbl) true
        pure (S, k1, st'.2.2)
      else do
        let r ← SNat.sub st'.2.2 c
        let S ← Operations.set st'.1 (2 * lbl + 1) true
        pure (S, st'.2.1, r)
    else do
      let S ← Operations.set st'.1 (2 * lbl + 1) true
      pure (S, st'.2.1, st'.2.2)

/-- INTERNAL: a verbatim copy of the per-position closure inside `Pseudocode.unrank`
(`Interface/Pseudocode.lean`), with the `List.foldl` argument order. -/
def unrankStep (b : ℕ) (st : Finset ℕ × ℕ × ℕ) (t : ℕ) : Finset ℕ × ℕ × ℕ :=
  if 0 < st.2.1 then
    if st.2.2 < Nat.choose (b - (t + 1)) (st.2.1 - 1) then (insert t st.1, st.2.1 - 1, st.2.2)
    else (st.1, st.2.1, st.2.2 - Nat.choose (b - (t + 1)) (st.2.1 - 1))
  else st

/-- INTERNAL: `unrank` is `unrankStep`'s own fold, by definition. -/
theorem unrank_eq_fold (b k r : ℕ) :
    Pseudocode.unrank b k r = ((List.range b).foldl (unrankStep b) (∅, k, r)).1 := rfl

/-- `Program.binom n k` computes `Nat.choose n.get k.get` whenever `k.get ≤ n.get`.
PAPER: Interface/Pseudocode.lean:111-114 (the bridge obligation flagged beside `Pseudocode.mu0`).
BORROWED: the exact-division recurrence this follows, `Nat.add_one_mul_choose_eq`, is a
standard binomial identity, not argued in the paper. -/
theorem binom_val (n k : SNat) (h : k.get ≤ n.get) :
    (binom n k).val.get = Nat.choose n.get k.get := by
  unfold binom
  simp only [Charged.val_bind, SNat.val_index, SNat.get_lit]
  rw [Analysis.val_repeatFor']
  simp only [Charged.val_bind]
  generalize hnk : (SNat.sub n k).val = nk
  have hnkget : nk.get = n.get - k.get := by rw [← hnk]; exact SNat.get_sub n k
  have key : ∀ i, i ≤ k.get → ((List.range i).foldl
      (fun (b : SNat) (r : ℕ) => (SNat.div (SNat.mul b (SNat.add nk
        (SNat.lit (r+1)).val).val).val (SNat.lit (r+1)).val).val) (SNat.lit 1).val).get
      = Nat.choose (nk.get + i) i := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hprev := ih (by omega)
      simp only [SNat.get_div, SNat.get_mul, SNat.get_add, SNat.get_lit]
      rw [hprev]
      have hid := Nat.add_one_mul_choose_eq (nk.get + i) i
      have e1 : nk.get + (i + 1) = (nk.get + i) + 1 := by omega
      rw [e1]
      have e2 : (nk.get + i).choose i * (nk.get + i + 1) = (nk.get + i + 1).choose (i + 1) * (i + 1) := by
        rw [mul_comm]; exact hid
      rw [e2, Nat.mul_div_cancel _ (by omega : 0 < i + 1)]
  have hkk := key k.get le_rfl
  rw [hkk, hnkget]
  congr 1
  omega

/-- INTERNAL: reading the position just set in a `List Bool`. -/
theorem getD_set_self (l : List Bool) (i : ℕ) (v : Bool) (h : i < l.length) :
    (l.set i v).getD i false = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, if_pos rfl, if_pos h, Option.getD_some]

/-- INTERNAL: reading any other position of a `List Bool` after one write. -/
theorem getD_set_ne (l : List Bool) (i j : ℕ) (v : Bool) (h : j ≠ i) :
    (l.set i v).getD j false = l.getD j false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set, if_neg (Ne.symm h)]

/-- INTERNAL: the inner loop never changes the length of its `List Bool` state: every write
is a same-length `List.set`. -/
theorem mu0Inner_length (b : SNat) (first : ℕ) (k rank : SNat) (S0 : List Bool) (n : ℕ) :
    ((Charged.repeatFor (innerStep b first) n (S0, k, rank)).val.1).length = S0.length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [val_repeatFor', List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ← val_repeatFor']
    generalize hst : (Charged.repeatFor (innerStep b first) n (S0, k, rank)).val = st at ih
    unfold innerStep
    simp only [Charged.val_bind, Interface.SNat.val_lt, Interface.SNat.get_lit]
    by_cases h0 : 0 < st.2.1.get
    · simp only [h0, decide_true, if_true]
      by_cases hincl : st.2.2.get < (binom (b.sub (SNat.lit (n+1)).val).val
          (st.2.1.sub (SNat.lit 1).val).val).val.get
      · simp only [Charged.val_bind, Interface.SNat.val_lt, hincl, decide_true, if_true,
          Charged.val_pure, Interface.val_set, List.length_set]
        exact ih
      · simp only [Charged.val_bind, Interface.SNat.val_lt, hincl, decide_false,
          Bool.false_eq_true, if_false, Charged.val_pure, Interface.val_set, List.length_set]
        exact ih
    · simp only [h0, decide_false, Bool.false_eq_true, if_false, Charged.val_bind,
        Charged.val_pure, Interface.val_set, List.length_set]
      exact ih

/-- INTERNAL: the inner loop after `n` steps (`n ≤ b.get`) has touched only the positions
`[2 * first, 2 * (first + n))`; everywhere else it still reads as `S0`. -/
theorem mu0Inner_untouched (b : SNat) (first : ℕ) (k rank : SNat) (S0 : List Bool) (n : ℕ) :
    ∀ e, (e < 2 * first ∨ 2 * (first + n) ≤ e) →
      ((Charged.repeatFor (innerStep b first) n (S0, k, rank)).val.1).getD e false
        = S0.getD e false := by
  induction n with
  | zero => intro e _; rfl
  | succ n ih =>
    intro e he
    rw [val_repeatFor', List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ← val_repeatFor']
    generalize hst : (Charged.repeatFor (innerStep b first) n (S0, k, rank)).val = st
    have hst1 : st.1.getD e false = S0.getD e false := by
      rw [← hst]; exact ih e (by omega)
    unfold innerStep
    simp only [Charged.val_bind, Interface.SNat.val_lt, Interface.SNat.get_lit]
    have hne1 : e ≠ 2 * (first + n) := by omega
    have hne2 : e ≠ 2 * (first + n) + 1 := by omega
    by_cases h0 : 0 < st.2.1.get
    · simp only [h0, decide_true, if_true]
      by_cases hincl : st.2.2.get < (binom (b.sub (SNat.lit (n+1)).val).val
          (st.2.1.sub (SNat.lit 1).val).val).val.get
      · simp only [Charged.val_bind, Interface.SNat.val_lt, hincl, decide_true, if_true,
          Charged.val_pure, Interface.val_set]
        rw [getD_set_ne _ _ _ _ hne1]
        exact hst1
      · simp only [Charged.val_bind, Interface.SNat.val_lt, hincl, decide_false,
          Bool.false_eq_true, if_false, Charged.val_pure, Interface.val_set]
        rw [getD_set_ne _ _ _ _ hne2]
        exact hst1
    · simp only [h0, decide_false, Bool.false_eq_true, if_false, Charged.val_bind,
        Charged.val_pure, Interface.val_set]
      rw [getD_set_ne _ _ _ _ hne2]
      exact hst1

/-- INTERNAL: `unrankStep`'s own fold only ever inserts positions it has already visited. -/
theorem unrankFold_sub (b k r : ℕ) :
    ∀ n, ((List.range n).foldl (unrankStep b) (∅, k, r)).1 ⊆ Finset.range n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    unfold unrankStep
    split
    · split
      · intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · simp
        · exact Finset.mem_range.2 (by have := Finset.mem_range.1 (ih hx); omega)
      · intro x hx
        exact Finset.mem_range.2 (by have := Finset.mem_range.1 (ih hx); omega)
    · intro x hx
      exact Finset.mem_range.2 (by have := Finset.mem_range.1 (ih hx); omega)

/-- INTERNAL: the joint induction carrying `Program.mu0`'s inner loop and `Pseudocode.unrank`'s
own fold in lockstep for `n ≤ b.get` steps: the stored numeric pair agrees with `unrankStep`'s,
every already-decided bit matches its accumulated set, and the `remaining ≤ positions left`
invariant needed to keep calling `binom_val` at a valid argument persists.
PAPER: Interface/Pseudocode.lean:111-114 (the invariant named there, proved here). -/
theorem mu0Inner_main (b : SNat) (first : ℕ) (k rank : SNat) (S0 : List Bool)
    (hk : k.get ≤ b.get) (hr : rank.get < Nat.choose b.get k.get)
    (hlen : 2 * (first + b.get) ≤ S0.length) :
    ∀ n, n ≤ b.get →
      ((Charged.repeatFor (innerStep b first) n (S0, k, rank)).val.2.1.get =
          ((List.range n).foldl (unrankStep b.get) (∅, k.get, rank.get)).2.1 ∧
        (Charged.repeatFor (innerStep b first) n (S0, k, rank)).val.2.2.get =
          ((List.range n).foldl (unrankStep b.get) (∅, k.get, rank.get)).2.2) ∧
      (∀ i < n,
        (Charged.repeatFor (innerStep b first) n (S0, k, rank)).val.1.getD (2 * (first + i)) false =
          (if i ∈ ((List.range n).foldl (unrankStep b.get) (∅, k.get, rank.get)).1 then true
            else S0.getD (2 * (first + i)) false) ∧
        (Charged.repeatFor (innerStep b first) n (S0, k, rank)).val.1.getD (2 * (first + i) + 1) false =
          (if i ∈ ((List.range n).foldl (unrankStep b.get) (∅, k.get, rank.get)).1 then
            S0.getD (2 * (first + i) + 1) false else true)) ∧
      (((List.range n).foldl (unrankStep b.get) (∅, k.get, rank.get)).2.1 ≤ b.get - n ∧
        ((List.range n).foldl (unrankStep b.get) (∅, k.get, rank.get)).2.2 <
          Nat.choose (b.get - n) ((List.range n).foldl (unrankStep b.get) (∅, k.get, rank.get)).2.1) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨⟨rfl, rfl⟩, fun i hi => absurd hi (by omega), by simpa using hk, by simpa using hr⟩
  | succ n ih =>
    intro hn
    obtain ⟨⟨hv1, hv2⟩, hbits, hb1, hb2⟩ := ih (by omega)
    rw [val_repeatFor', List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ← val_repeatFor', List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hst : (Charged.repeatFor (innerStep b first) n (S0, k, rank)).val = st at hv1 hv2 hbits
    generalize hQ : (List.range n).foldl (unrankStep b.get) (∅, k.get, rank.get) = Q at hv1 hv2 hbits hb1 hb2
    have hQsub : Q.1 ⊆ Finset.range n := hQ ▸ unrankFold_sub b.get k.get rank.get n
    have hnQ : n ∉ Q.1 := fun h => absurd (Finset.mem_range.1 (hQsub h)) (by omega)
    unfold innerStep unrankStep
    simp only [Charged.val_bind, Interface.SNat.val_lt, Interface.SNat.get_lit, hv1]
    by_cases h0 : 0 < Q.2.1
    · simp only [h0, decide_true, if_true]
      have hk1 : (SNat.sub st.2.1 (SNat.lit 1).val).val.get ≤
          (SNat.sub b (SNat.lit (n+1)).val).val.get := by
        simp only [Interface.SNat.get_sub, Interface.SNat.get_lit, hv1]; omega
      have hc : (binom (SNat.sub b (SNat.lit (n+1)).val).val
          (SNat.sub st.2.1 (SNat.lit 1).val).val).val.get =
          Nat.choose (b.get - (n+1)) (Q.2.1 - 1) := by
        rw [binom_val _ _ hk1]
        simp only [Interface.SNat.get_sub, Interface.SNat.get_lit, hv1]
      by_cases hincl : Q.2.2 < Nat.choose (b.get - (n+1)) (Q.2.1 - 1)
      · simp only [hincl, if_true]
        have hincl' : st.2.2.get < (binom (SNat.sub b (SNat.lit (n+1)).val).val
            (SNat.sub st.2.1 (SNat.lit 1).val).val).val.get := by rw [hc, hv2]; exact hincl
        simp only [Charged.val_bind, Interface.SNat.val_lt, hincl', decide_true, if_true,
          Charged.val_pure]
        refine ⟨⟨?_, hv2⟩, ?_, ?_, ?_⟩
        · simp only [Interface.SNat.get_sub, Interface.SNat.get_lit, hv1]
        · intro i hi
          rw [Interface.val_set]
          have hlenst : st.1.length = S0.length := by
            rw [← hst]; exact mu0Inner_length b first k rank S0 n
          by_cases hie : i = n
          · subst hie
            refine ⟨?_, ?_⟩
            · rw [getD_set_self _ _ _ (by omega)]
              simp only [Finset.mem_insert, true_or, if_true]
            · rw [getD_set_ne _ _ _ _ (by omega : 2*(first+i)+1 ≠ 2*(first+i))]
              simp only [Finset.mem_insert, true_or, if_true]
              rw [← hst]
              exact mu0Inner_untouched b first k rank S0 i _ (by omega)
          · have hi' : i < n := by omega
            obtain ⟨b1, b2⟩ := hbits i hi'
            have hne1 : 2 * (first + i) ≠ 2 * (first + n) := by omega
            have hne2 : 2 * (first + i) + 1 ≠ 2 * (first + n) := by omega
            rw [getD_set_ne _ _ _ _ hne1, getD_set_ne _ _ _ _ hne2]
            refine ⟨?_, ?_⟩
            · rw [b1]; congr 1; simp [Finset.mem_insert]; tauto
            · rw [b2]; congr 1; simp [Finset.mem_insert]; tauto
        · omega
        · trivial
      · simp only [hincl, if_false]
        have hincl' : ¬ st.2.2.get < (binom (SNat.sub b (SNat.lit (n+1)).val).val
            (SNat.sub st.2.1 (SNat.lit 1).val).val).val.get := by rw [hc, hv2]; exact hincl
        simp only [Charged.val_bind, Interface.SNat.val_lt, hincl', decide_false,
          Bool.false_eq_true, if_false, Charged.val_pure]
        have hpascal : Nat.choose (b.get - n) Q.2.1 =
            Nat.choose (b.get - (n+1)) (Q.2.1 - 1) + Nat.choose (b.get - (n+1)) Q.2.1 := by
          have e1 : b.get - (n+1) + 1 = b.get - n := by omega
          have e2 : Q.2.1 - 1 + 1 = Q.2.1 := by omega
          have := Nat.choose_succ_succ' (b.get - (n+1)) (Q.2.1 - 1)
          rwa [e1, e2] at this
        have hQ1 : Q.2.1 ≤ b.get - (n + 1) := by
          rcases lt_or_eq_of_le hb1 with hlt | heq
          · omega
          · exfalso
            apply hincl
            have hc1 : Nat.choose (b.get - (n+1)) (Q.2.1 - 1) = 1 := by
              have e : b.get - (n+1) = Q.2.1 - 1 := by omega
              rw [e, Nat.choose_self]
            have hc2 : Nat.choose (b.get - n) Q.2.1 = 1 := by rw [← heq, Nat.choose_self]
            omega
        refine ⟨⟨hv1, ?hb⟩, ?hc, hQ1, ?hd2⟩
        case hb => simp only [Interface.SNat.get_sub, hv2, hc]
        case hd2 => omega
        case hc =>
          intro i hi
          rw [Interface.val_set]
          have hlenst : st.1.length = S0.length := by
            rw [← hst]; exact mu0Inner_length b first k rank S0 n
          by_cases hie : i = n
          · subst hie
            refine ⟨?_, ?_⟩
            · rw [getD_set_ne _ _ _ _ (by omega : 2*(first+i) ≠ 2*(first+i)+1)]
              rw [← hst]
              have := mu0Inner_untouched b first k rank S0 i _ (Or.inr (le_refl (2 * (first + i))))
              rw [if_neg hnQ]
              exact this
            · rw [getD_set_self _ _ _ (by omega), if_neg hnQ]
          · have hi' : i < n := by omega
            obtain ⟨b1, b2⟩ := hbits i hi'
            have hne1 : 2 * (first + i) ≠ 2 * (first + n) + 1 := by omega
            have hne2 : 2 * (first + i) + 1 ≠ 2 * (first + n) + 1 := by omega
            rw [getD_set_ne _ _ _ _ hne1, getD_set_ne _ _ _ _ hne2]
            exact ⟨b1, b2⟩
    · simp only [h0, decide_false, Bool.false_eq_true, if_false, Charged.val_bind,
        Charged.val_pure]
      have hQ0 : Q.2.1 = 0 := by omega
      refine ⟨⟨hv1, hv2⟩, ?_, by omega, ?_⟩
      · intro i hi
        rw [Interface.val_set]
        have hlenst : st.1.length = S0.length := by
          rw [← hst]; exact mu0Inner_length b first k rank S0 n
        by_cases hie : i = n
        · subst hie
          refine ⟨?_, ?_⟩
          · rw [getD_set_ne _ _ _ _ (by omega : 2*(first+i) ≠ 2*(first+i)+1)]
            rw [← hst]
            have := mu0Inner_untouched b first k rank S0 i _ (Or.inr (le_refl (2 * (first + i))))
            rw [if_neg hnQ]
            exact this
          · rw [getD_set_self _ _ _ (by omega), if_neg hnQ]
        · have hi' : i < n := by omega
          obtain ⟨b1, b2⟩ := hbits i hi'
          have hne1 : 2 * (first + i) ≠ 2 * (first + n) + 1 := by omega
          have hne2 : 2 * (first + i) + 1 ≠ 2 * (first + n) + 1 := by omega
          rw [getD_set_ne _ _ _ _ hne1, getD_set_ne _ _ _ _ hne2]
          exact ⟨b1, b2⟩
      · rw [hQ0, Nat.choose_zero_right]
        rw [hQ0, Nat.choose_zero_right] at hb2
        omega

/-- The inner unranking loop of `Program.mu0`, run for the full `b.get` steps, writes exactly
the bit pattern `Pseudocode.unrank` describes: for `t < b.get`, the row position `2 (first + t)`
is set iff `t` unranks into the sample, and the column position `2 (first + t) + 1` is set iff
it does not, with every other position unchanged from `S0`.
PAPER: Interface/Pseudocode.lean:111-114 (the bridge obligation flagged beside `Pseudocode.mu0`);
algorithm.tex:215-224 (the `μ₀` draw this loop implements). -/
theorem mu0Inner_eq (b : SNat) (first : ℕ) (k rank : SNat) (S0 : List Bool)
    (hk : k.get ≤ b.get) (hr : rank.get < Nat.choose b.get k.get)
    (hlen : 2 * (first + b.get) ≤ S0.length) :
    ∀ t < b.get,
      ((Charged.repeatFor (innerStep b first) b.get (S0, k, rank)).val.1).getD (2 * (first + t)) false =
        (if t ∈ Pseudocode.unrank b.get k.get rank.get then true else S0.getD (2 * (first + t)) false) ∧
      ((Charged.repeatFor (innerStep b first) b.get (S0, k, rank)).val.1).getD (2 * (first + t) + 1) false =
        (if t ∈ Pseudocode.unrank b.get k.get rank.get then S0.getD (2 * (first + t) + 1) false else true) := by
  intro t ht
  obtain ⟨-, hbits, -, -⟩ := mu0Inner_main b first k rank S0 hk hr hlen b.get le_rfl
  rw [unrank_eq_fold]
  exact hbits t ht

/-- A dyadic draw's value is strictly below its parameter `M`, on every tape, whenever
`M.get` is positive: `Y < 2 ^ k` is exact (`uniformBits_cost`), so `M.get * Y < M.get * 2 ^ k`.
TEXLINE: sections/evaluation.tex:356-371 -/
theorem dyadicDraw_lt (tape : Coins ℕ) (M : SNat) (ζ : SRat) (cur : ℕ) (hM : 0 < M.get) :
    (dyadicDraw tape M ζ cur).val.1.get < M.get := by
  unfold dyadicDraw clog2
  simp only [Charged.val_bind, Charged.val_pure, SNat.get_toRat, SRat.get_div, SRat.get_natCeil,
    SNat.get_lit, SNat.get_sub, SNat.get_size, SNat.val_index, SNat.get_mul, SNat.get_pow2,
    SNat.get_div]
  generalize hc : ⌈(M.get : ℚ) / ζ.get⌉₊ = c
  generalize hk : (c - 1).size = k
  obtain ⟨hY, -, -⟩ := uniformBits_cost tape k cur
  generalize (uniformBits tape k cur) = U at hY ⊢
  generalize (Charged.val U).1.get = Y at hY ⊢
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]
  exact (Nat.mul_lt_mul_left hM).2 hY


/-- The inner unranking loop, viewed as the `Finset` of positions it sets, is `S0`'s view
together with the one block `Mu0Law.blk first b.get (unrank b.get k.get rank.get)`: the
Finset-level form of `mu0Inner_eq` that `mu0_tape`'s per-cell step actually needs, matching
`Pseudocode.mu0`'s own `pure (S ∪ (Finset.range …).image …)` step.
PAPER: Interface/Pseudocode.lean:111-114; algorithm.tex:215-224. -/
theorem mu0Inner_blk (b : SNat) (first p : ℕ) (k rank : SNat) (S0 : List Bool)
    (hk : k.get ≤ b.get) (hr : rank.get < Nat.choose b.get k.get)
    (hlen : 2 * p ≤ S0.length) (hfb : first + b.get ≤ p) :
    (Finset.range (2 * p)).filter
        (fun e => ((Charged.repeatFor (innerStep b first) b.get (S0, k, rank)).val.1).getD e false = true)
      = (Finset.range (2 * p)).filter (fun e => S0.getD e false = true) ∪
        Mu0Law.blk first b.get (Pseudocode.unrank b.get k.get rank.get) := by
  have hlen' : 2 * (first + b.get) ≤ S0.length := by omega
  have heq := mu0Inner_eq b first k rank S0 hk hr hlen'
  ext e
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union]
  by_cases hrange : 2 * first ≤ e ∧ e < 2 * (first + b.get)
  · obtain ⟨h1, h2⟩ := hrange
    have he2p : e < 2 * p := by omega
    simp only [he2p, true_and]
    set t := (e - 2 * first) / 2 with ht_def
    have ht : t < b.get := by omega
    have hte : e = 2 * (first + t) ∨ e = 2 * (first + t) + 1 := by omega
    obtain ⟨heq1, heq2⟩ := heq t ht
    rcases hte with hte | hte
    · rw [hte, heq1, Mu0Law.mem_blk]
      constructor
      · intro h
        split at h
        · exact Or.inr ⟨t, ht, Or.inl ⟨by assumption, rfl⟩⟩
        · exact Or.inl h
      · rintro (h | ⟨t', ht', (⟨hU, he⟩ | ⟨hU, he⟩)⟩)
        · split
          · rfl
          · exact h
        · obtain rfl : t' = t := by omega
          split
          · rfl
          · contradiction
        · omega
    · rw [hte, heq2, Mu0Law.mem_blk]
      constructor
      · intro h
        split at h
        · exact Or.inl h
        · exact Or.inr ⟨t, ht, Or.inr ⟨by assumption, rfl⟩⟩
      · rintro (h | ⟨t', ht', (⟨hU, he⟩ | ⟨hU, he⟩)⟩)
        · split
          · exact h
          · rfl
        · omega
        · obtain rfl : t' = t := by omega
          split
          · contradiction
          · rfl
  · push_neg at hrange
    have hout : e < 2 * first ∨ 2 * (first + b.get) ≤ e := by
      by_cases h1 : e < 2 * first
      · exact Or.inl h1
      · exact Or.inr (hrange (by omega))
    rw [mu0Inner_untouched b first k rank S0 b.get e hout]
    constructor
    · intro h
      exact Or.inl h
    · rintro (h | hmem)
      · exact h
      · exact absurd (Mu0Law.blk_bounds hmem) (by omega)


end Cellcounting.Analysis
