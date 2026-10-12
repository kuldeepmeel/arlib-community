import Esa22Copy.Meta.ModelClosure
import Mathlib.Data.Real.ENatENNReal
import Esa22Copy.Model.Prior
import Esa22Copy.Model.Run
import Esa22Copy.Interface.Encoding
import Esa22Copy.Interface.Pseudocode
import Esa22Copy.Interface.ProgramModel

/-!
# Space: the sample set never exceeds `thresh`

The paper's space argument (esa22-final.tex:507): "the size of the set of samples
kept by the algorithm is always `≤ thresh`".  Here it is proved for *every* tape,
not only those in the support, by an invariant on the charged program
`Esa22Copy.Program.estimate`:

* from a state with `|𝒳| < thr`, the drop-then-pick of one iteration ends at
  `|𝒳'| ≤ |𝒳| + 1 ≤ thr` and never rises above its end point (the erase comes
  first);
* if `|𝒳'| = thr` the throw only deletes, and the iteration either outputs `⊥`
  (after which nothing is held or charged) or leaves `|𝒳''| ≠ thr`, hence `< thr`;
* otherwise `|𝒳'| ≠ thr`, hence `< thr`.

So the high-water mark of `Cell.roster` over a run is at most `thr`, given
`0 < thr`, which holds for the paper's `thresh ε δ m` whenever `m ≥ 1`
(and the empty stream holds nothing).  The equality tests are what the
invariant uses; no `≥` test is substituted.
-/

namespace Esa22Copy.Analysis.SpaceProof

open Arlib.Computation (Block Coins Roster Sampler Charged Profile)
open Esa22Copy.Model.Operations (Op Cell)

variable {α : Type} [DecidableEq α] {w : ℕ}

/-- INTERNAL: what one `Roster.insert` holds: the cardinality change, as net and as peak,
and that it adds at most one element.
TEXLINE: esa22-final.tex:507 -/
theorem roster_insert_space (a : α) (d : Roster α) :
    (Roster.insert (κ := Op) (κₛ := Cell) a d).space.net Arlib.Computation.Cell.roster
        = ((Roster.insert (κ := Op) (κₛ := Cell) a d).val.card : ℤ) - d.card ∧
    (Roster.insert (κ := Op) (κₛ := Cell) a d).space.peak Arlib.Computation.Cell.roster
        = max 0 (((Roster.insert (κ := Op) (κₛ := Cell) a d).val.card : ℤ) - d.card) ∧
    (Roster.insert (κ := Op) (κₛ := Cell) a d).val.card ≤ d.card + 1 := by
  have hN := Roster.space_net_insert (κ := Op) a d Arlib.Computation.Cell.roster
  have hP := Roster.space_peak_insert (κ := Op) a d Arlib.Computation.Cell.roster
  simp only [Roster.cell, Esa22Copy.Interface.rosterCells_cell, if_true] at hN hP
  rw [← Roster.toFinset_insert (κ := Op) (κₛ := Cell), Roster.card_toFinset,
    Roster.card_toFinset] at hN hP
  refine ⟨hN, hP, ?_⟩
  rw [← Roster.card_toFinset, ← Roster.card_toFinset, Roster.toFinset_insert]
  exact Finset.card_insert_le _ _

/-- INTERNAL: lines afinal-drop and afinal-pick together end exactly `|𝒳'| - |𝒳|` cells
above where they started, never rise higher than that (the erase comes first), and
grow `𝒳` by at most one.
TEXLINE: esa22-final.tex:430-431, 507 -/
theorem arrival_space (a : α) (blk : Block w) (st : Esa22Copy.Program.State α) :
    (Esa22Copy.Program.arrival a blk st).space.net Arlib.Computation.Cell.roster
        = ((Esa22Copy.Program.arrival a blk st).val.card : ℤ) - st.samples.card ∧
    (Esa22Copy.Program.arrival a blk st).space.peak Arlib.Computation.Cell.roster
        = max 0 (((Esa22Copy.Program.arrival a blk st).val.card : ℤ) - st.samples.card) ∧
    (Esa22Copy.Program.arrival a blk st).val.card ≤ st.samples.card + 1 := by
  unfold Esa22Copy.Program.arrival
  have hE := Roster.space_net_erase (κ := Op) a st.samples Arlib.Computation.Cell.roster
  have hEp := Roster.space_peak_erase (κ := Op) (κₛ := Cell) a st.samples Arlib.Computation.Cell.roster
  simp only [Roster.cell, Esa22Copy.Interface.rosterCells_cell, if_true] at hE
  rw [← Roster.toFinset_erase (κ := Op) (κₛ := Cell), Roster.card_toFinset, Roster.card_toFinset] at hE
  have hEle := (Roster.erase (κ := Op) (κₛ := Cell) a st.samples).space.net_le_peak Arlib.Computation.Cell.roster
  cases h : (Sampler.accept (κ := Op) (κₛ := Cell) blk st.sampler).val
  · simp only [Charged.space_bind, Charged.val_bind, h, Profile.net_mul, Profile.peak_mul,
      Sampler.space_accept, Profile.net_one, Profile.peak_one, Bool.false_eq_true, if_false,
      Charged.space_pure, Charged.val_pure]
    omega
  · simp only [Charged.space_bind, Charged.val_bind, h, Profile.net_mul, Profile.peak_mul,
      Sampler.space_accept, Profile.net_one, Profile.peak_one, if_true]
    obtain ⟨h1, h2, h3⟩ := roster_insert_space a (Roster.erase (κ := Op) (κₛ := Cell) a st.samples).val
    rw [h1, h2]
    omega

/-- INTERNAL: line final-throw only deletes: peak `0`, net the change in cardinality,
and it never grows `𝒳`.
TEXLINE: esa22-final.tex:433, 507 -/
theorem thin_space (coins : Coins α) (X : Roster α) :
    (Esa22Copy.Program.thin coins X).space.peak Arlib.Computation.Cell.roster = 0 ∧
    (Esa22Copy.Program.thin coins X).space.net Arlib.Computation.Cell.roster
        = ((Esa22Copy.Program.thin coins X).val.card : ℤ) - X.card ∧
    (Esa22Copy.Program.thin coins X).val.card ≤ X.card := by
  unfold Esa22Copy.Program.thin
  refine ⟨?_, ?_, ?_⟩
  · exact Roster.space_peak_filterErase _ (fun x k => by simp) X _
  · have h := Roster.space_net_filterErase (κ := Op) (κₛ := Cell)
      (fun x => Coins.flip x coins) (fun x => Coins.space_flip x coins) X
      Arlib.Computation.Cell.roster
    simp only [Roster.cell, Esa22Copy.Interface.rosterCells_cell, if_true] at h
    exact h
  · rw [← Roster.card_toFinset, ← Roster.card_toFinset, Roster.toFinset_filterErase]
    exact Finset.card_filter_le _ _

/-- INTERNAL: one loop iteration started from `|𝒳| < thr` never holds more than `thr`
cells, and if it does not output `⊥` it leaves `|𝒳| < thr` with its net exactly
accounted for.  This is the paper's "`|𝒳| ≤ thresh` always" for one iteration.
TEXLINE: esa22-final.tex:428-442, 507 -/
theorem step_space (thr : ℕ) (st : Esa22Copy.Program.State α)
    (ar : α × Esa22Copy.Program.Randomness α w) (hc : st.samples.card < thr) :
    (st.samples.card : ℤ)
        + (Esa22Copy.Program.step thr (some st) ar).space.peak Arlib.Computation.Cell.roster ≤ thr ∧
    ∀ st', (Esa22Copy.Program.step thr (some st) ar).val = some st' →
      st'.samples.card < thr ∧
      (st.samples.card : ℤ)
        + (Esa22Copy.Program.step thr (some st) ar).space.net Arlib.Computation.Cell.roster
          ≤ st'.samples.card := by
  obtain ⟨a1, a2, a3⟩ := arrival_space ar.1 ar.2.bits st
  simp only [Esa22Copy.Program.step]
  set X := (Esa22Copy.Program.arrival ar.1 ar.2.bits st)
  simp only [Charged.space_bind, Charged.val_bind, Roster.val_cardEq, Roster.space_cardEq,
    Profile.net_mul, Profile.peak_mul, Profile.net_one, Profile.peak_one]
  have hXn := X.space.net_le_peak Arlib.Computation.Cell.roster
  by_cases hf : X.val.card = thr
  · obtain ⟨t1, t2, t3⟩ := thin_space ar.2.coins X.val
    simp only [hf, decide_true, if_true, Charged.space_bind, Charged.val_bind,
      Roster.val_cardEq, Roster.space_cardEq, Sampler.space_halve, Profile.net_mul,
      Profile.peak_mul, Profile.net_one, Profile.peak_one, t1]
    by_cases ht : (Esa22Copy.Program.thin ar.2.coins X.val).val.card = thr
    · simp only [ht, decide_true, if_true, Charged.space_pure, Charged.val_pure,
        Profile.net_one, Profile.peak_one, reduceCtorEq, false_imp_iff, imp_true_iff, and_true]
      omega
    · simp only [ht, decide_false, Bool.false_eq_true, if_false, Charged.space_pure,
        Charged.val_pure, Profile.net_one, Profile.peak_one, Option.some.injEq]
      refine ⟨by omega, ?_⟩
      rintro st' rfl
      refine ⟨by simp only; omega, ?_⟩
      simp only
      omega
  · simp only [hf, decide_false, Bool.false_eq_true, if_false, Charged.space_pure,
      Charged.val_pure, Profile.net_one, Profile.peak_one, Option.some.injEq]
    refine ⟨by omega, ?_⟩
    rintro st' rfl
    refine ⟨by simp only; omega, ?_⟩
    simp only
    omega

/-- INTERNAL: after `⊥` the loop holds nothing.
TEXLINE: esa22-final.tex:437 -/
theorem foldl_none_peak (thr : ℕ) :
    ∀ l : List (α × Esa22Copy.Program.Randomness α w),
      (Charged.foldl (Esa22Copy.Program.step thr) l none).space.peak
        Arlib.Computation.Cell.roster = 0 := by
  intro l
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [Charged.space_foldl_cons, Profile.peak_mul]
      have h : Esa22Copy.Program.step thr (none : Option (Esa22Copy.Program.State α)) x
          = pure none := rfl
      rw [h, Charged.val_pure, ih, Charged.space_pure]
      simp

/-- INTERNAL: the whole loop, started from `|𝒳| < thr`, never holds more than `thr`
cells, whatever the tape.
TEXLINE: esa22-final.tex:507 -/
theorem foldl_space (thr : ℕ) :
    ∀ (l : List (α × Esa22Copy.Program.Randomness α w)) (st : Esa22Copy.Program.State α),
      st.samples.card < thr →
      (st.samples.card : ℤ) + (Charged.foldl (Esa22Copy.Program.step thr) l (some st)).space.peak
        Arlib.Computation.Cell.roster ≤ thr := by
  intro l
  induction l with
  | nil => intro st hc; simp; omega
  | cons x l ih =>
      intro st hc
      obtain ⟨h1, h2⟩ := step_space thr st x hc
      have hn := (Esa22Copy.Program.step thr (some st) x).space.net_le_peak
        Arlib.Computation.Cell.roster
      simp only [Charged.space_foldl_cons, Profile.peak_mul]
      cases hv : (Esa22Copy.Program.step thr (some st) x).val with
      | none => rw [foldl_none_peak]; omega
      | some st' =>
          obtain ⟨h3, h4⟩ := h2 st' hv
          have := ih st' h3
          omega

/-- INTERNAL: Algorithm 1 with any threshold `thr > 0`, on any stream and any tape,
never holds more than `thr` roster cells.
TEXLINE: esa22-final.tex:507 -/
theorem estimate_peak_le (thr : ℕ) (hthr : 0 < thr) (s : List α)
    (t : List (Esa22Copy.Program.Randomness α w)) :
    (Esa22Copy.Program.estimate thr s t).space.peak Arlib.Computation.Cell.roster ≤ thr := by
  have hF := foldl_space thr (s.zip t) Esa22Copy.Program.initial (by
    simpa [Esa22Copy.Program.initial] using hthr)
  simp only [Esa22Copy.Program.initial, Roster.card_empty] at hF
  have hR : ∀ acc : Option (Esa22Copy.Program.State α),
      (Esa22Copy.Program.report acc).space.peak Arlib.Computation.Cell.roster = 0 := by
    intro acc
    cases acc with
    | none => rfl
    | some st =>
        simp [Esa22Copy.Program.report]
  unfold Esa22Copy.Program.estimate
  simp only [Charged.space_bind, Profile.peak_mul, hR]
  have := (Charged.foldl (Esa22Copy.Program.step thr) (s.zip t)
    (some Esa22Copy.Program.initial)).space.net_le_peak Arlib.Computation.Cell.roster
  simp only [Esa22Copy.Program.initial] at this ⊢
  omega

/-- INTERNAL: the paper's threshold is positive on a nonempty stream, which is what
lets the empty initial sample lie strictly below it.
TEXLINE: esa22-final.tex:425 -/
theorem thresh_pos {ε δ : ℝ} (hε0 : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1) {m : ℕ} (hm : 1 ≤ m) :
    0 < Esa22Copy.thresh ε δ m := by
  unfold Esa22Copy.thresh
  apply Nat.ceil_pos.mpr
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h8 : 1 < 8 * (m : ℝ) / δ := by
    rw [lt_div_iff₀ hδ0]; nlinarith
  have hl : 0 < Real.logb 2 (8 * (m : ℝ) / δ) := Real.logb_pos (by norm_num) h8
  positivity

end Esa22Copy.Analysis.SpaceProof

section
open scoped ENNReal

/-- Proof-side owner for `Esa22Copy.esa22copy_space`; its statement is fixed by the proof charter.
PAPER: esa22-final.tex:507 -/
theorem Esa22Copy.Analysis.space_proof (hprior : Prior) {n : ℕ} (s : List (Fin n)) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) : Arlib.Computation.worstSpace Arlib.Computation.Cell.roster 0 (Esa22Copy.run ε δ s) ≤ (Esa22Copy.thresh ε δ s.length : ℕ∞) := by
  apply Arlib.Computation.worstSpace_le
  intro p hp
  unfold Esa22Copy.run at hp
  rw [PMF.support_map] at hp
  obtain ⟨t, -, rfl⟩ := hp
  rcases Nat.eq_zero_or_pos s.length with h0 | h0
  · have hz : s.zip t = [] := List.zip_eq_nil_iff.mpr (Or.inl (List.length_eq_zero_iff.mp h0))
    unfold Esa22Copy.Program.estimate
    rw [hz]
    simp [Esa22Copy.Program.report, Esa22Copy.Program.initial]
  · have := Esa22Copy.Analysis.SpaceProof.estimate_peak_le _ (Esa22Copy.Analysis.SpaceProof.thresh_pos hε0 hδ0 hδ1 h0) s t
    push_cast
    omega

end

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `space_proof` closed by the `|𝒳| < thr` step invariant; no new files
-/
