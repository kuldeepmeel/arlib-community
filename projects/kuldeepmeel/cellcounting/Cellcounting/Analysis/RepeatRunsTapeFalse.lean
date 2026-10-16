import Cellcounting.Analysis.TapeWindow
import Cellcounting.Model.Program
import Cellcounting.Interface.Pseudocode
import Cellcounting.Interface.Encoding

/-!
# `repeatRuns_tape` is false as stated

`Interface/ProgramModel.lean` states `repeatRuns_tape`: if every run of `F`, from
any cursor, has the tape law "result `∼ G`, next bits fresh" (`hF`), then `R`
consecutive runs have the law of `R` independent copies of `G`.

That is false, because `hF` constrains the law of what `F` returns but not
*which* tape positions `F` reads.  The counterexample `flipBack` reads the bit
just **before** its start cursor (`cur - 1`) and returns cursor `max cur 1`.
Each single run satisfies `hF` with `G` uniform on `{0, 1}`: the bit it reads
is fair and lies before every bit it reports as unread.  But two consecutive
runs from cursor `0` both read bit `0`, so they always agree, and the output
`[0, 1]` has probability `0` instead of `1/4`.

The repair is a window hypothesis on `F`: every run reads only the bits between
its start and end cursors (`Cellcounting.Analysis.Window`, `TapeWindow.lean`).
Every concrete run of the program has one (`PhaseWindow.lean`).
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Cellcounting Arlib.Computation Cellcounting.Model.Operations

/-- INTERNAL: the counterexample run: read the bit before the cursor and report
cursor `max cur 1`. -/
noncomputable def flipBack (tape : Coins ℕ) (cur : ℕ) : Program.Prog (SRat × ℕ) := do
  let b ← Coins.flip (cur - 1) tape
  let z ← SRat.lit (if b then 1 else 0)
  pure (z, max cur 1)

/-- INTERNAL: the value of one `flipBack` run on the tape with heads `s`. -/
theorem flipBack_val (s : Finset ℕ) (cur : ℕ) :
    ((flipBack (Coins.ofFinset s) cur).val.1.get, (flipBack (Coins.ofFinset s) cur).val.2) =
      ((if cur - 1 ∈ s then 1 else 0 : ℚ), max cur 1) := by
  simp only [flipBack, Charged.val_bind, Charged.val_pure, Interface.val_flip_ofFinset,
    Interface.SRat.get_lit, decide_eq_true_eq]

/-- INTERNAL: the law the counterexample run satisfies `hF` with: uniform on `{0, 1}`. -/
noncomputable def flipBackLaw : PMF ℚ :=
  (tapeHeads 1).map fun q => if 0 ∈ q then 1 else 0

/-- INTERNAL: each single `flipBack` run, from any cursor, has the tape law `flipBackLaw`. -/
theorem flipBack_tape (cur n T : ℕ)
    (hT : ∀ s : Finset ℕ, (flipBack (Coins.ofFinset s) cur).val.2 + n ≤ T) :
    (tapeHeads T).map (fun s => ((flipBack (Coins.ofFinset s) cur).val.1.get,
        tapeRest s (flipBack (Coins.ofFinset s) cur).val.2 n)) =
      flipBackLaw.bind fun z => (tapeHeads n).map fun s' => (z, s') := by
  have hc : ∀ s, (flipBack (Coins.ofFinset s) cur).val.2 = max cur 1 := fun s =>
    congrArg Prod.snd (flipBack_val s cur)
  have hz : ∀ s, (flipBack (Coins.ofFinset s) cur).val.1.get = if cur - 1 ∈ s then 1 else 0 :=
    fun s => congrArg Prod.fst (flipBack_val s cur)
  have hT' : max cur 1 + n ≤ T := by have := hT ∅; rwa [hc] at this
  have hfun : (fun s => ((flipBack (Coins.ofFinset s) cur).val.1.get,
        tapeRest s (flipBack (Coins.ofFinset s) cur).val.2 n)) =
      fun s => (fun (x : Bool) (t : Finset ℕ) => ((if x then 1 else 0 : ℚ), tapeRest t (max cur 1) n))
        (decide (cur - 1 ∈ s)) s := by
    funext s; rw [hz, hc]; by_cases h : cur - 1 ∈ s <;> simp [h]
  rw [hfun, tapeHeads_split T (fun s => decide (cur - 1 ∈ s)) (fun _ => max cur 1) ?_
    (fun (x : Bool) (t : Finset ℕ) => ((if x then 1 else 0 : ℚ), tapeRest t (max cur 1) n)) ?_]
  · have hg : (tapeHeads T).map (fun s => decide (cur - 1 ∈ s)) =
        (tapeHeads 1).map (fun q => decide (0 ∈ q)) := by
      rw [← tapeHeads_rest T (cur - 1) 1 (by omega), PMF.map_comp]
      congr 1
      funext s
      show decide (cur - 1 ∈ s) = decide (0 ∈ tapeRest s (cur - 1) 1)
      unfold tapeRest
      apply decide_eq_decide.2
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · intro h; exact ⟨⟨cur - 1, ⟨h, le_rfl⟩, Nat.sub_self _⟩, Nat.one_pos⟩
      · rintro ⟨⟨i, ⟨hi, hi'⟩, hi0⟩, -⟩
        have : i = cur - 1 := by omega
        rwa [this] at hi
    have hk : ∀ x : Bool, (tapeHeads T).map
        (fun t => ((if x then 1 else 0 : ℚ), tapeRest t (max cur 1) n)) =
        (tapeHeads n).map fun s' => ((if x then 1 else 0 : ℚ), s') := by
      intro x
      rw [← tapeHeads_rest T (max cur 1) n hT', PMF.map_comp]
      rfl
    simp only [hk]
    rw [hg, flipBackLaw, PMF.bind_map, PMF.bind_map]
    congr 1
    funext q
    simp only [Function.comp_apply]
    by_cases h : 0 ∈ q <;> simp [h]
  · intro s s' h
    have := h (cur - 1) (by show cur - 1 < max cur 1; omega)
    exact decide_eq_decide.2 this.symm
  · intro s₀ t t' h
    show (_, tapeRest t (max cur 1) n) = (_, tapeRest t' (max cur 1) n)
    rw [tapeRest_congr t t' (max cur 1) n h]

/-- INTERNAL: `repeatRuns_tape` of `Interface/ProgramModel.lean` is false: a run that
re-reads an already-read bit satisfies its hypothesis `hF`, and two such runs are not
independent. TEXLINE: sections/algorithm.tex:670-690 -/
theorem repeatRuns_tape_false : ¬ (∀ (F : Arlib.Computation.Coins ℕ → ℕ → Cellcounting.Program.Prog (Cellcounting.Model.Operations.SRat × ℕ)) (G : PMF ℚ), (∀ cur n T : ℕ, (∀ s : Finset ℕ, (F (Arlib.Computation.Coins.ofFinset s) cur).val.2 + n ≤ T) → (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (F (Arlib.Computation.Coins.ofFinset s) cur).val; (r.1.get, ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) = G.bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s')))) → ∀ (R cur n T : ℕ), (∀ s : Finset ℕ, (Arlib.Computation.Charged.repeatFor (fun _ (st : List Cellcounting.Model.Operations.SRat × ℕ) => ((do let (z, c') ← F (Arlib.Computation.Coins.ofFinset s) st.2; let outs ← Cellcounting.Model.Operations.push st.1 z; pure (outs, c')) : Cellcounting.Program.Prog (List Cellcounting.Model.Operations.SRat × ℕ))) R ([], cur)).val.2 + n ≤ T) → (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (Arlib.Computation.Charged.repeatFor (fun _ (st : List Cellcounting.Model.Operations.SRat × ℕ) => ((do let (z, c') ← F (Arlib.Computation.Coins.ofFinset s) st.2; let outs ← Cellcounting.Model.Operations.push st.1 z; pure (outs, c')) : Cellcounting.Program.Prog (List Cellcounting.Model.Operations.SRat × ℕ))) R ([], cur)).val; (r.1.map Cellcounting.Model.Operations.SRat.get, ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) = (Cellcounting.Pseudocode.repeatRuns R G).bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s')))) := by
  intro H
  have h2 := H flipBack flipBackLaw (fun cur n T hT => flipBack_tape cur n T hT) 2 0 0 2 (by
    intro s
    simp [Charged.repeatFor, List.range_succ, flipBack])
  have hU1 : ∀ q : Finset ℕ, q ⊆ Finset.range 1 → q ∈ (tapeHeads 1).support := by
    intro q hq
    rw [PMF.mem_support_iff, tapeHeads_apply, if_pos hq]
    simp
  have hG0 : (0 : ℚ) ∈ flipBackLaw.support :=
    (PMF.mem_support_map_iff _ _ _).2 ⟨∅, hU1 ∅ (Finset.empty_subset _), by simp⟩
  have hG1 : (1 : ℚ) ∈ flipBackLaw.support :=
    (PMF.mem_support_map_iff _ _ _).2 ⟨{0}, hU1 {0} (by simp), by simp⟩
  have hR : (([0, 1] : List ℚ), (∅ : Finset ℕ)) ∈
      ((Pseudocode.repeatRuns 2 flipBackLaw).bind fun z =>
        (tapeHeads 0).map fun s' => (z, s')).support := by
    rw [PMF.mem_support_bind_iff]
    refine ⟨[0, 1], ?_, ?_⟩
    · show [0, 1] ∈ (((flipBackLaw.map fun z => [] ++ [z]).bind fun l =>
          (flipBackLaw.map fun z => l ++ [z]).bind PMF.pure)).support
      rw [PMF.mem_support_bind_iff]
      refine ⟨[0], (PMF.mem_support_map_iff _ _ _).2 ⟨0, hG0, rfl⟩, ?_⟩
      rw [PMF.bind_pure]
      exact (PMF.mem_support_map_iff _ _ _).2 ⟨1, hG1, rfl⟩
    · rw [PMF.mem_support_map_iff]
      exact ⟨∅, by simp [tapeHeads], rfl⟩
  rw [← h2, PMF.mem_support_map_iff] at hR
  obtain ⟨s, -, hs⟩ := hR
  have := congrArg Prod.fst hs
  by_cases h0 : 0 ∈ s <;> simp [Charged.repeatFor, List.range_succ, flipBack, h0] at this

end Cellcounting.Analysis
