import Esa22Copy.Model.Program
import Esa22Copy.Interface.Pseudocode
import Esa22Copy.Interface.Encoding
import Esa22Copy.Model.Prior
import Esa22Copy.Model.Prelude
import Esa22Copy.Model.Operations
import Esa22Copy.Model.Run
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

/-!
# The program and the model are the same algorithm

`Esa22Copy.Model.Program` is what the paper's claims are about: a charged
computation whose state is sealed and whose cost is an operator applied to it.
`Esa22Copy.Interface.Pseudocode` is the same algorithm as mathematics for the
answer/output object the correctness theorem measures. Time and space stay over
`Esa22Copy.Model.Program`; this file is only the transport for correctness.

It is a ladder. Each theorem below is proved from the ones above it, and
`output_bridge` is the top: it is the one lemma the analysis rewrites
through, and the only one anything outside this file should need.

## Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · every rung closed: `cardEq_full`, `arrival_toFinset`, `pick_law`,
  `thin_law`, `step_view`, `loop_view`, `loop_initial_view`, `report_view`,
  `estimate_val`, `estimate_law`, `output_bridge`.
-/

set_option autoImplicit false

namespace Esa22Copy

/-- The charged size test on the roster (lines Ifbegin and check) returns the same Boolean as the pseudocode's `full` test on the underlying finset.

INTERNAL: bridge between the program's charged test and the pseudocode's `Finset`-level test; the paper states no such lemma.
TEXLINE: esa22-final.tex:436, esa22-final.tex:440 -/
theorem cardEq_full {n : ℕ} (thr : ℕ) (X : Arlib.Computation.Roster (Fin n)) : (Arlib.Computation.Roster.cardEq thr X : Arlib.Computation.Charged Esa22Copy.Model.Operations.Op Esa22Copy.Model.Operations.Cell Bool).val = Esa22Copy.Interface.Pseudocode.full thr X.toFinset := by
  simp [Esa22Copy.Interface.Pseudocode.full]

/-- Pointwise in the coin block, the program's arrival step (lines afinal-drop and afinal-pick) drops a_i and reinserts it exactly when the block accepts at the current level.

INTERNAL: bridge between the program's `arrival` and the pseudocode's `drop`/`insert`; the paper states no such lemma.
TEXLINE: esa22-final.tex:425-426 -/
theorem arrival_toFinset {n w : ℕ} (a : Fin n) (f : Fin w → Bool) (st : Esa22Copy.Program.State (Fin n)) : (Esa22Copy.Program.arrival a (Arlib.Computation.Block.ofFun f) st).val.toFinset = if Esa22Copy.Interface.acceptsAt (Esa22Copy.Interface.view st).level (Arlib.Computation.Block.ofFun f) then insert a (Esa22Copy.Interface.Pseudocode.drop a (Esa22Copy.Interface.view st).sample) else Esa22Copy.Interface.Pseudocode.drop a (Esa22Copy.Interface.view st).sample := by
  rw [Esa22Copy.Interface.view_level]
  rw [← Esa22Copy.Interface.val_accept_eq (κ := Esa22Copy.Model.Operations.Op)
    (κₛ := Esa22Copy.Model.Operations.Cell) (Arlib.Computation.Block.ofFun f) st.sampler]
  unfold Esa22Copy.Program.arrival
  rw [Esa22Copy.Interface.Pseudocode.drop, Esa22Copy.Interface.view_sample]
  by_cases hpicked : (Arlib.Computation.Sampler.accept (Arlib.Computation.Block.ofFun f) st.sampler :
      Arlib.Computation.Charged Esa22Copy.Model.Operations.Op Esa22Copy.Model.Operations.Cell Bool).val
  · simp [hpicked]
  · simp [hpicked]

/-- Pushing uniform coin blocks through the arrival step gives the pseudocode's 'insert with probability p' distribution.

INTERNAL: bridge between the program's `arrival` under a uniform block and the pseudocode's `pick`; the paper states no such lemma.
TEXLINE: esa22-final.tex:426 -/
theorem pick_law {n w : ℕ} (a : Fin n) (st : Esa22Copy.Program.State (Fin n)) : (PMF.uniformOfFintype (Fin w → Bool)).map (fun f => (Esa22Copy.Program.arrival a (Arlib.Computation.Block.ofFun f) st).val.toFinset) = Esa22Copy.Interface.Pseudocode.pick w (Esa22Copy.Interface.view st).level a (Esa22Copy.Interface.Pseudocode.drop a (Esa22Copy.Interface.view st).sample) := by
  unfold Esa22Copy.Interface.Pseudocode.pick
  congr 1
  funext f
  exact arrival_toFinset a f st

/-- Thinning the roster with a uniform random subset as coins has the law of the pseudocode's line final-throw (each element kept independently with probability 1/2).

INTERNAL: bridge between the program's `thin` under a uniform coin subset and the pseudocode's `throw`; the paper states no such lemma.
TEXLINE: esa22-final.tex:428 -/
theorem thin_law {n : ℕ} (X : Arlib.Computation.Roster (Fin n)) : (PMF.uniformOfFintype (Finset (Fin n))).map (fun S => (Esa22Copy.Program.thin (Arlib.Computation.Coins.ofFinset S) X).val.toFinset) = Esa22Copy.Interface.Pseudocode.throw X.toFinset := by
  unfold Esa22Copy.Interface.Pseudocode.throw
  congr 1
  funext S
  unfold Esa22Copy.Program.thin
  rw [Arlib.Computation.Roster.toFinset_filterErase]
  simp only [Arlib.Computation.Coins.val_flip, Arlib.Computation.Coins.heads'_ofFinset]
  congr 1
  funext x
  exact decide_eq_true_eq

/-- One loop iteration: under the per-element randomness law, the viewed program step has the law of the pseudocode step.

INTERNAL: bridge between one iteration of the program's `step` and the pseudocode's `step`; the paper states no such lemma.
TEXLINE: esa22-final.tex:422-445 -/
theorem step_view {n w : ℕ} (thr : ℕ) (acc : Option (Esa22Copy.Program.State (Fin n))) (a : Fin n) : (Esa22Copy.cellLaw n w).map (fun c => Option.map Esa22Copy.Interface.view (Esa22Copy.Program.step thr acc (a, c)).val) = Esa22Copy.Interface.Pseudocode.step thr w (Option.map Esa22Copy.Interface.view acc) a := by
  cases acc with
  | none =>
      simp only [Esa22Copy.Interface.step_none, Esa22Copy.Interface.Pseudocode.step,
        Option.map_none, PMF.map, Function.comp_def, PMF.bind_const,
        Arlib.Computation.Charged.val_pure]
  | some st =>
      show (Esa22Copy.cellLaw n w).map
            (fun c => Option.map Esa22Copy.Interface.view
              (Esa22Copy.Program.step thr (some st) (a, c)).val)
          = Esa22Copy.Interface.Pseudocode.step thr w (some (Esa22Copy.Interface.view st)) a
      simp only [Esa22Copy.cellLaw, Esa22Copy.Interface.Pseudocode.step,
        Esa22Copy.Interface.Pseudocode.pick]
      rw [PMF.map_bind, PMF.bind_map]
      congr 1
      funext f
      rw [PMF.map_comp]
      simp only [Function.comp_apply]
      rw [← Esa22Copy.arrival_toFinset a f st]
      generalize hX : (Esa22Copy.Program.arrival a (Arlib.Computation.Block.ofFun f) st).val = X
      by_cases hfull : Esa22Copy.Interface.Pseudocode.full thr X.toFinset = true
      · rw [if_pos hfull]
        unfold Esa22Copy.Interface.Pseudocode.throw
        rw [PMF.map_comp]
        congr 1
        funext S
        have hthin : (Esa22Copy.Program.thin (Arlib.Computation.Coins.ofFinset S) X).val.toFinset
            = X.toFinset.filter (· ∈ S) := by
          unfold Esa22Copy.Program.thin
          rw [Arlib.Computation.Roster.toFinset_filterErase]
          simp only [Arlib.Computation.Coins.val_flip, Arlib.Computation.Coins.heads'_ofFinset]
          congr 1
          funext x
          exact decide_eq_true_eq
        have hfull' : (Arlib.Computation.Roster.cardEq thr X :
            Arlib.Computation.Charged Esa22Copy.Model.Operations.Op
              Esa22Copy.Model.Operations.Cell Bool).val = true := by
          rw [Esa22Copy.cardEq_full]; exact hfull
        simp only [Function.comp_apply, Esa22Copy.Program.step,
          Arlib.Computation.Charged.val_bind]
        rw [hX, if_pos hfull']
        rw [← hthin, ← Esa22Copy.cardEq_full thr
          (Esa22Copy.Program.thin (Arlib.Computation.Coins.ofFinset S) X).val]
        split_ifs with h2
        · simp [h2]
        · simp [h2, Esa22Copy.Interface.view, hthin, Esa22Copy.Interface.Pseudocode.halve]
      · rw [if_neg hfull]
        have hconst : ((fun c => Option.map Esa22Copy.Interface.view
              (Esa22Copy.Program.step thr (some st) (a, c)).val) ∘
            fun S => (⟨Arlib.Computation.Block.ofFun f, Arlib.Computation.Coins.ofFinset S⟩ :
              Esa22Copy.Program.Randomness (Fin n) w))
            = Function.const (Finset (Fin n))
              (some ⟨X.toFinset, (Esa22Copy.Interface.view st).level⟩) := by
          funext S
          have hcard : ¬ X.card = thr := by
            intro h
            exact hfull (by simp [Esa22Copy.Interface.Pseudocode.full,
              Arlib.Computation.Roster.card_toFinset, h])
          simp only [Function.comp_apply, Esa22Copy.Program.step,
            Arlib.Computation.Charged.val_bind]
          rw [hX]
          simp [hcard, Esa22Copy.Interface.view]
        rw [hconst, PMF.map_const]

/-- Induction on the stream, generalising over the accumulator: the folded program has the law of the pseudocode loop from any starting state.

INTERNAL: bridge between the program's folded `step` and the pseudocode's `loop`, by induction on the stream; the paper states no such lemma.
TEXLINE: esa22-final.tex:422-445 -/
theorem loop_view {n w : ℕ} (thr : ℕ) (s : List (Fin n)) (acc : Option (Esa22Copy.Program.State (Fin n))) : (Esa22Copy.tape n w s.length).map (fun t => Option.map Esa22Copy.Interface.view (Arlib.Computation.Charged.foldl (Esa22Copy.Program.step thr) (s.zip t) acc).val) = Esa22Copy.Interface.Pseudocode.loop thr w s (Option.map Esa22Copy.Interface.view acc) := by
  induction s generalizing acc with
  | nil =>
      simp [Esa22Copy.tape, Esa22Copy.Interface.Pseudocode.loop, PMF.pure_map]
  | cons a s' ih =>
      show (Esa22Copy.tape n w (s'.length + 1)).map
            (fun t => Option.map Esa22Copy.Interface.view
              (Arlib.Computation.Charged.foldl (Esa22Copy.Program.step thr) ((a :: s').zip t) acc).val)
          = Esa22Copy.Interface.Pseudocode.loop thr w (a :: s') (Option.map Esa22Copy.Interface.view acc)
      rw [Esa22Copy.Interface.Pseudocode.loop, ← Esa22Copy.step_view thr acc a, PMF.bind_map]
      simp only [Esa22Copy.tape]
      rw [PMF.map_bind]
      congr 1
      funext c
      rw [PMF.map_comp]
      exact ih (Esa22Copy.Program.step thr acc (a, c)).val

/-- Specialisation of loop_view to the initial state p = 1, X = ∅.

INTERNAL: specialisation of `loop_view` to Algorithm 1's initial state; the paper states no such lemma.
TEXLINE: esa22-final.tex:423 -/
theorem loop_initial_view {n w : ℕ} (thr : ℕ) (s : List (Fin n)) : (Esa22Copy.tape n w s.length).map (fun t => Option.map Esa22Copy.Interface.view (Esa22Copy.Interface.loop thr s t).val) = Esa22Copy.Interface.Pseudocode.loop thr w s (some Esa22Copy.Interface.Pseudocode.init) := by
  have h := Esa22Copy.loop_view (n := n) (w := w) thr s (some Esa22Copy.Program.initial)
  simp only [Option.map_some, Esa22Copy.Interface.view_initial] at h
  exact h

/-- The program's output line (|X|/p, or ⊥) agrees with the pseudocode's report on the viewed state.

INTERNAL: bridge between the program's `report` and the pseudocode's `report`; the paper states no such lemma.
TEXLINE: esa22-final.tex:443-444 -/
theorem report_view {n : ℕ} (acc : Option (Esa22Copy.Program.State (Fin n))) : (Esa22Copy.Program.report acc).val = Esa22Copy.Interface.Pseudocode.report (Option.map Esa22Copy.Interface.view acc) := by
  cases acc with
  | none => simp [Esa22Copy.Interface.report_none, Esa22Copy.Interface.Pseudocode.report]
  | some st =>
      simp [Esa22Copy.Interface.report_some_val, Esa22Copy.Interface.Pseudocode.report,
        Esa22Copy.Interface.view, Arlib.Computation.Roster.card_toFinset]

/-- Pointwise in the tape, the program's estimate is the pseudocode report of the viewed loop result.

INTERNAL: bridge between the program's `estimate` and the pseudocode's `report ∘ loop`; the paper states no such lemma.
TEXLINE: esa22-final.tex:422-445 -/
theorem estimate_val {n w : ℕ} (thr : ℕ) (s : List (Fin n)) (t : List (Esa22Copy.Program.Randomness (Fin n) w)) : (Esa22Copy.Program.estimate thr s t).val = Esa22Copy.Interface.Pseudocode.report (Option.map Esa22Copy.Interface.view (Esa22Copy.Interface.loop thr s t).val) := by
  rw [Esa22Copy.Interface.estimate_eq, Arlib.Computation.Charged.val_bind]
  exact Esa22Copy.report_view (Esa22Copy.Interface.loop thr s t).val

/-- The output law of the program over a random tape equals the pseudocode loop's law pushed through report.

INTERNAL: bridge between the program's output law (over a random tape of a given threshold/width) and the pseudocode loop's law; the paper states no such lemma.
TEXLINE: esa22-final.tex:422-445 -/
theorem estimate_law {n w : ℕ} (thr : ℕ) (s : List (Fin n)) : (Esa22Copy.tape n w s.length).map (fun t => (Esa22Copy.Program.estimate thr s t).val) = (Esa22Copy.Interface.Pseudocode.loop thr w s (some Esa22Copy.Interface.Pseudocode.init)).map Esa22Copy.Interface.Pseudocode.report := by
  have step1 : (Esa22Copy.tape n w s.length).map (fun t => (Esa22Copy.Program.estimate thr s t).val)
      = (Esa22Copy.tape n w s.length).map
          (fun t => Esa22Copy.Interface.Pseudocode.report
            (Option.map Esa22Copy.Interface.view (Esa22Copy.Interface.loop thr s t).val)) := by
    congr 1
    funext t
    exact Esa22Copy.estimate_val thr s t
  rw [step1, show (fun t => Esa22Copy.Interface.Pseudocode.report
      (Option.map Esa22Copy.Interface.view (Esa22Copy.Interface.loop thr s t).val))
      = Esa22Copy.Interface.Pseudocode.report ∘
        (fun t => Option.map Esa22Copy.Interface.view (Esa22Copy.Interface.loop thr s t).val)
      from rfl,
    ← PMF.map_comp, Esa22Copy.loop_initial_view]

/-- Capstone bridge: the program's output distribution equals the pseudocode's answer (first conjunct, by unfolding output/answer and rewriting with estimate_law at the parameters thr and w), together with the general tape-level law the analysis rewrites through.

INTERNAL: the object-equivalence bridge the correctness, space and time owners rewrite through; the paper never states this equivalence directly, it is the fact that `Model/Program.lean` and `Interface/Pseudocode.lean` are the same algorithm as Algorithm 1.
TEXLINE: esa22-final.tex:422-445 -/
theorem output_bridge {n : ℕ} (ε δ : ℝ) (s : List (Fin n)) : Esa22Copy.output ε δ s = Esa22Copy.Interface.Pseudocode.answer ε δ s ∧ ∀ (thr w : ℕ), (Esa22Copy.tape n w s.length).map (fun t => (Esa22Copy.Program.estimate thr s t).val) = (Esa22Copy.Interface.Pseudocode.loop thr w s (some Esa22Copy.Interface.Pseudocode.init)).map Esa22Copy.Interface.Pseudocode.report := by
  refine ⟨?_, fun thr w => Esa22Copy.estimate_law thr s⟩
  show (Esa22Copy.run ε δ s).map Arlib.Computation.Charged.val
      = Esa22Copy.Interface.Pseudocode.answer ε δ s
  unfold Esa22Copy.run Esa22Copy.Interface.Pseudocode.answer
  rw [PMF.map_comp]
  exact Esa22Copy.estimate_law (Esa22Copy.thresh ε δ s.length) s

end Esa22Copy
