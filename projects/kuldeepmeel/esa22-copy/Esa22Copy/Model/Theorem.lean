import Esa22Copy.Meta.ModelClosure
import Mathlib.Data.Real.ENatENNReal
import Esa22Copy.Model.Prior
import Esa22Copy.Model.Run
import Esa22Copy.Analysis.AccuracyProof
import Esa22Copy.Analysis.SpaceProof
import Esa22Copy.Analysis.SpaceBitsProof
import Esa22Copy.Analysis.TimeProof
import Esa22Copy.Analysis.TheoremProof

/-!
# Theorem `thm:main`: the F0-Estimator

> For any data stream `A` and any `0 < ε, δ < 1`, the algorithm outputs an
> `(ε,δ)`-approximation of `F0(A)`. The algorithm uses
> `O(ε⁻² · log n · (log m + log 1/δ))` space in the worst case. Furthermore,
> assuming that the set `𝒳` is maintained in a dictionary that supports
> membership, insertion, and deletion in `O(1)` expected time, the algorithm
> runs in `O(m)` expected time. (esa22-final.tex:501-503)

All claims are about the single object `run ε δ s` (`Model/Run.lean`): the
distribution of charged runs of Algorithm 1 (`Model/Program.lean`) with the
paper's `thresh ε δ m` and fresh, independent coins per iteration.

* `esa22copy_correct` — **accuracy**, the one claim that can fail: with
  probability `≥ 1 - δ` the output is not `⊥` and lies in the closed interval
  `[(1-ε)F0, (1+ε)F0]`.
* `esa22copy_space` — **worst-case space**, exact form: on every reachable run,
  at every point of it, the sample set holds at most `thresh ε δ m` elements
  (esa22-final.tex:507).  A bound on every outcome, not a probability-1 claim.
* `esa22copy_space_bigO` — the paper's **asymptotic space** in bits,
  `(cells) · ⌈log₂ n⌉ ≤ C · ε⁻² · log₂ n · (log₂ m + log₂ (1/δ))`, with `C`
  chosen before every parameter.  It carries `2 ≤ n` and `2 ≤ m`, which the paper
  does not state but which the `O`-form needs: at `m = 1` and `δ → 1` the right
  side tends to `0` while `thresh ≥ 36/ε²`; at `n = 1`, `log₂ n = 0`.  These
  guards are on this corollary only.
* `esa22copy_time` — **expected time**: `∃ C`, chosen before `n, s, ε, δ`, with
  expected step count `≤ C · (m + 1)`.  The `+1` absorbs the output line at
  `m = 0`.

**Cost model of the time claim.**  Steps are counted in arlib's standard
operations at unit price (`Model.Operations.rate`): every dictionary operation on
`𝒳` (erase, insert, the size test `cardEq`, the final `size`) is one step — the
paper's "`O(1)` expected-time dictionary, with `|𝒳|` maintained alongside",
idealised as a deterministic unit cost (the hash table's own randomness is not
modelled); the Bernoulli(`p`) draw, halving `p` and the final `|𝒳| · 2ᵏ` are one
step each; and the throw at line `final-throw` costs one coin per element of `𝒳`
plus one erase per discarded element, i.e. `Θ(thresh)`, never `O(1)`.  Computing
`thresh` is not charged.  Space is counted in `Cell.roster` cells, one per element
of `𝒳`; the registers holding `p`'s level, `|𝒳|` and the loop index are not
counted, as in the paper's proof.

**Hypotheses.**  Exactly `0 < ε < 1` and `0 < δ < 1`, as the paper states.  No
hypothesis on `m`, `n` or `F0` is added to the accuracy, exact-space or time
claims: `m = 0` and `F0 < thresh` are case splits for the analysis.  `hprior`
carries what the proof borrows from prior work (`Model/Prior.lean`, empty until
surveyed).
-/

set_option autoImplicit false

open scoped ENNReal

namespace Esa22Copy

open Arlib.Computation (worstSpace)
open Esa22Copy.Model.Operations (rate)

/-- **Accuracy** (esa22-final.tex:502; Problem 1, esa22-final.tex:319-323): for any
stream over `[n]` and any `0 < ε < 1`, `0 < δ < 1`, the F0-Estimator outputs a
number in `[(1-ε)F0, (1+ε)F0]` — not `⊥` — with probability at least `1 - δ`. -/
theorem esa22copy_correct (hprior : Prior) {n : ℕ} (s : List (Fin n)) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤ (output ε δ s).toOuterMeasure {o | Accurate ε (F0 s) o} := by
    exact Esa22Copy.Analysis.correct_proof hprior (n := n) s ε δ hε0 hε1 hδ0 hδ1

/-- **Worst-case space, exact** (esa22-final.tex:502, proof 507): on every
reachable run and at every point of it, the sample set holds at most
`thresh ε δ m` elements of `[n]`, starting from the empty set. -/
theorem esa22copy_space (hprior : Prior) {n : ℕ} (s : List (Fin n)) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    worstSpace Arlib.Computation.Cell.roster 0 (run ε δ s) ≤ (thresh ε δ s.length : ℕ∞) := by
    exact Esa22Copy.Analysis.space_proof hprior (n := n) s ε δ hε0 hε1 hδ0 hδ1

/-- **Worst-case space in bits, asymptotic** (esa22-final.tex:502): the sample set
occupies `O(ε⁻² · log n · (log m + log 1/δ))` bits, with an absolute constant `C`
chosen before every parameter.  Stated under `2 ≤ n` and `2 ≤ m`, without which
the `O`-form is false (see the module docstring). -/
theorem esa22copy_space_bigO (hprior : Prior) :
    ∃ C : ℝ, ∀ (n : ℕ) (s : List (Fin n)) (ε δ : ℝ),
      0 < ε → ε < 1 → 0 < δ → δ < 1 → 2 ≤ n → 2 ≤ s.length →
        (worstSpace Arlib.Computation.Cell.roster 0 (run ε δ s) : ℝ≥0∞) * (bitsPerItem n : ℝ≥0∞)
          ≤ ENNReal.ofReal (C * (1 / ε ^ 2) * Real.logb 2 n
              * (Real.logb 2 s.length + Real.logb 2 (1 / δ))) := by
    exact Esa22Copy.Analysis.space_bigO_proof hprior

/-- **Expected time** (esa22-final.tex:502, proof 509-511): under unit-cost
dictionary operations, the expected number of steps is `O(m)` — at most
`C · (m + 1)` for an absolute constant `C` chosen before `n`, `s`, `ε` and `δ`. -/
theorem esa22copy_time (hprior : Prior) :
    ∃ C : ℕ, ∀ (n : ℕ) (s : List (Fin n)) (ε δ : ℝ),
      0 < ε → ε < 1 → 0 < δ → δ < 1 →
        expectedSteps rate (run ε δ s) ≤ (C : ℝ≥0∞) * ((s.length : ℝ≥0∞) + 1) := by
    exact Esa22Copy.Analysis.time_proof hprior

/-- **Theorem `thm:main`** (esa22-final.tex:501-503): the F0-Estimator outputs an
`(ε,δ)`-approximation of `F0` with probability `≥ 1 - δ`; holds at most `thresh`
elements on every run, hence `O(ε⁻² · log n · (log m + log 1/δ))` bits; and runs
in `O(m)` expected time under unit-cost dictionary operations. -/
theorem esa22copy_main (hprior : Prior) :
    (∀ (n : ℕ) (s : List (Fin n)) (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        ENNReal.ofReal (1 - δ) ≤ (output ε δ s).toOuterMeasure {o | Accurate ε (F0 s) o}) ∧
    (∀ (n : ℕ) (s : List (Fin n)) (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        worstSpace Arlib.Computation.Cell.roster 0 (run ε δ s) ≤ (thresh ε δ s.length : ℕ∞)) ∧
    (∃ C : ℝ, ∀ (n : ℕ) (s : List (Fin n)) (ε δ : ℝ),
      0 < ε → ε < 1 → 0 < δ → δ < 1 → 2 ≤ n → 2 ≤ s.length →
        (worstSpace Arlib.Computation.Cell.roster 0 (run ε δ s) : ℝ≥0∞) * (bitsPerItem n : ℝ≥0∞)
          ≤ ENNReal.ofReal (C * (1 / ε ^ 2) * Real.logb 2 n
              * (Real.logb 2 s.length + Real.logb 2 (1 / δ)))) ∧
    (∃ C : ℕ, ∀ (n : ℕ) (s : List (Fin n)) (ε δ : ℝ),
      0 < ε → ε < 1 → 0 < δ → δ < 1 →
        expectedSteps rate (run ε δ s) ≤ (C : ℝ≥0∞) * ((s.length : ℝ≥0∞) + 1)) :=
  Esa22Copy.Analysis.main_of_parts (esa22copy_correct hprior) (esa22copy_space hprior)
    (esa22copy_space_bigO hprior) (esa22copy_time hprior)

end Esa22Copy

#modelClosureOfType Esa22Copy.esa22copy_main
#print axioms Esa22Copy.esa22copy_main

#surplusIn Esa22Copy.Model from Esa22Copy.esa22copy_main
