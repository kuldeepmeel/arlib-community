import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log
import Arlib.Computation.ChargedPMF

/-!
# Prelude: the vocabulary of the F0-Estimator theorem

The non-library symbols the audit surface states its claims in, and the
quantity the headline theorem (`thm:main`, esa22-final.tex:501-503) is about.

**Conventions.**

* A data stream `A = ⟨a₁, …, a_m⟩` over `[n]` (esa22-final.tex:303) is a
  `List (Fin n)`; `m` is its `length`.  `[n]` is relabelled `0, …, n-1`, which is
  harmless: nothing but the bit count `bitsPerItem n` depends on what the items
  are.  No abbreviation is introduced for it.
* **`log` means `log₂` throughout** (esa22-final.tex:327).  `thresh` below uses
  `Real.logb 2` exclusively, and every numeric chain of the analysis — including
  the opaque `log e` of Claim `lm:error-fail`, which is `Real.logb 2 (Real.exp 1)`
  — is to be read in base 2.  This is stated once, here, rather than per lemma.
* The algorithm's failure symbol `⊥` is `none : Option ℕ`; its numerical output
  `|X|/p` with `p = 2⁻ᵏ` is `some (|X| * 2ᵏ)`.

**Ledger (paper → Lean).**

* `F0(A) = |{a₁,…,a_m}|` (esa22-final.tex:316) → `F0`.
* `(ε,δ)`-approximation, Problem 1 (esa22-final.tex:319-323) → `Accurate`,
  with `⊥` counted as an error (the proof's event `Error`, esa22-final.tex:513-516)
  and the closed interval `[(1-ε)F0, (1+ε)F0]`.  Cross-check: on `some c`,
  `Accurate ε f0 (some c)` is arlib's `Arlib.Approximation.Between (1-ε) (1+ε)`
  applied to `(c : ℝ)` and `(f0 : ℝ)` (Arlib/Approximation/MulError.lean),
  by definition of `Between`.
* `thresh ← ⌈(12/ε²)·log(8m/δ)⌉` (esa22-final.tex:427) → `thresh`.  At `m = 0`
  Lean's `Real.logb 2 0 = 0` gives `thresh = 0`, which is harmless: the loop
  never runs.
* "each item requires `⌈log₂ n⌉` bits" (esa22-final.tex:507) → `bitsPerItem`.
* "expected running time" (esa22-final.tex:502) → `expectedSteps`.  Arlib has
  only the worst-case operators `worstSteps`/`worstSpace`
  (Arlib/Computation/ChargedPMF.lean), so the expectation operator is defined
  here, in the audited surface, because the time claim is a bound on it.
-/

open scoped ENNReal

namespace Esa22Copy

open Arlib.Computation

/-! ## Vocabulary -/

/-- **The sample-set capacity** `thresh = ⌈(12/ε²) · log₂(8m/δ)⌉`
(esa22-final.tex:427), as a natural number.

Base-2 logarithm by the paper's convention (esa22-final.tex:327); `⌈·⌉₊` is the
ceiling into `ℕ`.  It depends on `ε`, `δ` and the stream length `m` only, which is
why the algorithm must know `m` before reading the stream.  It is a real-number
computation, hence not a line of the charged program: `Model/Run.lean` applies it
to `s.length` and hands the result to the program, and computing it is not
charged (it is `O(1)` in the paper's model). -/
noncomputable def thresh (ε δ : ℝ) (m : ℕ) : ℕ :=
  ⌈12 / ε ^ 2 * Real.logb 2 (8 * (m : ℝ) / δ)⌉₊

/-- **Bits needed to store one element of `[n]`**: `⌈log₂ n⌉`
(esa22-final.tex:507), as Mathlib's `Nat.clog 2 n`.  Used only to state the
space claim in bits; the space theorem itself counts stored elements. -/
def bitsPerItem (n : ℕ) : ℕ := Nat.clog 2 n

/-- **The expected step count of a randomised charged computation**, under a
rate: `𝔼_{p ∼ μ} [steps R p]`, as an extended non-negative real.

`Charged.steps R p` is the tally of the run `p` priced by `R`; this is its mean
over the distribution of runs.  It is the time operator of the paper's
"`O(m)` expected time" (esa22-final.tex:502), absent from arlib, which provides
only `worstSteps`. -/
noncomputable def expectedSteps {κ κₛ α : Type} [Fintype κ] (R : Rate κ)
    (μ : PMF (Charged κ κₛ α)) : ℝ≥0∞ :=
  ∑' p, μ p * (Charged.steps R p : ℝ≥0∞)

/-! ## The quantity -/

/-- **The number of distinct elements of a stream**, `F0(A) = |{a₁,…,a_m}|`
(esa22-final.tex:316).  Mathlib's `List.card_toFinset` rewrites it as
`s.dedup.length`. -/
def F0 {α : Type} [DecidableEq α] (s : List α) : ℕ := s.toFinset.card

/-- **The success event of an `(ε,δ)`-approximation of `f0`** (Problem 1,
esa22-final.tex:319-323): the algorithm output a number `c`, not `⊥`, and
`(1-ε)·f0 ≤ c ≤ (1+ε)·f0` — the closed interval, compared in `ℝ`.

`⊥` (`none`) is a failure, exactly as in the proof's event `Error`
(esa22-final.tex:513-516), which includes outputting `⊥`. -/
def Accurate (ε : ℝ) (f0 : ℕ) : Option ℕ → Prop
  | none => False
  | some c => (1 - ε) * (f0 : ℝ) ≤ (c : ℝ) ∧ (c : ℝ) ≤ (1 + ε) * (f0 : ℝ)

end Esa22Copy
