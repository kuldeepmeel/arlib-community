import Cellcounting.Model.Run
import Cellcounting.Model.Prior
import Arlib.Computation.ChargedPMF
import Mathlib.Data.Nat.Log
import Cellcounting.Meta.ModelClosure
import Cellcounting.Analysis.AccuracyProof
import Cellcounting.Analysis.InfeasibleProof
import Cellcounting.Analysis.NonnegProof
import Cellcounting.Analysis.CostProof
import Cellcounting.Analysis.TheoremProof

/-!
# Theorem `thm:main`: an FPRAS for cell-bounded contingency tables

`sections/introduction.tex:21-35`.  There is one randomised algorithm that,
given `(r, c, b)` and rationals `ε, δ ∈ (0, 1)`, outputs a nonnegative rational
`Ẑ` with `P((1-ε) Z ≤ Ẑ ≤ (1+ε) Z) ≥ 1 - δ`, outputs zero on every execution
when `Ω(r, c, b)` is empty, uses independent unbiased bits, and runs within one
fixed polynomial in `L`, `ε⁻¹`, `log δ⁻¹` bit operations on every execution.

## How each claim is stated

* "There is one randomised algorithm" is stated about the paper's own program,
  `Cellcounting.Program.fpras` (`Model/Program.lean`).  The polynomial `(C, k)`
  is chosen **before** every input.  This is a statement decision: an
  unconstrained "there exists an algorithm" says nothing without a machine model.
* Accuracy (`fpras_accurate`) is the one claim that can fail.  It is a
  probability under the output law `output I ε δ` of `Model/Run.lean`, over a
  closed interval, with `Z` cast to `ℚ`.
* Zero on infeasible inputs (`fpras_zero_of_infeasible`) and nonnegativity
  (`fpras_nonneg`) hold on every execution.  They are stated over every point
  of the support of the output law, not as probability-one claims.
* The cost (`fpras_time`) is the worst case over every execution
  (`Arlib.Computation.worstSteps`), in the bit-operation currency of
  `Model/Operations.lean` at `rate = Rate.unit Op`.  The bound is
  `C · (L + ⌈ε⁻¹⌉ + ⌈log₂ ⌈δ⁻¹⌉⌉ + 1)^k`, with `L = inputLength I ε δ`.  The third
  family is implied by the first, since `L` includes `δ`'s encoding, and is kept
  because the paper states it.
* "No counting or sampling oracle; only fair bits" is structural.  The program's
  only randomness is `Coins.flip`, and its only operations are the primitives of
  `Model/Operations.lean`.
* Hypotheses: exactly `0 < m`, `0 < n`, `0 < ε < 1`, `0 < δ < 1`.  The paper's
  equal-totals side condition is dropped: unequal totals make `Ω` empty, and the
  program checks totals itself.  Feasibility, `p ≥ 1` and good multipliers are
  case splits or events inside the analysis, not hypotheses.
* `(hprior : Prior)`: whatever the proof borrows from prior work (currently
  nothing; the Edmonds–Karp augmentation bound is a candidate).
-/

namespace Cellcounting

open Arlib.Computation

/-- **Accuracy.**  With probability at least `1 - δ`, the estimate lies in
`[(1 - ε) Z, (1 + ε) Z]`. -/
theorem fpras_accurate (hprior : Prior) (I : Instance) (ε δ : ℚ)
    (hm : 0 < I.m) (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - (δ : ℝ)) ≤
      (output I ε δ).toOuterMeasure
        {Zhat | (1 - ε) * (I.Z : ℚ) ≤ Zhat ∧ Zhat ≤ (1 + ε) * (I.Z : ℚ)} := by
    exact Cellcounting.Analysis.fpras_accurate_owner hprior I ε δ hm hn hε hε1 hδ hδ1

/-- **Zero on infeasible inputs**, on every execution. -/
theorem fpras_zero_of_infeasible (hprior : Prior) (I : Instance) (ε δ : ℚ)
    (hm : 0 < I.m) (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1) :
    I.Omega = ∅ → ∀ Zhat ∈ (output I ε δ).support, Zhat = 0 := by
    exact Cellcounting.Analysis.fpras_zero_of_infeasible_owner hprior I ε δ hm hn hε hε1 hδ hδ1

/-- **Nonnegativity**, on every execution. -/
theorem fpras_nonneg (hprior : Prior) (I : Instance) (ε δ : ℚ)
    (hm : 0 < I.m) (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ Zhat ∈ (output I ε δ).support, 0 ≤ Zhat := by
    exact Cellcounting.Analysis.fpras_nonneg_owner hprior I ε δ hm hn hε hε1 hδ hδ1

/-- **Running time.**  One polynomial, fixed before the input, bounds the bit
operations and coin reads of every execution. -/
theorem fpras_time (hprior : Prior) :
    ∃ C k : ℕ, ∀ (I : Instance) (ε δ : ℚ),
      0 < I.m → 0 < I.n → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      worstSteps Model.Operations.rate (run I ε δ) ≤
        ((C * (inputLength I ε δ + ⌈ε⁻¹⌉₊ + Nat.clog 2 ⌈δ⁻¹⌉₊ + 1) ^ k : ℕ) : ℕ∞) := by
    exact Cellcounting.Analysis.fpras_time_owner hprior

/-- **Theorem `thm:main`.**  For the paper's algorithm `Program.fpras` there is one
polynomial bound `C · (·)^k` such that, for every instance with `m, n ≥ 1` and all
rationals `ε, δ ∈ (0, 1)`: the estimate is within a factor `1 ± ε` of `Z` with
probability at least `1 - δ`; it is zero on every execution when `Ω` is empty;
it is nonnegative on every execution; and every execution costs at most
`C · (L + ⌈ε⁻¹⌉ + ⌈log₂ δ⁻¹⌉ + 1)^k`. -/
theorem cellcounting_fpras (hprior : Prior) :
    ∃ C k : ℕ, ∀ (I : Instance) (ε δ : ℚ),
      0 < I.m → 0 < I.n → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ENNReal.ofReal (1 - (δ : ℝ)) ≤
          (output I ε δ).toOuterMeasure
            {Zhat | (1 - ε) * (I.Z : ℚ) ≤ Zhat ∧ Zhat ≤ (1 + ε) * (I.Z : ℚ)} ∧
        (I.Omega = ∅ → ∀ Zhat ∈ (output I ε δ).support, Zhat = 0) ∧
        (∀ Zhat ∈ (output I ε δ).support, 0 ≤ Zhat) ∧
        worstSteps Model.Operations.rate (run I ε δ) ≤
          ((C * (inputLength I ε δ + ⌈ε⁻¹⌉₊ + Nat.clog 2 ⌈δ⁻¹⌉₊ + 1) ^ k : ℕ) : ℕ∞) := by
  exact Cellcounting.Analysis.cellcounting_fpras_owner hprior

end Cellcounting

#modelClosureOfType Cellcounting.cellcounting_fpras
#print axioms Cellcounting.cellcounting_fpras

#surplusIn Cellcounting.Model from Cellcounting.cellcounting_fpras

/-!
HANDOFF NOTES
Review observations only; these notes do not change theorem status.
Proof trust: 6 proof-trust issue(s), starting with lean/Cellcounting/Analysis/ObserveAccurate.lean:389; lean/Cellcounting/Interface/ProgramModel.lean:2967
Randomness semantics: The headline's distribution is the map of a fixed-length fair-bit seed through a deterministic program, not a PMF built from the algorithm's own pure/bind/sample control flow. The step from 'each draw uses fresh independent unbiased bits' to this map is asserted in a docstring, not composed or proved where a reviewer reads.
-/
