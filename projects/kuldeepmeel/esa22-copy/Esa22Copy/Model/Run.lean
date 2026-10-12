import Mathlib.Probability.Distributions.Uniform
import Esa22Copy.Model.Prelude
import Esa22Copy.Model.Program

/-!
# Run: where the F0-Estimator's coins come from

`Esa22Copy.Program.estimate` takes its randomness as an argument and computes.
This file says how that randomness is drawn, and nothing else.

* `cellLaw n w` — one tape cell: a uniform block of `w` fair bits (the paper's
  `GenerateRandomBits`, esa22-final.tex:618) for the Bernoulli(`p`) pick, and an
  independent uniform subset of `Fin n` as the throw's coins — a uniform subset is
  exactly one independent fair coin per element.
* `tape n w k` — `k` independent cells, written **by recursion** so that the
  `cons` case unfolds definitionally: cross-iteration independence of the coins
  is a fact about this definition, not an assertion beside it.
* `run ε δ s` — the algorithm as a `PMF` of charged computations.  The accuracy,
  space and time claims are three operators applied to this one object.
* `output ε δ s` — its output distribution, `Charged.val` pushed forward.

**The tape length.**  `run` draws `tape n (s.length + 1) s.length`: exactly one
cell per stream element.  `Program.estimate` loops over `s.zip tape`, which
truncates to the shorter list, so this choice is what makes the loop visit every
stream element; nothing else in `Model/` states that the two lengths agree.
Every cell is drawn even if its coins are never read (the throw does not run, or
the run has already output `⊥`), which does not change the law of what is read.

**The block width.**  Each block has `s.length + 1` bits, the paper's
`GenerateRandomBits(m+1)`.  The level `k` of `p = 2⁻ᵏ` rises at most once per
iteration, so at the pick of iteration `i` it is `≤ i - 1 < m + 1`, and the draw
reads a true Bernoulli(`2⁻ᵏ`).  That invariant is a proof obligation for the
analysis, not a hypothesis.

**The threshold.**  `run` applies `Esa22Copy.thresh ε δ s.length` itself, so the
headline theorems are about Algorithm 1 with the paper's `thresh`, not about a
family of programs indexed by a free threshold.

The stream is an argument fixed before any coin is drawn: the adversary is
oblivious (esa22-final.tex:502, "for any data stream").
-/

set_option autoImplicit false

namespace Esa22Copy

open Arlib.Computation (Block Coins Charged)
open Esa22Copy.Model.Operations (Op Cell)

/-- **One cell of randomness**: a uniform `Fin w → Bool` sealed as a `Block w`,
and an independent uniform `Finset (Fin n)` sealed as the coins (heads = kept). -/
noncomputable def cellLaw (n w : ℕ) : PMF (Program.Randomness (Fin n) w) :=
  (PMF.uniformOfFintype (Fin w → Bool)).bind fun f =>
    (PMF.uniformOfFintype (Finset (Fin n))).map fun S =>
      ⟨Block.ofFun f, Coins.ofFinset S⟩

/-- **The tape**: `k` independent cells, each drawn by `cellLaw n w`. -/
noncomputable def tape (n w : ℕ) : ℕ → PMF (List (Program.Randomness (Fin n) w))
  | 0 => PMF.pure []
  | k + 1 => (cellLaw n w).bind fun c => (tape n w k).map fun t => c :: t

/-- **The F0-Estimator, run**: Algorithm 1 on stream `s` with the paper's
threshold `thresh ε δ m`, reading a tape of `m` cells of `m + 1`-bit blocks,
where `m = s.length`. -/
noncomputable def run {n : ℕ} (ε δ : ℝ) (s : List (Fin n)) :
    PMF (Charged Op Cell (Option ℕ)) :=
  (tape n (s.length + 1) s.length).map
    (Program.estimate (thresh ε δ s.length) s)

/-- **What the F0-Estimator outputs**: `none` for `⊥`, `some (|𝒳| · 2ᵏ)` for
`|𝒳|/p`. -/
noncomputable def output {n : ℕ} (ε δ : ℝ) (s : List (Fin n)) : PMF (Option ℕ) :=
  (run ε δ s).map Charged.val

end Esa22Copy

#modelClosure Esa22Copy.run
#modelClosure Esa22Copy.output
