import Cellcounting.Model.Program
import Arlib.Computation.ProbRAM
import Mathlib.Order.Lattice.Nat

/-!
# Where the fair bits come from

`Cellcounting.Program.fpras` takes its randomness as an argument, a sealed family
of fair bits `Coins ℕ` that it reads at positions `0, 1, 2, …` in order, one
`Coins.flip` per bit.  This file says how that family is drawn and nothing
else.

* `tapeHeads T`: the positions in `0..T-1` whose bit came up heads, for `T`
  independent fair bits (`Arlib.Computation.ProbRAM.fair`).  It is written by
  recursion, so the successor case unfolds definitionally.  Positions `≥ T` are
  tails.
* `tape T`: the same family, as the program's sealed `Coins ℕ`.
* `tapeLength I ε δ`: **the tape-length decision.**  It is the largest number of
  fair bits that any execution of `fpras I ε δ` reads, over every coin family.
  The program reads position `k` only after reading positions `0..k-1`, and it
  charges one `Op.rand .flip` per read.  So `tapeLength I ε δ` bounds every
  position any run reads, and every bit an execution reads is one of the `T`
  independent fair bits.  The pairing therefore never truncates a run.  The
  supremum is finite: every loop of the program has a bound computed from its
  input, and its number of reads is at most its step count, which `fpras_time`
  bounds.  If the supremum were infinite, `sSup` on `ℕ` would return `0`;
  ruling that out is part of the proof obligation of `fpras_accurate`.
* `run I ε δ`: the algorithm as a distribution over charged computations, one
  per coin family.  The time claim reads it with `worstSteps`.
* `output I ε δ`: the distribution of the returned estimate `Ẑ`.

Because `Coins.flip` is the program's only source of randomness, "uses
independent unbiased bits" (`sections/introduction.tex:30`) is a property of this
file together with `Model/Program.lean`.  It is not a hypothesis.
-/

namespace Cellcounting

open Arlib.Computation

/-- The positions among `0..T-1` whose fair bit came up heads, for `T`
independent fair bits. -/
noncomputable def tapeHeads : ℕ → PMF (Finset ℕ)
  | 0 => PMF.pure ∅
  | T + 1 => (tapeHeads T).bind fun s =>
      ProbRAM.fair.bind fun b => PMF.pure (if b then insert T s else s)

/-- `T` independent fair bits at positions `0..T-1` (tails beyond), as the
program's sealed coin family. -/
noncomputable def tape (T : ℕ) : PMF (Coins ℕ) :=
  (tapeHeads T).map Coins.ofFinset

/-- **The tape length**: the most fair bits any execution of the algorithm on
`(I, ε, δ)` reads. -/
noncomputable def tapeLength (I : Instance) (ε δ : ℚ) : ℕ :=
  sSup (Set.range fun s : Finset ℕ =>
    (Program.fpras I ε δ (Coins.ofFinset s)).cost (Model.Operations.Op.rand RandOp.flip))

/-- **The algorithm as a randomised charged computation**: `fpras I ε δ` run on a
tape of `tapeLength I ε δ` independent fair bits. -/
noncomputable def run (I : Instance) (ε δ : ℚ) :
    PMF (Charged Model.Operations.Op Model.Operations.Cell ℚ) :=
  (tape (tapeLength I ε δ)).map (Program.fpras I ε δ)

/-- **The output distribution**: the law of the estimate `Ẑ`. -/
noncomputable def output (I : Instance) (ε δ : ℚ) : PMF ℚ :=
  (run I ε δ).map Charged.val

end Cellcounting

#modelClosure Cellcounting.tapeHeads
#modelClosure Cellcounting.tape
#modelClosure Cellcounting.tapeLength
#modelClosure Cellcounting.run
#modelClosure Cellcounting.output
