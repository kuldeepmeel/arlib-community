import Cellcounting.Analysis.RefChainLaw

/-!
# One underlying transition of a trace stage

`stageStep` is one underlying transition of a single trace stage of the exact chain
`P_{a, w}` (`refStep`), counting the trace steps completed so far: a trace step ends each
time the chain is at a transversal after a transition (holding steps and rejections
included), exactly as in `refRestartStep`, and the stage freezes after `τ` of them.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: one underlying transition of a trace stage of `P_{a, w}`; `q.1` counts the
completed trace steps, `q.2` is the state.  Frozen once `τ` trace steps are done.
TEXLINE: sections/algorithm.tex:214-225 -/
noncomputable def stageStep (I : Instance) (ε δ : ℚ) (a : ℕ) (w : ℕ → ℕ → ℚ)
    (q : ℕ × Finset ℕ) : PMF (ℕ × Finset ℕ) :=
  if τParam I ε δ ≤ q.1 then PMF.pure q else
    (refStep I ε δ a w q.2).map fun S' =>
      match kind I ε δ S' with
      | .transversal => (q.1 + 1, S')
      | _ => (q.1, S')

end Cellcounting.Analysis
