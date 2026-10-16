import Cellcounting.Model.Run
import Cellcounting.Model.Prior
import Arlib.Computation.ChargedPMF
import Mathlib.Data.Nat.Log
import Cellcounting.Meta.ModelClosure
import Cellcounting.Interface.Encoding
import Cellcounting.Interface.Pseudocode
import Cellcounting.Interface.ProgramModel

/-!
# Zero output on infeasible inputs

`fpras_zero_of_infeasible_owner`: if `Ω(r,c,b)` is empty, every value in the
support of the output law is `0`.  The proof rewrites the output law to the
pseudocode law through the interface bridge `output_eq_fpras`; the pseudocode's
`fpras` returns `PMF.pure 0` exactly when `Pseudocode.feasible I` (that is,
`I.Omega.Nonempty`) fails.
-/

/-- Proof-side owner for `Cellcounting.fpras_zero_of_infeasible`; its statement is fixed by the proof charter.
PAPER: sections/introduction.tex:29 -/
theorem Cellcounting.Analysis.fpras_zero_of_infeasible_owner (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m) (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1) : I.Omega = ∅ → ∀ Zhat ∈ (output I ε δ).support, Zhat = 0 := by
  intro hΩ Zhat hZ
  have hfeas : ¬ Pseudocode.feasible I := by
    simp [Pseudocode.feasible, hΩ]
  rw [(output_eq_fpras I ε δ).1, Pseudocode.fpras, if_neg hfeas, PMF.support_pure] at hZ
  exact hZ

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · closed · via `output_eq_fpras` and the `else PMF.pure 0` branch of `Pseudocode.fpras`
-/
