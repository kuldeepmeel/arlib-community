import Cellcounting.Analysis.RefExperiment

/-!
# Stationary quantities of the exact Metropolis chain `P_{j, w}`

The laws and means that `prop:annealing` (`algorithm.tex:259-383`) compares the
reference phase with: the state space `X = A ∪ ⋃ A_il` inside the paired ground
set, the total multiplied mass `Λ = Σ_X λ` (`transport.tex:36-47`), the transversal
mass `Σ_A f_j` and the conditional transversal law `μ_j`, and the event that every
empirical mean of one observation trajectory is within relative error `η` of its
stationary mean (`p_0 = Σ_A f_j / Λ`, `p_il = w_il c_il(j) / Λ`,
`u = E_π G_j = Σ_A f_{j+1} / Λ`, `eq:alg-observable-identities`).
-/

namespace Cellcounting.Analysis

open Pseudocode

open Classical in
/-- INTERNAL: the transversals `A` of the paired state space.
TEXLINE: sections/signatures.tex:13-41 -/
noncomputable def transStates (I : Instance) (ε δ : ℚ) : Finset (Finset ℕ) :=
  (refStates I ε δ).filter fun S => kind I ε δ S = .transversal

open Classical in
/-- INTERNAL: the state space `X = A ∪ ⋃_{i ≠ l} A_il` of the enlarged chain.
TEXLINE: sections/transport.tex:13-16 -/
noncomputable def chainStates (I : Instance) (ε δ : ℚ) : Finset (Finset ℕ) :=
  (refStates I ε δ).filter fun S => kind I ε δ S ≠ .outside

/-- INTERNAL: the transversal mass `Σ_{S ∈ A} f_j(S)` (equal to `C(j)`).
TEXLINE: sections/algorithm.tex:167-172 -/
noncomputable def transMass (I : Instance) (ε δ : ℚ) (j : ℕ) : ℝ :=
  ∑ S ∈ transStates I ε δ, fWeight I ε δ j S

/-- INTERNAL: `μ_j`, the law `f_j / Σ_A f_j` on transversals (zero elsewhere): the
conditional law of `π` on `A` at parameter `j`.
TEXLINE: sections/algorithm.tex:43-50 -/
noncomputable def refMu (I : Instance) (ε δ : ℚ) (j : ℕ) (S : Finset ℕ) : ℝ :=
  if S ∈ transStates I ε δ then fWeight I ε δ j S / transMass I ε δ j else 0

/-- INTERNAL: `Λ = Σ_{S ∈ X} λ(S)` for the chain `P_{j, w}`.
TEXLINE: sections/transport.tex:36-47 -/
noncomputable def refLamTot (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ) : ℝ :=
  ∑ S ∈ chainStates I ε δ, refLam I ε δ S j w

/-- INTERNAL: every empirical mean of an observation trajectory of `P_{j, w}` (the
transversal frequency, each defect-type frequency, and the mean of `G_j`) has
relative error at most `η` about its stationary mean.
TEXLINE: sections/algorithm.tex:323-336 -/
def obsAccurate (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ) (o : RefObs) : Prop :=
  |(o.n0 : ℝ) / NavParam I ε δ - transMass I ε δ j / refLamTot I ε δ j w| ≤
      (ηParam I ε δ : ℝ) * (transMass I ε δ j / refLamTot I ε δ j w) ∧
    (∀ i < pSmall I ε δ, ∀ l < pSmall I ε δ, i ≠ l →
      |(o.nT i l : ℝ) / NavParam I ε δ - (w i l : ℝ) * cDef I ε δ j i l / refLamTot I ε δ j w| ≤
        (ηParam I ε δ : ℝ) * ((w i l : ℝ) * cDef I ε δ j i l / refLamTot I ε δ j w)) ∧
    |o.sumG / NavParam I ε δ - transMass I ε δ (j + 1) / refLamTot I ε δ j w| ≤
      (ηParam I ε δ : ℝ) * (transMass I ε δ (j + 1) / refLamTot I ε δ j w)

end Cellcounting.Analysis
