import Cellcounting.Analysis.RefChainLaw

/-!
# The stationary law, the kernel, the energy and the projection `Q` of `P_{j, w}`

The `L²(π)` objects of `sec:transport` (`transport.tex:34-98`, `transport.tex:506-520`)
for the exact Metropolis chain `P_{j, w}` (`refStep`) on `X = chainStates`:

* `refPi` — the stationary law `π = λ / Λ` (zero off `X`), with its mean
  `refPiMean` and variance `refPiVar` of an observable;
* `refPk` — the transition probabilities `P(S, S')` as reals;
* `refEnergy` — the energy `𝓔(g) = ⟨g, (I - P) g⟩_π` (`eq:energy`);
* `refQ` — the projection `𝓠`: values on transversals kept, values on each defect
  type `A_il` replaced by their conditional `π`-mean within that type.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: the stationary law `π = λ / Λ` of `P_{j, w}` on `X` (zero off `X`).
TEXLINE: sections/transport.tex:36-47 -/
noncomputable def refPi (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ) (S : Finset ℕ) : ℝ :=
  if S ∈ chainStates I ε δ then refLam I ε δ S j w / refLamTot I ε δ j w else 0

/-- INTERNAL: the stationary mean `E_π G`.
TEXLINE: sections/transport.tex:575-590 -/
noncomputable def refPiMean (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (G : Finset ℕ → ℝ) : ℝ :=
  ∑ S ∈ chainStates I ε δ, refPi I ε δ j w S * G S

/-- INTERNAL: the stationary variance `Var_π G`.
TEXLINE: sections/transport.tex:575-590 -/
noncomputable def refPiVar (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (G : Finset ℕ → ℝ) : ℝ :=
  ∑ S ∈ chainStates I ε δ, refPi I ε δ j w S * (G S - refPiMean I ε δ j w G) ^ 2

/-- INTERNAL: the transition probability `P(S, S')` of `P_{j, w}` as a real number.
TEXLINE: sections/transport.tex:60-69 -/
noncomputable def refPk (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (S S' : Finset ℕ) : ℝ :=
  (refStep I ε δ j w S S').toReal

/-- INTERNAL: the energy `𝓔(g) = ⟨g, (I - P) g⟩_π` of `eq:energy`, the sums
running over `X`.
TEXLINE: sections/transport.tex:86-96 -/
noncomputable def refEnergy (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (g : Finset ℕ → ℝ) : ℝ :=
  ∑ S ∈ chainStates I ε δ, refPi I ε δ j w S * g S *
    (g S - ∑ S' ∈ chainStates I ε δ, refPk I ε δ j w S S' * g S')

open Classical in
/-- INTERNAL: the projection `𝓠`: keep `g` on transversals (and off `X`), and replace
its values on a defect type `A_il` by their conditional `π`-mean on `A_il ∩ X`.
TEXLINE: sections/transport.tex:506-520 -/
noncomputable def refQ (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (g : Finset ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  match kind I ε δ S with
  | .defect i l =>
    (∑ S' ∈ (chainStates I ε δ).filter (fun S' => kind I ε δ S' = .defect i l),
        refPi I ε δ j w S' * g S') /
      ∑ S' ∈ (chainStates I ε δ).filter (fun S' => kind I ε δ S' = .defect i l),
        refPi I ε δ j w S'
  | _ => g S

end Cellcounting.Analysis
