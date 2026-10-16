import Cellcounting.Model.Run
import Cellcounting.Model.Prior
import Arlib.Computation.ChargedPMF
import Mathlib.Data.Nat.Log
import Cellcounting.Meta.ModelClosure
import Cellcounting.Analysis.AccuracyProof
import Cellcounting.Analysis.InfeasibleProof
import Cellcounting.Analysis.NonnegProof
import Cellcounting.Analysis.CostProof

/-- Proof-side assembly for `Cellcounting.cellcounting_fpras`: the four frontier owners,
with the polynomial `(C, k)` taken from the cost owner before any input. -/
theorem Cellcounting.Analysis.cellcounting_fpras_owner (hprior : Prior) :
    ∃ C k : ℕ, ∀ (I : Instance) (ε δ : ℚ),
      0 < I.m → 0 < I.n → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ENNReal.ofReal (1 - (δ : ℝ)) ≤
          (output I ε δ).toOuterMeasure
            {Zhat | (1 - ε) * (I.Z : ℚ) ≤ Zhat ∧ Zhat ≤ (1 + ε) * (I.Z : ℚ)} ∧
        (I.Omega = ∅ → ∀ Zhat ∈ (output I ε δ).support, Zhat = 0) ∧
        (∀ Zhat ∈ (output I ε δ).support, 0 ≤ Zhat) ∧
        Arlib.Computation.worstSteps Model.Operations.rate (run I ε δ) ≤
          ((C * (inputLength I ε δ + ⌈ε⁻¹⌉₊ + Nat.clog 2 ⌈δ⁻¹⌉₊ + 1) ^ k : ℕ) : ℕ∞) := by
  obtain ⟨C, k, htime⟩ := Cellcounting.Analysis.fpras_time_owner hprior
  exact ⟨C, k, fun I ε δ hm hn hε hε1 hδ hδ1 =>
    ⟨Cellcounting.Analysis.fpras_accurate_owner hprior I ε δ hm hn hε hε1 hδ hδ1,
      Cellcounting.Analysis.fpras_zero_of_infeasible_owner hprior I ε δ hm hn hε hε1 hδ hδ1,
      Cellcounting.Analysis.fpras_nonneg_owner hprior I ε δ hm hn hε hε1 hδ hδ1,
      htime I ε δ hm hn hε hε1 hδ hδ1⟩⟩
