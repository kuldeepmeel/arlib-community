import Cellcounting.Analysis.CostScale
import Cellcounting.Analysis.OracleCost
import Cellcounting.Analysis.ChainSetupCost
import Cellcounting.Analysis.AnnealRunCost
import Mathlib.Data.Nat.Factorial.Basic

/-!
# The setup and one annealing run cost a polynomial number of bit operations

`Cellcounting.Analysis.anneal_cost`: for any context with `CtxSize S C` and
`PenaltyOK S C`, parameters with `PmSize S Pm`, `p ≤ S`, and `ε` with
`ε⁻¹, ratLen ε ≤ S`, the setup `Program.chainSetup` (S8) and every annealing run
`Program.annealRun` (S9–S11) on its output cost at most `S ^ k` bit operations on
every tape, and the run returns a rational of length at most `S ^ k`.

The run makes at most `H (B_ret + N_av)` transitions, each with at most two
oracle calls (`oracle_cost`), on profiles that are box-valid by construction of
the pair labels: every small cell `s` owns exactly `b_s` pairs.  Each multiplier
write `w_il ← w_il n_0/n_il` adds at most `2T + 8` bits (a crude bound, `p²` writes per
phase, still polynomial), and `Σ G_j` is a sum of `N_av` quotients of oracle outputs,
bounded through a product common denominator rather than a doubling per addition.
The bound is uniform over tapes: no probabilistic reasoning is involved.

The proof composes two children at the interface `ChainSize`/`WSize`
(`Analysis/ChainSize.lean`, which also holds the shared `dyadicDraw_cost`,
`profile_cost`, `kind_cost`, `factQ_cost`): `chainSetup_cost` (the setup costs `S ^ c`
and its output satisfies `ChainSize (S ^ c)`, `WSize (S ^ c)`, `ratLen C(0) ≤ S ^ c`) and
`annealRun_cost_of` (any run on a chain with `ChainSize T` costs `T ^ k` and returns a
rational of length `T ^ k`), applied at `T = S ^ (c + 1)`.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Program
open Cellcounting.Model.Operations
open Cellcounting.Interface

/-- **Setup and annealing-run cost.**
PAPER: sections/algorithm.tex:428-603 (`lem:bounded-implementation`: "The
implemented run uses a number of bit operations bounded, on every execution, by
a fixed polynomial in `L` and `ε⁻¹`.  It returns a nonnegative rational of
polynomial bit length."). -/
theorem anneal_cost : ∃ k : ℕ, ∀ (S : ℕ) (C : Ctx) (Pm : Params) (pS : SNat) (εS : SRat),
    2 ≤ S → CtxSize S C → PenaltyOK S C → PmSize S Pm → pS.get ≤ S →
    0 < εS.get → εS.get⁻¹ ≤ S → ratLen εS.get ≤ S →
    Charged.steps rate (chainSetup C Pm pS εS) ≤ S ^ k ∧
    ∀ (tape : Coins ℕ) (cur : ℕ),
      Charged.steps rate (annealRun C (chainSetup C Pm pS εS).val.1 tape
          (chainSetup C Pm pS εS).val.2.1 (chainSetup C Pm pS εS).val.2.2.1
          (chainSetup C Pm pS εS).val.2.2.2 cur) ≤ S ^ k ∧
      ratLen (annealRun C (chainSetup C Pm pS εS).val.1 tape
          (chainSetup C Pm pS εS).val.2.1 (chainSetup C Pm pS εS).val.2.2.1
          (chainSetup C Pm pS εS).val.2.2.2 cur).val.1.get ≤ S ^ k := by
  obtain ⟨c, hc⟩ := chainSetup_cost
  obtain ⟨k, hk⟩ := annealRun_cost_of
  refine ⟨(c + 1) * (k + 1), ?_⟩
  intro S C Pm pS εS hS hC hpen hPm hpS hε hεi hεl
  obtain ⟨h1, h2, h3, h4⟩ := hc S C Pm pS εS hS hC hPm hpS hε hεi hεl
  have hS1 : 1 ≤ S := by omega
  have hcT : S ^ c ≤ S ^ (c + 1) := Nat.pow_le_pow_right hS1 (by omega)
  have hST : S ≤ S ^ (c + 1) := by
    calc S = S ^ 1 := (pow_one S).symm
      _ ≤ S ^ (c + 1) := Nat.pow_le_pow_right hS1 (by omega)
  have hfin : (S ^ (c + 1)) ^ k ≤ S ^ ((c + 1) * (k + 1)) := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right hS1 (Nat.mul_le_mul_left _ (by omega))
  have hcfin : S ^ c ≤ S ^ ((c + 1) * (k + 1)) :=
    Nat.pow_le_pow_right hS1 ((Nat.le_succ c).trans (Nat.le_mul_of_pos_right _ (by omega)))
  refine ⟨h1.trans hcfin, fun tape cur => ?_⟩
  obtain ⟨g1, g2⟩ := hk (S ^ (c + 1)) C _ _ _ _ (hS.trans hST) (hC.mono hST) (hpen.mono hST)
    (h2.mono hcT) (h3.mono hcT) (h4.trans hcT) tape cur
  exact ⟨g1.trans hfin, g2.trans hfin⟩

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · `anneal_cost` from `chainSetup_cost` and `annealRun_cost_of` (children proved;
  `oracle_cost` in `OracleCost.lean` is still open and is the only unproved dependency)
-/
