import Esa22Copy.Meta.ModelClosure
import Mathlib.Data.Real.ENatENNReal
import Esa22Copy.Model.Prior
import Esa22Copy.Model.Run
import Esa22Copy.Interface.Encoding
import Esa22Copy.Interface.Pseudocode
import Esa22Copy.Interface.ProgramModel
import Esa22Copy.Analysis.SpaceProof

/-!
# Space in bits, as a big-O bound

`space_bigO_proof` combines the element-count bound `space_proof`
(`worstSpace ≤ thresh`) with two pieces of real arithmetic:
`thresh_le_logb` (`thresh ≤ 49/ε² · (log₂ m + log₂ (1/δ))` for `m ≥ 2`) and
`bitsPerItem_le_two_logb` (`⌈log₂ n⌉ ≤ 2 log₂ n` for `n ≥ 2`).  The constant is
`C = 98`.
-/

section
open scoped ENNReal

/-- `⌈log₂ n⌉ ≤ 2 · log₂ n` once `n ≥ 2`.
INTERNAL: converts the `Nat.clog` of `bitsPerItem` into the `Real.logb` form of
the big-O statement.
TEXLINE: esa22-final.tex:507 -/
theorem Esa22Copy.Analysis.bitsPerItem_le_two_logb (n : ℕ) (hn : 2 ≤ n) :
    (Esa22Copy.bitsPerItem n : ℝ) ≤ 2 * Real.logb 2 n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 1 ≤ Real.logb 2 (n : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    simpa using hn'
  have h := Real.natCeil_logb_natCast 2 n
  push_cast at h
  unfold Esa22Copy.bitsPerItem
  rw [← h]
  have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ Real.logb 2 (n : ℝ))
  linarith

/-- `thresh ε δ m ≤ 49/ε² · (log₂ m + log₂ (1/δ))` for `m ≥ 2`.
INTERNAL: unfolds the ceiling in `thresh` and uses
`log₂ (8m/δ) = 3 + log₂ m + log₂ (1/δ)`, absorbing `3` and the ceiling's `+1`
using `log₂ m ≥ 1` and `1/ε² ≥ 1`.
TEXLINE: esa22-final.tex:427, esa22-final.tex:507 -/
theorem Esa22Copy.Analysis.thresh_le_logb (ε δ : ℝ) (m : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hm : 2 ≤ m) :
    (Esa22Copy.thresh ε δ m : ℝ) ≤
      49 * (1 / ε ^ 2) * (Real.logb 2 m + Real.logb 2 (1 / δ)) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hLm : 1 ≤ Real.logb 2 (m : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    simpa using hm'
  have hLd : 0 ≤ Real.logb 2 (1 / δ) :=
    Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hδ0]; linarith)
  have h8 : Real.logb 2 (8 : ℝ) = 3 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
  have hsplit : Real.logb 2 (8 * (m : ℝ) / δ) = 3 + Real.logb 2 m + Real.logb 2 (1 / δ) := by
    rw [show 8 * (m : ℝ) / δ = 8 * m * (1 / δ) by ring,
      Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by norm_num) (by positivity), h8]
  have hε2 : 0 < ε ^ 2 := by positivity
  have ha : 1 ≤ 1 / ε ^ 2 := by
    rw [le_div_iff₀ hε2, one_mul]
    have : ε ^ 2 < 1 := by nlinarith
    linarith
  unfold Esa22Copy.thresh
  rw [hsplit, show 12 / ε ^ 2 = 12 * (1 / ε ^ 2) by ring]
  set a := 1 / ε ^ 2
  set L := Real.logb 2 (m : ℝ)
  set D := Real.logb 2 (1 / δ)
  have ha0 : 0 ≤ a := by linarith
  have harg : 0 ≤ 12 * a * (3 + L + D) := by positivity
  have hc := Nat.ceil_lt_add_one harg
  have haL : a ≤ a * L := by nlinarith
  have haD : 0 ≤ a * D := mul_nonneg ha0 hLd
  have e1 : 12 * a * (3 + L + D) = 36 * a + 12 * (a * L) + 12 * (a * D) := by ring
  have e2 : 49 * a * (L + D) = 49 * (a * L) + 49 * (a * D) := by ring
  rw [e2]
  linarith

/-- Proof-side owner for `Esa22Copy.esa22copy_space_bigO`; its statement is fixed by the proof charter.
PAPER: esa22-final.tex:502, proof at esa22-final.tex:507 -/
theorem Esa22Copy.Analysis.space_bigO_proof (hprior : Prior) : ∃ C : ℝ, ∀ (n : ℕ) (s : List (Fin n)) (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 → 2 ≤ n → 2 ≤ s.length → (Arlib.Computation.worstSpace Arlib.Computation.Cell.roster 0 (Esa22Copy.run ε δ s) : ENNReal) * (Esa22Copy.bitsPerItem n : ENNReal) ≤ ENNReal.ofReal (C * (1 / ε ^ 2) * Real.logb 2 n * (Real.logb 2 s.length + Real.logb 2 (1 / δ))) := by
  refine ⟨98, fun n s ε δ hε0 hε1 hδ0 hδ1 hn hm => ?_⟩
  have hsp := Esa22Copy.Analysis.space_proof hprior s ε δ hε0 hε1 hδ0 hδ1
  have hsp' : (Arlib.Computation.worstSpace Arlib.Computation.Cell.roster 0
      (Esa22Copy.run ε δ s) : ENNReal) ≤ (Esa22Copy.thresh ε δ s.length : ENNReal) := by
    rw [← ENat.toENNReal_coe]
    exact ENat.toENNReal_le.mpr hsp
  have hT := Esa22Copy.Analysis.thresh_le_logb ε δ s.length hε0 hε1 hδ0 hδ1 hm
  have hB := Esa22Copy.Analysis.bitsPerItem_le_two_logb n hn
  have hB0 : (0 : ℝ) ≤ Esa22Copy.bitsPerItem n := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) ≤ Esa22Copy.thresh ε δ s.length := Nat.cast_nonneg _
  have hreal : (Esa22Copy.thresh ε δ s.length : ℝ) * (Esa22Copy.bitsPerItem n : ℝ) ≤
      98 * (1 / ε ^ 2) * Real.logb 2 n * (Real.logb 2 s.length + Real.logb 2 (1 / δ)) := by
    have hP : 0 ≤ 49 * (1 / ε ^ 2) * (Real.logb 2 s.length + Real.logb 2 (1 / δ)) :=
      le_trans hT0 hT
    calc (Esa22Copy.thresh ε δ s.length : ℝ) * (Esa22Copy.bitsPerItem n : ℝ)
        ≤ (49 * (1 / ε ^ 2) * (Real.logb 2 s.length + Real.logb 2 (1 / δ))) *
            (2 * Real.logb 2 n) := mul_le_mul hT hB hB0 hP
      _ = 98 * (1 / ε ^ 2) * Real.logb 2 n *
            (Real.logb 2 s.length + Real.logb 2 (1 / δ)) := by ring
  calc (Arlib.Computation.worstSpace Arlib.Computation.Cell.roster 0 (Esa22Copy.run ε δ s) :
        ENNReal) * (Esa22Copy.bitsPerItem n : ENNReal)
      ≤ (Esa22Copy.thresh ε δ s.length : ENNReal) * (Esa22Copy.bitsPerItem n : ENNReal) :=
        mul_le_mul_left hsp' _
    _ = ENNReal.ofReal ((Esa22Copy.thresh ε δ s.length : ℝ) * (Esa22Copy.bitsPerItem n : ℝ)) := by
        rw [ENNReal.ofReal_mul hT0, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `space_bigO_proof` from `space_proof`, `thresh_le_logb`, `bitsPerItem_le_two_logb`; C = 98
-/
