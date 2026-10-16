import Cellcounting.Analysis.TapeWindow
import Cellcounting.Interface.Pseudocode

/-!
# `k` fair tape bits read as a binary integer

`bitsVal s c k` is the integer whose binary digits, most significant first, are the
tape bits at positions `c, …, c + k - 1`.  On a fair tape of length `T ≥ c + k + n`,
this integer is uniform on `[0, 2^k)` (`Pseudocode.uniformBits k`), and the next `n`
bits after it are fresh fair bits independent of it (`bitsVal_tape`).  This is the
tape law of the program's `uniformBits`, stated without the program.
-/

namespace Cellcounting.Analysis

open Cellcounting Arlib.Computation

/-- INTERNAL: the tape bits at `c, …, c + k - 1`, most significant first, as an integer.
TEXLINE: sections/evaluation.tex:356-371 -/
def bitsVal (s : Finset ℕ) (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * bitsVal s c k + if c + k ∈ s then 1 else 0

/-- INTERNAL: `bitsVal` reads only the `k` bits it is about. -/
theorem bitsVal_congr (s s' : Finset ℕ) (c c' : ℕ) :
    ∀ k, (∀ i, i < k → (c + i ∈ s ↔ c' + i ∈ s')) → bitsVal s c k = bitsVal s' c' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    simp only [bitsVal, ih fun i hi => h i (by omega), h k (by omega)]

/-- INTERNAL: membership in the shifted window `tapeRest`. -/
theorem mem_tapeRest (s : Finset ℕ) (c n i : ℕ) : i ∈ tapeRest s c n ↔ c + i ∈ s ∧ i < n := by
  unfold tapeRest
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨j, ⟨hj, hcj⟩, rfl⟩, hi⟩
    exact ⟨by rwa [Nat.add_sub_cancel' hcj], hi⟩
  · rintro ⟨h, hi⟩
    exact ⟨⟨c + i, ⟨h, by omega⟩, by omega⟩, hi⟩

/-- INTERNAL: the law of `k` fair bits, pointwise. -/
theorem uniformBits_mass (k u : ℕ) :
    Pseudocode.uniformBits k u = if u < 2 ^ k then ((2 : ENNReal) ^ k)⁻¹ else 0 := by
  simp only [Pseudocode.uniformBits]
  split_ifs with h
  · rw [PMF.uniformOfFinset_apply_of_mem (hs := ⟨0, Finset.mem_range.2 (Nat.two_pow_pos k)⟩)
      (Finset.mem_range.2 h), Finset.card_range]; push_cast; rfl
  · exact PMF.uniformOfFinset_apply_of_notMem _ (by simpa using h)

/-- INTERNAL: one more fair bit, appended as the least significant digit, doubles the range. -/
theorem uniformBits_succ (k : ℕ) :
    Pseudocode.uniformBits (k + 1) = (Pseudocode.uniformBits k).bind fun y =>
      ProbRAM.fair.map fun b => 2 * y + if b then 1 else 0 := by
  ext x
  rw [PMF.bind_apply, tsum_eq_single (x / 2)]
  · rw [PMF.map_apply, tsum_bool, uniformBits_mass, uniformBits_mass]
    simp only [ProbRAM.fair_apply, Bool.false_eq_true, if_false, if_true]
    have hlt : x < 2 ^ (k + 1) ↔ x / 2 < 2 ^ k := by
      rw [pow_succ]; omega
    by_cases hx : x / 2 < 2 ^ k
    · rw [if_pos (hlt.2 hx), if_pos hx, pow_succ, ENNReal.mul_inv (by simp) (by simp)]
      rcases Nat.mod_two_eq_zero_or_one x with h | h
      · rw [if_pos (by omega), if_neg (by omega), add_zero, one_div]
      · rw [if_neg (by omega), if_pos (by omega), zero_add, one_div]
    · rw [if_neg (fun h => hx (hlt.1 h)), if_neg hx, zero_mul]
  · intro y hy
    rw [PMF.map_apply, tsum_bool, if_neg, if_neg, add_zero, mul_zero]
    · simp only [if_true]; omega
    · simp only [Bool.false_eq_true, if_false]; omega

/-- INTERNAL: `k` fair bits read as a binary integer are uniform on `[0, 2^k)`. -/
theorem tapeHeads_map_bitsVal (k : ℕ) :
    (tapeHeads k).map (fun s => bitsVal s 0 k) = Pseudocode.uniformBits k := by
  induction k with
  | zero =>
    ext x
    rw [uniformBits_mass]
    by_cases hx : x = 0 <;> simp [tapeHeads, bitsVal, hx]
    convert tsum_ite_eq (∅ : Finset ℕ) (fun _ => (1 : ENNReal))
  | succ k ih =>
    rw [uniformBits_succ, ← ih, PMF.bind_map]
    show ((tapeHeads k).bind fun s => ProbRAM.fair.bind fun b =>
      PMF.pure (if b then insert k s else s)).map _ = _
    rw [PMF.map_bind]
    apply bind_congr_support
    intro s hs
    have hsub := subset_of_mem_support_tapeHeads hs
    have hk : k ∉ s := fun h => by simpa using hsub h
    simp only [Function.comp, PMF.map_bind, PMF.pure_map]
    rw [PMF.map]
    congr 1
    funext b
    congr 1
    have hc : ∀ t : Finset ℕ, (∀ i, i < k → (i ∈ t ↔ i ∈ s)) →
        bitsVal t 0 k = bitsVal s 0 k := fun t ht =>
      bitsVal_congr t s 0 0 k fun i hi => by simpa using ht i hi
    cases b
    · simp [bitsVal, hk]
    · simp only [if_true, bitsVal, zero_add, Finset.mem_insert_self]
      rw [hc (insert k s) fun i hi => by simp; omega]

/-- INTERNAL: the tape law of `k` fair bits read at cursor `c`: the integer is uniform on
`[0, 2^k)` and the next `n` bits are fresh and independent of it.
TEXLINE: sections/evaluation.tex:356-371 -/
theorem bitsVal_tape (c k n T : ℕ) (hT : c + k + n ≤ T) :
    (tapeHeads T).map (fun s => (bitsVal s c k, tapeRest s (c + k) n)) =
      (Pseudocode.uniformBits k).bind fun z => (tapeHeads n).map fun s' => (z, s') := by
  -- move to the window of `k + n` bits starting at `c`
  have e : (fun s => (bitsVal s c k, tapeRest s (c + k) n)) =
      (fun r => (bitsVal r 0 k, tapeRest r k n)) ∘ (fun s => tapeRest s c (k + n)) := by
    funext s
    simp only [Function.comp]
    congr 1
    · exact bitsVal_congr _ _ _ _ k fun i hi => by
        rw [mem_tapeRest]; simp [show i < k + n by omega]
    · ext i
      simp only [mem_tapeRest]
      constructor
      · rintro ⟨h, hi⟩; exact ⟨⟨by rwa [← Nat.add_assoc], by omega⟩, hi⟩
      · rintro ⟨⟨h, -⟩, hi⟩; exact ⟨by rwa [Nat.add_assoc], hi⟩
  rw [e, ← PMF.map_comp, tapeHeads_rest T c (k + n) (by omega)]
  -- split the window at `k`
  have hsplit := tapeHeads_split (k + n) (fun r => bitsVal r 0 k) (fun _ => k)
    (fun s s' h => bitsVal_congr s' s 0 0 k fun i hi => by simpa using (h i hi).symm)
    (fun x r => (x, tapeRest r k n))
    (fun _ s s' h => by simp only [tapeRest_congr s s' k n h])
  rw [hsplit]
  have hval : (tapeHeads (k + n)).map (fun r => bitsVal r 0 k) = Pseudocode.uniformBits k := by
    have e2 : (fun r => bitsVal r 0 k) =
        (fun r => bitsVal r 0 k) ∘ (fun s => tapeRest s 0 k) := by
      funext r
      exact bitsVal_congr _ _ _ _ k fun i hi => by rw [mem_tapeRest]; simp [hi]
    rw [e2, ← PMF.map_comp, tapeHeads_rest (k + n) 0 k (by omega), tapeHeads_map_bitsVal]
  rw [hval]
  congr 1
  funext x
  rw [show (fun r => (x, tapeRest r k n)) = (fun s' => (x, s')) ∘ (fun r => tapeRest r k n) from rfl,
    ← PMF.map_comp, tapeHeads_rest (k + n) k n le_rfl]

end Cellcounting.Analysis
