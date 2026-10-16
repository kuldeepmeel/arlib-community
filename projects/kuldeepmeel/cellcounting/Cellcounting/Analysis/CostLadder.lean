import Cellcounting.Analysis.CostScale

/-!
# A power ladder for polynomial cost bounds

INTERNAL.  Small closure facts for bounds of the form `a ≤ S ^ i` with `2 ≤ S`:
products add exponents, sums of two cost one more power, constants below `2 ^ j`
fit under `S ^ j`, and a binary length costs one more power than its value.  The
preprocessing cost proofs (`prep_cost` and its children) push every value and every
step price through these.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

/-- INTERNAL: products add exponents. -/
theorem pw_mul {S a b i j : ℕ} (ha : a ≤ S ^ i) (hb : b ≤ S ^ j) : a * b ≤ S ^ (i + j) := by
  rw [pow_add]; exact Nat.mul_le_mul ha hb

/-- INTERNAL: raising the exponent. -/
theorem pw_mono {S a i j : ℕ} (hS : 2 ≤ S) (ha : a ≤ S ^ i) (hij : i ≤ j) : a ≤ S ^ j :=
  ha.trans (Nat.pow_le_pow_right (by omega) hij)

/-- INTERNAL: a sum of two costs one more power. -/
theorem pw_add {S a b i : ℕ} (hS : 2 ≤ S) (ha : a ≤ S ^ i) (hb : b ≤ S ^ i) :
    a + b ≤ S ^ (i + 1) := by
  rw [pow_succ]; have := Nat.mul_le_mul_left (S ^ i) hS; omega

/-- INTERNAL: a constant below `2 ^ j` is below `S ^ j`. -/
theorem pw_const {S c j : ℕ} (hS : 2 ≤ S) (h : c ≤ 2 ^ j) : c ≤ S ^ j :=
  h.trans (Nat.pow_le_pow_left hS j)

/-- INTERNAL: every power is positive. -/
theorem pw_one {S j : ℕ} (hS : 2 ≤ S) : 1 ≤ S ^ j := Nat.one_le_pow _ _ (by omega)

/-- INTERNAL: a binary length costs one more power than its value. -/
theorem pw_bitLen {S a i : ℕ} (hS : 2 ≤ S) (ha : a ≤ S ^ i) : bitLen a ≤ S ^ (i + 1) := by
  have h1 := bitLen_le_succ a
  have := pw_add hS ha (pw_one hS (j := i)); omega

/-- INTERNAL: `S ≤ S ^ 1`, for feeding plain bounds into the ladder. -/
theorem pw_self {S a : ℕ} (ha : a ≤ S) : a ≤ S ^ 1 := by rwa [pow_one]

/-- INTERNAL: a constant multiple of a power. -/
theorem pw_cmul {S c a i j : ℕ} (hS : 2 ≤ S) (hc : c ≤ 2 ^ j) (ha : a ≤ S ^ i) :
    c * a ≤ S ^ (j + i) := pw_mul (pw_const hS hc) ha

/-- INTERNAL: a read with a default returns an entry or the default. -/
theorem getD_mem_or {α : Type} (l : List α) (i : ℕ) (d : α) : l.getD i d ∈ l ∨ l.getD i d = d := by
  induction l generalizing i with
  | nil => right; simp
  | cons a l ih =>
    cases i with
    | zero => left; simp
    | succ i =>
      rcases ih i with h | h
      · left; simp only [List.getD_cons_succ]; exact List.mem_cons_of_mem a h
      · right; simpa using h

/-- INTERNAL: a property of every entry and of the default holds of every read. -/
theorem getD_prop {α : Type} {P : α → Prop} (l : List α) (i : ℕ) (d : α) (hl : ∀ a ∈ l, P a)
    (hd : P d) : P (l.getD i d) :=
  (getD_mem_or l i d).elim (hl _) (fun h => by rw [h]; exact hd)

/-- INTERNAL: a property of every entry and of the written value holds after a write. -/
theorem set_prop {α : Type} {P : α → Prop} (l : List α) (i : ℕ) (a : α) (hl : ∀ b ∈ l, P b)
    (ha : P a) : ∀ b ∈ l.set i a, P b := fun _ hb =>
  (List.mem_or_eq_of_mem_set hb).elim (hl _) (fun h => by rw [h]; exact ha)

end Cellcounting.Analysis
