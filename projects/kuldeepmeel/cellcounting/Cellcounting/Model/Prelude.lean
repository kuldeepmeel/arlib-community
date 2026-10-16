import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Cell-bounded contingency tables: vocabulary and the counted quantity

The paper (Theorem `thm:main`, `sections/introduction.tex:21-35`) approximately
counts the nonnegative integer `m × n` matrices with prescribed row sums `r`,
column sums `c` and entrywise upper bounds `b`.  This file fixes what an input
is, how long its binary encoding is, and the number `Z(r,c,b)` the theorem is
about.  It holds definitions only.

## Correspondence ledger

* `sections/introduction.tex:4-6` (dimensions, margins, bounds, binary
  encoding) -> `Cellcounting.Instance`.  The paper's "equal totals" side
  condition is **not** a field: it is a statement decision (restatement
  `hypothesisLedger`, verdict `discharge-internally`).  Unequal totals make the
  feasible set empty, and the program checks the totals itself.
  Nonnegativity of `r, c, b` is by typing (`ℕ`).
* `eq:feasible-set` (`sections/introduction.tex:7-14`) -> `Instance.Omega`:
  matrices `X : Fin m → Fin n → ℕ` with `∑ j, X i j = r i`, `∑ i, X i j = c j`
  and `X i j ≤ b i j`.  The entry bound is enforced by drawing each entry from
  `Finset.range (b i j + 1)`, which is also what makes the set finite.
* `Z(r,c,b) = |Ω(r,c,b)|` -> `Instance.Z`.  Each table is counted once.
* "`L` is the total binary input length, including the accuracy parameters"
  -> `inputLength`.  The paper never fixes an encoding; this is a **statement
  decision** (restatement `modelingChoices`, "Encoding defining L").  Every
  natural number costs `Nat.size k + 1` bits (`bitLen`), so every cell, even a
  zero-bound one, costs at least one bit (the paper uses `d = O(L)`); a rational
  costs the lengths of its numerator's absolute value and of its denominator
  (`ratLen`), so `⌈log₂ ε⁻¹⌉ ≤ L` (the paper uses this at `scales.tex:86`).
  `Model/Program.lean` computes the parameter `K` from exactly this function,
  read through the charged primitive `SNat.inputLength` of
  `Model/Operations.lean`, whose value is `inputLength` itself.

No Mathlib declaration counts contingency tables, so there is no library
cross-check for `Instance.Z`.
-/

namespace Cellcounting

/-! ## Vocabulary -/

/-- An input `(m, n, r, c, b)`: dimensions, row margins, column margins and cell
bounds, all natural numbers given in binary.  The paper's `m, n ≥ 1` is a
hypothesis of the theorem, not a field; the equal-totals condition is neither. -/
structure Instance where
  /-- Number of rows. -/
  m : ℕ
  /-- Number of columns. -/
  n : ℕ
  /-- Row margins `r_i`. -/
  r : Fin m → ℕ
  /-- Column margins `c_j`. -/
  c : Fin n → ℕ
  /-- Cell upper bounds `b_ij`; zero is allowed. -/
  b : Fin m → Fin n → ℕ

/-- Binary length of a natural number in the fixed encoding: its bit size plus
one, so that `0` costs one bit. -/
def bitLen (k : ℕ) : ℕ := Nat.size k + 1

/-- Binary length of a rational: the lengths of the absolute value of its
numerator and of its denominator. -/
def ratLen (q : ℚ) : ℕ := bitLen q.num.natAbs + bitLen q.den

/-- **The input length `L`** of `(m, n, r, c, b, ε, δ)`: the sum of the binary
lengths of `m`, `n`, every margin, every cell bound (including zero bounds),
and the two accuracy parameters. -/
def inputLength (I : Instance) (ε δ : ℚ) : ℕ :=
  bitLen I.m + bitLen I.n + ∑ i, bitLen (I.r i) + ∑ j, bitLen (I.c j)
    + ∑ i, ∑ j, bitLen (I.b i j) + ratLen ε + ratLen δ

/-! ## The quantity -/

/-- **`Ω(r,c,b)`** (`eq:feasible-set`): the nonnegative integer matrices with
row sums `r`, column sums `c`, and `X i j ≤ b i j` for every cell. -/
def Instance.Omega (I : Instance) : Finset (Fin I.m → Fin I.n → ℕ) :=
  (Fintype.piFinset fun i => Fintype.piFinset fun j => Finset.range (I.b i j + 1)).filter
    (fun X => (∀ i, ∑ j, X i j = I.r i) ∧ ∀ j, ∑ i, X i j = I.c j)

/-- **`Z(r,c,b) = |Ω(r,c,b)|`**, the number of cell-bounded contingency tables:
the quantity the theorem approximates. -/
def Instance.Z (I : Instance) : ℕ := I.Omega.card

end Cellcounting
