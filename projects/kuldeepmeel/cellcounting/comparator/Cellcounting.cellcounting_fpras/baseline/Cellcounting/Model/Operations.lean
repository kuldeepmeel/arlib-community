import Arlib.Computation.Charged
import Arlib.Computation.Rand
import Arlib.Computation.Std
import Mathlib.Data.Rat.Floor
import Cellcounting.Model.Prelude

/-!
# The cost currency: bit operations on sealed numbers, and fair coins

The paper bounds "total bit operations" (`sections/introduction.tex:30-41`):
preprocessing, max-flow tests, random-bit generation, all rational and integer
arithmetic, and producing the output.  Arlib's `Num` carrier charges one unit
per arithmetic operation whatever the size of its operands.  Under that unit-cost
model repeated squaring builds exponentially long numbers in polynomially many
steps, so a polynomial bound would say much less than the paper claims
(restatement `modelingChoices`, "Cost model for total bit operations": unit-cost
arithmetic would be "a strictly weaker (and potentially vacuous) claim").  The
paper counts primitives Arlib does not supply, so this file declares a
project-local currency (outcome 2 of the brief).

## The currency

* `Op.bit` — one bit operation.  Every arithmetic primitive below charges a
  **number of `Op.bit`s that grows with the binary length of its operands**:
  linear for addition, subtraction, comparison and bit-length reads; the product
  of the operand lengths for multiplication and division of naturals; and the
  product of the (length + 1)s of the two operands for rational operations, which
  covers the `gcd` normalisation.  These are the schoolbook bit complexities.
  They are declared prices, not proved ones.  A different polynomial pricing
  would change the constants and exponent in `fpras_time`, but not whether a
  polynomial bound exists.  Reading the input length `L` (`SNat.inputLength`)
  costs `L` bit operations, the price of one pass over the encoded input; its
  value is `Model/Prelude.lean`'s `inputLength`, so the `L` the program computes
  its parameters from is literally the `L` of the theorem.
* `Op.rand o` — the randomness operations of `Arlib.Computation.RandOp`.  The
  program reads its fair bits with `Arlib.Computation.Coins.flip`, which charges
  one `Op.rand .flip`.  The other three `RandOp`s are present only because
  `RandOps.charge` must be injective, and the program never performs them.

The theorem prices every operation at one step (`rate = Rate.unit Op`), so the
step count of a run is its number of bit operations plus its number of coin
reads.

## Sealed numbers

`SNat` and `SRat` hold a natural number and a rational number.  Their
constructors and fields are private, and their views `SNat.get`/`SRat.get` are
`noncomputable`.  So a program cannot create, inspect, compare or combine one
except through the charged primitives below, and every quantity the algorithm
branches on comes from a charged comparison.

## Addressing

The program also keeps ordinary `List`s of these values (margins, residual
capacities, multiplier tables, membership bits of the paired state) and plain
`ℕ` positions into them.  Reading or writing position `i` of a list costs
`i + 1` (`get`, `set`); appending costs the list length (`push`); allocating a
list of length `k` costs `k + 1` (`replicate`); and comparing two positions
costs their bit lengths (`idxEq`, `idxLt`).  Arithmetic on positions and loop
indices (the round index a `Charged.repeatFor` supplies, `i + 1`, `2 * i`) is
uncharged control.  This is the one place the model is coarser than "every bit
operation is charged".  It is a **model gap**, recorded in `Model/Program.lean`'s
ledger.  These numbers are bounded by the shape of the input and of the
paper's parameters, never by data that can grow.

## What certifies these prices

Nothing needs to: they are definitions of the currency, and `fpras_time` is a
statement in it.  No `Prior` field is attached to this file.
-/

set_option autoImplicit false

namespace Cellcounting.Model

namespace Operations

open Arlib.Computation

/-- **The currency.**  One bit operation, or one standard randomness
operation. -/
inductive Op where
  /-- One bit operation. -/
  | bit
  /-- One randomness operation; the program performs only `RandOp.flip`. -/
  | rand (o : RandOp)
  deriving DecidableEq

/-- Every operation, as a list. -/
def Op.all : List Op :=
  [.bit, .rand .flip, .rand .accept, .rand .halve, .rand .inflate]

/-- The currency is finite, so `CostVec.steps` can sum over it. -/
instance : Fintype Op :=
  Fintype.ofList Op.all (by intro o; cases o with
    | bit => decide
    | rand r => cases r <;> decide)

/-- The randomness operations, filed under `Op.rand`. -/
instance randOps : RandOps Op where
  charge := Op.rand
  charge_injective := by intro a b h; cases h; rfl

/-- The storage currency.  No space claim is made, so Arlib's standard kinds are
used unchanged. -/
abbrev Cell := Arlib.Computation.Cell

/-- **The rate the theorem uses**: every operation of the currency is one
step. -/
abbrev rate : Rate Op := Rate.unit Op

/-- INTERNAL: charge `k` bit operations and return `a`.  Private, so it is not a
primitive a program can call; every public wrapper below fixes its own `k`. -/
private def bits {α : Type} (k : ℕ) (a : α) : Charged Op Cell α :=
  Charged.opMany Op.bit k a

/-! ## Sealed naturals -/

/-- **A sealed natural number.**  Built only by the charged primitives of this
file, read only through them. -/
structure SNat where
  private mk ::
  private raw : ℕ

/-- **A sealed rational number.** -/
structure SRat where
  private mk ::
  private raw : ℚ

namespace SNat

/-- The number held.  **Specification-only.** -/
noncomputable def get (x : SNat) : ℕ := x.raw

/-- A constant or an input number, at the price of its length. -/
def lit (k : ℕ) : Charged Op Cell SNat := bits (bitLen k) ⟨k⟩

/-- Addition. -/
def add (x y : SNat) : Charged Op Cell SNat :=
  bits (bitLen x.raw + bitLen y.raw) ⟨x.raw + y.raw⟩

/-- Truncated subtraction. -/
def sub (x y : SNat) : Charged Op Cell SNat :=
  bits (bitLen x.raw + bitLen y.raw) ⟨x.raw - y.raw⟩

/-- Multiplication (schoolbook). -/
def mul (x y : SNat) : Charged Op Cell SNat :=
  bits (bitLen x.raw * bitLen y.raw) ⟨x.raw * y.raw⟩

/-- Floor division (`x / 0 = 0`). -/
def div (x y : SNat) : Charged Op Cell SNat :=
  bits (bitLen x.raw * bitLen y.raw) ⟨x.raw / y.raw⟩

/-- Remainder. -/
def mod (x y : SNat) : Charged Op Cell SNat :=
  bits (bitLen x.raw * bitLen y.raw) ⟨x.raw % y.raw⟩

/-- `x ≤ y`. -/
def le (x y : SNat) : Charged Op Cell Bool :=
  bits (bitLen x.raw + bitLen y.raw) (decide (x.raw ≤ y.raw))

/-- `x < y`. -/
def lt (x y : SNat) : Charged Op Cell Bool :=
  bits (bitLen x.raw + bitLen y.raw) (decide (x.raw < y.raw))

/-- `x = y`. -/
def eq (x y : SNat) : Charged Op Cell Bool :=
  bits (bitLen x.raw + bitLen y.raw) (decide (x.raw = y.raw))

/-- The encoded length `bitLen x = Nat.size x + 1` of `Model/Prelude.lean`. -/
def bitLen (x : SNat) : Charged Op Cell SNat :=
  bits (Cellcounting.bitLen x.raw) ⟨Cellcounting.bitLen x.raw⟩

/-- The bit size `Nat.size x`, so that `Nat.clog 2 x = Nat.size (x - 1)`. -/
def size (x : SNat) : Charged Op Cell SNat :=
  bits (Cellcounting.bitLen x.raw) ⟨Nat.size x.raw⟩

/-- `2 ^ x`, at the price of the length of the result. -/
def pow2 (x : SNat) : Charged Op Cell SNat :=
  bits (x.raw + 1) ⟨2 ^ x.raw⟩

/-- The same number as a sealed rational. -/
def toRat (x : SNat) : Charged Op Cell SRat :=
  bits (Cellcounting.bitLen x.raw) ⟨(x.raw : ℚ)⟩

/-- **Read a number as a position or a loop count**, at the price of its
length.  This is how a computed count becomes the range of a
`Charged.repeatFor`, and how a drawn index addresses a list. -/
def index (x : SNat) : Charged Op Cell ℕ :=
  bits (Cellcounting.bitLen x.raw) x.raw

end SNat

/-- A default sealed natural (zero), so lists of them can be read with a
fallback. -/
instance : Inhabited SNat := ⟨⟨0⟩⟩

namespace SRat

/-- The number held.  **Specification-only.** -/
noncomputable def get (x : SRat) : ℚ := x.raw

/-- A constant or an input rational, at the price of its length. -/
def lit (q : ℚ) : Charged Op Cell SRat := bits (ratLen q) ⟨q⟩

/-- Addition. -/
def add (x y : SRat) : Charged Op Cell SRat :=
  bits ((ratLen x.raw + 1) * (ratLen y.raw + 1)) ⟨x.raw + y.raw⟩

/-- Subtraction. -/
def sub (x y : SRat) : Charged Op Cell SRat :=
  bits ((ratLen x.raw + 1) * (ratLen y.raw + 1)) ⟨x.raw - y.raw⟩

/-- Multiplication. -/
def mul (x y : SRat) : Charged Op Cell SRat :=
  bits ((ratLen x.raw + 1) * (ratLen y.raw + 1)) ⟨x.raw * y.raw⟩

/-- Division (`x / 0 = 0`; the program guards every division it relies on). -/
def div (x y : SRat) : Charged Op Cell SRat :=
  bits ((ratLen x.raw + 1) * (ratLen y.raw + 1)) ⟨x.raw / y.raw⟩

/-- `x ≤ y`. -/
def le (x y : SRat) : Charged Op Cell Bool :=
  bits ((ratLen x.raw + 1) * (ratLen y.raw + 1)) (decide (x.raw ≤ y.raw))

/-- `x < y`. -/
def lt (x y : SRat) : Charged Op Cell Bool :=
  bits ((ratLen x.raw + 1) * (ratLen y.raw + 1)) (decide (x.raw < y.raw))

/-- `⌊x⌋`, as a rational. -/
def floor (x : SRat) : Charged Op Cell SRat :=
  bits ((ratLen x.raw + 1) * (ratLen x.raw + 1)) ⟨((⌊x.raw⌋ : ℤ) : ℚ)⟩

/-- `⌊x⌋₊`, as a natural number (zero for negative `x`). -/
def natFloor (x : SRat) : Charged Op Cell SNat :=
  bits ((ratLen x.raw + 1) * (ratLen x.raw + 1)) ⟨⌊x.raw⌋₊⟩

/-- `⌈x⌉₊`, as a natural number (zero for negative `x`). -/
def natCeil (x : SRat) : Charged Op Cell SNat :=
  bits ((ratLen x.raw + 1) * (ratLen x.raw + 1)) ⟨⌈x.raw⌉₊⟩

/-- `2 ^ ⌊x⌋` for an integer exponent of either sign, at the price of the length
of the result. -/
def zpow2 (x : SRat) : Charged Op Cell SRat :=
  bits (ratLen x.raw + (⌊x.raw⌋ : ℤ).natAbs + 1) ⟨(2 : ℚ) ^ (⌊x.raw⌋ : ℤ)⟩

/-- **Write the answer.**  The paper's cost includes producing the output; this
is the one place a rational leaves the sealed world, and it pays its length. -/
def output (x : SRat) : Charged Op Cell ℚ :=
  bits (ratLen x.raw) x.raw

end SRat

/-- A default sealed rational (zero). -/
instance : Inhabited SRat := ⟨⟨0⟩⟩

/-! ## The input length -/

/-- **Read the input length** `L = inputLength I ε δ`: the very function of
`Model/Prelude.lean` that the cost conjunct of the theorem is stated in, at the
price of `L` bit operations, one pass over the encoded input.  This is the one
site where the program learns `L` (restatement caller guard
"shared-inputLength-contract": Program must not re-derive an equivalent). -/
def SNat.inputLength (I : Instance) (ε δ : ℚ) : Charged Op Cell SNat :=
  bits (Cellcounting.inputLength I ε δ) ⟨Cellcounting.inputLength I ε δ⟩

/-! ## Addressing -/

/-- Read position `i` of a list (the default value past its end), at the price
of walking to it. -/
def get {α : Type} [Inhabited α] (l : List α) (i : ℕ) : Charged Op Cell α :=
  bits (i + 1) (l.getD i default)

/-- Overwrite position `i` of a list, at the price of walking to it. -/
def set {α : Type} (l : List α) (i : ℕ) (a : α) : Charged Op Cell (List α) :=
  bits (i + 1) (l.set i a)

/-- Append one entry, at the price of walking the list. -/
def push {α : Type} (l : List α) (a : α) : Charged Op Cell (List α) :=
  bits (l.length + 1) (l ++ [a])

/-- Allocate a list of `k` copies of `a`. -/
def replicate {α : Type} (k : ℕ) (a : α) : Charged Op Cell (List α) :=
  bits (k + 1) (List.replicate k a)

/-- Compare two positions for equality. -/
def idxEq (i j : ℕ) : Charged Op Cell Bool :=
  bits (bitLen i + bitLen j) (decide (i = j))

/-- Compare two positions. -/
def idxLt (i j : ℕ) : Charged Op Cell Bool :=
  bits (bitLen i + bitLen j) (decide (i < j))

end Operations

end Cellcounting.Model
