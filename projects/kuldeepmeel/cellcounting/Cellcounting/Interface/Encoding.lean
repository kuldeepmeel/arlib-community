import Cellcounting.Model.Run

/-!
# Encoding: what the correctness proofs read off the charged program

Definitions and `rfl` lemmas only.  Every lemma here is proved by `rfl`.  Every
definition is `noncomputable`, because it reads a sealed carrier, and none of
them performs or charges an operation.  No headline statement mentions anything
in this file.  It does three things.

## 1. The class indirection

`Model/Program.lean` reads its fair bits with `Arlib.Computation.Coins.flip`,
which charges `randOpcode Op .flip`, i.e. `RandOps.charge .flip` under the
instance `Model.Operations.randOps`.  `Model/Run.lean` and the theorem name the
same opcode as `Op.rand RandOp.flip`.  The two are definitionally equal but not
syntactically equal, and `simp` does not unfold an instance projection to see
it.  `randOpcode_eq` collapses the indirection.  `RandOps` is the only
operation class the program goes through.  Its bit operations are charged in
the project's own currency (`Op.bit`, see `Model/Operations.lean`), and the
storage currency `Model.Operations.Cell` is a reducible alias of
`Arlib.Computation.Cell`, so neither needs a lemma.

## 2. The specification's views of a run

The program keeps every number in the sealed carriers `SNat`/`SRat`, read by
their `noncomputable` views `SNat.get`/`SRat.get` of `Model/Operations.lean`.
The views added here are the ones the correctness side quantifies over:

* `estimate I ε δ c`: the answer `Ẑ` of the execution on the coin family `c`.
  `Model/Run.lean`'s `output I ε δ` is the law of `estimate I ε δ` under the
  tape law `tape (tapeLength I ε δ)` (as `PMF.map` of `run`, then of
  `Charged.val`; the rewrite into one `PMF.map` is a theorem, not `rfl`, and
  belongs to `Interface/ProgramModel.lean`).
* `flipsRead I ε δ s`: the number of fair bits read by the execution on the
  tape with heads `s`.  `tapeLength` is the supremum of exactly this function
  (`tapeLength_eq`); proving that supremum is attained, so that the tape never
  truncates a run, is an obligation of the accuracy proof.

## 3. Handles on `Model/` subterms

The fields of `SNat`, `SRat` and `Coins` are private, so a correctness proof
cannot name what a primitive returns except through the views.  For every
primitive of `Model/Operations.lean` there is one `@[simp]` lemma stating its
value through `SNat.get`/`SRat.get` (the cost side is not stated here: time
claims stay on the program side).  `val_flip_ofFinset` restates arlib's
`Coins.val_flip` on the boundary family `Coins.ofFinset s`.  Arlib's lemma
leaves the `Decidable` instance of the membership mentioning `heads'`, so
after `simp` the two sides of a goal can differ only in that instance.

## Correspondence with the transcript

These views are not pseudocode, and they do not restate any step.  The answer
object of S11/S12 (`SRat.output` of the median) is `estimate`.  S0's `L` is
`SNat.inputLength`, whose value (`get_inputLength`) is `Prelude`'s
`inputLength`, the function the cost conjunct is stated in.  The fair bits of
S6/S9/S10 are `Coins.flip` reads (`val_flip_ofFinset`).  Every arithmetic step
of S1–S12 is one of the primitives whose value is stated in §3.
-/

set_option autoImplicit false

namespace Cellcounting.Interface

open Arlib.Computation (Charged Coins RandOp randOpcode)
open Cellcounting.Model.Operations

/-! ## 1. The class indirection -/

/-- **The randomness opcodes of the program's currency**: arlib's
`randOpcode Op o` (through the instance `Model.Operations.randOps`) is
`Op.rand o`. -/
@[simp] theorem randOpcode_eq (o : RandOp) : randOpcode Op o = Op.rand o := rfl

/-! ## 2. Views of a run -/

/-- **The answer of one execution**: the estimate `Ẑ` that `fpras I ε δ`
returns when it reads its fair bits from the coin family `c`.
Specification-only. -/
noncomputable def estimate (I : Instance) (ε δ : ℚ) (c : Coins ℕ) : ℚ :=
  (Program.fpras I ε δ c).val

/-- `estimate` is the value of the program on that coin family. -/
theorem estimate_eq (I : Instance) (ε δ : ℚ) (c : Coins ℕ) :
    estimate I ε δ c = (Program.fpras I ε δ c).val := rfl

/-- **The fair bits one execution reads**: the `Op.rand .flip` count of
`fpras I ε δ` on the tape whose heads are `s`.  Specification-only. -/
noncomputable def flipsRead (I : Instance) (ε δ : ℚ) (s : Finset ℕ) : ℕ :=
  (Program.fpras I ε δ (Coins.ofFinset s)).cost (Op.rand RandOp.flip)

/-- `tapeLength` is the supremum of the bits read over all tapes. -/
theorem tapeLength_eq (I : Instance) (ε δ : ℚ) :
    tapeLength I ε δ = sSup (Set.range (flipsRead I ε δ)) := rfl

/-! ## 3. What each primitive returns -/

/-- One fair bit of the boundary family with heads `s`.  Priority `high`, so
that it fires before arlib's `Coins.val_flip`, whose result carries a
`Decidable` instance stated through `heads'` that does not match `decide (a ∈ s)`
syntactically. -/
@[simp high] theorem val_flip_ofFinset (a : ℕ) (s : Finset ℕ) :
    (Coins.flip a (Coins.ofFinset s) : Program.Prog Bool).val = decide (a ∈ s) := rfl

/-! ### Sealed naturals -/

namespace SNat

@[simp] theorem get_default : (default : SNat).get = 0 := rfl

@[simp] theorem get_lit (k : ℕ) : (SNat.lit k).val.get = k := rfl

@[simp] theorem get_add (x y : SNat) : (SNat.add x y).val.get = x.get + y.get := rfl

@[simp] theorem get_sub (x y : SNat) : (SNat.sub x y).val.get = x.get - y.get := rfl

@[simp] theorem get_mul (x y : SNat) : (SNat.mul x y).val.get = x.get * y.get := rfl

@[simp] theorem get_div (x y : SNat) : (SNat.div x y).val.get = x.get / y.get := rfl

@[simp] theorem get_mod (x y : SNat) : (SNat.mod x y).val.get = x.get % y.get := rfl

@[simp] theorem val_le (x y : SNat) : (SNat.le x y).val = decide (x.get ≤ y.get) := rfl

@[simp] theorem val_lt (x y : SNat) : (SNat.lt x y).val = decide (x.get < y.get) := rfl

@[simp] theorem val_eq (x y : SNat) : (SNat.eq x y).val = decide (x.get = y.get) := rfl

@[simp] theorem get_bitLen (x : SNat) :
    (SNat.bitLen x).val.get = Cellcounting.bitLen x.get := rfl

@[simp] theorem get_size (x : SNat) : (SNat.size x).val.get = Nat.size x.get := rfl

@[simp] theorem get_pow2 (x : SNat) : (SNat.pow2 x).val.get = 2 ^ x.get := rfl

@[simp] theorem get_toRat (x : SNat) : (SNat.toRat x).val.get = (x.get : ℚ) := rfl

@[simp] theorem val_index (x : SNat) : (SNat.index x).val = x.get := rfl

@[simp] theorem get_inputLength (I : Instance) (ε δ : ℚ) :
    (SNat.inputLength I ε δ).val.get =
      Cellcounting.inputLength I ε δ := rfl

end SNat

/-! ### Sealed rationals -/

namespace SRat

@[simp] theorem get_default : (default : SRat).get = 0 := rfl

@[simp] theorem get_lit (q : ℚ) : (SRat.lit q).val.get = q := rfl

@[simp] theorem get_add (x y : SRat) : (SRat.add x y).val.get = x.get + y.get := rfl

@[simp] theorem get_sub (x y : SRat) : (SRat.sub x y).val.get = x.get - y.get := rfl

@[simp] theorem get_mul (x y : SRat) : (SRat.mul x y).val.get = x.get * y.get := rfl

@[simp] theorem get_div (x y : SRat) : (SRat.div x y).val.get = x.get / y.get := rfl

@[simp] theorem val_le (x y : SRat) : (SRat.le x y).val = decide (x.get ≤ y.get) := rfl

@[simp] theorem val_lt (x y : SRat) : (SRat.lt x y).val = decide (x.get < y.get) := rfl

@[simp] theorem get_floor (x : SRat) : (SRat.floor x).val.get = ((⌊x.get⌋ : ℤ) : ℚ) := rfl

@[simp] theorem get_natFloor (x : SRat) : (SRat.natFloor x).val.get = ⌊x.get⌋₊ := rfl

@[simp] theorem get_natCeil (x : SRat) : (SRat.natCeil x).val.get = ⌈x.get⌉₊ := rfl

@[simp] theorem get_zpow2 (x : SRat) :
    (SRat.zpow2 x).val.get = (2 : ℚ) ^ (⌊x.get⌋ : ℤ) := rfl

@[simp] theorem val_output (x : SRat) : (SRat.output x).val = x.get := rfl

end SRat

/-! ### Addressing -/

@[simp] theorem val_get {α : Type} [Inhabited α] (l : List α) (i : ℕ) :
    (Model.Operations.get l i).val = l.getD i default := rfl

@[simp] theorem val_set {α : Type} (l : List α) (i : ℕ) (a : α) :
    (Model.Operations.set l i a).val = l.set i a := rfl

@[simp] theorem val_push {α : Type} (l : List α) (a : α) :
    (Model.Operations.push l a).val = l ++ [a] := rfl

@[simp] theorem val_replicate {α : Type} (k : ℕ) (a : α) :
    (Model.Operations.replicate k a).val = List.replicate k a := rfl

@[simp] theorem val_idxEq (i j : ℕ) : (Model.Operations.idxEq i j).val = decide (i = j) := rfl

@[simp] theorem val_idxLt (i j : ℕ) : (Model.Operations.idxLt i j).val = decide (i < j) := rfl

end Cellcounting.Interface
