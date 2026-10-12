import Esa22Copy.Model.Run

/-!
# Encoding: the specification's handles on the F0-Estimator program

`Model/Program.lean` writes Algorithm 1 (`algo:afinal`, esa22-final.tex:422-445)
against arlib's sealed carriers and operation classes.  This file gives the
proofs three kinds of handle on it, and nothing else.  Every lemma here is
`rfl`; nothing here charges; no headline statement mentions anything here.

## 1. Collapsing the class indirection

The program charges `Roster.opcode Op o` and `randOpcode Op o` and occupies
`RosterCells.cell ι`; the statements and the cost bookkeeping speak of
`StdOp.roster o`, `StdOp.rand o` and `Cell.roster`.  These are definitionally
equal and not syntactically equal.  One `@[simp]` lemma per class the program
uses — `RosterOps`, `RandOps`, `RosterCells` — and no more: the program uses no
other carrier (no `Slot`, `Num`, `Dict`, …), and declares no currency of its own.

## 2. The specification's views of a run

The program's state `Program.State α` holds a sealed `Roster α` and a sealed
`Sampler`.  The analysis reasons about the set `𝒳` and the level `k` of
`p = 2⁻ᵏ`, so `Snapshot` is that pair and `view` reads it off a state through
arlib's specification-only accessors (`Roster.toFinset`, `Sampler.levelOf`).
`view` is `noncomputable` on purpose: it is a reading for invariants, never a
line of the algorithm.  `acceptsAt k b` is the outcome of the Bernoulli(`2⁻ᵏ`)
draw of line `afinal-pick` stated through the block's bits; arlib's
`Sampler.val_accept` asks each development for exactly this one-line bridge
(`val_accept_eq`).

## 3. Handles on `Model/` subterms

* `loop thr s tape` — the `for i = 1 to m` fold inside `Program.estimate`,
  before line `output`; `estimate_eq` splits `estimate` into `loop` then
  `Program.report`.
* `step_none`, `report_none` — the halting at `⊥` (line `fail`): after `none`
  every later iteration and the report are `pure none`.
* `report_some_val` — line `output`, `|𝒳|/p = |𝒳| · 2ᵏ`, read off a state.

## Correspondence with the restatement's `algorithmTranscript`

| transcript step | `Model/Program.lean` | handle here |
|---|---|---|
| input | `Program.estimate thr s tape` | `estimate_eq` |
| init (`p ← 1`, `𝒳 ← ∅`) | `Program.initial` | `view_initial` |
| init (`thresh`) | `Esa22Copy.thresh`, applied in `Esa22Copy.run` | — |
| line:beginfor | `Charged.foldl (Program.step thr) (s.zip tape)` | `loop` |
| line:afinal-drop | `Roster.erase` in `Program.arrival` | `rosterOps_charge` |
| line:afinal-pick | `Sampler.accept`, `Roster.insert` in `Program.arrival` | `acceptsAt`, `val_accept_eq` |
| line:Ifbegin (`|𝒳| = thresh`) | first `Roster.cardEq` in `Program.step` | — |
| line:final-throw | `Program.thin` (`Roster.filterErase`, `Coins.flip`) | — |
| line:p | `Sampler.halve` in `Program.step` | `randOps_charge` |
| line:check / line:fail | second `Roster.cardEq`; `none` | `step_none`, `report_none` |
| line:output | `Program.report` (`Roster.size`, `Sampler.inflate`) | `report_some_val` |

No mismatch between the transcript and `Model/Program.lean` was found: the line
order drop → pick → test → throw → halve → test is the program's, both tests
are equalities, the throw tosses one coin per element of `𝒳`, and `⊥` halts
(as an `Option`-carrying accumulator on which every later step is `pure none`).
-/

set_option autoImplicit false

namespace Esa22Copy.Interface

open Arlib.Computation (Roster RosterOp RosterOps RosterCells RandOp RandOps StdOp Block
  Sampler Charged)
open Esa22Copy.Model.Operations (Op Cell)

/-! ## 1. Collapsing the class indirection -/

/-- The program's roster opcodes are arlib's standard `StdOp.roster`. -/
@[simp] theorem rosterOps_charge (o : RosterOp) : (RosterOps.charge o : Op) = StdOp.roster o :=
  rfl

/-- The program's randomness opcodes are arlib's standard `StdOp.rand`. -/
@[simp] theorem randOps_charge (o : RandOp) : (RandOps.charge o : Op) = StdOp.rand o :=
  rfl

/-- An element of the sample set occupies one `Cell.roster`. -/
@[simp] theorem rosterCells_cell (ι : Type) :
    (RosterCells.cell ι : Cell) = Arlib.Computation.Cell.roster :=
  rfl

/-! ## 2. The specification's views of a run -/

/-- **What the analysis sees of the algorithm's state**: the sample set `𝒳` and
the level `k` of the sampling rate `p = 2⁻ᵏ`. -/
structure Snapshot (α : Type) where
  /-- The sample set `𝒳`. -/
  sample : Finset α
  /-- The level `k`, with `p = 2⁻ᵏ`. -/
  level : ℕ

variable {α : Type} [DecidableEq α] {w : ℕ}

/-- **The specification-only reading of a program state.** -/
noncomputable def view (st : Program.State α) : Snapshot α :=
  ⟨st.samples.toFinset, st.sampler.levelOf⟩

@[simp] theorem view_sample (st : Program.State α) :
    (view st).sample = st.samples.toFinset := rfl

@[simp] theorem view_level (st : Program.State α) :
    (view st).level = st.sampler.levelOf := rfl

/-- Line init: `𝒳 = ∅`, `p = 1`. -/
@[simp] theorem view_initial : view (Program.initial : Program.State α) = ⟨∅, 0⟩ := rfl

/-- **The outcome of the Bernoulli(`2⁻ᵏ`) draw** of line `afinal-pick` against a
block `b`: its first `k` bits are all one.  `false` if the block is shorter than
`k` (arlib's junk value; the analysis must show `k ≤ w` at every draw). -/
noncomputable def acceptsAt (k : ℕ) (b : Block w) : Bool :=
  if k ≤ w then ((List.ofFn b.get).take k).all id else false

/-- The bridge arlib's `Sampler.val_accept` asks for: a draw against a sampler
at level `k` is `acceptsAt k`. -/
@[simp] theorem val_accept_eq {κ κₛ : Type} [DecidableEq κ] [RandOps κ] (b : Block w)
    (s : Sampler) : (Sampler.accept b s : Charged κ κₛ Bool).val = acceptsAt s.levelOf b :=
  rfl

/-! ## 3. Handles on `Model/` subterms -/

/-- **The loop `for i = 1 to m`** of `Program.estimate`, before line `output`:
the final state, or `none` if the run output `⊥`. -/
noncomputable def loop (thr : ℕ) (s : List α) (tape : List (Program.Randomness α w)) :
    Charged Op Cell (Option (Program.State α)) :=
  Charged.foldl (Program.step thr) (s.zip tape) (some Program.initial)

/-- `Program.estimate` is `loop` followed by `Program.report`. -/
theorem estimate_eq (thr : ℕ) (s : List α) (tape : List (Program.Randomness α w)) :
    Program.estimate thr s tape = loop thr s tape >>= Program.report :=
  rfl

/-- **Halting at `⊥`**: once a run has output `⊥`, an iteration does nothing. -/
@[simp] theorem step_none (thr : ℕ) (ar : α × Program.Randomness α w) :
    Program.step thr none ar = pure none :=
  rfl

omit [DecidableEq α] in
/-- A run that output `⊥` reports `⊥`, at no cost. -/
@[simp] theorem report_none : Program.report (α := α) none = pure none :=
  rfl

omit [DecidableEq α] in
/-- **Line output**: a surviving run reports `|𝒳| · 2ᵏ`. -/
@[simp] theorem report_some_val (st : Program.State α) :
    (Program.report (some st)).val = some (st.samples.card * 2 ^ st.sampler.levelOf) :=
  rfl

end Esa22Copy.Interface
