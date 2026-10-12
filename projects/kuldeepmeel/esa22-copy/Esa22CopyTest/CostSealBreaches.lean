import Esa22Copy.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Roster
import Arlib.Computation.Rand
import Arlib.Computation.Slot
import Arlib.Computation.Std

/-!
# The seal, made to fail

`Model/Program.lean` runs `#programSeal` on every build, and it passes.  That
is not evidence.  An audit that has never rejected anything is
not known to reject anything, and the two commands are exactly the kind of code
whose failure mode is silence — a filter that matches nothing reports a clean
build.

Each test below is a `#guard_msgs` block: it **passes when the checker produces
exactly the stated error**, so a future change that quietly opens one of these
routes turns this file red.  This is the same discipline as
`ArlibTest/Computation.lean` §3, applied to the checkers rather than to the
compiler.

Every planted cheat is placed in the canonical `Esa22Copy.Program` namespace,
the only one `#programSeal` accepts.  Each successive seal sees all cheats
declared so far, so its expected error checks that the latest breach is
rejected alongside the earlier ones.

## What is covered

* §1 — the cheats the *compiler* rejects, so that a change making one of them
  compile is caught before either seal is reached.
* §2 — `#programSeal`: the routes past the compiler, inside the algorithm —
  including the one that only a *transitive* scan catches, which is the property
  `reaches` exists for and the first test to run if it is ever touched.
The positive direction is covered by the main build: `Model/Program.lean` runs
the command over the real algorithm and it reports clean.
-/

namespace Esa22CopyTest

open Arlib.Computation

/-! ## 1. What the compiler rejects on its own -/

/-! Copying a computation's result to drop its charges.  This is the cheat that
would make every bound in the development vacuous, and it does not compile,
because `Charged.val` is `noncomputable`. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Charged.val', which is 'noncomputable'
-/
#guard_msgs in
def dropTally (p : Charged StdOp Cell Nat) : Charged StdOp Cell Nat := pure p.val

/-! Reading a dictionary's size without asking it.  `Roster.card` is the
specification's view and is `noncomputable`, so a program that wants the number
must call `Roster.size` and pay. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Roster.card', which is 'noncomputable'
-/
#guard_msgs in
def freeSize (d : Roster Nat) : Nat := d.card

/-! Forging a tally.  There is no syntax for asserting what something cost. -/
/--
error: Invalid `⟨...⟩` notation: Constructor for `Arlib.Computation.Charged` is marked as private
-/
#guard_msgs in
example : Charged StdOp Cell Nat := ⟨0, 0, 1⟩

/-! ## 2. `#programSeal` — the routes past the compiler -/

end Esa22CopyTest

namespace Esa22Copy.Program

open Arlib.Computation

/-! **Laundering a tally through a change of currency.**  `exchange` is
computable and takes a `Charged` to a `Charged`, so nothing the compiler checks
stands in the way; at a rate of zero it re-prices any computation at nothing. -/
def cheatExchange (p : Charged StdOp Cell Nat) : Charged StdOp Cell Nat :=
  Charged.exchange (fun _ => (0 : CostVec StdOp)) p

/--
error: Seal breach in Esa22Copy.Program: [(Esa22Copy.Program.cheatExchange,
  Arlib.Computation.Charged.exchange)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22Copy.Program

/-! **Silencing the compiler.**  Writing `noncomputable def` turns off the half
of the seal §1 relies on.  Nothing else about this declaration is wrong, which is
the point: the marker alone is the breach. -/
noncomputable def cheatNoncomputable : Real := 0

/--
error: Seal breach in Esa22Copy.Program: [(Esa22Copy.Program.cheatNoncomputable, noncomputableProgram),
 (Esa22Copy.Program.cheatExchange,
  Arlib.Computation.Charged.exchange)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22Copy.Program

/-! **Projecting a dictionary's contents through the eliminator.**  `casesOn` is
generated public even though the constructor is private, and it is compiled, so
this is the one route the compiler genuinely leaves open. -/
def cheatCasesOn (d : Roster Nat) : Nat :=
  Roster.casesOn (motive := fun _ => Nat) d (fun elems _ => elems.length)

/--
error: Seal breach in Esa22Copy.Program: [(Esa22Copy.Program.cheatCasesOn, Arlib.Computation.Roster.casesOn),
 (Esa22Copy.Program.cheatNoncomputable, noncomputableProgram),
 (Esa22Copy.Program.cheatExchange,
  Arlib.Computation.Charged.exchange)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22Copy.Program

/-! **Pricing a line by hand.**  `Charged.op o a` is arlib's escape hatch — one
operation of the currency, returning a value the algorithm computed for itself —
and a program may not call it inline. Standard operations come from arlib;
project-local operations come from `Model/Operations.lean`.

The cheat below is exactly what the algorithm used to do, and it is the shape to
watch for: the charge says "one coin" and the argument is an `O(level)` scan of a
bare bit block, read at a level nobody paid for.  The seal cannot see that the
argument is expensive — nothing can — so it forbids the escape hatch directly in
`Program.lean`. The honest fix for a line that genuinely needs one is to expose
the primitive in the operation model. -/
-- The original wrote this against the development's own `BitBlock` and
-- `acceptsAt`, which is the shape the algorithm actually had. Here it is a
-- bare function on `Nat`, so that the breach library builds with nothing but
-- arlib and can be a default target from the first commit of a project. The
-- property under test is unchanged: the charge says one coin, and the seal
-- cannot see what the argument cost.
def cheatHandPriced (level : Nat) (bits : Nat → Bool) : Charged StdOp Cell Bool :=
  Charged.op (StdOp.rand .accept) (bits level)

/--
error: Seal breach in Esa22Copy.Program: [(Esa22Copy.Program.cheatCasesOn, Arlib.Computation.Roster.casesOn),
 (Esa22Copy.Program.cheatHandPriced, Arlib.Computation.Charged.op),
 (Esa22Copy.Program.cheatNoncomputable, noncomputableProgram),
 (Esa22Copy.Program.cheatExchange,
  Arlib.Computation.Charged.exchange)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22Copy.Program

/-! **Reading the sampling level.**  The level is inside a `Sampler` and
`Sampler.levelOf` is noncomputable, so the compiler rejects this before the seal
gets to it — which is the stronger of the two rejections.  With `level : ℕ` a
bare field, `|X| * 2 ^ level` was the driver's arithmetic on a number nobody
asked for. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Sampler.levelOf', which is 'noncomputable'
-/
#guard_msgs in
def _root_.Esa22CopyTest.cheatPeekLevel (s : Sampler) (n : Nat) : Nat := n * 2 ^ s.levelOf

/-! **Observing a computation's own tally.**  `Charged.cost` is computable and
"produces no value" — until `decide` is applied to it.  `Roster.cost_filterErase`
equates a thinning pass's tally to `d.card`, so a program that may read `cost`
has a free cardinality and therefore a free `cardEq`. -/
def cheatCost (p : Charged StdOp Cell Nat) : CostVec StdOp := p.cost

/--
error: Seal breach in Esa22Copy.Program: [(Esa22Copy.Program.cheatCasesOn, Arlib.Computation.Roster.casesOn),
 (Esa22Copy.Program.cheatCost, Arlib.Computation.Charged.cost),
 (Esa22Copy.Program.cheatHandPriced, Arlib.Computation.Charged.op),
 (Esa22Copy.Program.cheatNoncomputable, noncomputableProgram),
 (Esa22Copy.Program.cheatExchange,
  Arlib.Computation.Charged.exchange)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22Copy.Program

/-! **The same read, one hop away.**  `Charged.steps` is deliberately absent from
`forbiddenInProgram`: it is `CostVec.steps C p.cost`, so a blacklist of *direct*
mentions would miss it entirely.  This test is what makes the transitive walk a
checked fact rather than an intention, and it is the one to run first if
`reaches` is ever changed.

Note which constant the message names — the intermediary the program actually
called, not the forbidden constant behind it.  That is the name whose call site
has to change. -/
def cheatTransitive (p : Charged StdOp Cell Nat) : Nat := Charged.steps (Rate.unit StdOp) p

/--
error: Seal breach in Esa22Copy.Program: [(Esa22Copy.Program.cheatCasesOn, Arlib.Computation.Roster.casesOn),
 (Esa22Copy.Program.cheatTransitive, Arlib.Computation.Charged.steps),
 (Esa22Copy.Program.cheatCost, Arlib.Computation.Charged.cost),
 (Esa22Copy.Program.cheatHandPriced, Arlib.Computation.Charged.op),
 (Esa22Copy.Program.cheatNoncomputable, noncomputableProgram),
 (Esa22Copy.Program.cheatExchange,
  Arlib.Computation.Charged.exchange)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22Copy.Program

/-! **Reading what a computation holds.**  This one the compiler rejects on its
own, and for a stronger reason than it rejects `Charged.cost`: a tally tells a
program which branch it took, which it already knew, while a profile tells it how
much data it holds — which is exactly what the data seal hides.  `decide
(p.space.net k = 1)` after an insertion is a free membership test. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Charged.space', which is 'noncomputable'
-/
#guard_msgs in
def _root_.Esa22CopyTest.readProfile (p : Charged StdOp Cell Nat) : Profile Cell := p.space

/-! **Measuring a dictionary directly.**  `Residency.at'` is the space analogue
of `Roster.card`, and noncomputable for the same reason. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Residency.at'', which is 'noncomputable'
-/
#guard_msgs in
def _root_.Esa22CopyTest.readResidency (r : Residency Cell) : Nat := r.at' Cell.roster

/-! **Supplying your own measure.**  `opUpdate` is computable and takes the
measure as an argument, so nothing the compiler checks objects to a measure that
reports nothing — this is `Charged.exchange (fun _ => 0)` for space.  A program
calls `Roster.insert`, which passes a measure private to `Roster`. -/
def cheatMeasure (d : Roster Nat) : Charged StdOp Cell (Roster Nat) :=
  Charged.opUpdate (StdOp.roster .insert) (fun _ => Residency.ofFun fun _ => 0) id d

/--
error: Seal breach in Esa22Copy.Program: [(Esa22Copy.Program.cheatCasesOn, Arlib.Computation.Roster.casesOn),
 (Esa22Copy.Program.cheatMeasure, Arlib.Computation.Charged.opUpdate),
 (Esa22Copy.Program.cheatMeasure, Arlib.Computation.Residency.ofFun),
 (Esa22Copy.Program.cheatTransitive, Arlib.Computation.Charged.steps),
 (Esa22Copy.Program.cheatCost, Arlib.Computation.Charged.cost),
 (Esa22Copy.Program.cheatHandPriced, Arlib.Computation.Charged.op),
 (Esa22Copy.Program.cheatNoncomputable, noncomputableProgram),
 (Esa22Copy.Program.cheatExchange,
  Arlib.Computation.Charged.exchange)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22Copy.Program

/-! **Reading the measured peak.**  `Charged.peakAt` is computable on purpose —
`#guard` has to read it for the protocol's execution tests — so the compiler does
not object, and the seal is what stops an algorithm from using it as a free size
query.  Same standing as `Charged.cost`. -/
def cheatPeakAt (p : Charged StdOp Cell Nat) : Int := p.peakAt Cell.roster

/--
error: Seal breach in Esa22Copy.Program: [(Esa22Copy.Program.cheatCasesOn, Arlib.Computation.Roster.casesOn),
 (Esa22Copy.Program.cheatMeasure, Arlib.Computation.Charged.opUpdate),
 (Esa22Copy.Program.cheatMeasure, Arlib.Computation.Residency.ofFun),
 (Esa22Copy.Program.cheatTransitive, Arlib.Computation.Charged.steps),
 (Esa22Copy.Program.cheatCost, Arlib.Computation.Charged.cost),
 (Esa22Copy.Program.cheatHandPriced, Arlib.Computation.Charged.op),
 (Esa22Copy.Program.cheatPeakAt, Arlib.Computation.Charged.peakAt),
 (Esa22Copy.Program.cheatNoncomputable, noncomputableProgram),
 (Esa22Copy.Program.cheatExchange,
  Arlib.Computation.Charged.exchange)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Esa22Copy.Program

end Esa22Copy.Program
