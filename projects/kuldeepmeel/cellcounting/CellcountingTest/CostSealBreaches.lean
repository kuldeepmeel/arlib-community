import Cellcounting.Meta.CostSeal
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

Every `#programSeal` cheat gets its **own module**, under
`CellcountingTest/CostSealBreaches/`.  The seal accepts only the canonical
namespace `Cellcounting.Program` — a seal that could be pointed at any namespace
could be pointed at an empty one — so every planted cheat has to live there, and
inside one file they would accumulate.  A module per cheat keeps each expected
message a single entry and keeps the tests independent of the order they run in.
This file checks the two guards on the argument itself: that any other
namespace is refused, and that a canonical namespace with nothing in it is
refused rather than reported clean.

## What is covered

* §1 — the cheats the *compiler* rejects, so that a change making one of them
  compile is caught before either seal is reached.
* §2 — `#programSeal`: the guards on its argument here, and the routes past the
  compiler, inside the algorithm, one module each under
  `CellcountingTest/CostSealBreaches/` (`Exchange`, `Noncomputable`, `CasesOn`,
  `HandPriced`, `Cost`, `Transitive`, `Measure`, `PeakAt`) — including the one
  that only a *transitive* scan catches (`Transitive`), which is the property
  `reaches` exists for and the first test to run if it is ever touched.
The positive direction is covered by the main build: `Model/Program.lean` runs
the command over the real algorithm and it reports clean.
-/

namespace CellcountingTest

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

/-! These two are compiler rejections too, of the sealed carriers' views. -/

/-! **Reading the sampling level.**  The level is inside a `Sampler` and
`Sampler.levelOf` is noncomputable, so the compiler rejects this before the seal
gets to it — which is the stronger of the two rejections.  With `level : ℕ` a
bare field, `|X| * 2 ^ level` was the driver's arithmetic on a number nobody
asked for. -/
namespace Breach.PeekLevel.Program
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Sampler.levelOf', which is 'noncomputable'
-/
#guard_msgs in
def cheat (s : Sampler) (n : Nat) : Nat := n * 2 ^ s.levelOf
end Breach.PeekLevel.Program

/-! **Reading what a computation holds.**  This one the compiler rejects on its
own, and for a stronger reason than it rejects `Charged.cost`: a tally tells a
program which branch it took, which it already knew, while a profile tells it how
much data it holds — which is exactly what the data seal hides.  `decide
(p.space.net k = 1)` after an insertion is a free membership test. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Charged.space', which is 'noncomputable'
-/
#guard_msgs in
def readProfile (p : Charged StdOp Cell Nat) : Profile Cell := p.space

/-! **Measuring a dictionary directly.**  `Residency.at'` is the space analogue
of `Roster.card`, and noncomputable for the same reason. -/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Residency.at'', which is 'noncomputable'
-/
#guard_msgs in
def readResidency (r : Residency Cell) : Nat := r.at' Cell.roster

/-! ## 2. `#programSeal` — the guards on its argument

The breaches themselves are in `CellcountingTest/CostSealBreaches/`, one module
each; see the module docstring. -/

/-! **Pointing the seal somewhere else.**  A seal that took any namespace could
be aimed at one the algorithm does not live in, and would then report clean. -/
namespace Breach.Elsewhere.Program
def cheat (p : Charged StdOp Cell Nat) : Charged StdOp Cell Nat :=
  Charged.exchange (fun _ => (0 : CostVec StdOp)) p
end Breach.Elsewhere.Program

/--
error: Program seal must target the canonical namespace Cellcounting.Program, not CellcountingTest.Breach.Elsewhere.Program.
-/
#guard_msgs (whitespace := lax) in
#programSeal CellcountingTest.Breach.Elsewhere.Program

/-! **A vacuous seal.**  Nothing in this module is in `Cellcounting.Program`, so
the seal has nothing to check — and says so instead of reporting clean. -/
/--
error: Program seal checked zero declarations under Cellcounting.Program.  Put the executable declarations from Model/Program.lean in this exact namespace; a vacuous seal is not a seal.
-/
#guard_msgs (whitespace := lax) in
#programSeal Cellcounting.Program

end CellcountingTest
