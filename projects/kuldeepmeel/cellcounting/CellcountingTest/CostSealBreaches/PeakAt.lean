import Cellcounting.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Roster
import Arlib.Computation.Rand
import Arlib.Computation.Slot
import Arlib.Computation.Std

/-!
# `#programSeal` breach: PeakAt

One planted breach per module.  `#programSeal` accepts only the canonical
namespace `Cellcounting.Program`, so the cheats can no longer be kept apart by
namespace inside one file; a module of their own is what keeps each expected
message a single entry and each test independent of the others.  Nothing may
import this module: it plants a declaration in the program's namespace.
-/

open Arlib.Computation

/-! **Reading the measured peak.**  `Charged.peakAt` is computable on purpose —
`#guard` has to read it for the protocol's execution tests — so the compiler does
not object, and the seal is what stops an algorithm from using it as a free size
query.  Same standing as `Charged.cost`. -/
namespace Cellcounting.Program
def cheat (p : Charged StdOp Cell Nat) : Int := p.peakAt Cell.roster
end Cellcounting.Program

/--
error: Seal breach in Cellcounting.Program: [(Cellcounting.Program.cheat, Arlib.Computation.Charged.peakAt)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Cellcounting.Program
