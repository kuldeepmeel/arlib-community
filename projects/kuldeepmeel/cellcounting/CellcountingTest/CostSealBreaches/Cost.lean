import Cellcounting.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Roster
import Arlib.Computation.Rand
import Arlib.Computation.Slot
import Arlib.Computation.Std

/-!
# `#programSeal` breach: Cost

One planted breach per module.  `#programSeal` accepts only the canonical
namespace `Cellcounting.Program`, so the cheats can no longer be kept apart by
namespace inside one file; a module of their own is what keeps each expected
message a single entry and each test independent of the others.  Nothing may
import this module: it plants a declaration in the program's namespace.
-/

open Arlib.Computation

/-! **Observing a computation's own tally.**  `Charged.cost` is computable and
"produces no value" — until `decide` is applied to it.  `Roster.cost_filterErase`
equates a thinning pass's tally to `d.card`, so a program that may read `cost`
has a free cardinality and therefore a free `cardEq`. -/
namespace Cellcounting.Program
def cheat (p : Charged StdOp Cell Nat) : CostVec StdOp := p.cost
end Cellcounting.Program

/--
error: Seal breach in Cellcounting.Program: [(Cellcounting.Program.cheat, Arlib.Computation.Charged.cost)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Cellcounting.Program
