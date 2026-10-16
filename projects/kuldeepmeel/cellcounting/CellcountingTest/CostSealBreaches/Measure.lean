import Cellcounting.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Roster
import Arlib.Computation.Rand
import Arlib.Computation.Slot
import Arlib.Computation.Std

/-!
# `#programSeal` breach: Measure

One planted breach per module.  `#programSeal` accepts only the canonical
namespace `Cellcounting.Program`, so the cheats can no longer be kept apart by
namespace inside one file; a module of their own is what keeps each expected
message a single entry and each test independent of the others.  Nothing may
import this module: it plants a declaration in the program's namespace.
-/

open Arlib.Computation

/-! **Supplying your own measure.**  `opUpdate` is computable and takes the
measure as an argument, so nothing the compiler checks objects to a measure that
reports nothing — this is `Charged.exchange (fun _ => 0)` for space.  A program
calls `Roster.insert`, which passes a measure private to `Roster`. -/
namespace Cellcounting.Program
def cheat (d : Roster Nat) : Charged StdOp Cell (Roster Nat) :=
  Charged.opUpdate (StdOp.roster .insert) (fun _ => Residency.ofFun fun _ => 0) id d
end Cellcounting.Program

/--
error: Seal breach in Cellcounting.Program: [(Cellcounting.Program.cheat, Arlib.Computation.Charged.opUpdate), (Cellcounting.Program.cheat, Arlib.Computation.Residency.ofFun)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Cellcounting.Program
