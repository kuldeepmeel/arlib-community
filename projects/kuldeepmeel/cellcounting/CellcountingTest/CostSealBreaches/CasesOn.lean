import Cellcounting.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Roster
import Arlib.Computation.Rand
import Arlib.Computation.Slot
import Arlib.Computation.Std

/-!
# `#programSeal` breach: CasesOn

One planted breach per module.  `#programSeal` accepts only the canonical
namespace `Cellcounting.Program`, so the cheats can no longer be kept apart by
namespace inside one file; a module of their own is what keeps each expected
message a single entry and each test independent of the others.  Nothing may
import this module: it plants a declaration in the program's namespace.
-/

open Arlib.Computation

/-! **Projecting a dictionary's contents through the eliminator.**  `casesOn` is
generated public even though the constructor is private, and it is compiled, so
this is the one route the compiler genuinely leaves open. -/
namespace Cellcounting.Program
def cheat (d : Roster Nat) : Nat :=
  Roster.casesOn (motive := fun _ => Nat) d (fun elems _ => elems.length)
end Cellcounting.Program

/--
error: Seal breach in Cellcounting.Program: [(Cellcounting.Program.cheat, Arlib.Computation.Roster.casesOn)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Cellcounting.Program
