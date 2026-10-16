import Cellcounting.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Roster
import Arlib.Computation.Rand
import Arlib.Computation.Slot
import Arlib.Computation.Std

/-!
# `#programSeal` breach: Transitive

One planted breach per module.  `#programSeal` accepts only the canonical
namespace `Cellcounting.Program`, so the cheats can no longer be kept apart by
namespace inside one file; a module of their own is what keeps each expected
message a single entry and each test independent of the others.  Nothing may
import this module: it plants a declaration in the program's namespace.
-/

open Arlib.Computation

/-! **The same read, one hop away.**  `Charged.steps` is deliberately absent from
`forbiddenInProgram`: it is `CostVec.steps C p.cost`, so a blacklist of *direct*
mentions would miss it entirely.  This test is what makes the transitive walk a
checked fact rather than an intention, and it is the one to run first if
`reaches` is ever changed.

Note which constant the message names — the intermediary the program actually
called, not the forbidden constant behind it.  That is the name whose call site
has to change. -/
namespace Cellcounting.Program
def cheat (p : Charged StdOp Cell Nat) : Nat := Charged.steps (Rate.unit StdOp) p
end Cellcounting.Program

/--
error: Seal breach in Cellcounting.Program: [(Cellcounting.Program.cheat, Arlib.Computation.Charged.steps)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal Cellcounting.Program
