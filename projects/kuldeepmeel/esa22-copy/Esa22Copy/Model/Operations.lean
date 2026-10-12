import Arlib.Computation.Std

/-!
# Operations: what one charged step of the F0-Estimator is

**Outcome: arlib already has every primitive the paper uses**, so this file is
an alias layer over arlib's standard currency and declares no operation of its
own.

Every line of Algorithm 1 (esa22-final.tex:422-445) that does work is one of
arlib's sealed operations:

| paper line | arlib operation | opcode |
|---|---|---|
| `X ← X ∖ {aᵢ}` (afinal-drop) | `Roster.erase` | `StdOp.roster .erase` |
| with prob. `p`, `X ← X ∪ {aᵢ}` (afinal-pick) | `Sampler.accept`, `Roster.insert` | `.rand .accept`, `.roster .insert` |
| `if |X| = thresh` (Ifbegin, check) | `Roster.cardEq` | `.roster .cardEq` |
| throw each element w.p. ½ (final-throw) | `Roster.filterErase` with `Coins.flip` | one `.rand .flip` per element of `X`, one `.roster .erase` per discarded element |
| `p ← p/2` (line p) | `Sampler.halve` | `.rand .halve` |
| `Output |X|/p` (output) | `Roster.size`, `Sampler.inflate` | `.roster .size`, `.rand .inflate` |

**The cost model** (`rate`): every opcode costs one step.  This is how the
paper's hypothesis — `𝒳` is kept in a dictionary with `O(1)` expected-time
membership, insertion and deletion, and `|𝒳|` is maintained alongside `𝒳`
(esa22-final.tex:502, 509) — is realised: as a deterministic unit price per
dictionary operation.  It is a **model gap**, recorded as such: the hash table's
own randomness is not modelled, and arlib's `StdImpl` interface deliberately
cannot express an expected-time implementation.  The throw at line
`final-throw` is *not* one paid token: `Roster.filterErase` charges one coin per
element it visits, i.e. `|𝒳| = thresh` at that point, which is the paper's
`O(thresh)` (esa22-final.tex:509).  The Bernoulli(`2⁻ᵏ`) draw `Sampler.accept` is
one operation by arlib's declared price (the standard "sampling a geometric
variable is unit cost" assumption, Arlib/Computation/Rand.lean).

**The storage kind**: an element of the sample set occupies one `Cell.roster`
(arlib's `stdRosterCells`).  The registers holding the level of `p`, `|𝒳|` and
the loop index are not counted, exactly as in the paper's proof
(esa22-final.tex:507).
-/

set_option autoImplicit false

namespace Esa22Copy.Model

namespace Operations

/-- The work currency: arlib's standard operations. -/
abbrev Op : Type := Arlib.Computation.StdOp

/-- The storage currency: arlib's standard cell kinds.  Sample-set elements
occupy `Arlib.Computation.Cell.roster`. -/
abbrev Cell : Type := Arlib.Computation.Cell

/-- The price list: every operation costs one step. -/
abbrev rate : Arlib.Computation.Rate Op := Arlib.Computation.Rate.unit Op

end Operations

end Esa22Copy.Model
