import Esa22Copy.Model.Operations
import Esa22Copy.Meta.CostSeal
import Esa22Copy.Meta.ModelClosure

/-!
# Program: Algorithm 1, F0-Estimator, as a charged computation

The paper's Algorithm 1 (`algo:afinal`, esa22-final.tex:422-445), transcribed
line by line against arlib's sealed carriers: the sample set `𝒳` is a
`Roster`, the rate `p = 2⁻ᵏ` is a `Sampler` (which holds the level `k` and never
lets it out), the bits of the Bernoulli(`p`) draw are a `Block`, and the coins of
the throw are a `Coins`.  Every line that does work is one of arlib's charged
operations (see `Model/Operations.lean` for the table), so the tally of a run is
the work the run did, computed by the elaborator.

The program is deterministic given its randomness, which is a separate argument
(`tape`) from its input (`s`): `Model/Run.lean` draws the tape.

## Correspondence ledger

Paper line → Lean:

* **input** `A = ⟨a₁,…,a_m⟩, ε, δ` → `estimate thr s tape`.  `ε, δ` enter only
  through `thr`, which `Model/Run.lean` sets to `Esa22Copy.thresh ε δ s.length`.
* **init** `p ← 1; 𝒳 ← ∅` → `initial` (`Sampler.start`, `Roster.empty`; both
  free: they hold nothing).  `thresh ← ⌈12/ε² · log(8m/δ)⌉` → *not a program
  line*: it is a real logarithm and a ceiling, noncomputable, so it is computed
  in `Model/Prelude.lean` (`Esa22Copy.thresh`) and applied in `Model/Run.lean` at
  `s.length`; its computation is not charged.  **Statement decision.**
* **line:beginfor** `for i = 1 to m` → the `Charged.foldl` in `estimate`, over
  `s.zip tape` (one tape cell per stream element; `Model/Run.lean` supplies a
  tape of exactly `s.length` cells).
* **line:afinal-drop** `𝒳 ← 𝒳 ∖ {aᵢ}` → `Roster.erase` in `arrival`.
* **line:afinal-pick** with probability `p`, `𝒳 ← 𝒳 ∪ {aᵢ}` →
  `Sampler.accept` on this iteration's block, then `Roster.insert` in `arrival`.
* **line:Ifbegin** `if |𝒳| = thresh` → the first `Roster.cardEq` in `step`
  (equality, as in the paper).
* **line:final-throw** throw away each element of `𝒳` w.p. ½ → `thin`
  (`Roster.filterErase`, keeping `x` iff its coin `Coins.flip x` is heads; one
  coin per element of `𝒳`).
* **line:p** `p ← p/2` → `Sampler.halve` in `step`.
* **line:check** `if |𝒳| = thresh` → the second `Roster.cardEq` in `step`
  (equality).
* **line:fail** `Output ⊥` → `step` returns `none`.  **Halting.**  The paper's
  `Output` terminates the run.  Here the loop accumulator is an
  `Option State`, and every later iteration on `none` is `pure none`: it performs
  no operation and holds nothing, so the value, the tally and the space profile
  of the whole run are exactly those of a run that stopped at the failing
  iteration.  This is the "Option-carrying accumulator" form of early exit; it
  was chosen over `Charged.foldlWhile` because `foldlWhile` returns the state
  *before* the step that declines, which would lose the `⊥`, and because arlib
  provides `cons` lemmas for `foldl` but not for `foldlWhile`.
* **line:output** `Output |𝒳|/p` → `report`: `Roster.size` then
  `Sampler.inflate`, i.e. `some (|𝒳| · 2ᵏ)`.  `p` is always `2⁻ᵏ`, so `|𝒳|/p` is
  the natural number `|𝒳| · 2ᵏ`; no real division.  **Statement decision**: the
  theorem casts it to `ℝ`.

Paper quantity → Lean carrier:

* `𝒳` → `State.samples : Roster α`; `p = 2⁻ᵏ` → `State.sampler : Sampler`;
  `⊥` → `none`; `thresh` → the argument `thr : ℕ`; `m` → `s.length`;
  `GenerateRandomBits` for the pick → `Randomness.bits : Block w`
  (`Model/Run.lean` takes `w = s.length + 1`, the paper's `m + 1`); the throw's
  coins → `Randomness.coins : Coins α`.

Omitted / represented differently:

* Both size tests are kept as equality (`Roster.cardEq`), never `≥`.
* The dictionary's `O(1)` *expected* time is idealised as unit cost
  (`Model/Operations.lean`) — **model gap**, stated in the theorem docstring.
* **No RAM realization of the dictionary is claimed.**  The only concrete
  roster realization in the pinned arlib, `Arlib.Computation.RAMRoster`, is a
  direct-address flag buffer: `O(1)` worst-case per operation, but `Θ(n)`
  reserved storage, so it cannot meet the space claim (`thresh · ⌈log₂ n⌉`
  bits) and the time claim at once.  The paper's hash table (expected `O(1)`,
  `O(|𝒳|)` storage) has no arlib counterpart; the time and space theorems are
  therefore about the charged `Roster` currency, not about RAM code.
  **Model gap**, left visible.
* Algorithms 2 and 3 (`algo:bfinal`, `algo:cfinal`) are analysis devices and do
  not appear here.

## Subroutines

There is no subroutine beyond arlib's sealed operations.

* `arrival` (lines afinal-drop, afinal-pick).  Input: item `a`, block, state.
  Output: `𝒳 ∖ {a}` or `(𝒳 ∖ {a}) ∪ {a}`.  Implementation: arlib
  `Roster.erase`, `Sampler.accept`, `Roster.insert` (proved semantics:
  `Roster.toFinset_erase`, `Roster.toFinset_insert`, `Sampler.val_accept`).
  **Validity condition / proof obligation**: `Sampler.accept` on a `Block w`
  draws Bernoulli(`2⁻ᵏ`) only when the level `k ≤ w`; otherwise it returns
  `false` (arlib's junk value).  The analysis must prove the invariant
  "level after `i` iterations `≤ i`", so that `k ≤ m < m + 1 = w` at every call;
  no hypothesis is added for it.
* `thin` (line final-throw).  Implementation: arlib `Roster.filterErase` with
  `Coins.flip` (proved semantics `Roster.toFinset_filterErase`; proved cost
  `Roster.cost_filterErase`: one flip per element plus one erase per discarded
  element).
* Cost obligations (all for later proof-side passes): each iteration not running
  the throw costs `O(1)`; one running it costs `O(1) + 2|𝒳|` with `|𝒳| = thresh`
  (esa22-final.tex:509).  These are consequences of the arlib cost lemmas, not
  assumptions.
-/

set_option autoImplicit false

namespace Esa22Copy.Program

open Arlib.Computation (Block Coins Roster Sampler Charged)
open Esa22Copy.Model.Operations (Op Cell)

/-- **The randomness one loop iteration consumes**: a block of `w` fair bits for
the Bernoulli(`p`) draw of line `afinal-pick`, and a family of fair coins, one per
element, for the throw of line `final-throw` (read only if the throw runs). -/
structure Randomness (α : Type) (w : ℕ) where
  /-- The bits the pick's Bernoulli(`2⁻ᵏ`) draw reads (`GenerateRandomBits`). -/
  bits : Block w
  /-- One fair coin per element, for the throw. -/
  coins : Coins α

/-- **The algorithm's state between iterations**: the sample set `𝒳` and the
sampling rate `p = 2⁻ᵏ`. -/
structure State (α : Type) where
  /-- The sample set `𝒳`. -/
  samples : Roster α
  /-- The sampling rate `p`, held as its level. -/
  sampler : Sampler

variable {α : Type} [DecidableEq α] {w : ℕ}

/-- **Line init**: `p ← 1`, `𝒳 ← ∅`. -/
def initial : State α := ⟨Roster.empty, Sampler.start⟩

/-- **Lines afinal-drop and afinal-pick**: `𝒳 ← 𝒳 ∖ {a}`, then with
probability `p`, `𝒳 ← 𝒳 ∪ {a}`. -/
def arrival (a : α) (blk : Block w) (st : State α) : Charged Op Cell (Roster α) := do
  let dropped ← Roster.erase a st.samples
  let picked ← Sampler.accept blk st.sampler
  if picked then Roster.insert a dropped else pure dropped

/-- **Line final-throw**: throw away each element of `𝒳` with probability `½`,
keeping an element exactly when its coin is heads. -/
def thin (coins : Coins α) (X : Roster α) : Charged Op Cell (Roster α) :=
  Roster.filterErase (fun x => Coins.flip x coins) X

/-- **One iteration of the loop** (esa22-final.tex:428-442), on stream item `a`
with this iteration's randomness.  `none` is `⊥`: once a run has output `⊥`,
every later iteration does nothing and costs nothing. -/
def step (thr : ℕ) (acc : Option (State α)) (ar : α × Randomness α w) :
    Charged Op Cell (Option (State α)) :=
  match acc with
  | none => pure none
  | some st => do
    let X ← arrival ar.1 ar.2.bits st
    let full ← Roster.cardEq thr X
    if full then
      let thinned ← thin ar.2.coins X
      let halved ← Sampler.halve st.sampler
      let stillFull ← Roster.cardEq thr thinned
      if stillFull then pure none
      else pure (some ⟨thinned, halved⟩)
    else pure (some ⟨X, st.sampler⟩)

/-- **Lines fail and output**: `⊥`, or `|𝒳|/p = |𝒳| · 2ᵏ`. -/
def report (acc : Option (State α)) : Charged Op Cell (Option ℕ) :=
  match acc with
  | none => pure none
  | some st => do
    let size ← Roster.size st.samples
    let estimate ← Sampler.inflate size st.sampler
    pure (some estimate)

/-- **Algorithm 1, F0-Estimator** (esa22-final.tex:422-445), on stream `s` with
threshold `thr`, reading one tape cell per stream element. -/
def estimate (thr : ℕ) (s : List α) (tape : List (Randomness α w)) :
    Charged Op Cell (Option ℕ) := do
  let final ← Charged.foldl (step thr) (s.zip tape) (some initial)
  report final

end Esa22Copy.Program

#programSeal Esa22Copy.Program
#executableModule Esa22Copy.Model.Program
#surplusIn Esa22Copy.Model.Program from Esa22Copy.Program.estimate
