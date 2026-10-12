import Esa22Copy.Interface.Encoding

/-!
# Pseudocode: Algorithm 1, F0-Estimator, as mathematics

The paper's Algorithm 1 (`algo:afinal`, esa22-final.tex:422-445) written over
`Finset` and `PMF`, for the correctness proof.  Its object is the **answer**: the
law of what the algorithm outputs, `none` for `⊥` or `some (|𝒳| · 2ᵏ)` for
`|𝒳|/p`.  Time and space are not modelled here — they are operators applied to
`Esa22Copy.Program.estimate` (`Model/Program.lean`) and stay on that side.  This
file carries no step count, no throw count and no space field: none of those is
a property of the answer.

## Why there are two definitions of the same algorithm

`Model/Program.lean` holds `𝒳` in arlib's sealed `Roster`, which is a
duplicate-free *list*, not a set.  That is deliberate: the algorithm's expensive
line, the throw at `final-throw`, *is* an iteration over the dictionary
(`Roster.filterErase` folds over the stored order, tossing one coin per element),
and charging that iteration correctly is the point of the program.  But a
`Roster` is not extensional.  Two rosters holding the same set, reached by
different histories (inserted in a different order, or thinned from different
orders), are different terms, so two runs that agree on `𝒳` as a set need not
agree on the program's state.  The analysis compares laws of *sets* — Claim
`cl:loop` says each element of `S_i` is in `Y_k` independently with probability
`2⁻ᵏ`, and the coupling of esa22-final.tex:684 identifies `(p_j, 𝒳_j)` with
`(p_j, Y_{k,j})` in law — and a law over rosters would distinguish outcomes the
argument identifies.  `Finset` is exactly the quotient the argument needs, and
on it the analysis gets the whole of Mathlib.  Computability has nothing to do
with it: both sides are noncomputable.

The bridge (next pass) is `Esa22Copy.output ε δ s = answer ε δ s`, proved through
`Esa22Copy.Interface.view`, which reads the program state as the `Snapshot`
(`Finset` sample, level) this file evolves.  Nothing in this file needs a
reachability hypothesis to state: the model only does what the program can do.
In particular the pick reads the bits of a `w`-bit block exactly as
`Sampler.accept` does — including arlib's junk value `false` when the level
exceeds `w` — rather than drawing an idealised Bernoulli(`2⁻ᵏ`).  That the level
stays `≤ m < w = m + 1` is an analysis obligation, not baked into the model.

## Randomness, drawn lazily

The program reads a pre-drawn tape (`Esa22Copy.tape`, `Model/Run.lean`): one
cell per stream element, each a uniform `Fin w → Bool` and an independent
uniform `Finset α`.  The model draws the same two laws lazily — the block at the
pick, the subset only if the throw runs, nothing after `⊥` — which is the same
distribution of everything that is read.

## Correspondence ledger (restatement `algorithmTranscript` → here → program)

| transcript step | pseudocode | `Model/Program.lean` |
|---|---|---|
| input `A, ε, δ` | `answer ε δ s` | `Esa22Copy.output` / `Program.estimate` |
| init `p ← 1; 𝒳 ← ∅` | `init` | `Program.initial` |
| init `thresh ← ⌈12/ε² · log(8m/δ)⌉` | `Esa22Copy.thresh` (Prelude), applied in `answer` | applied in `Esa22Copy.run` |
| line:beginfor `for i = 1 to m` | `loop` (recursion over `s`) | `Charged.foldl (Program.step thr) (s.zip tape)` |
| line:afinal-drop `𝒳 ← 𝒳 ∖ {aᵢ}` | `drop` | `Roster.erase` in `Program.arrival` |
| line:afinal-pick w.p. `p`, `𝒳 ← 𝒳 ∪ {aᵢ}` | `pick` (via `Interface.acceptsAt`) | `Sampler.accept`, `Roster.insert` in `Program.arrival` |
| line:Ifbegin `if |𝒳| = thresh` | `full` | first `Roster.cardEq` in `Program.step` |
| line:final-throw | `throw` | `Program.thin` (`Roster.filterErase`, `Coins.flip`) |
| line:p `p ← p/2` | `halve` | `Sampler.halve` in `Program.step` |
| line:check `if |𝒳| = thresh` / line:fail `Output ⊥` | `full` again; `step` returns `none` | second `Roster.cardEq`; `pure none` |
| line:output `Output |𝒳|/p` | `report` | `Program.report` (`Roster.size`, `Sampler.inflate`) |

Both size tests are the same equality test, as in the paper and the program, so
one function `full` represents lines `Ifbegin` and `check`.  The line order
drop → pick → test → throw → halve → test is kept, and `⊥` halts: `step` on
`none` is `PMF.pure none`.

**No `MODEL:` gap was found** between the transcript and `Model/Program.lean`.
Two points the bridge must discharge rather than assume:

* the program loops over `s.zip tape`, which truncates; `Esa22Copy.run` draws a
  tape of exactly `s.length` cells, and the model loops over all of `s`;
* `p` is held as a level `k` with `p = 2⁻ᵏ` on both sides, and the answer is the
  natural number `|𝒳| · 2ᵏ`; `report_cast` is the arithmetic that this is the
  paper's real `|𝒳|/p`.

The relaxed Algorithm 2 and the level-sample Algorithm 3 are the analysis's
devices and are not here.
-/

set_option autoImplicit false

namespace Esa22Copy.Interface.Pseudocode

open Arlib.Computation (Block)

variable {α : Type} [DecidableEq α]

/-! ## The lines of Algorithm 1 -/

/-- **Line init**: `p ← 1` (level `0`), `𝒳 ← ∅`. -/
def init : Snapshot α := ⟨∅, 0⟩

/-- **Line afinal-drop**: `𝒳 ← 𝒳 ∖ {a}`. -/
def drop (a : α) (X : Finset α) : Finset α := X.erase a

/-- **Line afinal-pick**: with probability `p = 2⁻ᵏ`, `𝒳 ← 𝒳 ∪ {a}`.  The draw
reads a fresh uniform block of `w` fair bits and accepts iff its first `k` bits
are all one (`Interface.acceptsAt`, the outcome of `Sampler.accept`); it rejects
when `k > w`, as the program does. -/
noncomputable def pick (w k : ℕ) (a : α) (X : Finset α) : PMF (Finset α) :=
  (PMF.uniformOfFintype (Fin w → Bool)).map fun f =>
    if acceptsAt k (Block.ofFun f) then insert a X else X

/-- **Lines Ifbegin and check**: the test `|𝒳| = thresh`. -/
def full (thr : ℕ) (X : Finset α) : Bool := decide (X.card = thr)

/-- **Line final-throw**: throw away each element of `𝒳` with probability `½`,
independently — keep exactly the elements of `𝒳` in a fresh uniform subset of
`α` (one fair coin per element; heads = kept). -/
noncomputable def throw [Fintype α] (X : Finset α) : PMF (Finset α) :=
  (PMF.uniformOfFintype (Finset α)).map fun S => X.filter (· ∈ S)

/-- **Line p**: `p ← p/2`, i.e. the level goes up by one. -/
def halve (k : ℕ) : ℕ := k + 1

/-- **Line output** (and line fail): `⊥`, or `|𝒳|/p = |𝒳| · 2ᵏ`. -/
def report : Option (Snapshot α) → Option ℕ
  | none => none
  | some st => some (st.sample.card * 2 ^ st.level)

/-! ## The loop -/

/-- **One iteration** (esa22-final.tex:428-442) on stream item `a`, with
threshold `thr` and pick blocks of width `w`.  `none` is `⊥`, and halts. -/
noncomputable def step [Fintype α] (thr w : ℕ) :
    Option (Snapshot α) → α → PMF (Option (Snapshot α))
  | none, _ => PMF.pure none
  | some st, a =>
    (pick w st.level a (drop a st.sample)).bind fun X =>
      if full thr X then
        (throw X).map fun Y =>
          if full thr Y then none else some ⟨Y, halve st.level⟩
      else PMF.pure (some ⟨X, st.level⟩)

/-- **Line beginfor**, `for i = 1 to m`: the iterations over `s`, in order, from
the accumulator `acc`. -/
noncomputable def loop [Fintype α] (thr w : ℕ) :
    List α → Option (Snapshot α) → PMF (Option (Snapshot α))
  | [], acc => PMF.pure acc
  | a :: s, acc => (step thr w acc a).bind (loop thr w s)

/-- **Algorithm 1 on input `(A, ε, δ)`**: the law of its answer, with the paper's
`thresh ε δ m` and pick blocks of `m + 1` bits (`GenerateRandomBits(m+1)`), where
`m = s.length` — the same parameters `Esa22Copy.run` gives the program. -/
noncomputable def answer [Fintype α] (ε δ : ℝ) (s : List α) : PMF (Option ℕ) :=
  (loop (thresh ε δ s.length) (s.length + 1) s (some init)).map report

/-! ## The program's integer answer is the paper's real one -/

/-- **The sampling rate** `p = 2⁻ᵏ` at level `k`, as the paper's real number. -/
noncomputable def samplingRate (k : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ k

/-- `|𝒳| · 2ᵏ`, cast to `ℝ`, is the paper's output `|𝒳|/p` with `p = 2⁻ᵏ`. -/
theorem report_cast (c k : ℕ) : ((c * 2 ^ k : ℕ) : ℝ) = (c : ℝ) / samplingRate k := by
  simp [samplingRate, div_eq_mul_inv, inv_pow]

end Esa22Copy.Interface.Pseudocode
