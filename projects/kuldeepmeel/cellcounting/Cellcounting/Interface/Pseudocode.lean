import Cellcounting.Model.Run
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.Order.Floor.Div

/-!
# The algorithm of `thm:main`, as mathematics

`Cellcounting.Pseudocode.fpras I ε δ : PMF ℚ` is the paper's algorithm written
over `ℕ`, `ℚ`, `Finset`, `Multiset`, functions and `PMF`: the law of the answer
`Ẑ`.  It is the object the correctness proof reasons about.  The bridge (next
pass) proves that it is the law `Cellcounting.output I ε δ` of the charged
program `Cellcounting.Program.fpras` read on the tape of `Model/Run.lean`.  Time
and space are **not** modelled here: they are operators on the charged program
(`fpras_time`), and nothing in this file counts anything the program pays for.

## Why there are two definitions

Both sides are noncomputable, so this is not about computability.  The program
holds **ordered representations**, and its expensive work is iterating over
them.  The paired state is a `List Bool` of `2p` membership bits, scanned
bit by bit to find the `u`-th occupied element.  The multipliers are a `p × p`
`List (List SRat)` read by walking to a position.  The tightened margins, the
small, free and tree cells, and the run outputs are lists of sealed numbers, and
every read of an entry costs its position.  The `R` run outputs are pushed in
run order and insertion-sorted before the median is read.  All of the fair bits
come from **one** tape, read at a threaded cursor.  That is the right term to
charge: the cost theorem is about exactly these iterations.

The correctness argument compares **laws of sets**.  The Metropolis chain lives
on `p`-subsets `S` of the ground set (`signatures.tex:13-41`).  The median
depends only on the multiset of the run outputs.  The analysis conditions on
independent fresh draws, not on positions of one shared tape.  Two
representations that hold the same set by different histories are different
terms, and a statement about the law of the state would otherwise have to
quotient them by hand at every step.  So this side uses `Finset ℕ` for the
state, `Multiset ℚ` for the median, functions `ℕ → ℕ`, `ℕ → ℚ` for vectors and
tables, and a fresh `PMF` draw wherever the program reads the tape.  The
program's loops become `loop` (a `List.foldlM` over `List.range`, the shape of
`Charged.repeatFor`) or `List.foldl`.

This program uses no sealed dictionary of `Arlib/Computation`.  Its ordered
carriers are plain `List`s read through charged `get`/`set`.  The quotient is
therefore the elementary one, `List Bool ↦ Finset ℕ` (`fun l => (range (2p)).filter
(l.getD · false)`), `List (List SRat) ↦ ℕ → ℕ → ℚ` (`getD` with default `0`),
`List SRat ↦ Multiset ℚ` for the outputs.  No claim of the paper is about
the representation, so the model loses nothing the theorem needs.

## Conventions shared with the program

Where the paper says "choose" or "a fixed order", this file fixes the same
choice as `Model/Program.lean`.  The law of `Ẑ` depends on these choices, so a
different choice here would be a different algorithm.

* Retained cells are listed in row-major order.  Pairs are labelled
  consecutively per small cell, in that order (`pairCells`).  Pair `i` owns
  ground elements `2i` (row) and `2i + 1` (column).
* Large cells are sorted by decreasing bound, stably (`sortedLarge`, insertion by
  `List.orderedInsert`).  Kruskal keeps a cell iff its endpoints carry different
  component labels (`kruskalStep`).
* The root of a component is its least-indexed vertex (`roots`).  Leaf
  elimination runs in reverse breadth-first order from the roots (`elimOrder`).
* "A uniform element of `S`" (resp. of its complement) is the `u`-th by
  increasing position (`nthWith`), with `u` from a dyadic draw.
* The hold bit holds on `true`.  The bin walk starts at bin `0`.  The exact
  dyadic trial for `2^{-k}` accepts iff `k` fair bits are all `0`.
  Binomial unranking is lexicographic (`unrank`).
* Preprocessing S1–S4 is done once, before the `R` runs.

## Correspondence ledger

| Transcript step (paper) | Pseudocode | Program |
|---|---|---|
| S0, `L` | `Cellcounting.inputLength` itself, read by `KParam` | `Program.inputLen` (`SNat.inputLength`) |
| S1, feasibility (`scales.tex:8-24`) | `feasible` (`Ω ≠ ∅`) | `Program.feasible` (`Σr = Σc`, `network`, `maxFlow`) |
| "return zero if infeasible" | `else PMF.pure 0` in `fpras` | `else` branch of `Program.fpras` |
| S2, tightening (`scales.tex:24-44`) | `cellLow`, `cellHigh`, `cellRange`, `retained`, `tRow`, `tCol` | `Program.cellMin`, `cellMax`, `feasibleAtLeast`, `tighten` |
| S3, `eq:parameters` | `dParam`, `KParam`, `γParam`, `AParam`, `BParam`, `WParam`, `HParam` | `Program.params` |
| S4, split, `p`, forest, roots, `M_f` | `smallCells`, `largeCells`, `pSmall`, `sortedLarge`, `kruskalStep`, `forest`, `roots`, `visit`, `elimOrder`, `Mf` | `Program.splitCells`, `sortDesc`, `kruskal`, `rootsOf`, `orient`, `buildCtx`; `pS` in `fpras` |
| S5, `eq:penalty` | `margin`, `baseLoad`, `treeValues`, `boxDist`, `penalty` | `Program.margin`, `penalty`, `distQ`, `absQ` |
| `lem:dyadic-integer-draw` | `uniformBits`, `dyadicDraw`, `dyadicTrial` | `Program.uniformBits`, `dyadicDraw` |
| S6, `prop:weight-oracle` | `oSigma`, `oN`, `oQ`, `oKbin`, `oEll`, `oKd`, `oZeta`, `oKs`, `oDepth`, `levelExp`, `binPoint`, `binExp`, `binAccept`, `walkStep`, `sampleBin`, `ratioSample`, `ratioAvg`, `pow2Approx`, `binOffsets`, `corrSample`, `corrAvg`, `oracle` | `Program.oracleParams`, `levelExp`, `binPoint`, `binExp`, `binAccept`, `walkStep`, `sampleBin`, `ratioAvg`, `pow2Approx`, `binOffsets`, `corrAvg`, `oracle` |
| S7, `p = 0` | `zeroRun` | `Program.zeroRun` |
| S8, setup for `p ≥ 1` | `smallB`, `nSmall`, `pairCells`, `pairCell`, `cellFirst`, `qParam`, `CpParam`, `CdParam`, `KobsParam`, `ηParam`, `τParam`, `BretParam`, `NavParam`, `JstarParam`, `ξParam`, `kAccParam`, `w0`, `C0` | `Program.chainSetup` |
| paired encoding, types `A`, `A_il` | `profile`, `kind` (into `Program.Kind`) | `Program.profile`, `kind` |
| `λ`, `eq:lifts` | `lam` | `Program.lam` |
| S10, implemented transition | `nthWith`, `acceptTest`, `step` | `Program.nthWith`, `acceptTest`, `step` |
| S9a, `μ₀` and capped restart | `unrank`, `mu0`, `Restart`, `restartStep`, `restart` | `Program.binom`, `mu0`, `Restart`, `restart` |
| S9b, observation | `Obs`, `observeState`, `observe` | `Program.Obs`, `observeState`, `observe` |
| S9c, abort test, `R̂_j`, `eq:alg-multiplier-update` | `allPositive`, `updateW`, `phase` | `Program.allPositive`, `updateW`, `phase` |
| S11, single-run output | `RunState`, `annealRun` | `Program.Run`, `annealRun` |
| S12, `s`, `R = 10s + 1`, median | `sRep`, `repeatRuns`, `orderStat`, `fpras` | `Program.fpras`, `insertAsc`, `orderStat` |

## What the bridge has to carry

These are the places where this file states the paper's answer and the program
reaches it by a procedure.  The bridge proves the procedure; nothing here
assumes it.

* **S1** is `I.Omega.Nonempty`.  The program decides it by the totals test and
  at most `V³` Edmonds–Karp augmentations (`V = m + n + 2`).  That this cap
  suffices is the Edmonds–Karp `O(VE)` bound, cited by the paper and not proved
  there.  It is the heaviest bridge obligation (or a `Prior` field).
* **S2** is `min`/`max` of `X i j` over `Ω`.  The program reaches them by binary
  search with `bitLen b_ij` rounds of the flow test.
* `⌈log₂ x⌉` is `Nat.clog 2 x`.  The program's `Program.clog2` computes
  `Nat.size (x - 1)`.  `size_pred_eq_clog` (below, proved) identifies them.
* `C(n, k)` is `Nat.choose`.  The program's product formula `Program.binom n k`
  equals it for `k ≤ n`.  Inside `mu0` this is always the case, by the unranking
  invariant `remaining ≤ positions left`.  That invariant is internal to the
  bridge proof of `mu0`, not a hypothesis.
* Fair bits: `uniformBits k` is the uniform law on `[0, 2^k)`.  The program
  reads `k` tape bits, most significant first.  The tape of `Model/Run.lean` has
  `tapeLength I ε δ` fair bits and tails beyond.  The two laws agree only if no
  execution reads past `tapeLength`, the attainment obligation recorded in
  `Model/Run.lean`.

## MODEL: gaps inherited from `Model/Program.lean`

The program's own ledger flags four reconstructions (R1–R4) made without
`evaluation.tex`/`scales.tex` in hand.  This file mirrors them, because the
program does them and the bridge compares laws.  It does **not** endorse them.
They are model-repair items if the paper says otherwise:

* **R1** (`baseLoad`): a small cell adds `x_s` to its row and `b_s - y_s` to its
  column.
* **R2** (`binPoint`, `binOffsets`, `ratioSample`, `corrSample`): bin intervals
  `[⌈(b+1)v/B⌉, ⌈(b+1)(v+1)/B⌉)`, cube point `(b+1)v/B`, ratio sample
  `2^{⌊aD/H⌋ - ⌊(a+1)D/H⌋}`, correction `α_v 2^β`, `β = ⌊jD(v)/H⌋ - jD(z)/H`.
* **R3** (`pow2Approx`): `h = ⌊β s' + 1/2⌋`; the bisection returns its lower
  endpoint.
* **R4** (`oEll`): `ℓ_in = ⌈K_bin (H + dB + 16 Q_in/θ + 2)⌉`, literally.

No transcript step is missing from the program, and the program adds no step
the transcript lacks.

## Vectors and defaults

A program list read with `getD` (default `0`) is a function `ℕ → ℕ` or
`ℕ → ℚ` here.  Each function in this file agrees with the program's list on
every position the program reads, which is the range the program allocated.
The value elsewhere is whatever falls out of the formula.  No definition here
reads a position the program cannot.
-/

set_option autoImplicit false

namespace Cellcounting.Pseudocode

open Arlib.Computation (ProbRAM)

/-! ## Bridging arithmetic -/

/-- **`⌈log₂ x⌉`, as the program computes it.**  `Program.clog2` returns
`Nat.size (x - 1)`; this file writes `Nat.clog 2 x`, the paper's `⌈log₂ x⌉`.
They agree for every `x`, including `0` and `1`. -/
theorem size_pred_eq_clog (x : ℕ) : Nat.size (x - 1) = Nat.clog 2 x := by
  refine eq_of_forall_ge_iff fun y => ?_
  rw [Nat.size_le, Nat.clog_le_iff_le_pow Nat.one_lt_two]
  have := Nat.two_pow_pos y
  omega

/-! ## Loops and fair bits -/

/-- `Charged.repeatFor` in `PMF`: run `f i` for `i = 0, …, k - 1`. -/
noncomputable def loop {β : Type} (f : ℕ → β → PMF β) (k : ℕ) (b : β) : PMF β :=
  (List.range k).foldlM (fun b i => f i b) b

/-- `k` fair bits read as a binary integer: uniform on `[0, 2^k)`. -/
noncomputable def uniformBits (k : ℕ) : PMF ℕ :=
  PMF.uniformOfFinset (Finset.range (2 ^ k)) ⟨0, Finset.mem_range.2 (Nat.two_pow_pos k)⟩

/-- **`lem:dyadic-integer-draw`** (`evaluation.tex:356-371`): `k` is the least
natural with `M·2^{-k} ≤ ζ`, i.e. `⌈log₂ ⌈M/ζ⌉⌉`; draw `Y` uniform on `[0, 2^k)`
and return `⌊M·Y/2^k⌋`. -/
noncomputable def dyadicDraw (M : ℕ) (ζ : ℚ) : PMF ℕ :=
  (uniformBits (Nat.clog 2 ⌈(M : ℚ) / ζ⌉₊)).map fun Y =>
    M * Y / 2 ^ Nat.clog 2 ⌈(M : ℚ) / ζ⌉₊

/-- The exact dyadic trial of probability `2^{-k}`: `k` fair bits, all `0`. -/
noncomputable def dyadicTrial (k : ℕ) : PMF Bool :=
  (uniformBits k).map fun Y => decide (Y = 0)

/-! ## S1: feasibility -/

/-- **S1** (`scales.tex:8-24`): the answer of the flow test.  An integral flow
of value `Σ r = Σ c` is exactly a feasible table, so the test answers
`Ω(r, c, b) ≠ ∅`. -/
def feasible (I : Instance) : Prop := I.Omega.Nonempty

noncomputable instance (I : Instance) : Decidable (feasible I) :=
  inferInstanceAs (Decidable I.Omega.Nonempty)

/-! ## S2: tightening -/

/-- `l_ij`, the least value of cell `(i, j)` over `Ω` (`0` if `Ω = ∅`, a case the
algorithm never reaches). -/
noncomputable def cellLow (I : Instance) (i : Fin I.m) (j : Fin I.n) : ℕ :=
  if h : I.Omega.Nonempty then (I.Omega.image fun X => X i j).min' (h.image _) else 0

/-- `u_ij`, the greatest value of cell `(i, j)` over `Ω`. -/
noncomputable def cellHigh (I : Instance) (i : Fin I.m) (j : Fin I.n) : ℕ :=
  if h : I.Omega.Nonempty then (I.Omega.image fun X => X i j).max' (h.image _) else 0

/-- The tightened bound `b_s = u_s - l_s`. -/
noncomputable def cellRange (I : Instance) (i : Fin I.m) (j : Fin I.n) : ℕ :=
  cellHigh I i j - cellLow I i j

/-- A cell of the tightened table: row, column, bound. -/
abbrev Entry := ℕ × ℕ × ℕ

/-- The retained cells `(i, j, u_ij - l_ij)` with positive bound, in row-major
order.  Cells with `b_s = 0` are deleted; all vertices are retained. -/
noncomputable def retained (I : Instance) : List Entry :=
  (List.finRange I.m).flatMap fun i => (List.finRange I.n).filterMap fun j =>
    if 0 < cellRange I i j then some (i.val, j.val, cellRange I i j) else none

/-- Tightened row margin `r_i - Σ_j l_ij`. -/
noncomputable def tRow (I : Instance) (i : ℕ) : ℕ :=
  if h : i < I.m then I.r ⟨i, h⟩ - ∑ j, cellLow I ⟨i, h⟩ j else 0

/-- Tightened column margin `c_j - Σ_i l_ij`. -/
noncomputable def tCol (I : Instance) (j : ℕ) : ℕ :=
  if h : j < I.n then I.c ⟨j, h⟩ - ∑ i, cellLow I i ⟨j, h⟩ else 0

/-! ## S3: the global parameters (`eq:parameters`, `scales.tex:48-56`) -/

/-- `d = mn + m + n + 2`, with the original dimensions. -/
noncomputable def dParam (I : Instance) : ℕ := I.m * I.n + I.m + I.n + 2

/-- `K = 20 (L + d + ⌈log₂ ε⁻¹⌉ + 1)`, with `L = inputLength I ε δ`. -/
noncomputable def KParam (I : Instance) (ε δ : ℚ) : ℕ :=
  20 * (inputLength I ε δ + dParam I + Nat.clog 2 ⌈ε⁻¹⌉₊ + 1)

/-- `γ = ε / (512 d K)`. -/
noncomputable def γParam (I : Instance) (ε δ : ℚ) : ℚ :=
  ε / (512 * dParam I * KParam I ε δ)

/-- `A = ⌈4K/γ⌉`. -/
noncomputable def AParam (I : Instance) (ε δ : ℚ) : ℕ :=
  ⌈(4 * KParam I ε δ : ℚ) / γParam I ε δ⌉₊

/-- `B = 16 A d²`. -/
noncomputable def BParam (I : Instance) (ε δ : ℚ) : ℕ := 16 * AParam I ε δ * dParam I ^ 2

/-- `W = 100 d B`. -/
noncomputable def WParam (I : Instance) (ε δ : ℚ) : ℕ := 100 * dParam I * BParam I ε δ

/-- `H = 10 A d² (W + 1)`. -/
noncomputable def HParam (I : Instance) (ε δ : ℚ) : ℕ :=
  10 * AParam I ε δ * dParam I ^ 2 * (WParam I ε δ + 1)

/-! ## S4: small and large cells, the maximum spanning forest -/

/-- Small cells, `b_s < W`, in retained order. -/
noncomputable def smallCells (I : Instance) (ε δ : ℚ) : List Entry :=
  (retained I).filter fun e => e.2.2 < WParam I ε δ

/-- Large cells, `b_s ≥ W`, in retained order. -/
noncomputable def largeCells (I : Instance) (ε δ : ℚ) : List Entry :=
  (retained I).filter fun e => ¬ e.2.2 < WParam I ε δ

/-- `p = Σ_{s small} b_s`. -/
noncomputable def pSmall (I : Instance) (ε δ : ℚ) : ℕ :=
  ((smallCells I ε δ).map fun e => e.2.2).sum

/-- Large cells by decreasing bound, ties in retained order: each cell is
inserted before the first one of strictly smaller bound. -/
noncomputable def sortedLarge (I : Instance) (ε δ : ℚ) : List Entry :=
  (largeCells I ε δ).foldl
    (fun acc x => acc.orderedInsert (fun a b : Entry => b.2.2 < a.2.2) x) []

/-- Kruskal's state: tree cells, free cells, and a component label per vertex
(rows `0..m-1`, columns `m..m+n-1`). -/
structure Forest where
  /-- Tree cells `T`, in insertion order. -/
  tree : List Entry
  /-- Free cells `F`, in insertion order. -/
  free : List Entry
  /-- Component label of each vertex. -/
  comp : ℕ → ℕ

/-- One Kruskal step (`scales.tex:91-99`): a cell joining two current components
enters the tree and the components merge; otherwise it is free. -/
noncomputable def kruskalStep (m : ℕ) (F : Forest) (e : Entry) : Forest :=
  if F.comp e.1 = F.comp (m + e.2.1) then
    { F with free := F.free ++ [e] }
  else
    { F with
      tree := F.tree ++ [e]
      comp := fun w => if F.comp w = F.comp (m + e.2.1) then F.comp e.1 else F.comp w }

/-- **S4**: the maximum-capacity spanning forest of the large-cell graph. -/
noncomputable def forest (I : Instance) (ε δ : ℚ) : Forest :=
  (sortedLarge I ε δ).foldl (kruskalStep I.m) ⟨[], [], id⟩

/-- One root per component: its least-indexed vertex. -/
noncomputable def roots (I : Instance) (ε δ : ℚ) : List ℕ :=
  (List.range (I.m + I.n)).filter fun v =>
    decide (∀ u < v, (forest I ε δ).comp u ≠ (forest I ε δ).comp v)

/-- Breadth-first discovery of `w` through tree edge `t`: visited set, queue,
and the discovered `(vertex, parent edge)` pairs, newest first. -/
noncomputable def visit (w t : ℕ) (st : Finset ℕ × List ℕ × List (ℕ × ℕ)) :
    Finset ℕ × List ℕ × List (ℕ × ℕ) :=
  if w ∈ st.1 then st else (insert w st.1, st.2.1 ++ [w], (w, t) :: st.2.2)

/-- The leaf-elimination order: every nonroot vertex with its parent tree edge,
in reverse breadth-first order from the roots, so children come before their
parents. -/
noncomputable def elimOrder (I : Instance) (ε δ : ℚ) : List (ℕ × ℕ) :=
  let T := (forest I ε δ).tree
  ((List.range (I.m + I.n)).foldl (fun st k =>
    match st.2.1[k]? with
    | none => st
    | some u => (List.range T.length).foldl (fun st' t =>
        let e := T.getD t (0, 0, 0)
        if e.1 = u then visit (I.m + e.2.1) t st'
        else if I.m + e.2.1 = u then visit e.1 t st' else st') st)
    ((roots I ε δ).toFinset, roots I ε δ, [])).2.2

/-- `M_f = ∏_{e ∈ F} (b_e + 1)`. -/
noncomputable def Mf (I : Instance) (ε δ : ℚ) : ℕ :=
  ((forest I ε δ).free.map fun e => e.2.2 + 1).prod

/-! ## S5: the penalty `D(x, y, z)` (`eq:penalty`, `scales.tex:113-126`) -/

/-- Number of small cells. -/
noncomputable def nSmall (I : Instance) (ε δ : ℚ) : ℕ := (smallCells I ε δ).length

/-- Number of free cells, `e`. -/
noncomputable def nFree (I : Instance) (ε δ : ℚ) : ℕ := (forest I ε δ).free.length

/-- The `k`-th small cell. -/
noncomputable def smallAt (I : Instance) (ε δ : ℚ) (k : ℕ) : Entry :=
  (smallCells I ε δ).getD k (0, 0, 0)

/-- The `k`-th free cell. -/
noncomputable def freeAt (I : Instance) (ε δ : ℚ) (k : ℕ) : Entry :=
  (forest I ε δ).free.getD k (0, 0, 0)

/-- The `t`-th tree cell. -/
noncomputable def treeAt (I : Instance) (ε δ : ℚ) (t : ℕ) : Entry :=
  (forest I ε δ).tree.getD t (0, 0, 0)

/-- The prescribed (tightened) margin of vertex `v`. -/
noncomputable def margin (I : Instance) (v : ℕ) : ℚ :=
  if v < I.m then (tRow I v : ℚ) else (tCol I (v - I.m) : ℚ)

/-- The load of vertex `v` from the non-tree cells: a small cell adds `x_s` to
its row and `b_s - y_s` to its column (R1); a free cell adds `z_e` to both
endpoints. -/
noncomputable def baseLoad (I : Instance) (ε δ : ℚ) (x y : ℕ → ℕ) (z : ℕ → ℚ) (v : ℕ) : ℚ :=
  (∑ k ∈ Finset.range (nSmall I ε δ),
      ((if (smallAt I ε δ k).1 = v then (x k : ℚ) else 0) +
        (if I.m + (smallAt I ε δ k).2.1 = v then (((smallAt I ε δ k).2.2 - y k : ℕ) : ℚ)
          else 0))) +
    ∑ k ∈ Finset.range (nFree I ε δ),
      ((if (freeAt I ε δ k).1 = v then z k else 0) +
        (if I.m + (freeAt I ε δ k).2.1 = v then z k else 0))

/-- Leaf elimination: along `elimOrder`, the tree value of a nonroot vertex's
parent edge is its margin minus its current load, which is then added to the
parent.  Returns the final loads and the tree values `z_t`. -/
noncomputable def treeValues (I : Instance) (ε δ : ℚ) (x y : ℕ → ℕ) (z : ℕ → ℚ) :
    (ℕ → ℚ) × (ℕ → ℚ) :=
  (elimOrder I ε δ).foldl (fun st vt =>
    let e := treeAt I ε δ vt.2
    let ztv := margin I vt.1 - st.1 vt.1
    let other := if vt.1 = e.1 then I.m + e.2.1 else e.1
    (Function.update st.1 other (st.1 other + ztv), Function.update st.2 vt.2 ztv))
    (baseLoad I ε δ x y z, fun _ => 0)

/-- `dist(x, [0, b])`. -/
noncomputable def boxDist (x b : ℚ) : ℚ :=
  if x < 0 then -x else if b < x then x - b else 0

/-- **`D(x, y, z)`** `= A (Σ_roots |δ_v| + Σ_{t ∈ T} dist(z_t, [0, b_t]) / b_t)`. -/
noncomputable def penalty (I : Instance) (ε δ : ℚ) (x y : ℕ → ℕ) (z : ℕ → ℚ) : ℚ :=
  (AParam I ε δ : ℚ) *
    (((roots I ε δ).map fun v => |(treeValues I ε δ x y z).1 v - margin I v|).sum +
      ∑ t ∈ Finset.range (forest I ε δ).tree.length,
        boxDist ((treeValues I ε δ x y z).2 t) ((treeAt I ε δ t).2.2 : ℚ) /
          ((treeAt I ε δ t).2.2 : ℚ))

/-! ## S6: the weight oracle (`prop:weight-oracle`, `evaluation.tex:40-482`) -/

/-- `σ = ξ_in / (50 (H + 1))`. -/
noncomputable def oSigma (I : Instance) (ε δ : ℚ) (ξin : ℚ) : ℚ :=
  ξin / (50 * ((HParam I ε δ : ℚ) + 1))

/-- `N_in = ⌈10⁶ (H + 1) / (θ σ²)⌉`. -/
noncomputable def oN (I : Instance) (ε δ : ℚ) (ξin θ : ℚ) : ℕ :=
  ⌈1000000 * ((HParam I ε δ : ℚ) + 1) / (θ * oSigma I ε δ ξin ^ 2)⌉₊

/-- `Q_in = (d + 1)(H + 1) N_in`. -/
noncomputable def oQ (I : Instance) (ε δ : ℚ) (ξin θ : ℚ) : ℕ :=
  (dParam I + 1) * (HParam I ε δ + 1) * oN I ε δ ξin θ

/-- `K_bin = 2 (10⁴ d² B)²`. -/
noncomputable def oKbin (I : Instance) (ε δ : ℚ) : ℕ :=
  2 * (10000 * dParam I ^ 2 * BParam I ε δ) ^ 2

/-- `ℓ_in = ⌈K_bin (H + dB + 16 Q_in/θ + 2)⌉` (R4). -/
noncomputable def oEll (I : Instance) (ε δ : ℚ) (ξin θ : ℚ) : ℕ :=
  ⌈(oKbin I ε δ : ℚ) * (((HParam I ε δ + dParam I * BParam I ε δ + 2 : ℕ) : ℚ) +
    16 * (oQ I ε δ ξin θ : ℚ) / θ)⌉₊

/-- `⌈log₂ (4d)⌉`, the bits of one walk proposal. -/
noncomputable def oKd (I : Instance) : ℕ := Nat.clog 2 (4 * dParam I)

/-- `ζ = θ / (8 Q_in)`, the tolerance of the offset draws. -/
noncomputable def oZeta (I : Instance) (ε δ : ℚ) (ξin θ : ℚ) : ℚ :=
  θ / (8 * (oQ I ε δ ξin θ : ℚ))

/-- `log₂ s'`, where `s' = 2^{⌈log₂ ⌈32/σ⌉⌉}` is the power of two in
`[32/σ, 64/σ]`. -/
noncomputable def oKs (I : Instance) (ε δ : ℚ) (ξin : ℚ) : ℕ :=
  Nat.clog 2 ⌈32 / oSigma I ε δ ξin⌉₊

/-- The bisection depth `⌈log₂ (512/σ)⌉`. -/
noncomputable def oDepth (I : Instance) (ε δ : ℚ) (ξin : ℚ) : ℕ :=
  Nat.clog 2 ⌈512 / oSigma I ε δ ξin⌉₊

/-- `⌊a D / H⌋`: `V_a = 2^{-⌊a D/H⌋}`. -/
noncomputable def levelExp (I : Instance) (ε δ : ℚ) (a : ℕ) (D : ℚ) : ℤ :=
  ⌊(a : ℚ) * D / (HParam I ε δ : ℚ)⌋

/-- The cube point of a bin vector, `z_e = (b_e + 1) v_e / B` (R2). -/
noncomputable def binPoint (I : Instance) (ε δ : ℚ) (v : ℕ → ℕ) : ℕ → ℚ :=
  fun k => (((freeAt I ε δ k).2.2 + 1) * v k : ℕ) / (BParam I ε δ : ℚ)

/-- The exponent of `V_a` at a bin. -/
noncomputable def binExp (I : Instance) (ε δ : ℚ) (a : ℕ) (x y : ℕ → ℕ) (v : ℕ → ℕ) : ℤ :=
  levelExp I ε δ a (penalty I ε δ x y (binPoint I ε δ v))

/-- The Metropolis decision from bin `v` to bin `w` for `V_a`: accept with
probability `min{1, V_a(w)/V_a(v)} = 2^{-max(0, k_a(w) - k_a(v))}`. -/
noncomputable def binAccept (I : Instance) (ε δ : ℚ) (a : ℕ) (x y : ℕ → ℕ)
    (v w : ℕ → ℕ) : PMF (ℕ → ℕ) :=
  if binExp I ε δ a x y w ≤ binExp I ε δ a x y v then PMF.pure w
  else (dyadicTrial (binExp I ε δ a x y w - binExp I ε δ a x y v).toNat).map
    fun ok => if ok then w else v

/-- One step of the bin walk for `V_a`: signed coordinate direction `u` with
probability `2^{-⌈log₂ 4d⌉}` each, otherwise hold; a move off `{0..B-1}^e` holds. -/
noncomputable def walkStep (I : Instance) (ε δ : ℚ) (a : ℕ) (x y : ℕ → ℕ) (v : ℕ → ℕ) :
    PMF (ℕ → ℕ) := do
  let u ← uniformBits (oKd I)
  if u < 2 * nFree I ε δ then
    if u % 2 = 1 then
      if v (u / 2) = BParam I ε δ - 1 then pure v
      else binAccept I ε δ a x y v (Function.update v (u / 2) (v (u / 2) + 1))
    else
      if v (u / 2) = 0 then pure v
      else binAccept I ε δ a x y v (Function.update v (u / 2) (v (u / 2) - 1))
  else pure v

/-- One bin sample for `V_a`: a fresh walk of `ℓ_in` steps from bin `0`.  With no
free cell the bin space is a single point and nothing is drawn. -/
noncomputable def sampleBin (I : Instance) (ε δ : ℚ) (ξin θ : ℚ) (a : ℕ) (x y : ℕ → ℕ) :
    PMF (ℕ → ℕ) :=
  if nFree I ε δ = 0 then PMF.pure fun _ => 0
  else loop (fun _ v => walkStep I ε δ a x y v) (oEll I ε δ ξin θ) fun _ => 0

/-- One ratio sample `V_{a+1}(v)/V_a(v) = 2^{⌊aD/H⌋ - ⌊(a+1)D/H⌋}` (R2). -/
noncomputable def ratioSample (I : Instance) (ε δ : ℚ) (a : ℕ) (x y : ℕ → ℕ) (v : ℕ → ℕ) : ℚ :=
  (2 : ℚ) ^ (levelExp I ε δ a (penalty I ε δ x y (binPoint I ε δ v)) -
    levelExp I ε δ (a + 1) (penalty I ε δ x y (binPoint I ε δ v)))

/-- `R̂_a`: the average of `N_in` ratio samples at fresh bin walks for `V_a`. -/
noncomputable def ratioAvg (I : Instance) (ε δ : ℚ) (ξin θ : ℚ) (a : ℕ) (x y : ℕ → ℕ) :
    PMF ℚ :=
  (loop (fun _ s => (sampleBin I ε δ ξin θ a x y).map fun v => s + ratioSample I ε δ a x y v)
    (oN I ε δ ξin θ) 0).map fun s => s / (oN I ε δ ξin θ : ℚ)

/-- `2^β`, approximately (R3): round `β` to the grid `h/s'`, then bisect `[0, 8]`
to depth `⌈log₂ (512/σ)⌉`, comparing `mid^{s'}` with `2^h`. -/
noncomputable def pow2Approx (I : Instance) (ε δ : ℚ) (ξin : ℚ) (β : ℚ) : ℚ :=
  ((fun st : ℚ × ℚ =>
      if ((st.1 + st.2) / 2) ^ (2 ^ oKs I ε δ ξin) ≤
          (2 : ℚ) ^ ⌊β * 2 ^ oKs I ε δ ξin + 1 / 2⌋
        then ((st.1 + st.2) / 2, st.2) else (st.1, (st.1 + st.2) / 2))^[oDepth I ε δ ξin]
    (0, 8)).1

/-- Offsets uniform (to tolerance `ζ`) in the bin intervals
`I_{v_e} = [⌈(b_e+1) v_e/B⌉, ⌈(b_e+1)(v_e+1)/B⌉)` (R2): the integer point `z` and
`∏_e |I_{v_e}|`. -/
noncomputable def binOffsets (I : Instance) (ε δ : ℚ) (ξin θ : ℚ) (v : ℕ → ℕ) :
    PMF ((ℕ → ℚ) × ℕ) :=
  loop (fun k st =>
    let b1 := (freeAt I ε δ k).2.2 + 1
    let lo := (b1 * v k) ⌈/⌉ BParam I ε δ
    let hi := (b1 * (v k + 1)) ⌈/⌉ BParam I ε δ
    (dyadicDraw (hi - lo) (oZeta I ε δ ξin θ)).map fun off =>
      (Function.update st.1 k ((lo + off : ℕ) : ℚ), st.2 * (hi - lo)))
    (nFree I ε δ) (fun _ => 0, 1)

/-- One correction sample `α_v 2^β`, `α_v = B^e |I_v| / M_f`,
`β = ⌊jD(v)/H⌋ - jD(z)/H` (R2), at bin `v` and offset point `z`. -/
noncomputable def corrSample (I : Instance) (ε δ : ℚ) (ξin : ℚ) (j : ℕ) (x y : ℕ → ℕ)
    (v : ℕ → ℕ) (z : ℕ → ℚ) (len : ℕ) : ℚ :=
  ((BParam I ε δ ^ nFree I ε δ * len : ℕ) : ℚ) / (Mf I ε δ : ℚ) *
    pow2Approx I ε δ ξin ((binExp I ε δ j x y v : ℚ) -
      (j : ℚ) * penalty I ε δ x y z / (HParam I ε δ : ℚ))

/-- `T̂`: the average of `N_in` correction samples, each at a fresh bin walk for
`V_j` and fresh offsets. -/
noncomputable def corrAvg (I : Instance) (ε δ : ℚ) (ξin θ : ℚ) (j : ℕ) (x y : ℕ → ℕ) :
    PMF ℚ :=
  (loop (fun _ s => do
      let v ← sampleBin I ε δ ξin θ j x y
      let zl ← binOffsets I ε δ ξin θ v
      pure (s + corrSample I ε δ ξin j x y v zl.1 zl.2))
    (oN I ε δ ξin θ) 0).map fun s => s / (oN I ε δ ξin θ : ℚ)

/-- **The weight oracle** `ĥ_j(x, y) = M_f · ∏_{a<j} R̂_a · T̂`, on fresh draws. -/
noncomputable def oracle (I : Instance) (ε δ : ℚ) (x y : ℕ → ℕ) (j : ℕ) (ξin θ : ℚ) :
    PMF ℚ := do
  let P ← loop (fun a P => (ratioAvg I ε δ ξin θ a x y).map fun r => P * r) j 1
  let T ← corrAvg I ε δ ξin θ j x y
  pure ((Mf I ε δ : ℚ) * P * T)

/-! ## S7: one run for `p = 0` -/

/-- **S7** (`algorithm.tex:25-28`): one oracle call for `h_H(∅) = C(H)`, with
relative tolerance `ε/32` and failure probability `1/16`. -/
noncomputable def zeroRun (I : Instance) (ε δ : ℚ) : PMF ℚ :=
  oracle I ε δ (fun _ => 0) (fun _ => 0) (HParam I ε δ) (ε / 32) (1 / 16)

/-! ## S8: setup for `p ≥ 1` -/

/-- `b_s` of the `s`-th small cell. -/
noncomputable def smallB (I : Instance) (ε δ : ℚ) (s : ℕ) : ℕ := (smallAt I ε δ s).2.2

/-- The small cell of each pair label: cell `s` owns `b_s` consecutive labels. -/
noncomputable def pairCells (I : Instance) (ε δ : ℚ) : List ℕ :=
  (List.range (nSmall I ε δ)).flatMap fun s => List.replicate (smallB I ε δ s) s

/-- `s(i)`, the small cell of pair `i`. -/
noncomputable def pairCell (I : Instance) (ε δ : ℚ) (i : ℕ) : ℕ := (pairCells I ε δ).getD i 0

/-- The first pair label of small cell `s`. -/
noncomputable def cellFirst (I : Instance) (ε δ : ℚ) (s : ℕ) : ℕ :=
  ∑ t ∈ Finset.range s, smallB I ε δ t

/-- `q = W²`. -/
noncomputable def qParam (I : Instance) (ε δ : ℚ) : ℕ := WParam I ε δ ^ 2

/-- `C_p = p (1 + 8 p q²)`. -/
noncomputable def CpParam (I : Instance) (ε δ : ℚ) : ℕ :=
  pSmall I ε δ * (1 + 8 * pSmall I ε δ * qParam I ε δ ^ 2)

/-- `C_d = 8 + 32 p q³`. -/
noncomputable def CdParam (I : Instance) (ε δ : ℚ) : ℕ :=
  8 + 32 * pSmall I ε δ * qParam I ε δ ^ 3

/-- `K_obs = 10 p⁴ (9 C_p + 2 C_d)`. -/
noncomputable def KobsParam (I : Instance) (ε δ : ℚ) : ℕ :=
  10 * pSmall I ε δ ^ 4 * (9 * CpParam I ε δ + 2 * CdParam I ε δ)

/-- `η = ε / (200 (H + 1))`. -/
noncomputable def ηParam (I : Instance) (ε δ : ℚ) : ℚ :=
  ε / ((200 * (HParam I ε δ + 1) : ℕ) : ℚ)

/-- `τ = 2 K_obs (H + p + K + 5)`. -/
noncomputable def τParam (I : Instance) (ε δ : ℚ) : ℕ :=
  2 * KobsParam I ε δ * (HParam I ε δ + pSmall I ε δ + KParam I ε δ + 5)

/-- `B_ret = 2000 p² (H + 1)² τ`. -/
noncomputable def BretParam (I : Instance) (ε δ : ℚ) : ℕ :=
  2000 * pSmall I ε δ ^ 2 * (HParam I ε δ + 1) ^ 2 * τParam I ε δ

/-- `N_av = ⌈10⁸ p⁸ K_obs (H + 1) / η²⌉`. -/
noncomputable def NavParam (I : Instance) (ε δ : ℚ) : ℕ :=
  ⌈((100000000 * pSmall I ε δ ^ 8 * KobsParam I ε δ * (HParam I ε δ + 1) : ℕ) : ℚ) /
    ηParam I ε δ ^ 2⌉₊

/-- `J_* = 100 (H + 1)(B_ret + N_av + p + d + 1)`. -/
noncomputable def JstarParam (I : Instance) (ε δ : ℚ) : ℕ :=
  100 * (HParam I ε δ + 1) *
    (BretParam I ε δ + NavParam I ε δ + pSmall I ε δ + dParam I + 1)

/-- `ξ = η / (1000 J_*)`. -/
noncomputable def ξParam (I : Instance) (ε δ : ℚ) : ℚ :=
  ηParam I ε δ / ((1000 * JstarParam I ε δ : ℕ) : ℚ)

/-- `⌈log₂ ξ⁻¹⌉`, the bits of one acceptance threshold. -/
noncomputable def kAccParam (I : Instance) (ε δ : ℚ) : ℕ :=
  Nat.clog 2 ⌈(ξParam I ε δ)⁻¹⌉₊

/-- The initial multipliers `w^(0)` for `i ≠ l`: `6` if `s(i) = s(l)`, else
`6 (b_{s(i)} + 1) / (b_{s(l)} + 2)`; `0` on the diagonal and outside `p × p`. -/
noncomputable def w0 (I : Instance) (ε δ : ℚ) : ℕ → ℕ → ℚ := fun i l =>
  if i < pSmall I ε δ ∧ l < pSmall I ε δ ∧ i ≠ l then
    if pairCell I ε δ i = pairCell I ε δ l then 6
    else 6 * ((smallB I ε δ (pairCell I ε δ i) + 1 : ℕ) : ℚ) /
      ((smallB I ε δ (pairCell I ε δ l) + 2 : ℕ) : ℚ)
  else 0

/-- `C(0) = M_f ∏_{s small} (b_s + 1)`. -/
noncomputable def C0 (I : Instance) (ε δ : ℚ) : ℚ :=
  ((Mf I ε δ * ∏ s ∈ Finset.range (nSmall I ε δ), (smallB I ε δ s + 1) : ℕ) : ℚ)

/-! ## The paired state space (`signatures.tex:13-41`) -/

/-- The small-count profile `(x_s, y_s)` of a state `S ⊆ [0, 2p)`: row and column
elements present in small cell `s`. -/
noncomputable def profile (I : Instance) (ε δ : ℚ) (S : Finset ℕ) : (ℕ → ℕ) × (ℕ → ℕ) :=
  (fun s => ((Finset.range (pSmall I ε δ)).filter fun i =>
      pairCell I ε δ i = s ∧ 2 * i ∈ S).card,
    fun s => ((Finset.range (pSmall I ε δ)).filter fun i =>
      pairCell I ε δ i = s ∧ 2 * i + 1 ∈ S).card)

/-- The type of a state: a transversal (every pair singly occupied), the defect
class `A_il` (pair `i` empty, pair `l` full, the rest singly occupied), or
outside `X`. -/
noncomputable def kind (I : Instance) (ε δ : ℚ) (S : Finset ℕ) : Program.Kind :=
  let E := (Finset.range (pSmall I ε δ)).filter fun i => 2 * i ∉ S ∧ 2 * i + 1 ∉ S
  let F := (Finset.range (pSmall I ε δ)).filter fun i => 2 * i ∈ S ∧ 2 * i + 1 ∈ S
  if E.card = 0 then (if F.card = 0 then .transversal else .outside)
  else if E.card = 1 ∧ F.card = 1 then .defect (E.sup id) (F.sup id) else .outside

/-- The implemented `λ(S)` at level `a`: a fresh oracle value `ĥ_a(x, y)` (with
`ξ_in = θ = ξ`), times `∏_s x_s! y_s! / b_s!` (`eq:lifts`), times `w_il` on
`A_il`. -/
noncomputable def lam (I : Instance) (ε δ : ℚ) (S : Finset ℕ) (k : Program.Kind) (a : ℕ)
    (w : ℕ → ℕ → ℚ) : PMF ℚ :=
  (oracle I ε δ (profile I ε δ S).1 (profile I ε δ S).2 a (ξParam I ε δ) (ξParam I ε δ)).map
    fun h =>
      let f := h * ∏ s ∈ Finset.range (nSmall I ε δ),
        ((((profile I ε δ S).1 s).factorial : ℚ) * (((profile I ε δ S).2 s).factorial : ℚ) /
          ((smallB I ε δ s).factorial : ℚ))
      match k with
      | .defect i l => f * w i l
      | _ => f

/-! ## S10: one implemented Metropolis transition -/

/-- The `t`-th element (from `0`, increasing) of `[0, 2p)` whose membership in
`S` is `val`; `0` if there is none. -/
noncomputable def nthWith (I : Instance) (ε δ : ℚ) (S : Finset ℕ) (val : Bool) (t : ℕ) : ℕ :=
  ((List.range (2 * pSmall I ε δ)).filter fun e => decide (e ∈ S) == val).getD t 0

/-- Accept with probability `⌊c·2^k⌋/2^k`, `k = ⌈log₂ ξ⁻¹⌉`: a `k`-bit uniform
integer below the downward-rounded dyadic threshold. -/
noncomputable def acceptTest (I : Instance) (ε δ : ℚ) (c : ℚ) : PMF Bool :=
  (uniformBits (kAccParam I ε δ)).map fun Y =>
    decide (Y < ⌊c * (2 ^ kAccParam I ε δ : ℕ)⌋₊)

/-- **S10** (`transport.tex:68-74`, `algorithm.tex:394-425`): hold on a fair
bit; otherwise exchange a uniform element of `S` with a uniform element of its
complement (dyadic draws, `M = p`, `ζ = ξ`); reject outside `X` before any
evaluation; otherwise two fresh evaluations `λ(S')`, `λ(S)`, the ratio clipped at
one, and a dyadic acceptance threshold. -/
noncomputable def step (I : Instance) (ε δ : ℚ) (a : ℕ) (w : ℕ → ℕ → ℚ) (S : Finset ℕ) :
    PMF (Finset ℕ) := do
  let hold ← ProbRAM.fair
  if hold then pure S else do
    let u1 ← dyadicDraw (pSmall I ε δ) (ξParam I ε δ)
    let u2 ← dyadicDraw (pSmall I ε δ) (ξParam I ε δ)
    let S' := insert (nthWith I ε δ S false u2) (S.erase (nthWith I ε δ S true u1))
    match kind I ε δ S' with
    | .outside => pure S
    | k' => do
      let lNew ← lam I ε δ S' k' a w
      let lOld ← lam I ε δ S (kind I ε δ S) a w
      let ok ← acceptTest I ε δ (min 1 (lNew / lOld))
      pure (if ok then S' else S)

/-! ## S9a: the fresh `μ₀` draw and the capped restart -/

/-- Lexicographic unranking: the `r`-th `k`-subset of `[0, b)`, built greedily
(include `t` iff `r < C(b - t - 1, k' - 1)` for the `k'` still to choose). -/
noncomputable def unrank (b k r : ℕ) : Finset ℕ :=
  ((List.range b).foldl (fun st t =>
    if 0 < st.2.1 then
      if st.2.2 < Nat.choose (b - (t + 1)) (st.2.1 - 1) then (insert t st.1, st.2.1 - 1, st.2.2)
      else (st.1, st.2.1, st.2.2 - Nat.choose (b - (t + 1)) (st.2.1 - 1))
    else st) ((∅ : Finset ℕ), k, r)).1

/-- **A fresh `μ₀` draw** (`algorithm.tex:215-224`): per small cell `s`, `k_s` by a
dyadic draw from `{0..b_s}`, then a `k_s`-subset of its `b_s` pairs by a dyadic
draw of a rank in `[0, C(b_s, k_s))`; those pairs use their row element, the rest
their column element. -/
noncomputable def mu0 (I : Instance) (ε δ : ℚ) : PMF (Finset ℕ) :=
  loop (fun s S => do
    let k ← dyadicDraw (smallB I ε δ s + 1) (ξParam I ε δ)
    let rank ← dyadicDraw (Nat.choose (smallB I ε δ s) k) (ξParam I ε δ)
    pure (S ∪ (Finset.range (smallB I ε δ s)).image fun t =>
      if t ∈ unrank (smallB I ε δ s) k rank then 2 * (cellFirst I ε δ s + t)
      else 2 * (cellFirst I ε δ s + t) + 1))
    (nSmall I ε δ) ∅

/-- The restart in progress: the state, the stage `a`, trace steps finished in
it, and the transitions taken so far.  `used` is the algorithm's own counter for
the `B_ret` cap.  It decides the abort, so it is part of the answer, not a cost
meter. -/
structure Restart where
  /-- Current state. -/
  S : Finset ℕ
  /-- Current stage `a ∈ 1..j`. -/
  stage : ℕ
  /-- Trace steps completed in this stage. -/
  hits : ℕ
  /-- Underlying transitions taken (the cap counter). -/
  used : ℕ
  /-- All stages done. -/
  finished : Bool
  /-- Another transition was needed after the cap. -/
  aborted : Bool

/-- One iteration of the capped restart of phase `j`: stop if finished or
aborted; abort if `B_ret` transitions are used; otherwise one transition of
`P_{a, w^(a)}`, and a trace step ends at a transversal. -/
noncomputable def restartStep (I : Instance) (ε δ : ℚ) (ws : ℕ → ℕ → ℕ → ℚ) (j : ℕ)
    (st : Restart) : PMF Restart :=
  if st.finished then pure st else if st.aborted then pure st else
  if BretParam I ε δ ≤ st.used then pure { st with aborted := true } else do
    let S' ← step I ε δ st.stage (ws st.stage) st.S
    match kind I ε δ S' with
    | .transversal =>
      if st.hits + 1 = τParam I ε δ then
        pure ⟨S', st.stage + 1, 0, st.used + 1, decide (st.stage = j), false⟩
      else pure ⟨S', st.stage, st.hits + 1, st.used + 1, false, false⟩
    | _ => pure ⟨S', st.stage, st.hits, st.used + 1, false, false⟩

/-- **S9a**: from `S0`, for `a = 1..j`, `τ` trace steps of `P_{a, w^(a)}`, at most
`B_ret` transitions in all.  `j = 0` returns `S0`. -/
noncomputable def restart (I : Instance) (ε δ : ℚ) (ws : ℕ → ℕ → ℕ → ℚ) (j : ℕ)
    (S0 : Finset ℕ) : PMF Restart :=
  loop (fun _ st => restartStep I ε δ ws j st) (BretParam I ε δ + 1)
    ⟨S0, 1, 0, 0, decide (j = 0), false⟩

/-! ## S9b: observation -/

/-- The observation tallies: the current state, `n_0`, `n_il`, and `Σ G_j`. -/
structure Obs where
  /-- Current state. -/
  S : Finset ℕ
  /-- Transversals observed. -/
  n0 : ℕ
  /-- States of `A_il` observed. -/
  nT : ℕ → ℕ → ℕ
  /-- `Σ G_j` over the observed states. -/
  sumG : ℚ

/-- Observe the current state: count its type; at a transversal add
`G_j = ĥ_{j+1}/ĥ_j` from two fresh oracle calls (the factorial factors cancel);
`G_j = 0` off `A`. -/
noncomputable def observeState (I : Instance) (ε δ : ℚ) (j : ℕ) (o : Obs) : PMF Obs :=
  match kind I ε δ o.S with
  | .transversal => do
    let hNext ← oracle I ε δ (profile I ε δ o.S).1 (profile I ε δ o.S).2 (j + 1)
      (ξParam I ε δ) (ξParam I ε δ)
    let hCur ← oracle I ε δ (profile I ε δ o.S).1 (profile I ε δ o.S).2 j
      (ξParam I ε δ) (ξParam I ε δ)
    pure { o with n0 := o.n0 + 1, sumG := o.sumG + hNext / hCur }
  | .defect i l =>
    pure { o with nT := fun a b => if a = i ∧ b = l then o.nT i l + 1 else o.nT a b }
  | .outside => pure o

/-- **S9b**: `N_av` observed states of `P_{j, w^(j)}` from `S0`, the starting
state included. -/
noncomputable def observe (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ) (S0 : Finset ℕ) :
    PMF Obs := do
  let o0 ← observeState I ε δ j ⟨S0, 0, fun _ _ => 0, 0⟩
  loop (fun _ o => do
      let S' ← step I ε δ j w o.S
      observeState I ε δ j { o with S := S' })
    (NavParam I ε δ - 1) o0

/-! ## S9c: the abort test and the update -/

/-- Every type count is positive: `n_0 > 0` and `n_il > 0` for all `i ≠ l < p`. -/
def allPositive (p : ℕ) (o : Obs) : Prop :=
  0 < o.n0 ∧ ∀ i < p, ∀ l < p, i ≠ l → 0 < o.nT i l

noncomputable instance (p : ℕ) (o : Obs) : Decidable (allPositive p o) :=
  inferInstanceAs (Decidable (0 < o.n0 ∧ ∀ i < p, ∀ l < p, i ≠ l → 0 < o.nT i l))

/-- `eq:alg-multiplier-update`: `w_il ← w_il · n_0 / n_il` for `i ≠ l < p`. -/
noncomputable def updateW (p : ℕ) (w : ℕ → ℕ → ℚ) (o : Obs) : ℕ → ℕ → ℚ := fun i l =>
  if i < p ∧ l < p ∧ i ≠ l then w i l * (o.n0 : ℚ) / (o.nT i l : ℚ) else w i l

/-- The annealing run in progress: stored multipliers `w^(0..j)`, `∏ R̂`, and
whether some phase aborted. -/
structure RunState where
  /-- `w^(a)`, for the stages stored so far. -/
  ws : ℕ → ℕ → ℕ → ℚ
  /-- `∏ R̂_j` so far. -/
  prod : ℚ
  /-- Some phase aborted. -/
  aborted : Bool

/-- **Phase `j`** (`algorithm.tex:214-249`): fresh `μ₀`, capped restart, `N_av`
observations; after the zero-count test, `R̂_j = û / p̂_0` and, if `j + 1 < H`,
`w^(j+1)`.  An aborted run does nothing further. -/
noncomputable def phase (I : Instance) (ε δ : ℚ) (j : ℕ) (st : RunState) : PMF RunState :=
  if st.aborted then pure st else do
    let S0 ← mu0 I ε δ
    let rs ← restart I ε δ st.ws j S0
    if rs.aborted then pure { st with aborted := true } else do
      let o ← observe I ε δ j (st.ws j) rs.S
      if allPositive (pSmall I ε δ) o then
        let R := (o.sumG / (NavParam I ε δ : ℚ)) / ((o.n0 : ℚ) / (NavParam I ε δ : ℚ))
        if j + 1 < HParam I ε δ then
          pure ⟨Function.update st.ws (j + 1) (updateW (pSmall I ε δ) (st.ws j) o),
            st.prod * R, false⟩
        else pure ⟨st.ws, st.prod * R, false⟩
      else pure { st with aborted := true }

/-! ## S11: one annealing run -/

/-- **S11** (`algorithm.tex:251-254`), `p ≥ 1`: phases `j = 0..H-1` from `w^(0)`;
output `C(0) ∏_j R̂_j`, or `0` after an abort. -/
noncomputable def annealRun (I : Instance) (ε δ : ℚ) : PMF ℚ :=
  (loop (phase I ε δ) (HParam I ε δ)
      ⟨fun a => if a = 0 then w0 I ε δ else fun _ _ => 0, 1, false⟩).map
    fun st => if st.aborted then 0 else C0 I ε δ * st.prod

/-! ## S12: amplification by the median -/

/-- `s = ⌈log₂ δ⁻¹⌉`. -/
noncomputable def sRep (δ : ℚ) : ℕ := Nat.clog 2 ⌈δ⁻¹⌉₊

/-- `R` independent runs of `μ`, outputs in run order. -/
noncomputable def repeatRuns (R : ℕ) (μ : PMF ℚ) : PMF (List ℚ) :=
  loop (fun _ l => μ.map fun z => l ++ [z]) R []

/-- The order statistic at position `k` (from `0`) of the multiset of outputs. -/
noncomputable def orderStat (l : List ℚ) (k : ℕ) : ℚ :=
  ((l : Multiset ℚ).sort).getD k 0

/-- **The paper's algorithm** (`thm:main`, proof at `algorithm.tex:607-707`): the
law of `Ẑ`.  Infeasible inputs give `0` with no draw.  Otherwise
`s = ⌈log₂ δ⁻¹⌉`, `R = 10 s + 1` independent single runs (`p = 0`: `zeroRun`;
`p ≥ 1`: `annealRun`) and their median, the order statistic at `5 s`. -/
noncomputable def fpras (I : Instance) (ε δ : ℚ) : PMF ℚ :=
  if feasible I then
    (repeatRuns (10 * sRep δ + 1)
        (if pSmall I ε δ = 0 then zeroRun I ε δ else annealRun I ε δ)).map
      fun outs => orderStat outs (5 * sRep δ)
  else PMF.pure 0

end Cellcounting.Pseudocode
