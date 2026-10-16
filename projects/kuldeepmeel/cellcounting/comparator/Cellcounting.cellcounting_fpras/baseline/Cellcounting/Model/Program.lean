import Cellcounting.Model.Operations
import Cellcounting.Meta.CostSeal
import Cellcounting.Meta.ModelClosure

/-!
# The algorithm of Theorem `thm:main`, as a charged program

`Cellcounting.Program.fpras I ε δ tape : Charged Op Cell ℚ` is the paper's
algorithm, transcribed from the restatement's `algorithmTranscript` (steps
S0–S12).  It reads its fair bits from the sealed coin family `tape` (law in
`Model/Run.lean`) at positions `0, 1, 2, …`, threading the position as a cursor.
Every arithmetic step is a bit-length-charged primitive of
`Model/Operations.lean` on sealed numbers (`SNat`, `SRat`).  Loops are
`Charged.foldl`, `Charged.repeatFor` and `Charged.repeatWhile`, each with a bound
computed before the loop starts.  There is no recursion and no rejection loop.

## Encoding, and why

The theorem bounds **bit operations on every execution**.  So every number that
can grow is sealed, and every operation on one is charged by operand length.
This is what makes the time claim non-vacuous: repeated squaring cannot build a
long number for free.  Positions and loop indices are plain `ℕ` with uncharged
bookkeeping arithmetic (see "Model gaps").  The paired binary state is `2p`
membership bits (`List Bool`): element `2i` is the row element and `2i + 1` the
column element of pair `i`.  Multipliers are exact rationals.  The program
computes no real number and no partition function: no `C(j)` for `j > 0`, and no
`c_il(j)`.

## Correspondence ledger

| Paper | Lean |
|---|---|
| S0, `L` (input length) | `inputLen`, i.e. the charged read `SNat.inputLength` whose value is `Prelude`'s `inputLength I ε δ`, the same function the theorem's cost bound uses |
| S1, feasibility test (`scales.tex:8-24`, `algorithm.tex:17-18`) | `feasible`: explicit `Σr = Σc` test, then `network` + `maxFlow` (Edmonds–Karp: `bfs`, `bottleneck`, `pushFlow`, `augment`) |
| "return zero if infeasible" | the `else` branch of `fpras`: `SRat.lit 0`, `SRat.output`; no coin is read |
| S2, tightening (`scales.tex:24-44`) | `cellMin`, `cellMax`, `feasibleAtLeast`, `tighten`, `Tight` |
| S3, `eq:parameters` (`d, K, γ, A, B, W, H`) | `params`, `Params` |
| S4, small/large split, `p`, maximum spanning forest, roots, `F`, `M_f` | `splitCells`, `sortDesc`, `kruskal`, `rootsOf`, `orient`, `buildCtx`, `Ctx`; `p` in `fpras` |
| S5, `eq:penalty` `D(x,y,z)` | `penalty` (leaf elimination along `Ctx.order`) |
| S6, `prop:weight-oracle` (`evaluation.tex:40-482`) | `oracle`, `oracleParams`/`OParams` (`σ, N_in, Q_in, K_bin, ℓ_in, s', depth, ζ`), `sampleBin`, `walkStep`, `binAccept`, `ratioAvg` (`R_a`), `corrAvg` (`T`), `binOffsets`, `pow2Approx` |
| `lem:dyadic-integer-draw` | `dyadicDraw` (with `uniformBits`) |
| S7, `p = 0`: one oracle call, `ξ_in = ε/32`, `θ = 1/16`, `j = H` | `zeroRun` |
| S8, `p ≥ 1` setup: `q, C_p, C_d, K_obs, η, τ, B_ret, N_av, J_*, ξ`, `w^(0)`, `C(0)` | `chainSetup`, `Chain`, `Phase` |
| paired encoding, profile, types `A`, `A_il` (`signatures.tex:13-41`) | `profile`, `kind`, `Kind` |
| `λ = f_j` on `A`, `w_il f_j` on `A_il`; `eq:lifts` | `lam` (fresh oracle value times `∏ x_s! y_s!/b_s!`, times `w_il`) |
| S10, implemented Metropolis transition | `step` (hold bit; two dyadic element draws; reject outside `X` *before* any oracle call; two fresh oracle calls; clip at one; `acceptTest`) |
| S9a, `μ₀` draw and capped trace restart | `mu0` (with `binom`), `restart`, `Restart` |
| S9b, `N_av` observations, `G_j`, type counts | `observe`, `observeState`, `Obs` |
| S9c, zero-count abort, then `R̂_j = û/p̂_0`, `eq:alg-multiplier-update` | `allPositive` (tested **before** any division), `updateW`, `phase` |
| S11, single-run output `C(0) ∏ R̂_j`, or `0` after an abort | `annealRun`, `Run` |
| S12, `s = ⌈log₂ δ⁻¹⌉`, `R = 10s + 1`, median | `fpras` (`R` runs on consecutive tape stretches), `orderStat` at position `5s = (R-1)/2` |

The guards the restatement asks for are visible in the text.  The equal-totals
test comes before the max-flow call (`feasible`).  An infeasible input never
reaches S2.  `p = 0` is dispatched once, before any `p`-dependent parameter
(`fpras`, then `chainSetup`).  The zero-count abort precedes the divisions
(`phase`).  A proposal outside `X` is rejected before evaluation (`step`).  Every
weight evaluation is its own `oracle` call on fresh bits: two in `step` and two
in `observeState`, with nothing cached.  An abort short-circuits the remaining
phases (`phase`) and makes the run output zero (`annealRun`).

## Choices the paper leaves open (statement-neutral fixed conventions)

* Each component's root is its least-indexed vertex (rows `0..m-1`, then columns
  `m..m+n-1`).  Kruskal breaks capacity ties stably, in row-major cell order.
* The bin walk starts from bin `0`.
* Pairs are labelled consecutively per small cell, in row-major order of the
  small cells.  Subset ranks are decoded lexicographically.  "A uniform element
  of `S`" (resp. of its complement) is the `u`-th by increasing position.
* The hold bit holds on `true`.  The exact dyadic trial for probability `2^{-Δ}`
  reads `Δ` bits and accepts iff they are all `0`.
* Edmonds–Karp is given `V³` augmentations, `V = m + n + 2`.  Its `O(VE)`
  augmentation bound is cited by the paper (Edmonds–Karp 1972), not proved; it
  is a **proof obligation** (or a `Prior` field).
* Preprocessing S1–S4 is done once, before the `R` runs.

## Reconstructed details: to be checked against the paper

This pass had the restatement, not the paper's `evaluation.tex`/`scales.tex`
text.  The following lines are reconstructed from the restatement's summary.
They are flagged so that the handoff can compare them with the paper.

* **R1** (`penalty`): a small cell contributes `x_s` to its row margin and
  `b_s - y_s` to its column margin.  These agree with the table value `x_s` on
  balanced profiles.  The restatement does not say how an unbalanced profile
  enters the margin equations.
* **R2** (`binPoint`, `binOffsets`, `ratioAvg`, `corrAvg`): bin `v_e` of a free
  coordinate covers the integers `[⌈(b_e+1)v_e/B⌉, ⌈(b_e+1)(v_e+1)/B⌉)`, and its
  cube point is `(b_e+1)v_e/B`.  The ratio sample is
  `V_{a+1}(v)/V_a(v) = 2^{⌊aD(v)/H⌋ - ⌊(a+1)D(v)/H⌋}`.  The correction sample is
  `α_v 2^β` with `β = ⌊jD(v)/H⌋ - jD(z)/H`.  This makes
  `M_f ∏_a R_a · E[T] = h_j(x,y)` exactly.
* **R3** (`pow2Approx`): `β` is rounded to the nearest grid point,
  `h = ⌊β s' + 1/2⌋`, and the bisection returns its lower endpoint.
* **R4** (`oracleParams`): `ℓ_in = ⌈K_bin (H + dB + 16 Q_in/θ + 2)⌉`, literally as
  the restatement writes it.  A mixing-time bound would usually have
  `log₂(16 Q_in/θ)` here.  Both are polynomial, and a longer lazy walk is no
  worse in total variation.

## Model gaps

* Position and loop-index arithmetic (`i + 1`, `2 * i`, `m + j`, `V * V * V`, the
  tape cursor) is uncharged.  Comparisons of positions are charged
  (`idxEq`, `idxLt`).
* Data lives in plain `List`s, read and written through the charged `get`/`set`.
  This is a deviation from Arlib's program language (§2.5), which wants data in
  sealed carriers.
* `#programSeal`'s forbidden list (tool-owned `Meta/CostSeal.lean`) does not yet
  name the eliminators of the project's own sealed types
  (`SNat.casesOn`/`rec`, `SRat.casesOn`/`rec`).  The program does not use them,
  but nothing mechanical prevents it.
-/

set_option autoImplicit false

namespace Cellcounting.Program

open Arlib.Computation
open Cellcounting.Model
open Cellcounting.Model.Operations

/-- A charged computation in the bit-operation currency. -/
abbrev Prog := Charged Operations.Op Operations.Cell

/-- A cell of a (tightened) table: row, column, and its bound. -/
abbrev Entry := ℕ × ℕ × SNat

/-! ## Arithmetic and addressing helpers -/

/-- `Σ` of a list of sealed naturals. -/
def sumN (l : List SNat) : Prog SNat := do
  let z ← SNat.lit 0
  Charged.foldl (fun acc x => SNat.add acc x) l z

/-- `⌈log₂ x⌉ = Nat.clog 2 x`, computed as `Nat.size (x - 1)`. -/
def clog2 (x : SNat) : Prog SNat := do
  let one ← SNat.lit 1
  let y ← SNat.sub x one
  SNat.size y

/-- `⌈a / b⌉` for `b ≥ 1`. -/
def ceilDivN (a b : SNat) : Prog SNat := do
  let one ← SNat.lit 1
  let s ← SNat.add a b
  let s' ← SNat.sub s one
  SNat.div s' b

/-- `⌊x / 2⌋`. -/
def half (x : SNat) : Prog SNat := do
  let two ← SNat.lit 2
  SNat.div x two

/-- Read entry `(u, v)` of a matrix. -/
def get2 {α : Type} [Inhabited α] (M : List (List α)) (u v : ℕ) : Prog α := do
  let row ← Operations.get M u
  Operations.get row v

/-- Overwrite entry `(u, v)` of a matrix. -/
def set2 {α : Type} (M : List (List α)) (u v : ℕ) (a : α) : Prog (List (List α)) := do
  let row ← Operations.get M u
  let row' ← Operations.set row v a
  Operations.set M u row'

/-! ## Fair bits and the dyadic integer draw -/

/-- One fair bit, read from the tape at the cursor; the cursor advances. -/
def coin (tape : Coins ℕ) (cur : ℕ) : Prog (Bool × ℕ) := do
  let b ← Coins.flip cur tape
  pure (b, cur + 1)

/-- `k` fair bits, read as the binary integer `Y ∈ [0, 2^k)`. -/
def uniformBits (tape : Coins ℕ) (k : ℕ) (cur : ℕ) : Prog (SNat × ℕ) := do
  let z ← SNat.lit 0
  let one ← SNat.lit 1
  let two ← SNat.lit 2
  Charged.repeatFor (fun _ (st : SNat × ℕ) => do
    let (bit, cur') ← coin tape st.2
    let y2 ← SNat.mul st.1 two
    if bit then do
      let y ← SNat.add y2 one
      pure (y, cur')
    else pure (y2, cur')) k (z, cur)

/-- **`lem:dyadic-integer-draw`** (`evaluation.tex:356-371`): for `M ≥ 1` and
`0 < ζ < 1`, let `k` be the least natural with `M·2^{-k} ≤ ζ`, draw `Y` uniform on
`[0, 2^k)` with `k` fair bits, and output `⌊M·Y/2^k⌋`.  The least such `k` is
`⌈log₂ ⌈M/ζ⌉⌉`. -/
def dyadicDraw (tape : Coins ℕ) (M : SNat) (ζ : SRat) (cur : ℕ) : Prog (SNat × ℕ) := do
  let Mq ← SNat.toRat M
  let q ← SRat.div Mq ζ
  let c ← SRat.natCeil q
  let k ← clog2 c
  let kI ← SNat.index k
  let (Y, cur') ← uniformBits tape kI cur
  let MY ← SNat.mul M Y
  let pk ← SNat.pow2 k
  let out ← SNat.div MY pk
  pure (out, cur')

/-! ## S0: reading the input and its length -/

/-- Read a list of input naturals into sealed numbers. -/
def readList (l : List ℕ) : Prog (List SNat) :=
  Charged.foldl (fun acc k => do
    let x ← SNat.lit k
    Operations.push acc x) l []

/-- Read a matrix of input naturals. -/
def readMatrix (rows : List (List ℕ)) : Prog (List (List SNat)) :=
  Charged.foldl (fun acc row => do
    let xs ← readList row
    Operations.push acc xs) rows []

/-- **S0**: the input length `L`.  It is read through the charged primitive
`SNat.inputLength`, whose value is `Prelude`'s `inputLength I ε δ` itself, the
quantity the cost conjunct of the theorem is stated in.  `L` is not re-derived
here (restatement caller guard "shared-inputLength-contract"). -/
def inputLen (I : Instance) (ε δ : ℚ) : Prog SNat :=
  SNat.inputLength I ε δ

/-! ## S1: the feasibility test (Edmonds–Karp maximum flow) -/

/-- The network of `scales.tex:8-24` as a capacity matrix on `m + n + 2`
vertices: source `0`, row `i` at `1 + i`, column `j` at `1 + m + j`, sink
`m + n + 1`; source→row arcs carry `r_i`, row→column arcs `b_ij`, column→sink
arcs `c_j`. -/
def network (m n : ℕ) (r c : List SNat) (b : List (List SNat)) :
    Prog (List (List SNat)) := do
  let z ← SNat.lit 0
  let row0 ← Operations.replicate (m + n + 2) z
  let cap0 ← Operations.replicate (m + n + 2) row0
  let cap1 ← Charged.repeatFor (fun i cap => do
    let ri ← Operations.get r i
    set2 cap 0 (1 + i) ri) m cap0
  let cap2 ← Charged.repeatFor (fun i cap => do
    let bi ← Operations.get b i
    Charged.repeatFor (fun j cap' => do
      let bij ← Operations.get bi j
      set2 cap' (1 + i) (1 + m + j) bij) n cap) m cap1
  Charged.repeatFor (fun j cap => do
    let cj ← Operations.get c j
    set2 cap (1 + m + j) (m + n + 1) cj) n cap2

/-- Breadth-first search from the source in a residual matrix on `V` vertices.
Returns the parent array (`none` for an unreached vertex). -/
def bfs (V : ℕ) (res : List (List SNat)) : Prog (List (Option ℕ)) := do
  let zero ← SNat.lit 0
  let par0 ← Operations.replicate V (none : Option ℕ)
  let par ← Operations.set par0 0 (some 0)
  let ord ← Operations.replicate V 0
  let st ← Charged.repeatFor (fun k (st : List (Option ℕ) × List ℕ × ℕ) => do
    let live ← idxLt k st.2.2
    if live then do
      let u ← Operations.get st.2.1 k
      let row ← Operations.get res u
      Charged.repeatFor (fun v (st' : List (Option ℕ) × List ℕ × ℕ) => do
        let cap ← Operations.get row v
        let pos ← SNat.lt zero cap
        if pos then do
          let pv ← Operations.get st'.1 v
          match pv with
          | some _ => pure st'
          | none => do
            let par' ← Operations.set st'.1 v (some u)
            let ord' ← Operations.set st'.2.1 st'.2.2 v
            pure (par', ord', st'.2.2 + 1)
        else pure st') V st
    else pure st) V (par, ord, 1)
  pure st.1

/-- The bottleneck residual capacity along the parent path from the sink. -/
def bottleneck (V : ℕ) (res : List (List SNat)) (par : List (Option ℕ)) :
    Prog SNat := do
  let st ← Charged.repeatFor (fun _ (st : ℕ × Option SNat) => do
    let atSrc ← idxEq st.1 0
    if atSrc then pure st else do
      let pu ← Operations.get par st.1
      match pu with
      | none => pure st
      | some u => do
        let cuv ← get2 res u st.1
        match st.2 with
        | none => pure (u, some cuv)
        | some bn => do
          let smaller ← SNat.lt cuv bn
          if smaller then pure (u, some cuv) else pure (u, some bn)) V (V - 1, none)
  match st.2 with
  | none => SNat.lit 0
  | some bn => pure bn

/-- Push `bn` units along the parent path from the sink. -/
def pushFlow (V : ℕ) (res : List (List SNat)) (par : List (Option ℕ)) (bn : SNat) :
    Prog (List (List SNat)) := do
  let st ← Charged.repeatFor (fun _ (st : ℕ × List (List SNat)) => do
    let atSrc ← idxEq st.1 0
    if atSrc then pure st else do
      let pu ← Operations.get par st.1
      match pu with
      | none => pure st
      | some u => do
        let fwd ← get2 st.2 u st.1
        let fwd' ← SNat.sub fwd bn
        let res1 ← set2 st.2 u st.1 fwd'
        let bwd ← get2 res1 st.1 u
        let bwd' ← SNat.add bwd bn
        let res2 ← set2 res1 st.1 u bwd'
        pure (u, res2)) V (V - 1, res)
  pure st.2

/-- One Edmonds–Karp augmentation along a shortest residual path; `none` when
the sink is unreachable. -/
def augment (V : ℕ) (res : List (List SNat)) :
    Prog (Option (List (List SNat) × SNat)) := do
  let par ← bfs V res
  let pt ← Operations.get par (V - 1)
  match pt with
  | none => pure none
  | some _ => do
    let bn ← bottleneck V res par
    let res' ← pushFlow V res par bn
    pure (some (res', bn))

/-- The maximum-flow value, by at most `V³` Edmonds–Karp augmentations (their
`O(VE)` bound is a proof obligation). -/
def maxFlow (V : ℕ) (cap : List (List SNat)) : Prog SNat := do
  let z ← SNat.lit 0
  let st ← Charged.repeatWhile (fun _ (st : List (List SNat) × SNat) => do
    let a ← augment V st.1
    match a with
    | none => pure none
    | some (res', bn) => do
      let f ← SNat.add st.2 bn
      pure (some (res', f))) (V * V * V) (cap, z)
  pure st.2

/-- **S1, the feasibility test.**  First the explicit equal-totals comparison,
then the max-flow value against `Σ r`. -/
def feasible (m n : ℕ) (r c : List SNat) (b : List (List SNat)) : Prog Bool := do
  let sr ← sumN r
  let sc ← sumN c
  let totalsEqual ← SNat.eq sr sc
  if totalsEqual then do
    let cap ← network m n r c b
    let f ← maxFlow (m + n + 2) cap
    SNat.eq f sr
  else pure false

/-! ## S2: tightening -/

/-- Rounds of a binary search over `[0, x]`: `bitLen x ≥ ⌈log₂ (x + 1)⌉`. -/
def searchRounds (x : SNat) : Prog ℕ := do
  let len ← SNat.bitLen x
  SNat.index len

/-- `l_ij`, the least feasible value of cell `(i, j)`: binary search for the
least `v ≤ b_ij` such that the instance with `b_ij := v` is feasible. -/
def cellMin (m n : ℕ) (r c : List SNat) (b : List (List SNat)) (i j : ℕ) :
    Prog SNat := do
  let bij ← get2 b i j
  let lo ← SNat.lit 0
  let k ← searchRounds bij
  let st ← Charged.repeatFor (fun _ (st : SNat × SNat) => do
    let isOpen ← SNat.lt st.1 st.2
    if isOpen then do
      let s ← SNat.add st.1 st.2
      let mid ← half s
      let b' ← set2 b i j mid
      let ok ← feasible m n r c b'
      if ok then pure (st.1, mid) else do
        let one ← SNat.lit 1
        let lo' ← SNat.add mid one
        pure (lo', st.2)
    else pure st) k (lo, bij)
  pure st.2

/-- Feasibility with the extra lower bound `X_ij ≥ v`: subtract `v` from the
cell and its two margins, rejecting at once if any would become negative. -/
def feasibleAtLeast (m n : ℕ) (r c : List SNat) (b : List (List SNat)) (i j : ℕ)
    (v : SNat) : Prog Bool := do
  let ri ← Operations.get r i
  let cj ← Operations.get c j
  let bij ← get2 b i j
  let okR ← SNat.le v ri
  if okR then do
    let okC ← SNat.le v cj
    if okC then do
      let okB ← SNat.le v bij
      if okB then do
        let ri' ← SNat.sub ri v
        let r' ← Operations.set r i ri'
        let cj' ← SNat.sub cj v
        let c' ← Operations.set c j cj'
        let bij' ← SNat.sub bij v
        let b' ← set2 b i j bij'
        feasible m n r' c' b'
      else pure false
    else pure false
  else pure false

/-- `u_ij`, the greatest feasible value of cell `(i, j)`, searched in
`[l_ij, b_ij]`. -/
def cellMax (m n : ℕ) (r c : List SNat) (b : List (List SNat)) (i j : ℕ) (lo : SNat) :
    Prog SNat := do
  let bij ← get2 b i j
  let k ← searchRounds bij
  let st ← Charged.repeatFor (fun _ (st : SNat × SNat) => do
    let isOpen ← SNat.lt st.1 st.2
    if isOpen then do
      let one ← SNat.lit 1
      let s ← SNat.add st.1 st.2
      let s1 ← SNat.add s one
      let mid ← half s1
      let ok ← feasibleAtLeast m n r c b i j mid
      if ok then pure (mid, st.2) else do
        let hi' ← SNat.sub mid one
        pure (st.1, hi')
    else pure st) k (lo, bij)
  pure st.1

/-- The tightened instance (`scales.tex:24-44`): margins with all incident
minima subtracted, and the retained cells `(i, j, u_ij - l_ij)` with positive
bound.  All row and column vertices are retained. -/
structure Tight where
  /-- Tightened row margins. -/
  rows : List SNat
  /-- Tightened column margins. -/
  cols : List SNat
  /-- Retained cells, with bound `u - l > 0`. -/
  cells : List Entry

/-- Entrywise `a_i - b_i` for `i < k`. -/
def subLists (a b : List SNat) (k : ℕ) : Prog (List SNat) :=
  Charged.repeatFor (fun i acc => do
    let x ← Operations.get a i
    let y ← Operations.get b i
    let d ← SNat.sub x y
    Operations.push acc d) k []

/-- **S2**: the extrema `l_ij`, `u_ij` of every cell, by binary search with
flow feasibility, and the tightened instance. -/
def tighten (m n : ℕ) (r c : List SNat) (b : List (List SNat)) : Prog Tight := do
  let z ← SNat.lit 0
  let lowR0 ← Operations.replicate m z
  let lowC0 ← Operations.replicate n z
  let st ← Charged.repeatFor (fun i st0 =>
    Charged.repeatFor (fun j (st : List SNat × List SNat × List Entry) => do
      let l ← cellMin m n r c b i j
      let u ← cellMax m n r c b i j l
      let w ← SNat.sub u l
      let lr ← Operations.get st.1 i
      let lr' ← SNat.add lr l
      let lowR ← Operations.set st.1 i lr'
      let lc ← Operations.get st.2.1 j
      let lc' ← SNat.add lc l
      let lowC ← Operations.set st.2.1 j lc'
      let keep ← SNat.lt z w
      if keep then do
        let cells ← Operations.push st.2.2 (i, j, w)
        pure (lowR, lowC, cells)
      else pure (lowR, lowC, st.2.2)) n st0) m (lowR0, lowC0, [])
  let rows ← subLists r st.1 m
  let cols ← subLists c st.2.1 n
  pure ⟨rows, cols, st.2.2⟩

/-! ## S3: the global parameters (`eq:parameters`) -/

/-- The parameters of `eq:parameters` (`scales.tex:48-56`). -/
structure Params where
  /-- `d = mn + m + n + 2`, with the original dimensions. -/
  d : SNat
  /-- `K = 20 (L + d + ⌈log₂ ε⁻¹⌉ + 1)`. -/
  K : SNat
  /-- `A = ⌈4K/γ⌉` with `γ = ε/(512 d K)`. -/
  A : SNat
  /-- `B = 16 A d²`. -/
  B : SNat
  /-- `W = 100 d B`. -/
  W : SNat
  /-- `H = 10 A d² (W + 1)`. -/
  H : SNat

/-- **S3**: exact computation of `d, K, γ, A, B, W, H`. -/
def params (m n : ℕ) (L : SNat) (ε : SRat) : Prog Params := do
  let mS ← SNat.lit m
  let nS ← SNat.lit n
  let mn ← SNat.mul mS nS
  let t1 ← SNat.add mn mS
  let t2 ← SNat.add t1 nS
  let two ← SNat.lit 2
  let d ← SNat.add t2 two
  let oneQ ← SRat.lit 1
  let inv ← SRat.div oneQ ε
  let ce ← SRat.natCeil inv
  let lg ← clog2 ce
  let one ← SNat.lit 1
  let s1 ← SNat.add L d
  let s2 ← SNat.add s1 lg
  let s3 ← SNat.add s2 one
  let c20 ← SNat.lit 20
  let K ← SNat.mul c20 s3
  let c512 ← SNat.lit 512
  let dK ← SNat.mul d K
  let den ← SNat.mul c512 dK
  let denQ ← SNat.toRat den
  let γ ← SRat.div ε denQ
  let c4 ← SNat.lit 4
  let fK ← SNat.mul c4 K
  let fKq ← SNat.toRat fK
  let q ← SRat.div fKq γ
  let A ← SRat.natCeil q
  let d2 ← SNat.mul d d
  let c16 ← SNat.lit 16
  let a16 ← SNat.mul c16 A
  let B ← SNat.mul a16 d2
  let c100 ← SNat.lit 100
  let d100 ← SNat.mul c100 d
  let W ← SNat.mul d100 B
  let c10 ← SNat.lit 10
  let a10 ← SNat.mul c10 A
  let ad2 ← SNat.mul a10 d2
  let W1 ← SNat.add W one
  let H ← SNat.mul ad2 W1
  pure ⟨d, K, A, B, W, H⟩

/-! ## S4: small and large cells, the maximum spanning forest -/

/-- Split retained cells into small (`b < W`) and large ones, with their
counts. -/
def splitCells (W : SNat) (cells : List Entry) :
    Prog ((List Entry × ℕ) × (List Entry × ℕ)) :=
  Charged.foldl (fun (st : (List Entry × ℕ) × (List Entry × ℕ)) (e : Entry) => do
    let isSmall ← SNat.lt e.2.2 W
    if isSmall then do
      let s ← Operations.push st.1.1 e
      pure ((s, st.1.2 + 1), st.2)
    else do
      let l ← Operations.push st.2.1 e
      pure (st.1, (l, st.2.2 + 1))) cells (([], 0), ([], 0))

/-- Insert `x` into a list sorted by decreasing bound, after every entry whose
bound is at least `x`'s. -/
def insertDesc (l : List Entry) (x : Entry) : Prog (List Entry) := do
  let st ← Charged.foldl (fun (st : List Entry × Bool) (y : Entry) => do
    if st.2 then do
      let o ← Operations.push st.1 y
      pure (o, true)
    else do
      let smaller ← SNat.lt y.2.2 x.2.2
      if smaller then do
        let o ← Operations.push st.1 x
        let o' ← Operations.push o y
        pure (o', true)
      else do
        let o ← Operations.push st.1 y
        pure (o, false)) l ([], false)
  if st.2 then pure st.1 else Operations.push st.1 x

/-- Large cells sorted by decreasing capacity (insertion sort, stable). -/
def sortDesc (l : List Entry) : Prog (List Entry) :=
  Charged.foldl (fun acc x => insertDesc acc x) l []

/-- Kruskal's construction (`scales.tex:91-99`) on the bipartite graph with
vertices `0..m-1` (rows) and `m..m+n-1` (columns): add a large cell, in order
of decreasing capacity, whenever it joins two current components.  Returns the
tree cells, the free cells (with counts) and the final component labels. -/
def kruskal (m n : ℕ) (large : List Entry) :
    Prog ((List Entry × ℕ) × (List Entry × ℕ) × List ℕ) := do
  let comp0 ← Charged.repeatFor (fun v acc => Operations.push acc v) (m + n) []
  Charged.foldl (fun (st : (List Entry × ℕ) × (List Entry × ℕ) × List ℕ) (e : Entry) => do
    let cu ← Operations.get st.2.2 e.1
    let cv ← Operations.get st.2.2 (m + e.2.1)
    let same ← idxEq cu cv
    if same then do
      let f ← Operations.push st.2.1.1 e
      pure (st.1, (f, st.2.1.2 + 1), st.2.2)
    else do
      let t ← Operations.push st.1.1 e
      let comp' ← Charged.repeatFor (fun w comp => do
        let cw ← Operations.get comp w
        let hit ← idxEq cw cv
        if hit then Operations.set comp w cu else pure comp) (m + n) st.2.2
      pure ((t, st.1.2 + 1), st.2.1, comp')) large (([], 0), ([], 0), comp0)

/-- One root per component: its least-indexed vertex. -/
def rootsOf (V : ℕ) (comp : List ℕ) : Prog (List ℕ) := do
  let seen0 ← Operations.replicate V false
  let st ← Charged.repeatFor (fun v (st : List Bool × List ℕ) => do
    let cv ← Operations.get comp v
    let s ← Operations.get st.1 cv
    if s then pure st else do
      let seen ← Operations.set st.1 cv true
      let rs ← Operations.push st.2 v
      pure (seen, rs)) V (seen0, [])
  pure st.2

/-- Breadth-first search state over the forest: visited marks, the queue, its
length, and the discovered `(vertex, parent tree edge)` pairs, newest first. -/
abbrev Orient := (List Bool × List ℕ × ℕ) × List (ℕ × ℕ)

/-- Discover vertex `w` through tree edge `t`, unless already visited. -/
def visit (w t : ℕ) (st : Orient) : Prog Orient := do
  let seen ← Operations.get st.1.1 w
  if seen then pure st else do
    let vis ← Operations.set st.1.1 w true
    let q ← Operations.set st.1.2.1 st.1.2.2 w
    pure ((vis, q, st.1.2.2 + 1), (w, t) :: st.2)

/-- Orient the forest from its roots.  The result lists every nonroot vertex
with its parent tree edge, in reverse breadth-first order, so leaves come before
their parents: the order of leaf elimination. -/
def orient (m n : ℕ) (tree : List Entry) (nTree : ℕ) (roots : List ℕ) :
    Prog (List (ℕ × ℕ)) := do
  let vis0 ← Operations.replicate (m + n) false
  let q0 ← Operations.replicate (m + n) 0
  let st0 ← Charged.foldl (fun (st : List Bool × List ℕ × ℕ) v => do
    let vis ← Operations.set st.1 v true
    let q ← Operations.set st.2.1 st.2.2 v
    pure (vis, q, st.2.2 + 1)) roots (vis0, q0, 0)
  let st ← Charged.repeatFor (fun k (st : Orient) => do
    let live ← idxLt k st.1.2.2
    if live then do
      let u ← Operations.get st.1.2.1 k
      Charged.repeatFor (fun t (st' : Orient) => do
        let e ← Operations.get tree t
        let atRow ← idxEq e.1 u
        if atRow then visit (m + e.2.1) t st' else do
          let atCol ← idxEq (m + e.2.1) u
          if atCol then visit e.1 t st' else pure st') nTree st
    else pure st) (m + n) (st0, [])
  pure st.2

/-- Everything the weight oracle reads: the tightened margins, the small, free
and tree cells, the elimination order, the roots, `M_f`, and the global
parameters it uses. -/
structure Ctx where
  /-- Number of rows. -/
  m : ℕ
  /-- Number of columns. -/
  n : ℕ
  /-- Tightened row margins. -/
  rows : List SNat
  /-- Tightened column margins. -/
  cols : List SNat
  /-- Small cells (`b < W`). -/
  small : List Entry
  /-- Their number. -/
  nSmall : ℕ
  /-- Free cells `F`: large cells outside the forest. -/
  free : List Entry
  /-- Their number `e`. -/
  nFree : ℕ
  /-- Tree cells `T`. -/
  tree : List Entry
  /-- Their number. -/
  nTree : ℕ
  /-- Leaf-elimination order: `(vertex, parent tree edge)`, leaves first. -/
  order : List (ℕ × ℕ)
  /-- One root per component. -/
  roots : List ℕ
  /-- `M_f = ∏_{e ∈ F} (b_e + 1)`. -/
  Mf : SNat
  /-- `d`. -/
  d : SNat
  /-- `B`. -/
  B : SNat
  /-- `H`. -/
  H : SNat
  /-- `A` as a rational. -/
  Aq : SRat
  /-- `H` as a rational. -/
  Hq : SRat
  /-- `B` as a rational. -/
  Bq : SRat

/-- **S4**: the small/large split, the forest, roots, elimination order and
`M_f`. -/
def buildCtx (m n : ℕ) (T : Tight) (Pm : Params) : Prog Ctx := do
  let ((small, nSmall), (large, _)) ← splitCells Pm.W T.cells
  let sorted ← sortDesc large
  let ((tree, nTree), (free, nFree), comp) ← kruskal m n sorted
  let rts ← rootsOf (m + n) comp
  let order ← orient m n tree nTree rts
  let one ← SNat.lit 1
  let Mf ← Charged.foldl (fun acc (e : Entry) => do
    let b1 ← SNat.add e.2.2 one
    SNat.mul acc b1) free one
  let Aq ← SNat.toRat Pm.A
  let Hq ← SNat.toRat Pm.H
  let Bq ← SNat.toRat Pm.B
  pure ⟨m, n, T.rows, T.cols, small, nSmall, free, nFree, tree, nTree, order, rts, Mf,
    Pm.d, Pm.B, Pm.H, Aq, Hq, Bq⟩

/-! ## S5: the penalty `D(x, y, z)` (`eq:penalty`) -/

/-- Add `x` to entry `v` of a vector. -/
def addAt (acc : List SRat) (v : ℕ) (x : SRat) : Prog (List SRat) := do
  let a ← Operations.get acc v
  let a' ← SRat.add a x
  Operations.set acc v a'

/-- The prescribed (tightened) margin of vertex `v`. -/
def margin (C : Ctx) (v : ℕ) : Prog SRat := do
  let isRow ← idxLt v C.m
  if isRow then do
    let x ← Operations.get C.rows v
    SNat.toRat x
  else do
    let x ← Operations.get C.cols (v - C.m)
    SNat.toRat x

/-- `|x|`. -/
def absQ (x : SRat) : Prog SRat := do
  let z ← SRat.lit 0
  let neg ← SRat.lt x z
  if neg then SRat.sub z x else pure x

/-- `dist(x, [0, b])`. -/
def distQ (x b : SRat) : Prog SRat := do
  let z ← SRat.lit 0
  let neg ← SRat.lt x z
  if neg then SRat.sub z x else do
    let over ← SRat.lt b x
    if over then SRat.sub x b else pure z

/-- **`D(x, y, z)`** (`scales.tex:113-126`).  The small cells contribute `x_s` to
their row and `b_s - y_s` to their column; the free cells contribute `z_e` to
both endpoints; leaf elimination then solves each tree value from the margin of
its nonroot endpoint; finally
`D = A (Σ_roots |δ_v| + Σ_{t ∈ T} dist(z_t, [0, b_t]) / b_t)`. -/
def penalty (C : Ctx) (x y : List SNat) (zf : List SRat) : Prog SRat := do
  let zero ← SRat.lit 0
  let acc0 ← Operations.replicate (C.m + C.n) zero
  let acc1 ← Charged.repeatFor (fun k acc => do
    let s ← Operations.get C.small k
    let xs ← Operations.get x k
    let ys ← Operations.get y k
    let xq ← SNat.toRat xs
    let acc' ← addAt acc s.1 xq
    let cv ← SNat.sub s.2.2 ys
    let cq ← SNat.toRat cv
    addAt acc' (C.m + s.2.1) cq) C.nSmall acc0
  let acc2 ← Charged.repeatFor (fun k acc => do
    let e ← Operations.get C.free k
    let ze ← Operations.get zf k
    let acc' ← addAt acc e.1 ze
    addAt acc' (C.m + e.2.1) ze) C.nFree acc1
  let zt0 ← Operations.replicate C.nTree zero
  let st ← Charged.foldl (fun (st : List SRat × List SRat) (vt : ℕ × ℕ) => do
    let e ← Operations.get C.tree vt.2
    let marg ← margin C vt.1
    let av ← Operations.get st.1 vt.1
    let ztv ← SRat.sub marg av
    let zt ← Operations.set st.2 vt.2 ztv
    let atRow ← idxEq vt.1 e.1
    if atRow then do
      let acc ← addAt st.1 (C.m + e.2.1) ztv
      pure (acc, zt)
    else do
      let acc ← addAt st.1 e.1 ztv
      pure (acc, zt)) C.order (acc2, zt0)
  let rootSum ← Charged.foldl (fun s v => do
    let av ← Operations.get st.1 v
    let marg ← margin C v
    let dv ← SRat.sub av marg
    let a ← absQ dv
    SRat.add s a) C.roots zero
  let distSum ← Charged.repeatFor (fun t s => do
    let e ← Operations.get C.tree t
    let zv ← Operations.get st.2 t
    let bq ← SNat.toRat e.2.2
    let dd ← distQ zv bq
    let q ← SRat.div dd bq
    SRat.add s q) C.nTree zero
  let tot ← SRat.add rootSum distSum
  SRat.mul C.Aq tot

/-! ## S6: the weight oracle (`prop:weight-oracle`, `evaluation.tex:40-482`) -/

/-- The internal parameters of one oracle call (`evaluation.tex:327-354`). -/
structure OParams where
  /-- `N_in`, samples per average. -/
  N : ℕ
  /-- `N_in` as a rational. -/
  Nq : SRat
  /-- `ℓ_in`, steps of each bin walk. -/
  ell : ℕ
  /-- `⌈log₂ (4d)⌉`, bits per walk proposal. -/
  kd : ℕ
  /-- `2e`, the number of signed coordinate directions. -/
  twoE : SNat
  /-- `B - 1`, the last bin index. -/
  Bm1 : SNat
  /-- `ζ = θ/(8 Q_in)`, the offset-draw tolerance. -/
  ζ : SRat
  /-- `log₂ s'`. -/
  ks : ℕ
  /-- `s'`, the power of two in `[32/σ, 64/σ]`. -/
  sPrime : SNat
  /-- `⌈log₂ (512/σ)⌉`, the bisection depth. -/
  depth : ℕ
  /-- `B^e`. -/
  Be : SNat

/-- `σ, N_in, Q_in, K_bin, ℓ_in, s', depth, ζ` from `ξ_in` and `θ`. -/
def oracleParams (C : Ctx) (ξin θ : SRat) : Prog OParams := do
  let one ← SNat.lit 1
  let H1 ← SNat.add C.H one
  let H1q ← SNat.toRat H1
  -- σ = ξ_in / (50 (H + 1))
  let c50 ← SRat.lit 50
  let den ← SRat.mul c50 H1q
  let σ ← SRat.div ξin den
  -- N_in = ⌈10⁶ (H + 1) / (θ σ²)⌉
  let c1e6 ← SRat.lit 1000000
  let num ← SRat.mul c1e6 H1q
  let σ2 ← SRat.mul σ σ
  let θσ2 ← SRat.mul θ σ2
  let nq ← SRat.div num θσ2
  let N ← SRat.natCeil nq
  let NI ← SNat.index N
  let Nq ← SNat.toRat N
  -- Q_in = (d + 1)(H + 1) N_in
  let d1 ← SNat.add C.d one
  let dH ← SNat.mul d1 H1
  let Q ← SNat.mul dH N
  let Qq ← SNat.toRat Q
  -- K_bin = 2 (10⁴ d² B)²
  let d2 ← SNat.mul C.d C.d
  let c1e4 ← SNat.lit 10000
  let t ← SNat.mul c1e4 d2
  let t' ← SNat.mul t C.B
  let t2 ← SNat.mul t' t'
  let two ← SNat.lit 2
  let Kbin ← SNat.mul two t2
  -- ℓ_in = ⌈K_bin (H + dB + 16 Q_in/θ + 2)⌉
  let dB ← SNat.mul C.d C.B
  let s ← SNat.add C.H dB
  let s2 ← SNat.add s two
  let s2q ← SNat.toRat s2
  let c16 ← SRat.lit 16
  let q16 ← SRat.mul c16 Qq
  let q16θ ← SRat.div q16 θ
  let inner ← SRat.add s2q q16θ
  let Kq ← SNat.toRat Kbin
  let ellq ← SRat.mul Kq inner
  let ellN ← SRat.natCeil ellq
  let ell ← SNat.index ellN
  -- ⌈log₂ (4d)⌉
  let c4 ← SNat.lit 4
  let d4 ← SNat.mul c4 C.d
  let kdN ← clog2 d4
  let kd ← SNat.index kdN
  -- 2e and B - 1
  let eS ← SNat.lit C.nFree
  let twoE ← SNat.mul two eS
  let Bm1 ← SNat.sub C.B one
  -- ζ = θ / (8 Q_in)
  let c8 ← SRat.lit 8
  let q8 ← SRat.mul c8 Qq
  let ζ ← SRat.div θ q8
  -- s' = 2^⌈log₂ ⌈32/σ⌉⌉, the power of two in [32/σ, 64/σ]
  let c32 ← SRat.lit 32
  let r32 ← SRat.div c32 σ
  let c32N ← SRat.natCeil r32
  let ksN ← clog2 c32N
  let ks ← SNat.index ksN
  let sPrime ← SNat.pow2 ksN
  -- depth = ⌈log₂ (512/σ)⌉
  let c512 ← SRat.lit 512
  let r512 ← SRat.div c512 σ
  let c512N ← SRat.natCeil r512
  let depN ← clog2 c512N
  let depth ← SNat.index depN
  -- B^e
  let Be ← Charged.repeatFor (fun _ acc => SNat.mul acc C.B) C.nFree one
  pure ⟨NI, Nq, ell, kd, twoE, Bm1, ζ, ks, sPrime, depth, Be⟩

/-- `⌊a·D/H⌋`, the exponent with `V_a = 2^{-⌊a D/H⌋}`. -/
def levelExp (C : Ctx) (aq D : SRat) : Prog SRat := do
  let t ← SRat.mul aq D
  let u ← SRat.div t C.Hq
  SRat.floor u

/-- The cube point of a bin vector: `z_e = (b_e + 1) v_e / B`. -/
def binPoint (C : Ctx) (v : List SNat) : Prog (List SRat) := do
  let one ← SNat.lit 1
  Charged.repeatFor (fun k acc => do
    let e ← Operations.get C.free k
    let ve ← Operations.get v k
    let b1 ← SNat.add e.2.2 one
    let t ← SNat.mul b1 ve
    let tq ← SNat.toRat t
    let q ← SRat.div tq C.Bq
    Operations.push acc q) C.nFree []

/-- The exponent of `V_a` at a bin. -/
def binExp (C : Ctx) (aq : SRat) (x y : List SNat) (v : List SNat) : Prog SRat := do
  let z ← binPoint C v
  let D ← penalty C x y z
  levelExp C aq D

/-- The Metropolis decision between bins `v` and `w` for `V_a`: accept with
probability `min{1, V_a(w)/V_a(v)} = 2^{-max(0, k_a(w) - k_a(v))}`, by an exact
dyadic trial on that many fair bits. -/
def binAccept (C : Ctx) (tape : Coins ℕ) (aq : SRat) (x y : List SNat)
    (v w : List SNat) (cur : ℕ) : Prog (List SNat × ℕ) := do
  let kv ← binExp C aq x y v
  let kw ← binExp C aq x y w
  let downhill ← SRat.le kw kv
  if downhill then pure (w, cur) else do
    let dq ← SRat.sub kw kv
    let dN ← SRat.natFloor dq
    let dI ← SNat.index dN
    let (Y, cur') ← uniformBits tape dI cur
    let zero ← SNat.lit 0
    let ok ← SNat.eq Y zero
    if ok then pure (w, cur') else pure (v, cur')

/-- One step of the bin walk for `V_a`: each signed coordinate direction with
probability `2^{-⌈log₂ 4d⌉}`, otherwise hold; a move off `{0..B-1}^e` holds. -/
def walkStep (C : Ctx) (P : OParams) (tape : Coins ℕ) (aq : SRat) (x y : List SNat)
    (st : List SNat × ℕ) : Prog (List SNat × ℕ) := do
  let (u, cur) ← uniformBits tape P.kd st.2
  let moves ← SNat.lt u P.twoE
  if moves then do
    let two ← SNat.lit 2
    let one ← SNat.lit 1
    let zero ← SNat.lit 0
    let coord ← SNat.div u two
    let dir ← SNat.mod u two
    let ci ← SNat.index coord
    let vc ← Operations.get st.1 ci
    let up ← SNat.eq dir one
    if up then do
      let edge ← SNat.eq vc P.Bm1
      if edge then pure (st.1, cur) else do
        let vc' ← SNat.add vc one
        let w ← Operations.set st.1 ci vc'
        binAccept C tape aq x y st.1 w cur
    else do
      let edge ← SNat.eq vc zero
      if edge then pure (st.1, cur) else do
        let vc' ← SNat.sub vc one
        let w ← Operations.set st.1 ci vc'
        binAccept C tape aq x y st.1 w cur
  else pure (st.1, cur)

/-- One bin sample for `V_a`: a fresh walk of `ℓ_in` steps from the fixed bin
`0`.  With no free cells the bin space is `{()}` and nothing is drawn. -/
def sampleBin (C : Ctx) (P : OParams) (tape : Coins ℕ) (aq : SRat) (x y : List SNat)
    (cur : ℕ) : Prog (List SNat × ℕ) := do
  let noFree ← idxEq C.nFree 0
  if noFree then pure ([], cur) else do
    let zero ← SNat.lit 0
    let v0 ← Operations.replicate C.nFree zero
    Charged.repeatFor (fun _ st => walkStep C P tape aq x y st) P.ell (v0, cur)

/-- The average of `N_in` samples of `V_{a+1}(v)/V_a(v) = 2^{k_a(v) - k_{a+1}(v)}`,
`v` from fresh bin walks for `V_a`: the estimate of `R_a`. -/
def ratioAvg (C : Ctx) (P : OParams) (tape : Coins ℕ) (x y : List SNat) (a : ℕ)
    (cur : ℕ) : Prog (SRat × ℕ) := do
  let aS ← SNat.lit a
  let aq ← SNat.toRat aS
  let one ← SNat.lit 1
  let a1 ← SNat.add aS one
  let a1q ← SNat.toRat a1
  let zero ← SRat.lit 0
  let st ← Charged.repeatFor (fun _ (st : SRat × ℕ) => do
    let (v, cur') ← sampleBin C P tape aq x y st.2
    let z ← binPoint C v
    let D ← penalty C x y z
    let k0 ← levelExp C aq D
    let k1 ← levelExp C a1q D
    let dlt ← SRat.sub k0 k1
    let ratio ← SRat.zpow2 dlt
    let s ← SRat.add st.1 ratio
    pure (s, cur')) P.N (zero, cur)
  let avg ← SRat.div st.1 P.Nq
  pure (avg, st.2)

/-- `2^β`, approximately: round `β` to the grid `h/s'`, then bisect `[0, 8]` to
depth `⌈log₂ (512/σ)⌉`, comparing `mid^{s'}` (by `log₂ s'` squarings) with
`2^h`. -/
def pow2Approx (P : OParams) (β : SRat) : Prog SRat := do
  let sq ← SNat.toRat P.sPrime
  let t ← SRat.mul β sq
  let halfQ ← SRat.lit (1 / 2)
  let t' ← SRat.add t halfQ
  let h ← SRat.floor t'
  let target ← SRat.zpow2 h
  let lo ← SRat.lit 0
  let hi ← SRat.lit 8
  let st ← Charged.repeatFor (fun _ (st : SRat × SRat) => do
    let s ← SRat.add st.1 st.2
    let mid ← SRat.mul s halfQ
    let pw ← Charged.repeatFor (fun _ acc => SRat.mul acc acc) P.ks mid
    let below ← SRat.le pw target
    if below then pure (mid, st.2) else pure (st.1, mid)) P.depth (lo, hi)
  pure st.1

/-- Uniform integer offsets in the bin intervals
`I_{v_e} = [⌈(b_e+1) v_e/B⌉, ⌈(b_e+1)(v_e+1)/B⌉)`, by dyadic draws with tolerance
`ζ`; returns the integer point `z`, the product `∏ |I_{v_e}|`, and the cursor. -/
def binOffsets (C : Ctx) (P : OParams) (tape : Coins ℕ) (v : List SNat) (cur : ℕ) :
    Prog (List SRat × SNat × ℕ) := do
  let one ← SNat.lit 1
  Charged.repeatFor (fun k (st : List SRat × SNat × ℕ) => do
    let e ← Operations.get C.free k
    let ve ← Operations.get v k
    let b1 ← SNat.add e.2.2 one
    let t0 ← SNat.mul b1 ve
    let lo ← ceilDivN t0 C.B
    let ve1 ← SNat.add ve one
    let t1 ← SNat.mul b1 ve1
    let hi ← ceilDivN t1 C.B
    let len ← SNat.sub hi lo
    let (off, cur') ← dyadicDraw tape len P.ζ st.2.2
    let zk ← SNat.add lo off
    let zq ← SNat.toRat zk
    let zs ← Operations.push st.1 zq
    let prod ← SNat.mul st.2.1 len
    pure (zs, prod, cur')) C.nFree ([], one, cur)

/-- The average of `N_in` samples of the correction
`α_v 2^{-j D(z)/H} / V_j(v) = α_v 2^{β}`, `β = k_j(v) - j D(z)/H`,
`α_v = B^e |I_v| / M_f`, with `v` from a fresh bin walk for `V_j` and `z`
uniform in `I_v`. -/
def corrAvg (C : Ctx) (P : OParams) (tape : Coins ℕ) (x y : List SNat) (j : ℕ)
    (cur : ℕ) : Prog (SRat × ℕ) := do
  let jS ← SNat.lit j
  let jq ← SNat.toRat jS
  let zero ← SRat.lit 0
  let Mq ← SNat.toRat C.Mf
  let st ← Charged.repeatFor (fun _ (st : SRat × ℕ) => do
    let (v, cur1) ← sampleBin C P tape jq x y st.2
    let kv ← binExp C jq x y v
    let (z, lenProd, cur2) ← binOffsets C P tape v cur1
    let Dz ← penalty C x y z
    let t ← SRat.mul jq Dz
    let u ← SRat.div t C.Hq
    let β ← SRat.sub kv u
    let approx ← pow2Approx P β
    let BeI ← SNat.mul P.Be lenProd
    let BeIq ← SNat.toRat BeI
    let α ← SRat.div BeIq Mq
    let sample ← SRat.mul α approx
    let s ← SRat.add st.1 sample
    pure (s, cur2)) P.N (zero, cur)
  let avg ← SRat.div st.1 P.Nq
  pure (avg, st.2)

/-- **The weight oracle** `ĥ_j(x, y)`: `M_f · ∏_{a<j} R̂_a · T̂`, every call on
fresh bits. -/
def oracle (C : Ctx) (tape : Coins ℕ) (x y : List SNat) (j : ℕ) (ξin θ : SRat)
    (cur : ℕ) : Prog (SRat × ℕ) := do
  let P ← oracleParams C ξin θ
  let one ← SRat.lit 1
  let st ← Charged.repeatFor (fun a (st : SRat × ℕ) => do
    let (r, cur') ← ratioAvg C P tape x y a st.2
    let p ← SRat.mul st.1 r
    pure (p, cur')) j (one, cur)
  let (T, cur') ← corrAvg C P tape x y j st.2
  let Mq ← SNat.toRat C.Mf
  let t ← SRat.mul Mq st.1
  let out ← SRat.mul t T
  pure (out, cur')

/-! ## S8-S10: the paired state space and the implemented Metropolis chain -/

/-- What the chain needs about the small cells: `p`, the cell of each pair
label, the first label of each cell, the small bounds, `ξ`, and the acceptance
bit count `⌈log₂ ξ⁻¹⌉`. -/
structure Chain where
  /-- `p`, the number of pairs. -/
  p : ℕ
  /-- `p`, sealed. -/
  pS : SNat
  /-- Number of small cells. -/
  nsm : ℕ
  /-- `s(i)`, the small cell of pair `i`. -/
  pairCell : List ℕ
  /-- The first pair label of each small cell. -/
  cellFirst : List ℕ
  /-- `b_s` for each small cell. -/
  smallB : List SNat
  /-- `ξ`, the per-action error. -/
  ξ : SRat
  /-- `⌈log₂ ξ⁻¹⌉`. -/
  kAcc : ℕ
  /-- `⌈log₂ ξ⁻¹⌉`, sealed. -/
  kAccS : SNat

/-- The type of a state: a transversal, the defect class `A_il`, or outside
`X`. -/
inductive Kind where
  /-- Every pair singly occupied. -/
  | transversal
  /-- Pair `i` empty, pair `l` full, all others singly occupied. -/
  | defect (i l : ℕ)
  /-- Not in `X`. -/
  | outside

/-- The small-count profile `(x_s, y_s)` of a state: row and column elements
present, per small cell.  A state is `2p` membership bits; element `2i` is the
row element and `2i + 1` the column element of pair `i`. -/
def profile (K : Chain) (S : List Bool) : Prog (List SNat × List SNat) := do
  let z ← SNat.lit 0
  let one ← SNat.lit 1
  let x0 ← Operations.replicate K.nsm z
  let y0 ← Operations.replicate K.nsm z
  Charged.repeatFor (fun i (st : List SNat × List SNat) => do
    let s ← Operations.get K.pairCell i
    let rowIn ← Operations.get S (2 * i)
    let colIn ← Operations.get S (2 * i + 1)
    let x ← if rowIn then do
        let a ← Operations.get st.1 s
        let a' ← SNat.add a one
        Operations.set st.1 s a'
      else pure st.1
    let y ← if colIn then do
        let a ← Operations.get st.2 s
        let a' ← SNat.add a one
        Operations.set st.2 s a'
      else pure st.2
    pure (x, y)) K.p (x0, y0)

/-- Classify a state: counts of empty and full pairs, with the last of each. -/
def kind (K : Chain) (S : List Bool) : Prog Kind := do
  let st ← Charged.repeatFor (fun i (st : (ℕ × ℕ) × (ℕ × ℕ)) => do
    let rowIn ← Operations.get S (2 * i)
    let colIn ← Operations.get S (2 * i + 1)
    if rowIn then
      if colIn then pure (st.1, (st.2.1 + 1, i)) else pure st
    else
      if colIn then pure st else pure ((st.1.1 + 1, i), st.2)) K.p ((0, 0), (0, 0))
  let e0 ← idxEq st.1.1 0
  let f0 ← idxEq st.2.1 0
  if e0 then
    if f0 then pure .transversal else pure .outside
  else do
    let e1 ← idxEq st.1.1 1
    let f1 ← idxEq st.2.1 1
    if e1 then
      if f1 then pure (.defect st.1.2 st.2.2) else pure .outside
    else pure .outside

/-- `k!`, as a rational. -/
def factQ (k : SNat) : Prog SRat := do
  let kI ← SNat.index k
  let one ← SRat.lit 1
  Charged.repeatFor (fun i acc => do
    let iS ← SNat.lit (i + 1)
    let iq ← SNat.toRat iS
    SRat.mul acc iq) kI one

/-- The implemented `λ(S)`: a fresh oracle value `ĥ_a(x, y)` (with
`ξ_in = θ = ξ`), times the exact factor `∏_s x_s! y_s! / b_s!` (`eq:lifts`), times
`w_il` on the defect class `A_il`. -/
def lam (C : Ctx) (K : Chain) (tape : Coins ℕ) (S : List Bool) (k : Kind) (a : ℕ)
    (w : List (List SRat)) (cur : ℕ) : Prog (SRat × ℕ) := do
  let (x, y) ← profile K S
  let (h, cur') ← oracle C tape x y a K.ξ K.ξ cur
  let one ← SRat.lit 1
  let fac ← Charged.repeatFor (fun s acc => do
    let xs ← Operations.get x s
    let ys ← Operations.get y s
    let bs ← Operations.get K.smallB s
    let fx ← factQ xs
    let fy ← factQ ys
    let fb ← factQ bs
    let t ← SRat.mul acc fx
    let t' ← SRat.mul t fy
    SRat.div t' fb) K.nsm one
  let f ← SRat.mul h fac
  match k with
  | .defect i l => do
    let wil ← get2 w i l
    let g ← SRat.mul f wil
    pure (g, cur')
  | _ => pure (f, cur')

/-- The position of the `target`-th element (from `0`, in increasing order) whose
membership bit equals `val`. -/
def nthWith (K : Chain) (S : List Bool) (val : Bool) (target : ℕ) : Prog ℕ := do
  let st ← Charged.repeatFor (fun e (st : ℕ × ℕ) => do
    let bit ← Operations.get S e
    let hitIt := fun (st : ℕ × ℕ) => do
      let isT ← idxEq st.1 target
      if isT then pure (st.1 + 1, e) else pure (st.1 + 1, st.2)
    if bit then
      if val then hitIt st else pure st
    else
      if val then pure st else hitIt st) (2 * K.p) (0, 0)
  pure st.2

/-- Accept with probability `⌊c·2^k⌋/2^k`, `k = ⌈log₂ ξ⁻¹⌉`, by comparing a
`k`-bit uniform integer with the downward-rounded dyadic threshold. -/
def acceptTest (K : Chain) (tape : Coins ℕ) (c : SRat) (cur : ℕ) : Prog (Bool × ℕ) := do
  let pk ← SNat.pow2 K.kAccS
  let pq ← SNat.toRat pk
  let t ← SRat.mul c pq
  let m ← SRat.natFloor t
  let (Y, cur') ← uniformBits tape K.kAcc cur
  let ok ← SNat.lt Y m
  pure (ok, cur')

/-- **S10, one implemented transition of `P_{a,w}`**: hold on one fair bit;
otherwise draw a uniform element of `S` and one of its complement (dyadic draws,
`M = p`, `ζ = ξ`) and propose their exchange; reject a proposal outside `X`
**before** any oracle call; otherwise evaluate `λ(S')` and `λ(S)` by two fresh
oracle calls, clip the ratio at one, and accept by a dyadic threshold. -/
def step (C : Ctx) (K : Chain) (tape : Coins ℕ) (a : ℕ) (w : List (List SRat))
    (S : List Bool) (cur : ℕ) : Prog (List Bool × ℕ) := do
  let (hold, cur1) ← coin tape cur
  if hold then pure (S, cur1) else do
    let (u1, cur2) ← dyadicDraw tape K.pS K.ξ cur1
    let (u2, cur3) ← dyadicDraw tape K.pS K.ξ cur2
    let i1 ← SNat.index u1
    let i2 ← SNat.index u2
    let e1 ← nthWith K S true i1
    let e2 ← nthWith K S false i2
    let S1 ← Operations.set S e1 false
    let S' ← Operations.set S1 e2 true
    let k' ← kind K S'
    match k' with
    | .outside => pure (S, cur3)
    | _ => do
      let k ← kind K S
      let (lNew, cur4) ← lam C K tape S' k' a w cur3
      let (lOld, cur5) ← lam C K tape S k a w cur4
      let r ← SRat.div lNew lOld
      let one ← SRat.lit 1
      let capped ← SRat.le one r
      let (ok, cur6) ← if capped then acceptTest K tape one cur5
        else acceptTest K tape r cur5
      if ok then pure (S', cur6) else pure (S, cur6)

/-- `C(n, k)`, as `∏_{i=1}^{k} (n - k + i)/i`, exact at every prefix. -/
def binom (n k : SNat) : Prog SNat := do
  let kI ← SNat.index k
  let one ← SNat.lit 1
  let nk ← SNat.sub n k
  Charged.repeatFor (fun i acc => do
    let iS ← SNat.lit (i + 1)
    let num ← SNat.add nk iS
    let t ← SNat.mul acc num
    SNat.div t iS) kI one

/-- **A fresh `μ₀` draw**: per small cell, `k_s` uniform in `{0..b_s}` and a
uniform `k_s`-subset of its `b_s` pairs (a dyadic draw of a rank in
`[0, C(b_s, k_s))`, decoded by lexicographic binomial unranking); those pairs use
their row element, the rest their column element. -/
def mu0 (K : Chain) (tape : Coins ℕ) (cur : ℕ) : Prog (List Bool × ℕ) := do
  let S0 ← Operations.replicate (2 * K.p) false
  let one ← SNat.lit 1
  let zero ← SNat.lit 0
  Charged.repeatFor (fun s (st : List Bool × ℕ) => do
    let b ← Operations.get K.smallB s
    let first ← Operations.get K.cellFirst s
    let b1 ← SNat.add b one
    let (k, cur1) ← dyadicDraw tape b1 K.ξ st.2
    let cnt ← binom b k
    let (rank, cur2) ← dyadicDraw tape cnt K.ξ cur1
    let bI ← SNat.index b
    let st' ← Charged.repeatFor (fun t (st' : List Bool × SNat × SNat) => do
      let lbl := first + t
      let remaining ← SNat.lt zero st'.2.1
      if remaining then do
        let tS ← SNat.lit (t + 1)
        let rest ← SNat.sub b tS
        let k1 ← SNat.sub st'.2.1 one
        let c ← binom rest k1
        let incl ← SNat.lt st'.2.2 c
        if incl then do
          let S ← Operations.set st'.1 (2 * lbl) true
          pure (S, k1, st'.2.2)
        else do
          let r ← SNat.sub st'.2.2 c
          let S ← Operations.set st'.1 (2 * lbl + 1) true
          pure (S, st'.2.1, r)
      else do
        let S ← Operations.set st'.1 (2 * lbl + 1) true
        pure (S, st'.2.1, st'.2.2)) bI (st.1, k, rank)
    pure (st'.1, cur2)) K.nsm (S0, cur)

/-! ## S9: one phase of the annealing run -/

/-- The phase parameters of `eq:alg-phase-parameters`. -/
structure Phase where
  /-- `τ`, trace steps per stage. -/
  τ : SNat
  /-- `B_ret`, the restart transition cap. -/
  Bret : SNat
  /-- `B_ret`, as a loop count. -/
  BretN : ℕ
  /-- `N_av`, observed states per phase. -/
  Nav : SNat
  /-- `N_av`, as a loop count. -/
  NavN : ℕ
  /-- `H`, as a loop count. -/
  Hn : ℕ

/-- The restart of one phase: the current state, the stage `a`, trace steps done
in it, transitions used, and whether it finished or aborted. -/
structure Restart where
  /-- Current state. -/
  S : List Bool
  /-- Current stage `a ∈ 1..j`. -/
  stage : ℕ
  /-- Trace steps completed in this stage. -/
  hits : SNat
  /-- Underlying transitions used. -/
  used : SNat
  /-- All stages done. -/
  finished : Bool
  /-- The cap `B_ret` was exceeded. -/
  aborted : Bool
  /-- Tape cursor. -/
  cur : ℕ

/-- **S9a, the capped restart**: from the fresh `μ₀` state, for `a = 1..j` run `τ`
trace steps of `P_{a,w^(a)}`, a trace step ending at the next transversal after
at least one transition; at most `B_ret` transitions in all, and abort if another
is needed.  `j = 0` returns the `μ₀` state. -/
def restart (C : Ctx) (K : Chain) (tape : Coins ℕ) (Ph : Phase)
    (ws : List (List (List SRat))) (j : ℕ) (S0 : List Bool) (cur : ℕ) : Prog Restart := do
  let zero ← SNat.lit 0
  let one ← SNat.lit 1
  let fin0 ← idxEq j 0
  Charged.repeatFor (fun _ (st : Restart) => do
    if st.finished then pure st else
    if st.aborted then pure st else do
      let full ← SNat.le Ph.Bret st.used
      if full then pure { st with aborted := true } else do
        let w ← Operations.get ws st.stage
        let (S', cur') ← step C K tape st.stage w st.S st.cur
        let used ← SNat.add st.used one
        let k ← kind K S'
        match k with
        | .transversal => do
          let hits ← SNat.add st.hits one
          let stageDone ← SNat.eq hits Ph.τ
          if stageDone then do
            let last ← idxEq st.stage j
            pure ⟨S', st.stage + 1, zero, used, last, false, cur'⟩
          else pure ⟨S', st.stage, hits, used, false, false, cur'⟩
        | _ => pure ⟨S', st.stage, st.hits, used, false, false, cur'⟩)
    (Ph.BretN + 1) ⟨S0, 1, zero, zero, fin0, false, cur⟩

/-- The observation tallies: current state, `n_0`, the table `n_il`, `Σ G_j`. -/
structure Obs where
  /-- Current state. -/
  S : List Bool
  /-- `n_0`, transversals observed. -/
  n0 : SNat
  /-- `n_il`, states of `A_il` observed. -/
  nT : List (List SNat)
  /-- `Σ G_j` over observed states. -/
  sumG : SRat
  /-- Tape cursor. -/
  cur : ℕ

/-- Observe one state: increment its type counter; at a transversal add
`G_j = ĥ_{j+1}/ĥ_j` from **two fresh oracle calls** (the factorial factors
cancel); `G_j = 0` off `A`. -/
def observeState (C : Ctx) (K : Chain) (tape : Coins ℕ) (j : ℕ) (st : Obs) : Prog Obs := do
  let k ← kind K st.S
  let one ← SNat.lit 1
  match k with
  | .transversal => do
    let n0 ← SNat.add st.n0 one
    let (x, y) ← profile K st.S
    let (hNext, cur1) ← oracle C tape x y (j + 1) K.ξ K.ξ st.cur
    let (hCur, cur2) ← oracle C tape x y j K.ξ K.ξ cur1
    let g ← SRat.div hNext hCur
    let sg ← SRat.add st.sumG g
    pure ⟨st.S, n0, st.nT, sg, cur2⟩
  | .defect i l => do
    let c ← get2 st.nT i l
    let c' ← SNat.add c one
    let nT ← set2 st.nT i l c'
    pure ⟨st.S, st.n0, nT, st.sumG, st.cur⟩
  | .outside => pure st

/-- **S9b**: from the restart endpoint, `N_av` observed states of `P_{j,w^(j)}`,
the starting state included. -/
def observe (C : Ctx) (K : Chain) (tape : Coins ℕ) (Ph : Phase) (j : ℕ)
    (w : List (List SRat)) (S0 : List Bool) (cur : ℕ) : Prog Obs := do
  let zero ← SNat.lit 0
  let zq ← SRat.lit 0
  let row ← Operations.replicate K.p zero
  let tab ← Operations.replicate K.p row
  let st0 ← observeState C K tape j ⟨S0, zero, tab, zq, cur⟩
  Charged.repeatFor (fun _ (st : Obs) => do
    let (S', cur') ← step C K tape j w st.S st.cur
    observeState C K tape j ⟨S', st.n0, st.nT, st.sumG, cur'⟩) (Ph.NavN - 1) st0

/-- Whether every type count is positive: `n_0 > 0` and `n_il > 0` for all
`i ≠ l`. -/
def allPositive (K : Chain) (o : Obs) : Prog Bool := do
  let zero ← SNat.lit 0
  let ok0 ← SNat.lt zero o.n0
  if ok0 then
    Charged.repeatFor (fun i acc =>
      if acc then
        Charged.repeatFor (fun l acc' =>
          if acc' then do
            let diag ← idxEq i l
            if diag then pure true else do
              let c ← get2 o.nT i l
              SNat.lt zero c
          else pure false) K.p true
      else pure false) K.p true
  else pure false

/-- `eq:alg-multiplier-update`: `w_il ← w_il · n_0 / n_il` for `i ≠ l`. -/
def updateW (K : Chain) (w : List (List SRat)) (o : Obs) : Prog (List (List SRat)) := do
  let n0q ← SNat.toRat o.n0
  Charged.repeatFor (fun i acc =>
    Charged.repeatFor (fun l acc' => do
      let diag ← idxEq i l
      if diag then pure acc' else do
        let wil ← get2 acc' i l
        let nil ← get2 o.nT i l
        let nq ← SNat.toRat nil
        let t ← SRat.mul wil n0q
        let t' ← SRat.div t nq
        set2 acc' i l t') K.p acc) K.p w

/-- The state of an annealing run: stored multiplier tables `w^(0..j)`, the
product of ratio estimates, the abort flag, and the cursor. -/
structure Run where
  /-- `w^(0), …, w^(j)`. -/
  ws : List (List (List SRat))
  /-- `∏ R̂_j` so far. -/
  prod : SRat
  /-- Some phase aborted. -/
  aborted : Bool
  /-- Tape cursor. -/
  cur : ℕ

/-- **Phase `j`** (`algorithm.tex:214-249`): restart, observe, and — only after
the zero-count abort test — `R̂_j = û/p̂_0` and, if `j + 1 < H`, the multiplier
update.  An aborted run does nothing further. -/
def phase (C : Ctx) (K : Chain) (tape : Coins ℕ) (Ph : Phase) (j : ℕ) (st : Run) :
    Prog Run := do
  if st.aborted then pure st else do
    let (S0, cur1) ← mu0 K tape st.cur
    let rs ← restart C K tape Ph st.ws j S0 cur1
    if rs.aborted then pure ⟨st.ws, st.prod, true, rs.cur⟩ else do
      let w ← Operations.get st.ws j
      let o ← observe C K tape Ph j w rs.S rs.cur
      let pos ← allPositive K o
      if pos then do
        let Nq ← SNat.toRat Ph.Nav
        let u ← SRat.div o.sumG Nq
        let n0q ← SNat.toRat o.n0
        let p0 ← SRat.div n0q Nq
        let R ← SRat.div u p0
        let prod ← SRat.mul st.prod R
        let more ← idxLt (j + 1) Ph.Hn
        if more then do
          let w' ← updateW K w o
          let ws ← Operations.push st.ws w'
          pure ⟨ws, prod, false, o.cur⟩
        else pure ⟨st.ws, prod, false, o.cur⟩
      else pure ⟨st.ws, st.prod, true, o.cur⟩

/-- **S11, one annealing run** (`p ≥ 1`): phases `j = 0..H-1`; output
`C(0) ∏_j R̂_j`, or zero after an abort. -/
def annealRun (C : Ctx) (K : Chain) (tape : Coins ℕ) (Ph : Phase)
    (w0 : List (List SRat)) (C0 : SRat) (cur : ℕ) : Prog (SRat × ℕ) := do
  let one ← SRat.lit 1
  let st ← Charged.repeatFor (fun j st => phase C K tape Ph j st) Ph.Hn
    ⟨[w0], one, false, cur⟩
  if st.aborted then do
    let z ← SRat.lit 0
    pure (z, st.cur)
  else do
    let out ← SRat.mul C0 st.prod
    pure (out, st.cur)

/-- **S8, setup for `p ≥ 1`**: pair labels, `eq:alg-phase-parameters`,
`eq:alg-bit-parameters`, the initial multipliers `w^(0)` and `C(0)`. -/
def chainSetup (C : Ctx) (Pm : Params) (pS : SNat) (ε : SRat) :
    Prog (Chain × Phase × List (List SRat) × SRat) := do
  -- pair labels
  let lab ← Charged.repeatFor (fun s (st : List ℕ × List ℕ × List SNat × ℕ) => do
    let e ← Operations.get C.small s
    let bI ← SNat.index e.2.2
    let firsts ← Operations.push st.2.1 st.2.2.2
    let bs ← Operations.push st.2.2.1 e.2.2
    let cells ← Charged.repeatFor (fun _ acc => Operations.push acc s) bI st.1
    pure (cells, firsts, bs, st.2.2.2 + bI)) C.nSmall ([], [], [], 0)
  let (pairCell, cellFirst, smallB, p) := lab
  let one ← SNat.lit 1
  let H1 ← SNat.add Pm.H one
  -- q = W², C_p = p(1 + 8pq²), C_d = 8 + 32pq³, K_obs = 10p⁴(9C_p + 2C_d)
  let q ← SNat.mul Pm.W Pm.W
  let q2 ← SNat.mul q q
  let q3 ← SNat.mul q2 q
  let c8 ← SNat.lit 8
  let p8 ← SNat.mul c8 pS
  let p8q2 ← SNat.mul p8 q2
  let cp1 ← SNat.add one p8q2
  let Cp ← SNat.mul pS cp1
  let c32 ← SNat.lit 32
  let p32 ← SNat.mul c32 pS
  let p32q3 ← SNat.mul p32 q3
  let Cd ← SNat.add c8 p32q3
  let c9 ← SNat.lit 9
  let c2 ← SNat.lit 2
  let t9 ← SNat.mul c9 Cp
  let t2 ← SNat.mul c2 Cd
  let t92 ← SNat.add t9 t2
  let p2 ← SNat.mul pS pS
  let p4 ← SNat.mul p2 p2
  let c10 ← SNat.lit 10
  let p4' ← SNat.mul c10 p4
  let Kobs ← SNat.mul p4' t92
  -- η = ε / (200 (H + 1))
  let c200 ← SNat.lit 200
  let h200 ← SNat.mul c200 H1
  let h200q ← SNat.toRat h200
  let η ← SRat.div ε h200q
  -- τ = 2 K_obs (H + p + K + 5)
  let c5 ← SNat.lit 5
  let s1 ← SNat.add Pm.H pS
  let s2 ← SNat.add s1 Pm.K
  let s3 ← SNat.add s2 c5
  let k2 ← SNat.mul c2 Kobs
  let τ ← SNat.mul k2 s3
  -- B_ret = 2000 p² (H + 1)² τ
  let c2000 ← SNat.lit 2000
  let H1sq ← SNat.mul H1 H1
  let b1 ← SNat.mul c2000 p2
  let b2 ← SNat.mul b1 H1sq
  let Bret ← SNat.mul b2 τ
  let BretN ← SNat.index Bret
  -- N_av = ⌈10⁸ p⁸ K_obs (H + 1) / η²⌉
  let p8' ← SNat.mul p4 p4
  let c1e8 ← SNat.lit 100000000
  let n1 ← SNat.mul c1e8 p8'
  let n2 ← SNat.mul n1 Kobs
  let n3 ← SNat.mul n2 H1
  let n3q ← SNat.toRat n3
  let η2 ← SRat.mul η η
  let navq ← SRat.div n3q η2
  let Nav ← SRat.natCeil navq
  let NavN ← SNat.index Nav
  -- J_* = 100 (H + 1)(B_ret + N_av + p + d + 1), ξ = η / (1000 J_*)
  let c100 ← SNat.lit 100
  let j1 ← SNat.add Bret Nav
  let j2 ← SNat.add j1 pS
  let j3 ← SNat.add j2 Pm.d
  let j4 ← SNat.add j3 one
  let h100 ← SNat.mul c100 H1
  let Jstar ← SNat.mul h100 j4
  let c1000 ← SNat.lit 1000
  let J1000 ← SNat.mul c1000 Jstar
  let Jq ← SNat.toRat J1000
  let ξ ← SRat.div η Jq
  -- ⌈log₂ ξ⁻¹⌉
  let oneQ ← SRat.lit 1
  let invξ ← SRat.div oneQ ξ
  let cξ ← SRat.natCeil invξ
  let kAccS ← clog2 cξ
  let kAcc ← SNat.index kAccS
  let Hn ← SNat.index Pm.H
  -- w^(0)_il = 6 if s(i) = s(l), else 6 (b_{s(i)} + 1)/(b_{s(l)} + 2)
  let six ← SRat.lit 6
  let zeroQ ← SRat.lit 0
  let row ← Operations.replicate p zeroQ
  let tab ← Operations.replicate p row
  let w0 ← Charged.repeatFor (fun i acc =>
    Charged.repeatFor (fun l acc' => do
      let diag ← idxEq i l
      if diag then pure acc' else do
        let si ← Operations.get pairCell i
        let sl ← Operations.get pairCell l
        let same ← idxEq si sl
        if same then set2 acc' i l six else do
          let bi ← Operations.get smallB si
          let bl ← Operations.get smallB sl
          let bi1 ← SNat.add bi one
          let bl2 ← SNat.add bl c2
          let bi1q ← SNat.toRat bi1
          let bl2q ← SNat.toRat bl2
          let t ← SRat.mul six bi1q
          let v ← SRat.div t bl2q
          set2 acc' i l v) p acc) p tab
  -- C(0) = M_f ∏_s (b_s + 1)
  let c0 ← Charged.foldl (fun acc (b : SNat) => do
    let b1' ← SNat.add b one
    SNat.mul acc b1') smallB C.Mf
  let C0 ← SNat.toRat c0
  pure (⟨p, pS, C.nSmall, pairCell, cellFirst, smallB, ξ, kAcc, kAccS⟩,
    ⟨τ, Bret, BretN, Nav, NavN, Hn⟩, w0, C0)

/-- **S7, one run for `p = 0`**: a single oracle call for `h_H(∅) = C(H)` with
relative tolerance `ε/32` and failure probability `1/16`. -/
def zeroRun (C : Ctx) (Hn : ℕ) (ε : SRat) (tape : Coins ℕ) (cur : ℕ) :
    Prog (SRat × ℕ) := do
  let c32 ← SRat.lit 32
  let tol ← SRat.div ε c32
  let fail ← SRat.lit (1 / 16)
  oracle C tape [] [] Hn tol fail cur

/-! ## S12: amplification by the median -/

/-- Insert `x` into an ascending list, after every entry not greater than it. -/
def insertAsc (l : List SRat) (x : SRat) : Prog (List SRat) := do
  let st ← Charged.foldl (fun (st : List SRat × Bool) (y : SRat) => do
    if st.2 then do
      let o ← Operations.push st.1 y
      pure (o, true)
    else do
      let before ← SRat.lt x y
      if before then do
        let o ← Operations.push st.1 x
        let o' ← Operations.push o y
        pure (o', true)
      else do
        let o ← Operations.push st.1 y
        pure (o, false)) l ([], false)
  if st.2 then pure st.1 else Operations.push st.1 x

/-- The order statistic at position `idx` (from `0`). -/
def orderStat (outs : List SRat) (idx : ℕ) : Prog SRat := do
  let sorted ← Charged.foldl (fun acc x => insertAsc acc x) outs []
  Operations.get sorted idx

/-! ## The algorithm -/

/-- **The paper's algorithm** (Theorem `thm:main`), run on the instance `I` and
the accuracy parameters `ε, δ`, reading fair bits from `tape` from position `0`
on.

S0 reads the input and computes `L`.  S1 tests feasibility (equal totals, then
maximum flow); an infeasible input returns `0` without reading a coin.  S2–S4
tighten the instance, compute `eq:parameters`, and build the forest, once.
`s = ⌈log₂ δ⁻¹⌉` and `R = 10 s + 1`.  The `p = 0` / `p ≥ 1` dispatch is decided
once, before any `p`-dependent parameter.  Then `R` independent runs on
consecutive stretches of the tape, and their median, the order statistic at
`5 s = (R - 1)/2`. -/
def fpras (I : Instance) (ε δ : ℚ) (tape : Coins ℕ) : Prog ℚ := do
  let L ← inputLen I ε δ
  let r ← readList (List.ofFn I.r)
  let c ← readList (List.ofFn I.c)
  let b ← readMatrix (List.ofFn fun i => List.ofFn fun j => I.b i j)
  let feas ← feasible I.m I.n r c b
  if feas then do
    let T ← tighten I.m I.n r c b
    let εS ← SRat.lit ε
    let Pm ← params I.m I.n L εS
    let C ← buildCtx I.m I.n T Pm
    let zero ← SNat.lit 0
    let pS ← Charged.foldl (fun acc (e : Entry) => SNat.add acc e.2.2) C.small zero
    let δS ← SRat.lit δ
    let oneQ ← SRat.lit 1
    let invδ ← SRat.div oneQ δS
    let cδ ← SRat.natCeil invδ
    let s ← clog2 cδ
    let c10 ← SNat.lit 10
    let s10 ← SNat.mul c10 s
    let one ← SNat.lit 1
    let R ← SNat.add s10 one
    let RI ← SNat.index R
    let c5 ← SNat.lit 5
    let mid ← SNat.mul c5 s
    let midI ← SNat.index mid
    let pZero ← SNat.eq pS zero
    if pZero then do
      let Hn ← SNat.index Pm.H
      let st ← Charged.repeatFor (fun _ (st : List SRat × ℕ) => do
        let (z, cur) ← zeroRun C Hn εS tape st.2
        let outs ← Operations.push st.1 z
        pure (outs, cur)) RI ([], 0)
      let med ← orderStat st.1 midI
      SRat.output med
    else do
      let (K, Ph, w0, C0) ← chainSetup C Pm pS εS
      let st ← Charged.repeatFor (fun _ (st : List SRat × ℕ) => do
        let (z, cur) ← annealRun C K tape Ph w0 C0 st.2
        let outs ← Operations.push st.1 z
        pure (outs, cur)) RI ([], 0)
      let med ← orderStat st.1 midI
      SRat.output med
  else do
    let z ← SRat.lit 0
    SRat.output z

end Cellcounting.Program

#programSeal Cellcounting.Program
#executableModule Cellcounting.Model.Program
#surplusIn Cellcounting.Model.Program from Cellcounting.Program.fpras
