import Cellcounting.Model.Program
import Cellcounting.Interface.Encoding
import Mathlib.Tactic

/-!
# Flows on a capacity matrix

The vocabulary in which the feasibility test S1 (`Program.feasible`,
`sections/scales.tex:7-22`) is read.  Vertices are `0, …, V - 1`, the source is
`0` and the sink is `V - 1`.

* `capOf M u v` is entry `(u, v)` of a program matrix, `0` outside it.
* `IsFlow V cap f`: `f ≤ cap` arcwise and flow is conserved at every vertex other
  than the source and the sink.  Flows are natural-number valued, so this is the
  integral flow the paper speaks of.
* `flowValue V f`: net flow out of the source, as an integer.
* `netCap m n r c b`: the paper's network — source `0`, row `i` is vertex `1 + i`,
  column `j` is vertex `1 + m + j`, sink `m + n + 1`; source-to-row arcs carry `r i`,
  row-to-column arcs `b i j`, column-to-sink arcs `c j`.  This is the indexing of
  `Program.network`.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Cellcounting.Model.Operations

/-- INTERNAL: entry `(u, v)` of a capacity or residual matrix of the program, `0`
outside it.
TEXLINE: sections/scales.tex:7-12 -/
noncomputable def capOf (M : List (List SNat)) (u v : ℕ) : ℕ :=
  ((M.getD u []).getD v default).get

/-- INTERNAL: `f` is an integral flow on the vertices `0, …, V - 1` from the source
`0` to the sink `V - 1`, within the capacities `cap`.
TEXLINE: sections/scales.tex:7-12 -/
structure IsFlow (V : ℕ) (cap : ℕ → ℕ → ℕ) (f : ℕ → ℕ → ℕ) : Prop where
  le_cap : ∀ u v, f u v ≤ cap u v
  conserve : ∀ v, 0 < v → v + 1 < V →
    ∑ u ∈ Finset.range V, f u v = ∑ w ∈ Finset.range V, f v w

/-- INTERNAL: the value of a flow, the net flow out of the source.
TEXLINE: sections/scales.tex:11 -/
def flowValue (V : ℕ) (f : ℕ → ℕ → ℕ) : ℤ :=
  ∑ v ∈ Finset.range V, (f 0 v : ℤ) - ∑ u ∈ Finset.range V, (f u 0 : ℤ)

/-- INTERNAL: the capacities of the feasibility network on `m + n + 2` vertices, in the
vertex numbering of `Program.network`.
TEXLINE: sections/scales.tex:8-11 -/
def netCap (m n : ℕ) (r c : ℕ → ℕ) (b : ℕ → ℕ → ℕ) (u v : ℕ) : ℕ :=
  if u = 0 ∧ 1 ≤ v ∧ v ≤ m then r (v - 1)
  else if 1 ≤ u ∧ u ≤ m ∧ m + 1 ≤ v ∧ v ≤ m + n then b (u - 1) (v - 1 - m)
  else if m + 1 ≤ u ∧ u ≤ m + n ∧ v = m + n + 1 then c (u - 1 - m)
  else 0

end Cellcounting.Analysis
