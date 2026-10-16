import Cellcounting.Interface.Pseudocode
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The assignment boxes behind `h_j` and `C(j)`

The finite index sets of `eq:hj` and `eq:Cj` (`scales.tex:265-282`) over the
pseudocode's tightened data, and the names the contamination argument uses for
one *assignment* `(x, z)`: a balanced small profile `x` (with `y_s = b_s - x_s`)
and a free vector `z`.

* `freeBox` is `∏_{e ∈ F} {0, …, b_e}`, `smallBox` is `∏_s {0, …, b_s}`;
* `asgBox = smallBox × freeBox` is the set of assignments summed in `C(j)`;
* `asgPen p` is the penalty `D(x, y, z)` of the assignment, `asgTree p t` its
  tree value `z_t` (the leaf-elimination completion), and
* `treeMarg t k` is the tree marginal `a_t(k)` of `eq:tree-marginal-definition`
  (`integer-signatures.tex:420-430`): the `2^{-D}`-mass of the assignments whose
  tree value at `t` is `k`.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: the free box `∏_{e ∈ F} {0, …, b_e}` of `eq:hj`, indexed by the
free-cell positions of `forest`.
TEXLINE: sections/scales.tex:265-270 -/
noncomputable def freeBox (I : Instance) (ε δ : ℚ) : Finset (Fin (nFree I ε δ) → ℕ) :=
  Fintype.piFinset fun k => Finset.range ((freeAt I ε δ k).2.2 + 1)

/-- INTERNAL: a vector on `Fin N`, read as the `ℕ → ℚ` the penalty takes
(zero past `N`, a position the penalty never reads). -/
def extendQ {N : ℕ} (z : Fin N → ℕ) : ℕ → ℚ := fun k => if h : k < N then (z ⟨k, h⟩ : ℚ) else 0

/-- INTERNAL: a vector on `Fin N`, read as an `ℕ → ℕ` (zero past `N`). -/
def extendN {N : ℕ} (x : Fin N → ℕ) : ℕ → ℕ := fun k => if h : k < N then x ⟨k, h⟩ else 0

/-- INTERNAL: the balanced small profiles, parametrised by `x ∈ ∏_s {0..b_s}`
(`y_s = b_s - x_s`).
TEXLINE: sections/scales.tex:279-282 -/
noncomputable def smallBox (I : Instance) (ε δ : ℚ) : Finset (Fin (nSmall I ε δ) → ℕ) :=
  Fintype.piFinset fun s => Finset.range (smallB I ε δ s + 1)

/-- INTERNAL: the assignments `(x, z)` summed in `C(j)`: balanced small profiles
times the free box.
TEXLINE: sections/scales.tex:279-282 -/
noncomputable def asgBox (I : Instance) (ε δ : ℚ) :
    Finset ((Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) :=
  smallBox I ε δ ×ˢ freeBox I ε δ

/-- INTERNAL: the column view `y_s = b_s - x_s` of a balanced small profile. -/
noncomputable def balY (I : Instance) (ε δ : ℚ) (x : Fin (nSmall I ε δ) → ℕ) : ℕ → ℕ :=
  fun s => smallB I ε δ s - extendN x s

/-- INTERNAL: the penalty `D(x, y, z)` of an assignment.
TEXLINE: sections/scales.tex:113-126 -/
noncomputable def asgPen (I : Instance) (ε δ : ℚ)
    (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) : ℚ :=
  penalty I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2)

/-- INTERNAL: the tree values `z_t` of an assignment (the unique nonroot
completion, `lem:forest`).
TEXLINE: sections/scales.tex:109-113 -/
noncomputable def asgTree (I : Instance) (ε δ : ℚ)
    (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) : ℕ → ℚ :=
  (treeValues I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2)).2

/-- INTERNAL: the tree marginal `a_t(k)` of `eq:tree-marginal-definition`.
TEXLINE: sections/integer-signatures.tex:420-430 -/
noncomputable def treeMarg (I : Instance) (ε δ : ℚ) (t : ℕ) (k : ℤ) : ℝ :=
  ∑ p ∈ (asgBox I ε δ).filter (fun p => asgTree I ε δ p t = k),
    (2 : ℝ) ^ (-(asgPen I ε δ p : ℝ))

end Cellcounting.Analysis
