import Cellcounting.Analysis.HyperbolicForm

/-!
# The omission property of a set weight (`signatures.tex:79-90`)

Vocabulary for `lem:binary-contraction` and `lem:binary-signatures`.  A weight
`φ : Finset ℕ → ℝ` is considered on the `k`-subsets of a finite ground set `Γ`.

* `omMat φ P` is the two-omission matrix `(φ(P \ {x, y}))_{x ≠ y ∈ P}` (zero diagonal)
  at a display `P`;
* `OmitSig φ Γ k` is the omission property with positivity: `φ` is positive on the
  `k`-subsets of `Γ`, and at every display `P ⊆ Γ` of size `k + 2` the matrix
  `omMat φ P` has at most one positive eigenvalue (`Hyp`);
* `pairSum φ α β` sums the pair `{α, β}` at occupancy one:
  `U ↦ φ(U ∪ {α}) + φ(U ∪ {β})`.

`hyp_comp_inj` says that a principal submatrix of a `Hyp` matrix is `Hyp` ("fixing
inclusions restricts the quadratic test to a principal submatrix").
-/

namespace Cellcounting.Analysis

open Finset

/-- INTERNAL: the two-omission matrix `(φ(P \ {x, y}))_{x ≠ y ∈ P}`, zero on the diagonal.
TEXLINE: sections/signatures.tex:79-90 -/
noncomputable def omMat (φ : Finset ℕ → ℝ) (P : Finset ℕ) : P → P → ℝ :=
  fun x y => if x = y then 0 else φ (((P.erase x).erase y))

/-- INTERNAL: the omission property of `φ` on the `k`-subsets of `Γ`, with positivity:
`φ > 0` on every `k`-subset of `Γ`, and for every display `P ⊆ Γ` with `|P| = k + 2`
the two-omission matrix has at most one positive eigenvalue.
TEXLINE: sections/signatures.tex:79-90 -/
def OmitSig (φ : Finset ℕ → ℝ) (Γ : Finset ℕ) (k : ℕ) : Prop :=
  (∀ S ⊆ Γ, S.card = k → 0 < φ S) ∧ ∀ P ⊆ Γ, P.card = k + 2 → Hyp (omMat φ P)

/-- INTERNAL: summing the pair `{α, β}` at occupancy one.
TEXLINE: sections/signatures.tex:156-162 -/
noncomputable def pairSum (φ : Finset ℕ → ℝ) (α β : ℕ) : Finset ℕ → ℝ :=
  fun U => φ (insert α U) + φ (insert β U)

/-- INTERNAL: a principal submatrix (along an injection) of a `Hyp` matrix is `Hyp`.
TEXLINE: sections/signatures.tex:116-119 -/
theorem hyp_comp_inj {ι κ : Type*} [Fintype ι] [Fintype κ] {Q : ι → ι → ℝ} (hQ : Hyp Q)
    (e : κ → ι) (he : Function.Injective e) : Hyp (fun a b => Q (e a) (e b)) := by
  classical
  set ext : (κ → ℝ) → ι → ℝ := fun u i => if h : ∃ a, e a = i then u h.choose else 0
  have hext : ∀ u a, ext u (e a) = u a := by
    intro u a
    have h : ∃ a', e a' = e a := ⟨a, rfl⟩
    simp only [ext, dif_pos h]
    rw [he h.choose_spec]
  have hzero : ∀ u i, i ∉ Set.range e → ext u i = 0 := by
    intro u i hi
    simp only [ext]
    rw [dif_neg (by simpa [Set.mem_range] using hi)]
  have hqf : ∀ u w, qf Q (ext u) (ext w) = qf (fun a b => Q (e a) (e b)) u w := by
    intro u w
    unfold qf
    symm
    refine Fintype.sum_of_injective e he _ _ ?_ ?_
    · intro i hi
      exact Finset.sum_eq_zero fun h _ => by rw [hzero u i hi]; ring
    · intro a
      refine Fintype.sum_of_injective e he _ _ ?_ ?_
      · intro h hh; rw [hzero w h hh]; ring
      · intro b; rw [hext, hext]
  intro u w hu
  rw [← hqf] at hu ⊢
  rw [← hqf, ← hqf]
  exact hQ _ _ hu

end Cellcounting.Analysis
