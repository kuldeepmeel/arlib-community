import Cellcounting.Analysis.ContaminationBoxes
import Cellcounting.Analysis.EdgeMarginal
import Cellcounting.Analysis.TighteningCount

/-!
# Log-concave tree marginals (`lem:tree-marginal`)

`integer-signatures.tex:432-470`: for a tree cell `t`, the marginal
`a_t(k) = Σ_{z_t = k} 2^{-D}` of `C(H)` interpolates log-concavely between any two
positive values (`tree_marginal_interp`).

The proof is the paper's:

* `tmModel α` is the softened table model `eq:laminar-table-model` at `j = H` as an
  `EdgeModel` (`EdgeMarginal.lean`): small and free cells on `[0, b_s]`, tree cells
  on an interval `[-N, N]` containing every completion, vertex factors
  `α^{|L_v - κ_v|}` at nonroot vertices and `2^{-A |L_v - κ_v|}` at roots, and the
  unary tree factors `2^{-A dist(z_t, [0, b_t]) / b_t}`.  For `0 < α < 1` its
  marginal `a_{t;α}` is positive on `[-N, N]` and satisfies
  `a(k)² ≥ a(k-1) a(k+1)` (`EdgeModel.marg_pos`, `EdgeModel.marg_logconcave`, which
  carry the integer-signature argument), hence the global interpolation
  (`logconcave_rpow_interp`).
* At `α = 0` the surviving tables are exactly the assignments with their
  leaf-elimination completion, with weight `2^{-D}` (`tm_treeMarg_eq_marg`), and
  `α ↦ a_{t;α}(k)` is continuous, so the interpolation passes to the limit.

The tree interval is taken large enough to contain every completion directly,
instead of the paper's `[-10 d b_t, 10 d b_t]` from `lem:forest`; nothing else
depends on its size.  The hypothesis `0 < ε` is not used.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: a sequence positive on `[v, w]` with `a(j-1) a(j+1) ≤ a(j)²` inside lies above the weighted geometric chord (successive log-differences are nonincreasing).
TEXLINE: sections/integer-signatures.tex:462-466 -/
theorem logconcave_rpow_interp (a : ℤ → ℝ) (v k w : ℤ) (hvk : v < k) (hkw : k < w)
    (hpos : ∀ j, v ≤ j → j ≤ w → 0 < a j)
    (hlc : ∀ j, v < j → j < w → a (j - 1) * a (j + 1) ≤ a j ^ 2) :
    a v ^ (((w - k : ℤ) : ℝ) / ((w - v : ℤ) : ℝ)) *
      a w ^ (((k - v : ℤ) : ℝ) / ((w - v : ℤ) : ℝ)) ≤ a k := by
  set g : ℤ → ℝ := fun j => Real.log (a j) with hg
  set d : ℤ → ℝ := fun j => g (j + 1) - g j with hd
  have hloc : ∀ j, v < j → j < w → d j ≤ d (j - 1) := by
    intro j h1 h2
    have ha := hpos (j - 1) (by omega) (by omega)
    have hb := hpos (j + 1) (by omega) (by omega)
    have hc := hpos j (by omega) (by omega)
    have := Real.log_le_log (mul_pos ha hb) (hlc j h1 h2)
    rw [Real.log_mul ha.ne' hb.ne', Real.log_pow] at this
    simp only [hd, hg, sub_add_cancel]
    push_cast at this
    linarith
  have hM : ∀ n : ℕ, ∀ i, v ≤ i → i + n < w → d (i + n) ≤ d i := by
    intro n
    induction n with
    | zero => intro i _ _; simp
    | succ n ih =>
      intro i h1 h2
      have := hloc (i + (n + 1 : ℕ)) (by push_cast; omega) h2
      have e : i + ((n + 1 : ℕ) : ℤ) - 1 = i + n := by push_cast; ring
      rw [e] at this
      exact this.trans (ih i h1 (by push_cast at h2 ⊢; omega))
  set D := d (k - 1) with hD
  have hL : ∀ n : ℕ, (n : ℤ) ≤ k - v → (n : ℝ) * D ≤ g k - g (k - n) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro h
      have h1 := ih (by omega)
      have h2 := hM n (k - (n + 1 : ℕ)) (by push_cast; omega) (by push_cast; omega)
      have e : k - ((n + 1 : ℕ) : ℤ) + n = k - 1 := by push_cast; ring
      rw [e] at h2
      have e2 : g k - g (k - ((n + 1 : ℕ) : ℤ)) =
          (g k - g (k - n)) + d (k - ((n + 1 : ℕ) : ℤ)) := by
        simp only [hd]; push_cast; ring_nf
      rw [e2]; push_cast at h2 ⊢; linarith
  have hR : ∀ n : ℕ, (n : ℤ) ≤ w - k → g (k + n) - g k ≤ (n : ℝ) * D := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro h
      have h1 := ih (by omega)
      have h2 := hM (n + 1) (k - 1) (by omega) (by push_cast; omega)
      have e : k - 1 + ((n + 1 : ℕ) : ℤ) = k + n := by push_cast; ring
      rw [e] at h2
      have e2 : g (k + ((n + 1 : ℕ) : ℤ)) - g k = (g (k + n) - g k) + d (k + n) := by
        simp only [hd]; push_cast; ring_nf
      rw [e2]; push_cast; linarith
  have hL' := hL (k - v).toNat (by omega)
  have hR' := hR (w - k).toNat (by omega)
  have c1 : (((k - v).toNat : ℤ) : ℝ) = ((k - v : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg (by omega)]
  have c2 : (((w - k).toNat : ℤ) : ℝ) = ((w - k : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg (by omega)]
  have e1 : k - ((k - v).toNat : ℤ) = v := by omega
  have e2 : k + ((w - k).toNat : ℤ) = w := by omega
  rw [e1] at hL'; rw [e2] at hR'
  rw [show ((k - v).toNat : ℝ) = (((k - v).toNat : ℤ) : ℝ) by norm_cast, c1] at hL'
  rw [show ((w - k).toNat : ℝ) = (((w - k).toNat : ℤ) : ℝ) by norm_cast, c2] at hR'
  have hkv : (0 : ℝ) < ((k - v : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < k - v)
  have hwk : (0 : ℝ) < ((w - k : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < w - k)
  have hwv : ((w - v : ℤ) : ℝ) = ((w - k : ℤ) : ℝ) + ((k - v : ℤ) : ℝ) := by push_cast; ring
  have key : ((w - k : ℤ) : ℝ) * g v + ((k - v : ℤ) : ℝ) * g w ≤ ((w - v : ℤ) : ℝ) * g k := by
    have := mul_le_mul_of_nonneg_left hL' hwk.le
    have := mul_le_mul_of_nonneg_left hR' hkv.le
    rw [hwv]; nlinarith
  have hav := hpos v le_rfl (by omega)
  have haw := hpos w (by omega) le_rfl
  have hak := hpos k (by omega) (by omega)
  rw [Real.rpow_def_of_pos hav, Real.rpow_def_of_pos haw, ← Real.exp_add,
    ← Real.exp_log hak]
  apply Real.exp_le_exp.2
  have hwv0 : (0 : ℝ) < ((w - v : ℤ) : ℝ) := by rw [hwv]; linarith
  rw [← div_le_iff₀' hwv0] at key
  calc Real.log (a v) * (((w - k : ℤ) : ℝ) / ((w - v : ℤ) : ℝ)) +
        Real.log (a w) * (((k - v : ℤ) : ℝ) / ((w - v : ℤ) : ℝ))
      = (((w - k : ℤ) : ℝ) * g v + ((k - v : ℤ) : ℝ) * g w) / ((w - v : ℤ) : ℝ) := by
        simp only [hg]; ring
    _ ≤ g k := key


open Pseudocode Finset

section treeModel

variable (I : Instance) (ε δ : ℚ)

/-- INTERNAL: the retained cells of the softened table: small, free and tree cells.
TEXLINE: sections/integer-signatures.tex:345-360 -/
abbrev TmCell := Fin (nSmall I ε δ) ⊕ Fin (nFree I ε δ) ⊕ Fin (forest I ε δ).tree.length

/-- INTERNAL: the `(row, column, bound)` entry of a retained cell. -/
noncomputable def tmEntry : TmCell I ε δ → Entry
  | .inl s => smallAt I ε δ s
  | .inr (.inl f) => freeAt I ε δ f
  | .inr (.inr t) => treeAt I ε δ t

variable {I ε δ}

/-- INTERNAL: every cell of the model is retained. -/
theorem tmEntry_mem (c : TmCell I ε δ) : tmEntry I ε δ c ∈ retained I := by
  rcases c with s | f | t
  · exact smallAt_mem_retained I s.2
  · exact freeAt_mem_retained I f.2
  · exact treeAt_mem_retained I t.2

/-- INTERNAL: row and column of a cell are in range. -/
theorem tmEntry_lt (c : TmCell I ε δ) : (tmEntry I ε δ c).1 < I.m ∧ (tmEntry I ε δ c).2.1 < I.n :=
  mem_retained (tmEntry_mem c)

/-- INTERNAL: retained cells have positive width. -/
theorem tmEntry_pos (c : TmCell I ε δ) : 0 < (tmEntry I ε δ c).2.2 := by
  obtain ⟨i, j, he, hpos⟩ := mem_retained_iff I (tmEntry_mem c)
  rw [he]; exact hpos

variable (I ε δ)

/-- INTERNAL: the tightened margin of a vertex, as an integer. -/
noncomputable def tmMargZ (v : ℕ) : ℤ := if v < I.m then (tRow I v : ℤ) else (tCol I (v - I.m) : ℤ)

/-- INTERNAL: `margin` is the cast of `tmMargZ`. -/
theorem tm_margin_eq_margZ (v : ℕ) : margin I v = (tmMargZ I v : ℚ) := by
  unfold margin tmMargZ; split_ifs <;> simp

/-- INTERNAL: the row vertex of a cell, in `Fin (m + n)`. -/
noncomputable def tmRow (c : TmCell I ε δ) : Fin (I.m + I.n) :=
  ⟨(tmEntry I ε δ c).1, by have := (tmEntry_lt c).1; omega⟩

/-- INTERNAL: the column vertex `m + j` of a cell, in `Fin (m + n)`. -/
noncomputable def tmCol (c : TmCell I ε δ) : Fin (I.m + I.n) :=
  ⟨I.m + (tmEntry I ε δ c).2.1, by have := (tmEntry_lt c).2; omega⟩

/-- INTERNAL: the base of the vertex factor: `2^{-A}` at a root, `α` at a nonroot vertex. -/
noncomputable def tmVBase (α : ℝ) (v : ℕ) : ℝ :=
  if v ∈ roots I ε δ then (2 : ℝ) ^ (-(AParam I ε δ : ℝ)) else α

/-- INTERNAL: the vertex factor `base^{|L_v - κ_v|}` of `eq:laminar-table-model` at `j = H`.
TEXLINE: sections/integer-signatures.tex:370-380 -/
noncomputable def tmVf (α : ℝ) (v : ℕ) (s : ℤ) : ℝ := tmVBase I ε δ α v ^ (|s - tmMargZ I v|).toNat

/-- INTERNAL: a tree interval `[-N, N]` strictly containing every completion `z_t` of a box assignment (replaces the paper's `[-10 d b_t, 10 d b_t]` from `lem:forest`). -/
noncomputable def tmBound : ℤ :=
  ⌈∑ p ∈ asgBox I ε δ, ∑ t ∈ range (forest I ε δ).tree.length, |asgTree I ε δ p t|⌉ + 1

/-- INTERNAL: lower ends of the physical intervals: `0` for small and free cells, `-N` for tree cells. -/
noncomputable def tmLo : TmCell I ε δ → ℤ
  | .inr (.inr _) => -tmBound I ε δ
  | _ => 0

/-- INTERNAL: upper ends of the physical intervals: `b_s` for small and free cells, `N` for tree cells. -/
noncomputable def tmHi : TmCell I ε δ → ℤ
  | .inr (.inr _) => tmBound I ε δ
  | c => (tmEntry I ε δ c).2.2

/-- INTERNAL: the unary tree factor `2^{-A dist(s, [0, b_t]) / b_t}`. -/
noncomputable def tmTreePsi (t : ℕ) (s : ℤ) : ℝ :=
  (2 : ℝ) ^ (-(((AParam I ε δ : ℚ) * (boxDist (s : ℚ) ((treeAt I ε δ t).2.2 : ℚ) /
    ((treeAt I ε δ t).2.2 : ℚ)) : ℚ) : ℝ))

/-- INTERNAL: the cell factors: `1` on small and free cells, `tmTreePsi` on tree cells. -/
noncomputable def tmPsi : TmCell I ε δ → ℤ → ℝ
  | .inr (.inr t) => tmTreePsi I ε δ t
  | _ => fun _ => 1

/-- INTERNAL: the `α`-softened table model `eq:laminar-table-model` at `j = H`, as an `EdgeModel`.
TEXLINE: sections/integer-signatures.tex:370-385 -/
noncomputable def tmModel (α : ℝ) : EdgeModel (TmCell I ε δ) (Fin (I.m + I.n)) (Fin (I.m + I.n)) where
  row := tmRow I ε δ
  col := tmCol I ε δ
  lo := tmLo I ε δ
  hi := tmHi I ε δ
  φR := fun r s => if (r : ℕ) < I.m then tmVf I ε δ α r s else 1
  φK := fun r s => if I.m ≤ (r : ℕ) then tmVf I ε δ α r s else 1
  ψ := tmPsi I ε δ

/-! ### factor facts -/

/-- INTERNAL: `c^{|s - κ|}` is log-concave in `s` for `0 < c ≤ 1`. -/
theorem tm_pow_abs_lc {c : ℝ} (h0 : 0 < c) (h1 : c ≤ 1) (κ s : ℤ) :
    c ^ (|s - 1 - κ|).toNat * c ^ (|s + 1 - κ|).toNat ≤ (c ^ (|s - κ|).toNat) ^ 2 := by
  rw [← pow_add, ← pow_mul]
  apply pow_le_pow_of_le_one h0.le h1
  rcases le_total 0 (s - κ) with h | h
  · rcases eq_or_lt_of_le h with h' | h'
    · rw [abs_of_nonpos (by omega : s - 1 - κ ≤ 0), abs_of_nonneg (by omega : 0 ≤ s + 1 - κ),
        abs_of_nonneg h]; omega
    · rw [abs_of_nonneg (by omega : 0 ≤ s - 1 - κ), abs_of_nonneg (by omega : 0 ≤ s + 1 - κ),
        abs_of_nonneg h]; omega
  · rw [abs_of_nonpos (by omega : s - 1 - κ ≤ 0), abs_of_nonpos h]
    rcases le_total 0 (s + 1 - κ) with h2 | h2
    · rw [abs_of_nonneg h2]; omega
    · rw [abs_of_nonpos h2]; omega

/-- INTERNAL: midpoint convexity of `dist(·, [0, b])`. -/
theorem tm_boxDist_convex (s b : ℚ) (hb : 0 ≤ b) :
    2 * boxDist s b ≤ boxDist (s - 1) b + boxDist (s + 1) b := by
  unfold boxDist
  split_ifs <;> linarith

/-- INTERNAL: positivity of the vertex base for `α > 0`. -/
theorem tmVBase_pos {α : ℝ} (hα : 0 < α) (v : ℕ) : 0 < tmVBase I ε δ α v := by
  unfold tmVBase; split_ifs
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · exact hα

/-- INTERNAL: the vertex base is at most one for `α ≤ 1`. -/
theorem tmVBase_le_one {α : ℝ} (hα : α ≤ 1) (v : ℕ) : tmVBase I ε δ α v ≤ 1 := by
  unfold tmVBase; split_ifs
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp)
  · exact hα

/-- INTERNAL: positivity of the tree factor. -/
theorem tmTreePsi_pos (t : ℕ) (s : ℤ) : 0 < tmTreePsi I ε δ t s :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- INTERNAL: log-concavity of the tree factor. -/
theorem tmTreePsi_lc (t : ℕ) (s : ℤ) :
    tmTreePsi I ε δ t (s - 1) * tmTreePsi I ε δ t (s + 1) ≤ tmTreePsi I ε δ t s ^ 2 := by
  unfold tmTreePsi
  rw [← Real.rpow_add (by norm_num), sq, ← Real.rpow_add (by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hb : (0 : ℚ) ≤ ((treeAt I ε δ t).2.2 : ℚ) := by positivity
  have hc := tm_boxDist_convex (s : ℚ) _ hb
  have hA : (0 : ℚ) ≤ (AParam I ε δ : ℚ) := by positivity
  have key : (AParam I ε δ : ℚ) * (boxDist (s : ℚ) ((treeAt I ε δ t).2.2 : ℚ) /
      ((treeAt I ε δ t).2.2 : ℚ)) * 2 ≤
      (AParam I ε δ : ℚ) * (boxDist ((s - 1 : ℤ) : ℚ) ((treeAt I ε δ t).2.2 : ℚ) /
        ((treeAt I ε δ t).2.2 : ℚ)) +
      (AParam I ε δ : ℚ) * (boxDist ((s + 1 : ℤ) : ℚ) ((treeAt I ε δ t).2.2 : ℚ) /
        ((treeAt I ε δ t).2.2 : ℚ)) := by
    push_cast
    rw [← mul_add, mul_assoc, ← add_div]
    apply mul_le_mul_of_nonneg_left _ hA
    rw [mul_comm, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hb
  have key' := (Rat.cast_le (K := ℝ)).2 key
  push_cast at key' ⊢
  linarith

/-- INTERNAL: `1 ≤ N`. -/
theorem tmBound_pos : 1 ≤ tmBound I ε δ := by
  unfold tmBound
  have : (0 : ℚ) ≤ ∑ p ∈ asgBox I ε δ, ∑ t ∈ range (forest I ε δ).tree.length,
      |asgTree I ε δ p t| := by positivity
  have := Int.ceil_nonneg this
  omega

/-- INTERNAL: for `0 < α ≤ 1` the model has positive log-concave factors and positive widths.
TEXLINE: sections/integer-signatures.tex:380-385 -/
theorem tmModel_hyps {α : ℝ} (h0 : 0 < α) (h1 : α ≤ 1) : (tmModel I ε δ α).Hyps where
  width c := by
    rcases c with s | f | t
    · show (0 : ℤ) < ((tmEntry I ε δ (Sum.inl s)).2.2 : ℤ)
      exact_mod_cast tmEntry_pos (Sum.inl s)
    · show (0 : ℤ) < ((tmEntry I ε δ (Sum.inr (Sum.inl f))).2.2 : ℤ)
      exact_mod_cast tmEntry_pos (Sum.inr (Sum.inl f))
    · show -tmBound I ε δ < tmBound I ε δ
      have := tmBound_pos I ε δ; omega
  φR_pos r s := by
    simp only [tmModel]; split_ifs
    · exact pow_pos (tmVBase_pos I ε δ h0 _) _
    · exact one_pos
  φK_pos r s := by
    simp only [tmModel]; split_ifs
    · exact pow_pos (tmVBase_pos I ε δ h0 _) _
    · exact one_pos
  ψ_pos c s := by
    rcases c with s | f | t
    · exact one_pos
    · exact one_pos
    · exact tmTreePsi_pos I ε δ _ _
  φR_lc r s := by
    simp only [tmModel]; split_ifs
    · exact tm_pow_abs_lc (tmVBase_pos I ε δ h0 _) (tmVBase_le_one I ε δ h1 _) _ _
    · norm_num
  φK_lc r s := by
    simp only [tmModel]; split_ifs
    · exact tm_pow_abs_lc (tmVBase_pos I ε δ h0 _) (tmVBase_le_one I ε δ h1 _) _ _
    · norm_num
  ψ_lc c s := by
    rcases c with s | f | t
    · show (1 : ℝ) * 1 ≤ 1 ^ 2; norm_num
    · show (1 : ℝ) * 1 ≤ 1 ^ 2; norm_num
    · exact tmTreePsi_lc I ε δ _ _


/-! ### loads -/

/-- INTERNAL: the physical line sum of vertex `v` in a table. -/
noncomputable def tmLoad (X : TmCell I ε δ → ℤ) (v : ℕ) : ℤ :=
  ∑ c, ((if (tmEntry I ε δ c).1 = v then X c else 0) +
    (if I.m + (tmEntry I ε δ c).2.1 = v then X c else 0))

/-- INTERNAL: the row group sum of a row vertex is its line sum. -/
theorem tm_rowSum_eq (X : TmCell I ε δ → ℤ) (r : Fin (I.m + I.n)) (hr : (r : ℕ) < I.m) :
    ∑ c ∈ univ.filter (fun c => tmRow I ε δ c = r), X c = tmLoad I ε δ X r := by
  rw [sum_filter]; unfold tmLoad
  refine sum_congr rfl fun c _ => ?_
  have h1 : (tmRow I ε δ c = r) ↔ (tmEntry I ε δ c).1 = r := by
    simp [tmRow, Fin.ext_iff]
  have h2 : ¬ I.m + (tmEntry I ε δ c).2.1 = r := by omega
  by_cases h : (tmEntry I ε δ c).1 = (r : ℕ)
  · rw [if_pos (h1.2 h), if_pos h, if_neg h2, add_zero]
  · rw [if_neg (fun h' => h (h1.1 h')), if_neg h, if_neg h2, add_zero]

/-- INTERNAL: the column group sum of a column vertex is its line sum. -/
theorem tm_colSum_eq (X : TmCell I ε δ → ℤ) (r : Fin (I.m + I.n)) (hr : I.m ≤ (r : ℕ)) :
    ∑ c ∈ univ.filter (fun c => tmCol I ε δ c = r), X c = tmLoad I ε δ X r := by
  rw [sum_filter]; unfold tmLoad
  refine sum_congr rfl fun c _ => ?_
  have h1 : (tmCol I ε δ c = r) ↔ I.m + (tmEntry I ε δ c).2.1 = r := by
    simp [tmCol, Fin.ext_iff]
  have h2 : ¬ (tmEntry I ε δ c).1 = r := by have := (tmEntry_lt c).1; omega
  by_cases h : I.m + (tmEntry I ε δ c).2.1 = (r : ℕ)
  · rw [if_pos (h1.2 h), if_pos h, if_neg h2, zero_add]
  · rw [if_neg (fun h' => h (h1.1 h')), if_neg h, if_neg h2, add_zero]

/-- INTERNAL: the model weight is the product of vertex factors of line sums and cell factors. -/
theorem tmModel_weight (α : ℝ) (X : TmCell I ε δ → ℤ) :
    (tmModel I ε δ α).weight X =
      (∏ v : Fin (I.m + I.n), tmVf I ε δ α v (tmLoad I ε δ X v)) * ∏ c, tmPsi I ε δ c (X c) := by
  unfold EdgeModel.weight
  congr 1
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun r _ => ?_
  simp only [tmModel]
  by_cases hr : (r : ℕ) < I.m
  · rw [if_pos hr, if_neg (by omega), mul_one]; congr 1; exact tm_rowSum_eq I ε δ X r hr
  · rw [if_neg hr, if_pos (by omega), one_mul]; congr 1; exact tm_colSum_eq I ε δ X r (by omega)

/-- INTERNAL: the tree part of a table, as the `ℕ → ℚ` leaf elimination reads. -/
noncomputable def tmTreeVec (X : TmCell I ε δ → ℤ) (t : ℕ) : ℚ :=
  if h : t < (forest I ε δ).tree.length then (X (Sum.inr (Sum.inr ⟨t, h⟩)) : ℚ) else 0

/-- INTERNAL: the line sum of a table whose small and free part is `p` is the leaf-elimination incident sum `tLoadG` with base load `baseLoad p`. -/
theorem tmLoad_eq (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) (hp : p ∈ asgBox I ε δ)
    (X : TmCell I ε δ → ℤ) (hx : ∀ s, X (Sum.inl s) = p.1 s)
    (hz : ∀ f, X (Sum.inr (Sum.inl f)) = p.2 f) (v : ℕ) :
    ((tmLoad I ε δ X v : ℤ) : ℚ) =
      tLoadG (fun t => (treeAt I ε δ t).1) (fun t => I.m + (treeAt I ε δ t).2.1)
        (forest I ε δ).tree.length
        (baseLoad I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2)) (tmTreeVec I ε δ X) v := by
  have hp' := hp
  simp only [asgBox, smallBox, freeBox, mem_product, Fintype.mem_piFinset, mem_range] at hp'
  unfold tmLoad tLoadG baseLoad
  push_cast
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Finset.sum_range, Finset.sum_range,
    Finset.sum_range, add_assoc]
  congr 1
  · refine sum_congr rfl fun s _ => ?_
    have hle := hp'.1 s
    have e1 : extendN p.1 s = p.1 s := by simp [extendN]
    have e2 : (smallAt I ε δ s).2.2 - balY I ε δ p.1 s = p.1 s := by
      unfold balY; rw [e1]; unfold smallB at hle ⊢; omega
    rw [e1, e2, hx]; rfl
  congr 1
  · refine sum_congr rfl fun f _ => ?_
    have e1 : extendQ p.2 f = p.2 f := by simp [extendQ]
    rw [e1, hz]; rfl
  · refine sum_congr rfl fun t _ => ?_
    have e1 : tmTreeVec I ε δ X t = (X (Sum.inr (Sum.inr t)) : ℚ) := by simp [tmTreeVec]
    rw [e1]; rfl


/-! ### the table of an assignment -/

/-- INTERNAL: tree values are integers. -/
theorem tm_asgTree_floor (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) (t : ℕ) :
    ((⌊asgTree I ε δ p t⌋ : ℤ) : ℚ) = asgTree I ε δ p t := by
  obtain ⟨z, hz⟩ := asgTree_int I ε δ p t
  rw [hz, Int.floor_intCast]

/-- INTERNAL: the table of an assignment: `x`, `z`, and the leaf-elimination completion. -/
noncomputable def tmTable (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) :
    TmCell I ε δ → ℤ
  | .inl s => p.1 s
  | .inr (.inl f) => p.2 f
  | .inr (.inr t) => ⌊asgTree I ε δ p t⌋

/-- INTERNAL: the tree part of `tmTable p` is `asgTree p`. -/
theorem tmTreeVec_tmTable (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) (t : ℕ)
    (ht : t < (forest I ε δ).tree.length) :
    tmTreeVec I ε δ (tmTable I ε δ p) t = asgTree I ε δ p t := by
  simp only [tmTreeVec, dif_pos ht, tmTable]
  exact tm_asgTree_floor I ε δ p t

/-- INTERNAL: `tLoadG` reads tree values only below `N`. -/
theorem tm_tLoadG_congr {R Cv : ℕ → ℕ} {N : ℕ} {base Tv Tv' : ℕ → ℚ} (h : ∀ t < N, Tv t = Tv' t)
    (u : ℕ) : tLoadG R Cv N base Tv u = tLoadG R Cv N base Tv' u := by
  unfold tLoadG
  congr 1
  refine sum_congr rfl fun t ht => ?_
  rw [h t (mem_range.1 ht)]

/-- INTERNAL: eliminated vertices are vertices. -/
theorem tm_elim_fst_lt {x : ℕ × ℕ} (hx : x ∈ elimOrder I ε δ) : x.1 < I.m + I.n := by
  have hv := (pseudo_elimOrder_valid I ε δ).1
  have hlt := hv.lt x hx
  have hmem := mem_retained (treeAt_mem_retained I hlt)
  rcases hv.inc x hx with h | h <;> omega

/-- INTERNAL: eliminated vertices are not roots. -/
theorem tm_elim_fst_not_root {x : ℕ × ℕ} (hx : x ∈ elimOrder I ε δ) : x.1 ∉ roots I ε δ :=
  fun hr => (pseudo_elimOrder_valid I ε δ).2 _ hr (List.mem_map.2 ⟨x, hx, rfl⟩)

/-- INTERNAL: the completion satisfies every nonroot equation exactly (`tvFin_nonroot`, `elim_cover`). -/
theorem tmTable_nonroot (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ))
    (hp : p ∈ asgBox I ε δ) (v : ℕ) (hv : v < I.m + I.n) (hr : v ∉ roots I ε δ) :
    tmLoad I ε δ (tmTable I ε δ p) v = tmMargZ I v := by
  have hval := (pseudo_elimOrder_valid I ε δ).1
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (elim_cover I ε δ v hv hr)
  have h1 := tmLoad_eq I ε δ p hp (tmTable I ε δ p) (fun _ => rfl) (fun _ => rfl) x.1
  rw [tm_tLoadG_congr (Tv' := (tvFin (fun t => (treeAt I ε δ t).1)
      (fun t => I.m + (treeAt I ε δ t).2.1) (margin I)
      (baseLoad I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2)) (elimOrder I ε δ)).2)
    (fun t ht => by rw [tmTreeVec_tmTable I ε δ p t ht]; rfl),
    tvFin_nonroot hval _ x hx, tm_margin_eq_margZ] at h1
  exact_mod_cast h1

/-- INTERNAL: at a root, the final load of leaf elimination is the line sum of the table (`tvFin_root`). -/
theorem tmTable_root (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ))
    (hp : p ∈ asgBox I ε δ) (r : ℕ) (hr : r ∈ roots I ε δ) :
    ((tmLoad I ε δ (tmTable I ε δ p) r : ℤ) : ℚ) =
      (treeValues I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2)).1 r := by
  have hval := (pseudo_elimOrder_valid I ε δ).1
  rw [tmLoad_eq I ε δ p hp (tmTable I ε δ p) (fun _ => rfl) (fun _ => rfl) r,
    treeValues_eq_tvFin, tvFin_root hval _ r ((pseudo_elimOrder_valid I ε δ).2 r hr)]
  exact tm_tLoadG_congr (fun t ht => by rw [tmTreeVec_tmTable I ε δ p t ht]; rfl) r


/-! ### the weight at `α = 0` -/

/-- INTERNAL: `(2^{-A})^{|z|} = 2^{-A |z|}`. -/
theorem tm_pow_abs_eq (z : ℤ) :
    ((2 : ℝ) ^ (-(AParam I ε δ : ℝ))) ^ (|z|).toNat =
      (2 : ℝ) ^ (-((((AParam I ε δ : ℚ) * ((|z| : ℤ) : ℚ)) : ℚ) : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  have : (((|z|).toNat : ℕ) : ℝ) = ((|z| : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (abs_nonneg z)
  rw [this]; push_cast; ring

/-- INTERNAL: at `α = 0` the vertex factors of `tmTable p` are the root penalties. -/
theorem tm_vertex_prod_zero (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ))
    (hp : p ∈ asgBox I ε δ) :
    ∏ v : Fin (I.m + I.n), tmVf I ε δ 0 v (tmLoad I ε δ (tmTable I ε δ p) v) =
      ∏ r ∈ (roots I ε δ).toFinset, (2 : ℝ) ^ (-((((AParam I ε δ : ℚ) *
        |(treeValues I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2)).1 r - margin I r|) : ℚ) : ℝ)) := by
  rw [Fin.prod_univ_eq_prod_range (fun v => tmVf I ε δ 0 v (tmLoad I ε δ (tmTable I ε δ p) v))]
  have hset : (roots I ε δ).toFinset = (range (I.m + I.n)).filter (fun v => v ∈ roots I ε δ) := by
    ext v
    simp only [List.mem_toFinset, mem_filter, mem_range]
    constructor
    · intro h; exact ⟨((mem_roots_iff I ε δ v).1 h).1, h⟩
    · intro h; exact h.2
  rw [hset, prod_filter]
  refine prod_congr rfl fun v hv => ?_
  by_cases hr : v ∈ roots I ε δ
  · rw [if_pos hr]
    simp only [tmVf, tmVBase, if_pos hr]
    rw [tm_pow_abs_eq, ← tmTable_root I ε δ p hp v hr, tm_margin_eq_margZ]
    push_cast; rfl
  · rw [if_neg hr]
    simp only [tmVf, tmTable_nonroot I ε δ p hp v (mem_range.1 hv) hr, sub_self, abs_zero,
      Int.toNat_zero, pow_zero]

/-- INTERNAL: the cell factors of `tmTable p` are the tree penalties. -/
theorem tm_psi_prod (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) :
    ∏ c, tmPsi I ε δ c (tmTable I ε δ p c) =
      ∏ t ∈ range (forest I ε δ).tree.length, (2 : ℝ) ^ (-((((AParam I ε δ : ℚ) *
        (boxDist ((treeValues I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2)).2 t)
          ((treeAt I ε δ t).2.2 : ℚ) / ((treeAt I ε δ t).2.2 : ℚ))) : ℚ) : ℝ)) := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [tmPsi, prod_const_one, one_mul]
  rw [Finset.prod_range]
  refine prod_congr rfl fun t _ => ?_
  simp only [tmTreePsi, tmTable]
  rw [tm_asgTree_floor]; rfl

/-- INTERNAL: `D = Σ_roots A|δ_r| + Σ_t A dist(z_t, [0, b_t]) / b_t`. -/
theorem tm_asgPen_split (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ)) :
    asgPen I ε δ p =
      ∑ r ∈ (roots I ε δ).toFinset, (AParam I ε δ : ℚ) *
        |(treeValues I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2)).1 r - margin I r| +
      ∑ t ∈ range (forest I ε δ).tree.length, (AParam I ε δ : ℚ) *
        (boxDist ((treeValues I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2)).2 t)
          ((treeAt I ε δ t).2.2 : ℚ) / ((treeAt I ε δ t).2.2 : ℚ)) := by
  unfold asgPen penalty
  rw [← mul_sum, ← mul_sum, ← mul_add, List.sum_toFinset _ (roots_nodup I ε δ)]

/-- INTERNAL: the `α = 0` weight of the table of an assignment is `2^{-D}`: the surviving weight of `integer-signatures.tex:466-468`.
TEXLINE: sections/integer-signatures.tex:464-470 -/
theorem tmModel_weight_zero (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ))
    (hp : p ∈ asgBox I ε δ) :
    (tmModel I ε δ 0).weight (tmTable I ε δ p) = (2 : ℝ) ^ (-(asgPen I ε δ p : ℝ)) := by
  rw [tmModel_weight, tm_vertex_prod_zero I ε δ p hp, tm_psi_prod, tm_asgPen_split, Rat.cast_add,
    Rat.cast_sum, Rat.cast_sum, neg_add, Real.rpow_add (by norm_num), ← sum_neg_distrib,
    ← sum_neg_distrib, Real.rpow_sum_of_pos (by norm_num), Real.rpow_sum_of_pos (by norm_num)]


/-! ### `treeMarg` is the `α = 0` marginal -/

/-- INTERNAL: every completion lies strictly inside `[-N, N]`. -/
theorem tm_abs_asgTree_le (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ))
    (hp : p ∈ asgBox I ε δ) (t : ℕ) (ht : t < (forest I ε δ).tree.length) :
    |⌊asgTree I ε δ p t⌋| < tmBound I ε δ := by
  have h1 : |asgTree I ε δ p t| ≤ ∑ t ∈ range (forest I ε δ).tree.length, |asgTree I ε δ p t| :=
    single_le_sum (f := fun t => |asgTree I ε δ p t|) (fun _ _ => abs_nonneg _) (mem_range.2 ht)
  have h2 : ∑ t ∈ range (forest I ε δ).tree.length, |asgTree I ε δ p t| ≤
      ∑ p ∈ asgBox I ε δ, ∑ t ∈ range (forest I ε δ).tree.length, |asgTree I ε δ p t| :=
    single_le_sum (f := fun p => ∑ t ∈ range (forest I ε δ).tree.length, |asgTree I ε δ p t|)
      (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) hp
  have h3 := Int.le_ceil (∑ p ∈ asgBox I ε δ, ∑ t ∈ range (forest I ε δ).tree.length,
    |asgTree I ε δ p t|)
  have h4 : ((|⌊asgTree I ε δ p t⌋| : ℤ) : ℚ) ≤ (⌈∑ p ∈ asgBox I ε δ,
      ∑ t ∈ range (forest I ε δ).tree.length, |asgTree I ε δ p t|⌉ : ℚ) := by
    push_cast; rw [tm_asgTree_floor]; linarith
  have h5 := Int.cast_le.1 h4
  unfold tmBound; omega

/-- INTERNAL: the table of a box assignment lies in the model box. -/
theorem tmTable_mem_box (α : ℝ) (p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ))
    (hp : p ∈ asgBox I ε δ) : tmTable I ε δ p ∈ (tmModel I ε δ α).box := by
  have hp' := hp
  simp only [asgBox, smallBox, freeBox, mem_product, Fintype.mem_piFinset, mem_range] at hp'
  simp only [EdgeModel.box, Fintype.mem_piFinset, mem_Icc]
  rintro (s | f | t)
  · have := hp'.1 s
    refine ⟨by simp [tmModel, tmLo, tmTable], ?_⟩
    show ((p.1 s : ℕ) : ℤ) ≤ ((smallAt I ε δ s).2.2 : ℤ)
    unfold smallB at this; omega
  · have := hp'.2 f
    refine ⟨by simp [tmModel, tmLo, tmTable], ?_⟩
    show ((p.2 f : ℕ) : ℤ) ≤ ((freeAt I ε δ f).2.2 : ℤ)
    omega
  · have := tm_abs_asgTree_le I ε δ p hp t t.2
    show -tmBound I ε δ ≤ ⌊asgTree I ε δ p t⌋ ∧ ⌊asgTree I ε δ p t⌋ ≤ tmBound I ε δ
    rw [abs_lt] at this
    omega

/-- INTERNAL: every table of nonzero `α = 0` weight is the table of an assignment (uniqueness of the completion, `tvFin_unique`).
TEXLINE: sections/integer-signatures.tex:464-468 -/
theorem tmTable_surj (X : TmCell I ε δ → ℤ) (hX : X ∈ (tmModel I ε δ 0).box)
    (hw : (tmModel I ε δ 0).weight X ≠ 0) :
    ∃ p ∈ asgBox I ε δ, tmTable I ε δ p = X := by
  rw [tmModel_weight] at hw
  have hv := prod_ne_zero_iff.1 (mul_ne_zero_iff.1 hw).1
  have hL : ∀ v, v < I.m + I.n → v ∉ roots I ε δ → tmLoad I ε δ X v = tmMargZ I v := by
    intro v hvV hr
    have h := hv ⟨v, hvV⟩ (mem_univ _)
    simp only [tmVf, tmVBase, if_neg hr] at h
    have h0 : (|tmLoad I ε δ X v - tmMargZ I v|).toNat = 0 := by
      by_contra hn; exact h (zero_pow hn)
    rw [Int.toNat_eq_zero, abs_nonpos_iff, sub_eq_zero] at h0
    exact h0
  simp only [EdgeModel.box, Fintype.mem_piFinset, mem_Icc] at hX
  set p : (Fin (nSmall I ε δ) → ℕ) × (Fin (nFree I ε δ) → ℕ) :=
    (fun s => (X (Sum.inl s)).toNat, fun f => (X (Sum.inr (Sum.inl f))).toNat) with hpdef
  have hx : ∀ s, X (Sum.inl s) = ((p.1 s : ℕ) : ℤ) := fun s => by
    have := (hX (Sum.inl s)).1
    simp only [tmModel, tmLo] at this
    simp only [hpdef]; omega
  have hz : ∀ f, X (Sum.inr (Sum.inl f)) = ((p.2 f : ℕ) : ℤ) := fun f => by
    have := (hX (Sum.inr (Sum.inl f))).1
    simp only [tmModel, tmLo] at this
    simp only [hpdef]; omega
  have hp : p ∈ asgBox I ε δ := by
    simp only [asgBox, smallBox, freeBox, mem_product, Fintype.mem_piFinset, mem_range]
    refine ⟨fun s => ?_, fun f => ?_⟩
    · have h1 := (hX (Sum.inl s)).2
      have h2 := hx s
      simp only [tmModel, tmHi, tmEntry] at h1
      unfold smallB; omega
    · have h1 := (hX (Sum.inr (Sum.inl f))).2
      have h2 := hz f
      simp only [tmModel, tmHi, tmEntry] at h1
      omega
  refine ⟨p, hp, ?_⟩
  have hval := (pseudo_elimOrder_valid I ε δ).1
  have huniq := tvFin_unique (marg := margin I) hval
    (baseLoad I ε δ (extendN p.1) (balY I ε δ p.1) (extendQ p.2)) (tmTreeVec I ε δ X)
    (fun x hxm => by
      rw [← tmLoad_eq I ε δ p hp X hx hz x.1, hL x.1 (tm_elim_fst_lt I ε δ hxm)
        (tm_elim_fst_not_root I ε δ hxm), tm_margin_eq_margZ])
  funext c
  rcases c with s | f | t
  · exact (hx s).symm
  · exact (hz f).symm
  · have h := huniq t t.2
    simp only [tmTreeVec, dif_pos t.2] at h
    simp only [tmTable, asgTree]
    rw [treeValues_eq_tvFin, ← h, Int.floor_intCast]

/-- INTERNAL: `a_t(k)` is the `α = 0` value of the model marginal `a_{t;α}(k)`.
TEXLINE: sections/integer-signatures.tex:464-470 -/
theorem tm_treeMarg_eq_marg (t : ℕ) (ht : t < (forest I ε δ).tree.length) (k : ℤ) :
    treeMarg I ε δ t k = (tmModel I ε δ 0).marg (Sum.inr (Sum.inr ⟨t, ht⟩)) k := by
  unfold treeMarg EdgeModel.marg
  refine sum_bij_ne_zero (fun p _ _ => tmTable I ε δ p) ?_ ?_ ?_ ?_
  · intro p hp _
    rw [mem_filter] at hp ⊢
    refine ⟨tmTable_mem_box I ε δ 0 p hp.1, ?_⟩
    show ⌊asgTree I ε δ p t⌋ = k
    rw [hp.2, Int.floor_intCast]
  · intro p1 hp1 _ p2 hp2 _ h
    have h1 : ∀ s, p1.1 s = p2.1 s := fun s => by
      have := congrFun h (Sum.inl s); simp only [tmTable] at this; exact_mod_cast this
    have h2 : ∀ f, p1.2 f = p2.2 f := fun f => by
      have := congrFun h (Sum.inr (Sum.inl f)); simp only [tmTable] at this; exact_mod_cast this
    exact Prod.ext (funext h1) (funext h2)
  · intro X hX hw
    rw [mem_filter] at hX
    obtain ⟨p, hp, rfl⟩ := tmTable_surj I ε δ X hX.1 hw
    refine ⟨p, mem_filter.2 ⟨hp, ?_⟩, ?_, rfl⟩
    · have h := hX.2
      simp only [tmTable] at h
      rw [← tm_asgTree_floor, h]
    · rw [← tmModel_weight_zero I ε δ p hp]; exact hw
  · intro p hp _
    rw [tmModel_weight_zero I ε δ p (mem_filter.1 hp).1]


/-- INTERNAL: `α ↦ a_{t;α}(k)` is continuous (a finite sum of polynomials in `α`), so the limit `α ↓ 0` is the value at `0`. -/
theorem tm_marg_continuous (c : TmCell I ε δ) (k : ℤ) :
    Continuous fun α => (tmModel I ε δ α).marg c k := by
  have h : ∀ α, (tmModel I ε δ α).marg c k = ∑ X ∈ (tmModel I ε δ 0).box.filter (fun X => X c = k),
      (tmModel I ε δ α).weight X := fun _ => rfl
  simp only [h, tmModel_weight]
  apply continuous_finset_sum
  intro X _
  apply Continuous.mul _ continuous_const
  apply continuous_finset_prod
  intro v _
  unfold tmVf tmVBase
  exact (continuous_const.if_const _ continuous_id).pow _

/-- INTERNAL: positive tree-marginal values lie strictly inside `[-N, N]`. -/
theorem tm_treeMarg_range (t : ℕ) (ht : t < (forest I ε δ).tree.length) (j : ℤ)
    (hj : 0 < treeMarg I ε δ t j) : -tmBound I ε δ < j ∧ j < tmBound I ε δ := by
  unfold treeMarg at hj
  obtain ⟨p, hp, _⟩ := exists_ne_zero_of_sum_ne_zero hj.ne'
  rw [mem_filter] at hp
  have h := tm_abs_asgTree_le I ε δ p hp.1 t ht
  rw [hp.2, Int.floor_intCast, abs_lt] at h
  exact h

end treeModel

open Filter Topology in
/-- **Log-concave tree marginals** (`eq:tree-marginal-interpolation`).
PAPER: sections/integer-signatures.tex:432-470 -/
theorem tree_marginal_interp (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (t : ℕ)
    (ht : t < (forest I ε δ).tree.length) (v k w : ℤ) (hvk : v < k) (hkw : k < w)
    (hv : 0 < treeMarg I ε δ t v) (hw : 0 < treeMarg I ε δ t w) :
    treeMarg I ε δ t v ^ (((w - k : ℤ) : ℝ) / ((w - v : ℤ) : ℝ)) *
      treeMarg I ε δ t w ^ (((k - v : ℤ) : ℝ) / ((w - v : ℤ) : ℝ)) ≤ treeMarg I ε δ t k := by
  -- `0 < ε` is not needed: the model works for any multiplier `A ≥ 0`.
  have _ := hε
  set c0 : TmCell I ε δ := Sum.inr (Sum.inr ⟨t, ht⟩) with hc0
  have hrv := tm_treeMarg_range I ε δ t ht v hv
  have hrw := tm_treeMarg_range I ε δ t ht w hw
  have hlo : ∀ α, (tmModel I ε δ α).lo c0 = -tmBound I ε δ := fun _ => rfl
  have hhi : ∀ α, (tmModel I ε δ α).hi c0 = tmBound I ε δ := fun _ => rfl
  have hineq : ∀ α ∈ Set.Ioo (0 : ℝ) 1,
      (tmModel I ε δ α).marg c0 v ^ (((w - k : ℤ) : ℝ) / ((w - v : ℤ) : ℝ)) *
        (tmModel I ε δ α).marg c0 w ^ (((k - v : ℤ) : ℝ) / ((w - v : ℤ) : ℝ)) ≤
        (tmModel I ε δ α).marg c0 k := by
    intro α hα
    have hH := tmModel_hyps I ε δ hα.1 hα.2.le
    refine logconcave_rpow_interp (fun j => (tmModel I ε δ α).marg c0 j) v k w hvk hkw
      (fun j h1 h2 => ?_) (fun j h1 h2 => ?_)
    · exact (tmModel I ε δ α).marg_pos hH c0 j (by rw [hlo]; omega) (by rw [hhi]; omega)
    · exact (tmModel I ε δ α).marg_logconcave hH c0 j (by rw [hlo]; omega) (by rw [hhi]; omega)
  have hT : ∀ j, Tendsto (fun α => (tmModel I ε δ α).marg c0 j) (𝓝[>] 0)
      (𝓝 (treeMarg I ε δ t j)) := fun j => by
    rw [tm_treeMarg_eq_marg I ε δ t ht j]
    exact ((tm_marg_continuous I ε δ c0 j).tendsto 0).mono_left nhdsWithin_le_nhds
  have hwv : (0 : ℝ) < ((w - v : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < w - v)
  have hθ1 : (0 : ℝ) ≤ ((w - k : ℤ) : ℝ) / ((w - v : ℤ) : ℝ) :=
    div_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ w - k)) hwv.le
  have hθ2 : (0 : ℝ) ≤ ((k - v : ℤ) : ℝ) / ((w - v : ℤ) : ℝ) :=
    div_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ k - v)) hwv.le
  exact le_of_tendsto_of_tendsto (((hT v).rpow_const (Or.inr hθ1)).mul
    ((hT w).rpow_const (Or.inr hθ2))) (hT k)
    (by filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with α hα using hineq α hα)

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `tree_marginal_interp` via the `α`-softened `EdgeModel` and the limit `α ↓ 0`
-/
