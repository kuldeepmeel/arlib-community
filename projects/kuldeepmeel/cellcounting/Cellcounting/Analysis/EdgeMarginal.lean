import Cellcounting.Analysis.IntegerSignature

/-!
# Log-concave cell marginals of a bipartite table model

The two-view laminar encoding of `cor:hj-signatures` and the first half of the
proof of `lem:tree-marginal` (`integer-signatures.tex:330-470`), for an
abstract bipartite table model:

* cells `c : C`, each with a row `row c` and a column `col c`, and an integer
  interval `[lo c, hi c]` of physical values, `lo c < hi c`;
* positive log-concave row factors `φR`, column factors `φK` of the line sums
  and cell factors `ψ` of the cell values;
* `edgeWeight X = ∏_r φR_r(Σ_{row c = r} X_c) ∏_k φK_k(Σ_{col c = k} X_c) ∏_c ψ_c(X_c)`.

`edgeMarg t k` is the total weight of the tables in the box with `X_t = k`.
`edgeMarg_logconcave` is `a(k)² ≥ a(k-1) a(k+1)` and `edgeMarg_pos` its
positivity on `[lo t, hi t]`.

The proof follows the paper: row view `x_c = X_c - lo_c` and column view
`y_c = hi_c - X_c` of every cell, row groups of `x`'s, column groups of `y`'s
and unary cell factors form a laminar family; every pair other than `t` is
summed at balance (`good_sumPair`), and the removal signature at the display
two above the remaining total is the `2 × 2` matrix of `a(k-1), a(k), a(k+1)`.
-/

namespace Cellcounting.Analysis

open Finset

/-- INTERNAL: a bipartite table model with interval cells and positive factors.
TEXLINE: sections/integer-signatures.tex:345-380 -/
structure EdgeModel (C Rw Cl : Type*) where
  /-- The row of a cell. -/
  row : C → Rw
  /-- The column of a cell. -/
  col : C → Cl
  /-- Lower end of the physical interval. -/
  lo : C → ℤ
  /-- Upper end of the physical interval. -/
  hi : C → ℤ
  /-- Row factor of the row sum. -/
  φR : Rw → ℤ → ℝ
  /-- Column factor of the column sum. -/
  φK : Cl → ℤ → ℝ
  /-- Cell factor of the cell value. -/
  ψ : C → ℤ → ℝ

namespace EdgeModel

variable {C Rw Cl : Type*} [Fintype C] [DecidableEq C] [Fintype Rw] [DecidableEq Rw]
  [Fintype Cl] [DecidableEq Cl]

/-- INTERNAL: positivity and log-concavity of all factors, and positive widths. -/
structure Hyps (E : EdgeModel C Rw Cl) : Prop where
  width : ∀ c, E.lo c < E.hi c
  φR_pos : ∀ r s, 0 < E.φR r s
  φK_pos : ∀ k s, 0 < E.φK k s
  ψ_pos : ∀ c s, 0 < E.ψ c s
  φR_lc : ∀ r s, E.φR r (s - 1) * E.φR r (s + 1) ≤ E.φR r s ^ 2
  φK_lc : ∀ k s, E.φK k (s - 1) * E.φK k (s + 1) ≤ E.φK k s ^ 2
  ψ_lc : ∀ c s, E.ψ c (s - 1) * E.ψ c (s + 1) ≤ E.ψ c s ^ 2

/-- INTERNAL: the weight of a physical table. -/
noncomputable def weight (E : EdgeModel C Rw Cl) (X : C → ℤ) : ℝ :=
  (∏ r, E.φR r (∑ c ∈ univ.filter (fun c => E.row c = r), X c)) *
    (∏ k, E.φK k (∑ c ∈ univ.filter (fun c => E.col c = k), X c)) * ∏ c, E.ψ c (X c)

/-- INTERNAL: the box of physical tables. -/
noncomputable def box (E : EdgeModel C Rw Cl) : Finset (C → ℤ) :=
  Fintype.piFinset fun c => Icc (E.lo c) (E.hi c)

/-- INTERNAL: the marginal mass of the value `k` at cell `t`. -/
noncomputable def marg (E : EdgeModel C Rw Cl) (t : C) (k : ℤ) : ℝ :=
  ∑ X ∈ E.box.filter (fun X => X t = k), E.weight X

theorem weight_pos (E : EdgeModel C Rw Cl) (hE : E.Hyps) (X : C → ℤ) : 0 < E.weight X := by
  unfold weight
  have h1 := Finset.prod_pos fun r (_ : r ∈ univ) => hE.φR_pos r
    (∑ c ∈ univ.filter (fun c => E.row c = r), X c)
  have h2 := Finset.prod_pos fun k (_ : k ∈ univ) => hE.φK_pos k
    (∑ c ∈ univ.filter (fun c => E.col c = k), X c)
  have h3 := Finset.prod_pos fun c (_ : c ∈ univ) => hE.ψ_pos c (X c)
  positivity

/-- **Positivity of a cell marginal** on its whole interval.
TEXLINE: sections/integer-signatures.tex:445-450 -/
theorem marg_pos (E : EdgeModel C Rw Cl) (hE : E.Hyps) (t : C) (k : ℤ) (hk1 : E.lo t ≤ k)
    (hk2 : k ≤ E.hi t) : 0 < E.marg t k := by
  unfold marg
  set X : C → ℤ := fun c => if c = t then k else E.lo c
  have hX : X ∈ E.box.filter (fun X => X t = k) := by
    simp only [Finset.mem_filter, box, Fintype.mem_piFinset, Finset.mem_Icc, X, if_true,
      and_true]
    intro c
    by_cases hc : c = t
    · subst hc; simp [hk1, hk2]
    · simp [hc, (hE.width c).le]
  exact Finset.sum_pos' (fun X _ => (E.weight_pos hE X).le) ⟨X, hX, E.weight_pos hE X⟩

/-! ### The two-view laminar encoding -/

variable (E : EdgeModel C Rw Cl)

/-- INTERNAL: capacities of the row view `(c, true)` and column view `(c, false)`. -/
def mE : C × Bool → ℤ := fun p => E.hi p.1 - E.lo p.1

/-- INTERNAL: the laminar family: row groups of row views, column groups of
column views, and unary row-view cells. -/
def Gs : Rw ⊕ Cl ⊕ C → Finset (C × Bool)
  | .inl r => univ.filter (fun p => p.2 = true ∧ E.row p.1 = r)
  | .inr (.inl k) => univ.filter (fun p => p.2 = false ∧ E.col p.1 = k)
  | .inr (.inr c) => {(c, true)}

/-- INTERNAL: the factors, as functions of the coordinate sums of their groups. -/
def ψs : Rw ⊕ Cl ⊕ C → ℤ → ℝ
  | .inl r => fun s => E.φR r (s + ∑ c ∈ univ.filter (fun c => E.row c = r), E.lo c)
  | .inr (.inl k) => fun s => E.φK k (∑ c ∈ univ.filter (fun c => E.col c = k), E.hi c - s)
  | .inr (.inr c) => fun s => E.ψ c (E.lo c + s)

/-- INTERNAL: the full total `Σ_c M_c`. -/
def Rtot : ℤ := ∑ c, (E.hi c - E.lo c)

/-- INTERNAL: the laminar weight of the encoding. -/
noncomputable def F : (C × Bool → ℤ) → ℝ := laminarWeight E.mE E.Rtot E.Gs E.ψs

/-- INTERNAL: the two views of a physical table. -/
def disp (X : C → ℤ) : C × Bool → ℤ := fun p =>
  if p.2 then X p.1 - E.lo p.1 else E.hi p.1 - X p.1

theorem Gs_laminar : ∀ a a', E.Gs a ⊆ E.Gs a' ∨ E.Gs a' ⊆ E.Gs a ∨ Disjoint (E.Gs a) (E.Gs a') := by
  intro a a'
  rcases a with r | k | c <;> rcases a' with r' | k' | c'
  · by_cases h : r = r'
    · subst h; left; exact subset_rfl
    · right; right
      rw [Finset.disjoint_left]
      intro p hp hp'
      simp only [Gs, Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
      exact h (hp.2.symm.trans hp'.2)
  · right; right
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Gs, Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    rw [hp.1] at hp'; exact Bool.noConfusion hp'.1
  · by_cases h : E.row c' = r
    · right; left
      intro p hp
      simp only [Gs, Finset.mem_singleton] at hp
      subst hp
      simp [Gs, h]
    · right; right
      rw [Finset.disjoint_left]
      intro p hp hp'
      simp only [Gs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hp hp'
      subst hp'; exact h hp.2
  · right; right
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Gs, Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    rw [hp.1] at hp'; exact Bool.noConfusion hp'.1
  · by_cases h : k = k'
    · subst h; left; exact subset_rfl
    · right; right
      rw [Finset.disjoint_left]
      intro p hp hp'
      simp only [Gs, Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
      exact h (hp.2.symm.trans hp'.2)
  · right; right
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Gs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hp hp'
    subst hp'; exact Bool.noConfusion hp.1
  · by_cases h : E.row c = r'
    · left
      intro p hp
      simp only [Gs, Finset.mem_singleton] at hp
      subst hp
      simp [Gs, h]
    · right; right
      rw [Finset.disjoint_left]
      intro p hp hp'
      simp only [Gs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hp hp'
      subst hp; exact h hp'.2
  · right; right
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Gs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hp hp'
    subst hp; exact Bool.noConfusion hp'.1
  · by_cases h : c = c'
    · subst h; left; exact subset_rfl
    · right; right
      rw [Finset.disjoint_left]
      intro p hp hp'
      simp only [Gs, Finset.mem_singleton] at hp hp'
      rw [hp] at hp'; exact h (Prod.mk.inj hp').1

theorem ψs_pos (hE : E.Hyps) : ∀ a s, 0 < E.ψs a s := by
  intro a s
  rcases a with r | k | c
  · exact hE.φR_pos _ _
  · exact hE.φK_pos _ _
  · exact hE.ψ_pos _ _

theorem ψs_lc (hE : E.Hyps) : ∀ a s, E.ψs a (s - 1) * E.ψs a (s + 1) ≤ E.ψs a s ^ 2 := by
  intro a s
  rcases a with r | k | c
  · have := hE.φR_lc r (s + ∑ c ∈ univ.filter (fun c => E.row c = r), E.lo c)
    simp only [ψs]
    rw [show s - 1 + ∑ c ∈ univ.filter (fun c => E.row c = r), E.lo c =
        s + ∑ c ∈ univ.filter (fun c => E.row c = r), E.lo c - 1 by ring,
      show s + 1 + ∑ c ∈ univ.filter (fun c => E.row c = r), E.lo c =
        s + ∑ c ∈ univ.filter (fun c => E.row c = r), E.lo c + 1 by ring]
    exact this
  · have := hE.φK_lc k (∑ c ∈ univ.filter (fun c => E.col c = k), E.hi c - s)
    simp only [ψs]
    rw [show ∑ c ∈ univ.filter (fun c => E.col c = k), E.hi c - (s - 1) =
        ∑ c ∈ univ.filter (fun c => E.col c = k), E.hi c - s + 1 by ring,
      show ∑ c ∈ univ.filter (fun c => E.col c = k), E.hi c - (s + 1) =
        ∑ c ∈ univ.filter (fun c => E.col c = k), E.hi c - s - 1 by ring]
    linarith
  · have := hE.ψ_lc c (E.lo c + s)
    simp only [ψs]
    rw [show E.lo c + (s - 1) = E.lo c + s - 1 by ring,
      show E.lo c + (s + 1) = E.lo c + s + 1 by ring]
    exact this

theorem good_F (hE : E.Hyps) : Good E.mE univ E.Rtot E.F :=
  good_laminar E.mE E.Rtot E.Gs E.ψs (E.ψs_pos hE) (E.ψs_lc hE) E.Gs_laminar

theorem sum_prod_bool {M : Type*} [AddCommMonoid M] (f : C × Bool → M) :
    ∑ p, f p = ∑ c, (f (c, true) + f (c, false)) := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun c _ => by rw [Fintype.sum_bool]

theorem valid_disp (X : C → ℤ) (hX : X ∈ E.box) : Valid E.mE univ E.Rtot (E.disp X) := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc] at hX
  refine ⟨fun p => ?_, fun p _ => ?_, fun p hp => absurd (Finset.mem_univ p) hp, ?_⟩
  · have := hX p.1; simp only [disp]; split_ifs <;> omega
  · have := hX p.1; simp only [disp, mE]; split_ifs <;> omega
  · rw [sum_prod_bool]; simp only [disp, if_true, Bool.false_eq_true, if_false, Rtot]
    exact Finset.sum_congr rfl fun c _ => by ring

theorem sum_filter_view (b : Bool) (P : C → Prop) [DecidablePred P] (g : C × Bool → ℤ) :
    ∑ p ∈ univ.filter (fun p : C × Bool => p.2 = b ∧ P p.1), g p =
      ∑ c ∈ univ.filter P, g (c, b) := by
  rw [Finset.sum_filter, Finset.sum_filter, sum_prod_bool]
  refine Finset.sum_congr rfl fun c _ => ?_
  cases b <;> simp

theorem F_disp (X : C → ℤ) (hX : X ∈ E.box) : E.F (E.disp X) = E.weight X := by
  simp only [F, laminarWeight]
  rw [if_pos (E.valid_disp X hX)]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, weight, mul_assoc]
  congr 1
  · refine Finset.prod_congr rfl fun r _ => ?_
    simp only [Gs, ψs]
    congr 1
    rw [sum_filter_view true (fun c => E.row c = r)]
    simp only [disp, if_true]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  congr 1
  · refine Finset.prod_congr rfl fun k _ => ?_
    simp only [Gs, ψs]
    congr 1
    rw [sum_filter_view false (fun c => E.col c = k)]
    simp only [disp, Bool.false_eq_true, if_false]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  · refine Finset.prod_congr rfl fun c _ => ?_
    simp only [Gs, ψs, Finset.sum_singleton, disp, if_true]
    congr 1; ring

/-! ### Summing a set of cells at balance -/

/-- INTERNAL: the pair profile `(κ_c, M_c - κ_c)` of every summed cell `c ∈ A`. -/
def shift (A : Finset C) (κ : C → ℤ) : C × Bool → ℤ := fun p =>
  if p.1 ∈ A then (if p.2 then κ p.1 else E.hi p.1 - E.lo p.1 - κ p.1) else 0

/-- INTERNAL: the balanced profiles of the summed cells. -/
noncomputable def bal (A : Finset C) : Finset (C → ℤ) :=
  Fintype.piFinset fun c => if c ∈ A then Icc 0 (E.hi c - E.lo c) else {0}

/-- INTERNAL: the weight after summing every cell of `A` at balance. -/
noncomputable def WA (A : Finset C) : (C × Bool → ℤ) → ℝ := fun z =>
  haveI := Classical.propDecidable (∀ c ∈ A, z (c, true) = 0 ∧ z (c, false) = 0)
  if ∀ c ∈ A, z (c, true) = 0 ∧ z (c, false) = 0 then
    ∑ κ ∈ E.bal A, E.F (z + E.shift A κ) else 0

/-- INTERNAL: the active (not yet summed) coordinates. -/
def actS (A : Finset C) : Finset (C × Bool) := univ.filter fun p => p.1 ∉ A

theorem WA_empty : E.WA ∅ = E.F := by
  funext z
  simp only [WA, Finset.notMem_empty, IsEmpty.forall_iff, implies_true, if_true]
  have : E.bal ∅ = {0} := by
    ext κ
    simp only [bal, Finset.notMem_empty, if_false, Fintype.mem_piFinset, Finset.mem_singleton]
    exact ⟨fun h => funext h, fun h c => by rw [h]; rfl⟩
  rw [this, Finset.sum_singleton]
  congr 1
  funext p; simp [shift]

theorem WA_insert (hE : E.Hyps) (A : Finset C) (c : C) (hc : c ∉ A) :
    E.WA (insert c A) =
      sumPair (c, true) (c, false) (E.hi c - E.lo c).toNat (E.WA A) := by
  classical
  funext z
  have hM : (((E.hi c - E.lo c).toNat : ℕ) : ℤ) = E.hi c - E.lo c := by
    have := hE.width c; omega
  simp only [WA, sumPair]
  by_cases hz : z (c, true) = 0 ∧ z (c, false) = 0
  · rw [if_pos hz]
    have hcond : ∀ k : ℕ, (∀ c' ∈ A, (z + Pi.single (c, true) (k : ℤ) +
        Pi.single (c, false) ((((E.hi c - E.lo c).toNat : ℕ) : ℤ) - k) : C × Bool → ℤ)
          (c', true) = 0 ∧
        (z + Pi.single (c, true) (k : ℤ) +
        Pi.single (c, false) ((((E.hi c - E.lo c).toNat : ℕ) : ℤ) - k) : C × Bool → ℤ)
          (c', false) = 0) ↔
        ∀ c' ∈ A, z (c', true) = 0 ∧ z (c', false) = 0 := by
      intro k
      refine forall₂_congr fun c' hc' => ?_
      have hne : c' ≠ c := fun h => hc (h ▸ hc')
      simp [Pi.single_apply, hne]
    by_cases hA : ∀ c' ∈ A, z (c', true) = 0 ∧ z (c', false) = 0
    · have hins : ∀ c' ∈ insert c A, z (c', true) = 0 ∧ z (c', false) = 0 := by
        intro c' hc'
        rcases Finset.mem_insert.1 hc' with rfl | h
        · exact hz
        · exact hA c' h
      rw [if_pos hins]
      simp only [hcond, if_pos hA]
      rw [← Finset.sum_product']
      refine Finset.sum_nbij' (fun κ => ((κ c).toNat, Function.update κ c 0))
        (fun q => Function.update q.2 c (q.1 : ℤ)) ?_ ?_ ?_ ?_ ?_
      · intro κ hκ
        simp only [bal, Fintype.mem_piFinset, Finset.mem_coe] at hκ
        have hκc := hκ c
        simp only [Finset.mem_insert, true_or, if_true, Finset.mem_Icc] at hκc
        simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, bal,
          Fintype.mem_piFinset]
        refine ⟨by omega, fun c' => ?_⟩
        by_cases h : c' = c
        · subst h; simp [hc]
        · have := hκ c'
          simp only [Function.update_of_ne h, Finset.mem_insert, h, false_or] at this ⊢
          exact this
      · intro q hq
        simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, bal,
          Fintype.mem_piFinset] at hq
        simp only [Finset.mem_coe, bal, Fintype.mem_piFinset]
        intro c'
        by_cases h : c' = c
        · subst h; simp; omega
        · have := hq.2 c'
          simp only [Function.update_of_ne h, Finset.mem_insert, h, false_or]
          exact this
      · intro κ hκ
        simp only [bal, Fintype.mem_piFinset, Finset.mem_coe] at hκ
        have hκc := hκ c
        simp only [Finset.mem_insert, true_or, if_true, Finset.mem_Icc] at hκc
        funext c'
        by_cases h : c' = c
        · subst h; simp; omega
        · simp [Function.update_of_ne h]
      · intro q hq
        simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, bal,
          Fintype.mem_piFinset] at hq
        have hq2 := hq.2 c
        simp only [hc, if_false, Finset.mem_singleton] at hq2
        refine Prod.ext ?_ ?_
        · simp
        · funext c'
          by_cases h : c' = c
          · subst h; simp [hq2]
          · simp [Function.update_of_ne h]
      · intro κ hκ
        simp only [bal, Fintype.mem_piFinset, Finset.mem_coe] at hκ
        have hκc := hκ c
        simp only [Finset.mem_insert, true_or, if_true, Finset.mem_Icc] at hκc
        congr 1
        funext p
        obtain ⟨c', b⟩ := p
        simp only [shift, Pi.add_apply, Pi.single_apply, Prod.mk.injEq, Finset.mem_insert]
        by_cases h : c' = c
        · subst h
          cases b <;> simp [hc] <;> omega
        · cases b <;> simp [h, Function.update_of_ne h]
    · rw [if_neg (fun h => hA fun c' hc' => h c' (Finset.mem_insert_of_mem hc'))]
      simp only [hcond, if_neg hA, Finset.sum_const_zero]
  · rw [if_neg hz, if_neg (fun h => hz (h c (Finset.mem_insert_self c A)))]

theorem good_WA (hE : E.Hyps) (A : Finset C) :
    Good E.mE (actS A) (E.Rtot - ∑ c ∈ A, (E.hi c - E.lo c)) (E.WA A) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    rw [WA_empty]
    have : actS (C := C) ∅ = univ := by ext p; simp [actS]
    rw [this]; simpa using E.good_F hE
  | insert c A hc ih =>
    rw [WA_insert E hE A c hc]
    have hM : (((E.hi c - E.lo c).toNat : ℕ) : ℤ) = E.hi c - E.lo c := by
      have := hE.width c; omega
    have h1 := good_sumPair ih (a := (c, true)) (b := (c, false)) (M := (E.hi c - E.lo c).toNat)
      (by simp [actS, hc]) (by simp [actS, hc]) (by simp) (by simp [mE, hM]) (by simp [mE, hM])
      (by have := hE.width c; omega)
    have hS : ((actS A).erase (c, true)).erase (c, false) = actS (insert c A) := by
      ext ⟨c', b⟩
      simp only [actS, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, ne_eq, Prod.mk.injEq, not_or]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨fun h => ?_, h3⟩
        subst h; cases b <;> simp_all
      · rintro ⟨h1, h3⟩; exact ⟨fun h => h1 h.1, fun h => h1 h.1, h3⟩
    rw [hS, hM] at h1
    rw [Finset.sum_insert hc, show E.Rtot - (E.hi c - E.lo c + ∑ x ∈ A, (E.hi x - E.lo x)) =
      E.Rtot - ∑ c ∈ A, (E.hi c - E.lo c) - (E.hi c - E.lo c) by ring]
    exact h1

/-- INTERNAL: the display of the remaining pair `t` at physical value `j`. -/
def tdisp (t : C) (j : ℤ) : C × Bool → ℤ :=
  Pi.single (t, true) (j - E.lo t) + Pi.single (t, false) (E.hi t - j)

/-- INTERNAL: after summing every other cell at balance, the weight of the
balanced display of `t` at value `j` is the marginal `a_t(j)`.
TEXLINE: sections/integer-signatures.tex:440-455 -/
theorem WA_tdisp (hE : E.Hyps) (t : C) (j : ℤ) (hj1 : E.lo t ≤ j) (hj2 : j ≤ E.hi t) :
    E.WA (univ.erase t) (E.tdisp t j) = E.marg t j := by
  classical
  simp only [WA, marg]
  rw [if_pos]
  swap
  · intro c hc
    have hct : c ≠ t := Finset.ne_of_mem_erase hc
    simp [tdisp, Pi.single_apply, hct]
  refine Finset.sum_nbij' (fun κ c => if c = t then j else E.lo c + κ c)
    (fun X c => if c = t then 0 else X c - E.lo c) ?_ ?_ ?_ ?_ ?_
  · intro κ hκ
    simp only [bal, Fintype.mem_piFinset, Finset.mem_coe, Finset.mem_erase, ne_eq,
      Finset.mem_univ, and_true] at hκ
    simp only [Finset.mem_coe, Finset.mem_filter, box, Fintype.mem_piFinset, Finset.mem_Icc,
      if_true, and_true]
    intro c
    by_cases h : c = t
    · subst h; simp [hj1, hj2]
    · have := hκ c; simp only [h, not_false_eq_true, if_true, Finset.mem_Icc] at this
      simp only [h, if_false]; omega
  · intro X hX
    simp only [Finset.mem_coe, Finset.mem_filter, box, Fintype.mem_piFinset,
      Finset.mem_Icc] at hX
    simp only [bal, Fintype.mem_piFinset, Finset.mem_coe, Finset.mem_erase, ne_eq,
      Finset.mem_univ, and_true]
    intro c
    by_cases h : c = t
    · subst h; simp
    · have := hX.1 c; simp only [h, not_false_eq_true, if_true, if_false, Finset.mem_Icc]; omega
  · intro κ hκ
    simp only [bal, Fintype.mem_piFinset, Finset.mem_coe, Finset.mem_erase, ne_eq,
      Finset.mem_univ, and_true] at hκ
    funext c
    by_cases h : c = t
    · subst h; have := hκ c; simp at this; simp [this]
    · simp [h]
  · intro X hX
    simp only [Finset.mem_coe, Finset.mem_filter] at hX
    funext c
    by_cases h : c = t
    · subst h; simp [hX.2]
    · simp [h]
  · intro κ hκ
    simp only [bal, Fintype.mem_piFinset, Finset.mem_coe, Finset.mem_erase, ne_eq,
      Finset.mem_univ, and_true] at hκ
    have hXbox : (fun c => if c = t then j else E.lo c + κ c) ∈ E.box := by
      simp only [box, Fintype.mem_piFinset, Finset.mem_Icc]
      intro c
      by_cases h : c = t
      · subst h; simp [hj1, hj2]
      · have := hκ c; simp only [h, not_false_eq_true, if_true, Finset.mem_Icc] at this
        simp only [h, if_false]; omega
    rw [← E.F_disp _ hXbox]
    congr 1
    funext p
    obtain ⟨c, b⟩ := p
    by_cases h : c = t
    · subst h; cases b <;> simp [tdisp, shift, disp, Pi.single_apply]
    · cases b <;> simp [tdisp, shift, disp, Pi.single_apply, h] <;> ring

/-- **Log-concavity of a cell marginal**: `a_t(k-1) a_t(k+1) ≤ a_t(k)²` for
`lo_t < k < hi_t`.
PAPER: sections/integer-signatures.tex:432-462 -/
theorem marg_logconcave (hE : E.Hyps) (t : C) (k : ℤ) (hk1 : E.lo t < k) (hk2 : k < E.hi t) :
    E.marg t (k - 1) * E.marg t (k + 1) ≤ E.marg t k ^ 2 := by
  classical
  set A := univ.erase t
  have hgood := E.good_WA hE A
  have hr : E.Rtot - ∑ c ∈ A, (E.hi c - E.lo c) = E.hi t - E.lo t := by
    simp only [Rtot, A]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t)]; ring
  rw [hr] at hgood
  set z0 : C × Bool → ℤ := Pi.single (t, true) (k - E.lo t + 1) + Pi.single (t, false) (E.hi t - k + 1)
  have hz0 : Valid E.mE (actS A) (E.hi t - E.lo t + 2) z0 := by
    refine ⟨fun p => ?_, fun p hp => ?_, fun p hp => ?_, ?_⟩
    · obtain ⟨c, b⟩ := p
      simp only [z0, Pi.add_apply, Pi.single_apply, Prod.mk.injEq]
      split_ifs <;> omega
    · obtain ⟨c, b⟩ := p
      have hct : c = t := by simpa [actS, A] using hp
      subst hct
      cases b <;> simp [z0, mE, Pi.single_apply] <;> omega
    · obtain ⟨c, b⟩ := p
      have hct : c ≠ t := by simpa [actS, A] using hp
      simp [z0, Pi.single_apply, hct]
    · simp only [z0, Pi.add_apply, Finset.sum_add_distrib, sum_single_int]; ring
  have hH := hgood.2.2 z0 hz0
  have e1 : remMat (E.WA A) z0 (t, true) (t, true) = E.marg t (k - 1) := by
    rw [← E.WA_tdisp hE t (k - 1) (by omega) (by omega)]
    simp only [remMat]; congr 1
    funext p; obtain ⟨c, b⟩ := p
    by_cases h : c = t
    · subst h; cases b <;> simp [z0, tdisp, Pi.single_apply] <;> ring
    · cases b <;> simp [z0, tdisp, Pi.single_apply, h]
  have e2 : remMat (E.WA A) z0 (t, false) (t, false) = E.marg t (k + 1) := by
    rw [← E.WA_tdisp hE t (k + 1) (by omega) (by omega)]
    simp only [remMat]; congr 1
    funext p; obtain ⟨c, b⟩ := p
    by_cases h : c = t
    · subst h; cases b <;> simp [z0, tdisp, Pi.single_apply] <;> ring
    · cases b <;> simp [z0, tdisp, Pi.single_apply, h]
  have e3 : remMat (E.WA A) z0 (t, true) (t, false) = E.marg t k := by
    rw [← E.WA_tdisp hE t k (by omega) (by omega)]
    simp only [remMat]; congr 1
    funext p; obtain ⟨c, b⟩ := p
    by_cases h : c = t
    · subst h; cases b <;> simp [z0, tdisp, Pi.single_apply] <;> ring
    · cases b <;> simp [z0, tdisp, Pi.single_apply, h]
  have hpos := E.marg_pos hE t (k - 1) (by omega) (by omega)
  have := hH (ev (t, true)) (ev (t, false)) (by rw [qf_ev_ev, e1]; exact hpos)
  rwa [qf_ev_ev, qf_ev_ev, qf_ev_ev, e1, e2, e3] at this

end EdgeModel

end Cellcounting.Analysis
