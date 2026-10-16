import Cellcounting.Analysis.Contamination
import Cellcounting.Analysis.HyperbolicForm
import Cellcounting.Analysis.OmitSig

/-!
# The removal signature of `h_j` (`cor:hj-signatures`, removal half)

`integer-signatures.tex:325-400`.  Each small cell `s` contributes two count
coordinates, `(s, false)` for its row view `x_s` and `(s, true)` for its column view
`y_s`.  At every box-valid display `n` (`0 ≤ n_u ≤ b_s`) of total `p + 2`, the
two-removal matrix `(h_j(n - e_u - e_v))_{u, v}`, with zero entries for invalid
removals, has at most one positive eigenvalue (`hWeight_removal_hyp`).

The proof is the paper's:

* `hjModel j α` is the softened table model `eq:laminar-table-model` at a general `j`
  as an `EdgeModel` (as `tmModel` in `TreeMarginal.lean` does for `j = H`): small and
  free cells on `[0, b_s]`, tree cells on `[-N, N]` containing every completion of a
  box-valid display (`hjBound`), vertex factors `α^{|L_v - κ_v|}` at nonroots and
  `2^{-(jA/H)|L_v - κ_v|}` at roots, unary tree factors
  `2^{-(jA/H) dist(z_t,[0,b_t])/b_t}`.
* Every large (free and tree) cell is summed at balance (`EdgeModel.good_WA` with
  `largeSet`); the remaining total is `p` (`hj_rem_total`), and the third clause of
  `Good` at the display `n` gives the removal signature on all coordinates, restricted to
  the small ones by `hyp_comp_inj`.
* At an unbalanced small display the balanced sum is a sum of two-view weights
  (`EdgeModel.WA_eval`: rows read `x_s`, columns read `b_s - y_s`, the convention R1 of
  `penalty`); it is continuous in `α`, and at `α = 0` the surviving profiles are exactly
  the completed tables of the free assignments, each of weight `2^{-jD/H}`
  (`hj_zero_sum`).  So the removal entries converge to `h_j` (`hj_tendsto`), invalid
  removals stay zero, and `Hyp` passes to the limit (`hyp_of_tendsto`).

The tree interval is chosen to contain every completion directly, instead of the
paper's `[-10 d b_t, 10 d b_t]` from `lem:forest`.
-/

namespace Cellcounting.Analysis

open Pseudocode Finset

namespace EdgeModel

variable {C Rw Cl : Type*} [Fintype C] [DecidableEq C] [Fintype Rw] [DecidableEq Rw]
  [Fintype Cl] [DecidableEq Cl]

variable (E : EdgeModel C Rw Cl)

/-- INTERNAL: the weight of a two-view table: row factors read the row-view table `XR`,
column factors the column-view table `XK`, cell factors `XR`. -/
noncomputable def weight2 (XR XK : C → ℤ) : ℝ :=
  (∏ r, E.φR r (∑ c ∈ univ.filter (fun c => E.row c = r), XR c)) *
    (∏ k, E.φK k (∑ c ∈ univ.filter (fun c => E.col c = k), XK c)) * ∏ c, E.ψ c (XR c)

/-- INTERNAL: on a valid display the laminar weight is the two-view weight of its
physical row and column readings. -/
theorem F_eq_weight2 (w : C × Bool → ℤ) (hw : Valid E.mE univ E.Rtot w) :
    E.F w = E.weight2 (fun c => E.lo c + w (c, true)) (fun c => E.hi c - w (c, false)) := by
  simp only [F, laminarWeight]
  rw [if_pos hw]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, weight2, mul_assoc]
  congr 1
  · refine Finset.prod_congr rfl fun r _ => ?_
    simp only [Gs, ψs]
    congr 1
    rw [sum_filter_view true (fun c => E.row c = r), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  congr 1
  · refine Finset.prod_congr rfl fun k _ => ?_
    simp only [Gs, ψs]
    congr 1
    rw [sum_filter_view false (fun c => E.col c = k), ← Finset.sum_sub_distrib]
  · refine Finset.prod_congr rfl fun c _ => ?_
    simp only [Gs, ψs, Finset.sum_singleton]

/-- INTERNAL: the balanced sum `WA A` at a valid display of the remaining total is the
sum of two-view weights over the balanced profiles of the summed cells. -/
theorem WA_eval (A : Finset C) (z : C × Bool → ℤ)
    (hz : Valid E.mE (actS A) (E.Rtot - ∑ c ∈ A, (E.hi c - E.lo c)) z) :
    E.WA A z = ∑ κ ∈ E.bal A, E.weight2 (fun c => E.lo c + (z + E.shift A κ) (c, true))
      (fun c => E.hi c - (z + E.shift A κ) (c, false)) := by
  classical
  obtain ⟨h0, h1, h2, h3⟩ := hz
  have hzA : ∀ c ∈ A, z (c, true) = 0 ∧ z (c, false) = 0 := fun c hc =>
    ⟨h2 _ (by simp [actS, hc]), h2 _ (by simp [actS, hc])⟩
  simp only [WA]
  rw [if_pos hzA]
  refine Finset.sum_congr rfl fun κ hκ => E.F_eq_weight2 _ ?_
  simp only [bal, Fintype.mem_piFinset] at hκ
  refine ⟨fun p => ?_, fun p _ => ?_, fun p hp => absurd (Finset.mem_univ p) hp, ?_⟩
  · obtain ⟨c, b⟩ := p
    have hk := hκ c
    by_cases hc : c ∈ A
    · simp only [hc, if_true, Finset.mem_Icc] at hk
      have := hzA c hc
      cases b <;> simp [shift, hc, this] <;> omega
    · have := h0 (c, b); simp [shift, hc, this]
  · obtain ⟨c, b⟩ := p
    have hk := hκ c
    by_cases hc : c ∈ A
    · simp only [hc, if_true, Finset.mem_Icc] at hk
      have := hzA c hc
      cases b <;> simp [shift, hc, this, mE] <;> omega
    · have := h1 (c, b) (by simp [actS, hc]); simpa [shift, hc] using this
  · simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, h3, sum_prod_bool]
    have : ∑ c, (E.shift A κ (c, true) + E.shift A κ (c, false)) =
        ∑ c ∈ A, (E.hi c - E.lo c) := by
      rw [← Finset.sum_filter_add_sum_filter_not univ (fun c => c ∈ A)]
      rw [Finset.sum_eq_zero (s := univ.filter fun c => c ∉ A) (fun c hc => by
        simp only [Finset.mem_filter] at hc; simp [shift, hc.2]), add_zero]
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact Finset.sum_congr rfl fun c hc => by simp [shift, hc]
    rw [this]; ring

end EdgeModel

open Filter Topology in
/-- INTERNAL: `Hyp` is closed under entrywise limits. -/
theorem hyp_of_tendsto {ι : Type*} [Fintype ι] {l : Filter ℝ} [l.NeBot]
    {Q : ℝ → ι → ι → ℝ} {Q0 : ι → ι → ℝ}
    (hT : ∀ i h, Tendsto (fun α => Q α i h) l (𝓝 (Q0 i h))) (hH : ∀ᶠ α in l, Hyp (Q α)) :
    Hyp Q0 := by
  have hqf : ∀ u w, Tendsto (fun α => qf (Q α) u w) l (𝓝 (qf Q0 u w)) := by
    intro u w
    unfold qf
    exact tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun h _ =>
      ((hT i h).const_mul (u i)).mul_const (w h)
  intro u w hu
  have hev : ∀ᶠ α in l, 0 < qf (Q α) u u := (hqf u u).eventually (lt_mem_nhds hu)
  exact le_of_tendsto_of_tendsto ((hqf u u).mul (hqf w w)) ((hqf u w).pow 2)
    (by filter_upwards [hH, hev] with α h1 h2 using h1 u w h2)

section hjModel

variable (I : Instance) (ε δ : ℚ)

/-- INTERNAL: the penalty rate `j A / H` of `eq:laminar-table-model`. -/
noncomputable def hjRate (j : ℕ) : ℝ := (j : ℝ) * (AParam I ε δ : ℝ) / (HParam I ε δ : ℝ)

/-- INTERNAL: the rate `jA/H` is nonnegative. -/
theorem hjRate_nonneg (j : ℕ) : 0 ≤ hjRate I ε δ j := by unfold hjRate; positivity

/-- INTERNAL: the vertex base: `2^{-jA/H}` at a root, `α` at a nonroot vertex. -/
noncomputable def hjVBase (j : ℕ) (α : ℝ) (v : ℕ) : ℝ :=
  if v ∈ roots I ε δ then (2 : ℝ) ^ (-hjRate I ε δ j) else α

/-- INTERNAL: the vertex factor `base^{|L_v - κ_v|}`. -/
noncomputable def hjVf (j : ℕ) (α : ℝ) (v : ℕ) (s : ℤ) : ℝ :=
  hjVBase I ε δ j α v ^ (|s - tmMargZ I v|).toNat

/-- INTERNAL: the unary tree factor `2^{-(jA/H) dist(s, [0, b_t]) / b_t}`. -/
noncomputable def hjTreePsi (j : ℕ) (t : ℕ) (s : ℤ) : ℝ :=
  (2 : ℝ) ^ (-(hjRate I ε δ j * (((boxDist (s : ℚ) ((treeAt I ε δ t).2.2 : ℚ) /
    ((treeAt I ε δ t).2.2 : ℚ)) : ℚ) : ℝ)))

/-- INTERNAL: the cell factors: `1` on small and free cells, `hjTreePsi` on tree cells. -/
noncomputable def hjPsi (j : ℕ) : TmCell I ε δ → ℤ → ℝ
  | .inr (.inr t) => hjTreePsi I ε δ j t
  | _ => fun _ => 1

/-- INTERNAL: the box-valid (row view, column view, free) displays. -/
noncomputable def dispBox : Finset ((Fin (nSmall I ε δ) → ℕ) × (Fin (nSmall I ε δ) → ℕ) ×
    (Fin (nFree I ε δ) → ℕ)) :=
  smallBox I ε δ ×ˢ smallBox I ε δ ×ˢ freeBox I ε δ

/-- INTERNAL: the tree completion of a display. -/
noncomputable def dispTree (q : (Fin (nSmall I ε δ) → ℕ) × (Fin (nSmall I ε δ) → ℕ) ×
    (Fin (nFree I ε δ) → ℕ)) : ℕ → ℚ :=
  (treeValues I ε δ (extendN q.1) (extendN q.2.1) (extendQ q.2.2)).2

/-- INTERNAL: a tree interval `[-N, N]` strictly containing every completion of a
box-valid display (replaces `[-10 d b_t, 10 d b_t]` of `lem:forest`). -/
noncomputable def hjBound : ℤ :=
  ⌈∑ q ∈ dispBox I ε δ, ∑ t ∈ range (forest I ε δ).tree.length, |dispTree I ε δ q t|⌉ + 1

/-- INTERNAL: lower ends: `0` for small and free cells, `-N` for tree cells. -/
noncomputable def hjLo : TmCell I ε δ → ℤ
  | .inr (.inr _) => -hjBound I ε δ
  | _ => 0

/-- INTERNAL: upper ends: `b_s` for small and free cells, `N` for tree cells. -/
noncomputable def hjHi : TmCell I ε δ → ℤ
  | .inr (.inr _) => hjBound I ε δ
  | c => (tmEntry I ε δ c).2.2

/-- INTERNAL: the `α`-softened table model `eq:laminar-table-model` at a general `j`.
TEXLINE: sections/integer-signatures.tex:337-385 -/
noncomputable def hjModel (j : ℕ) (α : ℝ) :
    EdgeModel (TmCell I ε δ) (Fin (I.m + I.n)) (Fin (I.m + I.n)) where
  row := tmRow I ε δ
  col := tmCol I ε δ
  lo := hjLo I ε δ
  hi := hjHi I ε δ
  φR := fun r s => if (r : ℕ) < I.m then hjVf I ε δ j α r s else 1
  φK := fun r s => if I.m ≤ (r : ℕ) then hjVf I ε δ j α r s else 1
  ψ := hjPsi I ε δ j

/-- INTERNAL: positivity of the vertex base for `α > 0`. -/
theorem hjVBase_pos (j : ℕ) {α : ℝ} (hα : 0 < α) (v : ℕ) : 0 < hjVBase I ε δ j α v := by
  unfold hjVBase; split_ifs
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · exact hα

/-- INTERNAL: the vertex base is at most one for `α ≤ 1`. -/
theorem hjVBase_le_one (j : ℕ) {α : ℝ} (hα : α ≤ 1) (v : ℕ) : hjVBase I ε δ j α v ≤ 1 := by
  unfold hjVBase; split_ifs
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by have := hjRate_nonneg I ε δ j; linarith)
  · exact hα

/-- INTERNAL: log-concavity of the tree factor. -/
theorem hjTreePsi_lc (j : ℕ) (t : ℕ) (s : ℤ) :
    hjTreePsi I ε δ j t (s - 1) * hjTreePsi I ε δ j t (s + 1) ≤ hjTreePsi I ε δ j t s ^ 2 := by
  unfold hjTreePsi
  rw [← Real.rpow_add (by norm_num), sq, ← Real.rpow_add (by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hb : (0 : ℚ) ≤ ((treeAt I ε δ t).2.2 : ℚ) := by positivity
  have hc := tm_boxDist_convex (s : ℚ) _ hb
  have key : (boxDist (s : ℚ) ((treeAt I ε δ t).2.2 : ℚ) / ((treeAt I ε δ t).2.2 : ℚ)) * 2 ≤
      (boxDist ((s - 1 : ℤ) : ℚ) ((treeAt I ε δ t).2.2 : ℚ) / ((treeAt I ε δ t).2.2 : ℚ)) +
      (boxDist ((s + 1 : ℤ) : ℚ) ((treeAt I ε δ t).2.2 : ℚ) / ((treeAt I ε δ t).2.2 : ℚ)) := by
    push_cast
    rw [← add_div, mul_comm, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hb
  have key' := (Rat.cast_le (K := ℝ)).2 key
  push_cast at key' ⊢
  have hr := hjRate_nonneg I ε δ j
  nlinarith [mul_le_mul_of_nonneg_left key' hr]

/-- INTERNAL: `1 ≤ N`. -/
theorem hjBound_pos : 1 ≤ hjBound I ε δ := by
  unfold hjBound
  have : (0 : ℚ) ≤ ∑ q ∈ dispBox I ε δ, ∑ t ∈ range (forest I ε δ).tree.length,
      |dispTree I ε δ q t| := by positivity
  have := Int.ceil_nonneg this
  omega

/-- INTERNAL: for `0 < α ≤ 1` the model has positive log-concave factors and positive widths.
TEXLINE: sections/integer-signatures.tex:380-385 -/
theorem hjModel_hyps (j : ℕ) {α : ℝ} (h0 : 0 < α) (h1 : α ≤ 1) : (hjModel I ε δ j α).Hyps where
  width c := by
    rcases c with s | f | t
    · show (0 : ℤ) < ((tmEntry I ε δ (Sum.inl s)).2.2 : ℤ)
      exact_mod_cast tmEntry_pos (Sum.inl s)
    · show (0 : ℤ) < ((tmEntry I ε δ (Sum.inr (Sum.inl f))).2.2 : ℤ)
      exact_mod_cast tmEntry_pos (Sum.inr (Sum.inl f))
    · show -hjBound I ε δ < hjBound I ε δ
      have := hjBound_pos I ε δ; omega
  φR_pos r s := by
    simp only [hjModel]; split_ifs
    · exact pow_pos (hjVBase_pos I ε δ j h0 _) _
    · exact one_pos
  φK_pos r s := by
    simp only [hjModel]; split_ifs
    · exact pow_pos (hjVBase_pos I ε δ j h0 _) _
    · exact one_pos
  ψ_pos c s := by
    rcases c with s | f | t
    · exact one_pos
    · exact one_pos
    · exact Real.rpow_pos_of_pos (by norm_num) _
  φR_lc r s := by
    simp only [hjModel]; split_ifs
    · exact tm_pow_abs_lc (hjVBase_pos I ε δ j h0 _) (hjVBase_le_one I ε δ j h1 _) _ _
    · norm_num
  φK_lc r s := by
    simp only [hjModel]; split_ifs
    · exact tm_pow_abs_lc (hjVBase_pos I ε δ j h0 _) (hjVBase_le_one I ε δ j h1 _) _ _
    · norm_num
  ψ_lc c s := by
    rcases c with s | f | t
    · show (1 : ℝ) * 1 ≤ 1 ^ 2; norm_num
    · show (1 : ℝ) * 1 ≤ 1 ^ 2; norm_num
    · exact hjTreePsi_lc I ε δ j _ _

end hjModel

section hjLoads

variable (I : Instance) (ε δ : ℚ)

/-- INTERNAL: the physical line sum of vertex `v` for a two-view table: rows read `XR`,
columns read `XK`. -/
noncomputable def hjLoad (XR XK : TmCell I ε δ → ℤ) (v : ℕ) : ℤ :=
  ∑ c, ((if (tmEntry I ε δ c).1 = v then XR c else 0) +
    (if I.m + (tmEntry I ε δ c).2.1 = v then XK c else 0))

/-- INTERNAL: the row group sum of a row vertex is its line sum. -/
theorem hj_rowSum_eq (XR XK : TmCell I ε δ → ℤ) (r : Fin (I.m + I.n)) (hr : (r : ℕ) < I.m) :
    ∑ c ∈ univ.filter (fun c => tmRow I ε δ c = r), XR c = hjLoad I ε δ XR XK r := by
  rw [sum_filter]; unfold hjLoad
  refine sum_congr rfl fun c _ => ?_
  have h1 : (tmRow I ε δ c = r) ↔ (tmEntry I ε δ c).1 = r := by
    simp [tmRow, Fin.ext_iff]
  have h2 : ¬ I.m + (tmEntry I ε δ c).2.1 = r := by omega
  by_cases h : (tmEntry I ε δ c).1 = (r : ℕ)
  · rw [if_pos (h1.2 h), if_pos h, if_neg h2, add_zero]
  · rw [if_neg (fun h' => h (h1.1 h')), if_neg h, if_neg h2, add_zero]

/-- INTERNAL: the column group sum of a column vertex is its line sum. -/
theorem hj_colSum_eq (XR XK : TmCell I ε δ → ℤ) (r : Fin (I.m + I.n)) (hr : I.m ≤ (r : ℕ)) :
    ∑ c ∈ univ.filter (fun c => tmCol I ε δ c = r), XK c = hjLoad I ε δ XR XK r := by
  rw [sum_filter]; unfold hjLoad
  refine sum_congr rfl fun c _ => ?_
  have h1 : (tmCol I ε δ c = r) ↔ I.m + (tmEntry I ε δ c).2.1 = r := by
    simp [tmCol, Fin.ext_iff]
  have h2 : ¬ (tmEntry I ε δ c).1 = r := by have := (tmEntry_lt c).1; omega
  by_cases h : I.m + (tmEntry I ε δ c).2.1 = (r : ℕ)
  · rw [if_pos (h1.2 h), if_pos h, if_neg h2, zero_add]
  · rw [if_neg (fun h' => h (h1.1 h')), if_neg h, if_neg h2, add_zero]

/-- INTERNAL: the two-view model weight is the product of vertex factors of the line
sums and the cell factors. -/
theorem hjModel_weight2 (j : ℕ) (α : ℝ) (XR XK : TmCell I ε δ → ℤ) :
    (hjModel I ε δ j α).weight2 XR XK =
      (∏ v : Fin (I.m + I.n), hjVf I ε δ j α v (hjLoad I ε δ XR XK v)) *
        ∏ c, hjPsi I ε δ j c (XR c) := by
  unfold EdgeModel.weight2
  congr 1
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun r _ => ?_
  simp only [hjModel]
  by_cases hr : (r : ℕ) < I.m
  · rw [if_pos hr, if_neg (by omega), mul_one]; congr 1
    exact hj_rowSum_eq I ε δ XR XK r hr
  · rw [if_neg hr, if_pos (by omega), one_mul]; congr 1
    exact hj_colSum_eq I ε δ XR XK r (by omega)

/-- INTERNAL: the line sums of a two-view table whose small views are `x`, `b - y` and
whose free part is `zf` are the leaf-elimination incident sums with base load
`baseLoad x y zf`. -/
theorem hjLoad_eq (x y : Fin (nSmall I ε δ) → ℕ) (hyb : ∀ s, y s ≤ smallB I ε δ s)
    (zf : Fin (nFree I ε δ) → ℕ) (XR XK : TmCell I ε δ → ℤ)
    (hx : ∀ s, XR (Sum.inl s) = x s) (hy : ∀ s, XK (Sum.inl s) = (smallB I ε δ s : ℤ) - y s)
    (hzR : ∀ f, XR (Sum.inr (Sum.inl f)) = zf f) (hzK : ∀ f, XK (Sum.inr (Sum.inl f)) = zf f)
    (hT : ∀ t, XK (Sum.inr (Sum.inr t)) = XR (Sum.inr (Sum.inr t))) (v : ℕ) :
    ((hjLoad I ε δ XR XK v : ℤ) : ℚ) =
      tLoadG (fun t => (treeAt I ε δ t).1) (fun t => I.m + (treeAt I ε δ t).2.1)
        (forest I ε δ).tree.length
        (baseLoad I ε δ (extendN x) (extendN y) (extendQ zf)) (tmTreeVec I ε δ XR) v := by
  unfold hjLoad tLoadG baseLoad
  push_cast
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Finset.sum_range, Finset.sum_range,
    Finset.sum_range, add_assoc]
  congr 1
  · refine sum_congr rfl fun s _ => ?_
    have e1 : extendN x s = x s := by simp [extendN]
    have e2 : extendN y s = y s := by simp [extendN]
    have hle := hyb s
    rw [e1, e2, hx, hy]
    unfold smallB at hle ⊢
    simp only [tmEntry]
    push_cast [hle]
    rfl
  congr 1
  · refine sum_congr rfl fun f _ => ?_
    have e1 : extendQ zf f = zf f := by simp [extendQ]
    rw [e1, hzR, hzK]; rfl
  · refine sum_congr rfl fun t _ => ?_
    have e1 : tmTreeVec I ε δ XR t = (XR (Sum.inr (Sum.inr t)) : ℚ) := by simp [tmTreeVec]
    rw [e1, hT]; rfl

end hjLoads

section hjZero

variable (I : Instance) (ε δ : ℚ)

/-- INTERNAL: the large (free and tree) cells, summed at balance. -/
noncomputable def largeSet : Finset (TmCell I ε δ) := univ.filter fun c => c.isRight = true

/-- INTERNAL: the balanced profiles of the large cells (`EdgeModel.bal largeSet`). -/
noncomputable def hjBal : Finset (TmCell I ε δ → ℤ) :=
  Fintype.piFinset fun c => if c ∈ largeSet I ε δ then Icc 0 (hjHi I ε δ c - hjLo I ε δ c) else {0}

/-- INTERNAL: the row-view table: small row views `x`, large cells `lo + κ`. -/
noncomputable def xrOf (x : Fin (nSmall I ε δ) → ℕ) (κ : TmCell I ε δ → ℤ) : TmCell I ε δ → ℤ :=
  Sum.elim (fun s => (x s : ℤ)) (fun c => hjLo I ε δ (Sum.inr c) + κ (Sum.inr c))

/-- INTERNAL: the column-view table: small cells `b_s - y_s`, large cells `lo + κ`. -/
noncomputable def xkOf (y : Fin (nSmall I ε δ) → ℕ) (κ : TmCell I ε δ → ℤ) : TmCell I ε δ → ℤ :=
  Sum.elim (fun s => (smallB I ε δ s : ℤ) - y s) (fun c => hjLo I ε δ (Sum.inr c) + κ (Sum.inr c))

/-- INTERNAL: the summand of the balanced sum at profile `κ`. -/
noncomputable def hjWt (j : ℕ) (α : ℝ) (x y : Fin (nSmall I ε δ) → ℕ) (κ : TmCell I ε δ → ℤ) : ℝ :=
  (∏ v : Fin (I.m + I.n), hjVf I ε δ j α v (hjLoad I ε δ (xrOf I ε δ x κ) (xkOf I ε δ y κ) v)) *
    ∏ c, hjPsi I ε δ j c (xrOf I ε δ x κ c)

variable (x y : Fin (nSmall I ε δ) → ℕ)

/-- INTERNAL: the tree completion of `(x, y, zf)`. -/
noncomputable def hjTV (zf : Fin (nFree I ε δ) → ℕ) : (ℕ → ℚ) × (ℕ → ℚ) :=
  treeValues I ε δ (extendN x) (extendN y) (extendQ zf)

/-- INTERNAL: the balanced profile of the completed table of a free assignment. -/
noncomputable def κOf (zf : Fin (nFree I ε δ) → ℕ) : TmCell I ε δ → ℤ :=
  Sum.elim (fun _ => 0) (Sum.elim (fun f => (zf f : ℤ))
    (fun t => ⌊(hjTV I ε δ x y zf).2 t⌋ + hjBound I ε δ))

/-- INTERNAL: tree completions of integral displays are integers (`lem:forest`). -/
theorem hjTV_int (zf : Fin (nFree I ε δ) → ℕ) (t : ℕ) :
    (((⌊(hjTV I ε δ x y zf).2 t⌋ : ℤ)) : ℚ) = (hjTV I ε δ x y zf).2 t := by
  have hz : extendQ zf = fun k => ((extendN zf k : ℕ) : ℚ) := by
    funext k; unfold extendQ extendN; split_ifs <;> simp
  have := (treeValues_fold_int I ε δ (elimOrder I ε δ) (baseLoad I ε δ (extendN x) (extendN y)
    (fun k => ((extendN zf k : ℕ) : ℚ)), fun _ => 0)
    (fun v => baseLoad_int I ε δ _ _ _ v) (fun _ => zero_mem _)).2 t
  obtain ⟨k, hk⟩ := this
  have e : (hjTV I ε δ x y zf).2 t = k := by
    have hk' : (k : ℚ) = _ := hk
    rw [hk']; simp only [hjTV, treeValues, hz]
  rw [e, Int.floor_intCast]

variable {I ε δ x y}

/-- INTERNAL: every completion of a box-valid display lies strictly inside `[-N, N]`. -/
theorem hj_abs_tree_lt (hx : ∀ s, x s ≤ smallB I ε δ s) (hy : ∀ s, y s ≤ smallB I ε δ s)
    (zf : Fin (nFree I ε δ) → ℕ) (hzf : zf ∈ freeBox I ε δ) (t : ℕ)
    (ht : t < (forest I ε δ).tree.length) :
    |⌊(hjTV I ε δ x y zf).2 t⌋| < hjBound I ε δ := by
  have hq : (x, y, zf) ∈ dispBox I ε δ := by
    simp only [dispBox, smallBox, mem_product, Fintype.mem_piFinset, mem_range]
    exact ⟨fun s => by have := hx s; omega, fun s => by have := hy s; omega, hzf⟩
  have h1 : |dispTree I ε δ (x, y, zf) t| ≤
      ∑ t ∈ range (forest I ε δ).tree.length, |dispTree I ε δ (x, y, zf) t| :=
    single_le_sum (f := fun t => |dispTree I ε δ (x, y, zf) t|) (fun _ _ => abs_nonneg _)
      (mem_range.2 ht)
  have h2 : ∑ t ∈ range (forest I ε δ).tree.length, |dispTree I ε δ (x, y, zf) t| ≤
      ∑ q ∈ dispBox I ε δ, ∑ t ∈ range (forest I ε δ).tree.length, |dispTree I ε δ q t| :=
    single_le_sum (f := fun q => ∑ t ∈ range (forest I ε δ).tree.length, |dispTree I ε δ q t|)
      (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) hq
  have h3 := Int.le_ceil (∑ q ∈ dispBox I ε δ, ∑ t ∈ range (forest I ε δ).tree.length,
    |dispTree I ε δ q t|)
  have h4 : ((|⌊(hjTV I ε δ x y zf).2 t⌋| : ℤ) : ℚ) ≤ (⌈∑ q ∈ dispBox I ε δ,
      ∑ t ∈ range (forest I ε δ).tree.length, |dispTree I ε δ q t|⌉ : ℚ) := by
    push_cast; rw [hjTV_int]
    have : dispTree I ε δ (x, y, zf) t = (hjTV I ε δ x y zf).2 t := rfl
    rw [← this]; linarith
  have h5 := Int.cast_le.1 h4
  unfold hjBound; omega

end hjZero

section hjZero2

variable {I : Instance} {ε δ : ℚ} {x y : Fin (nSmall I ε δ) → ℕ}

/-- INTERNAL: the tree part of the completed table is the completion. -/
theorem hj_treeVec_κOf (zf : Fin (nFree I ε δ) → ℕ) (t : ℕ)
    (ht : t < (forest I ε δ).tree.length) :
    tmTreeVec I ε δ (xrOf I ε δ x (κOf I ε δ x y zf)) t = (hjTV I ε δ x y zf).2 t := by
  simp only [tmTreeVec, dif_pos ht, xrOf, κOf, Sum.elim_inr, hjLo]
  rw [show -hjBound I ε δ + (⌊(hjTV I ε δ x y zf).2 t⌋ + hjBound I ε δ) =
    ⌊(hjTV I ε δ x y zf).2 t⌋ by ring]
  exact hjTV_int I ε δ x y zf t

/-- INTERNAL: the line sums of the completed table are the leaf-elimination incident sums. -/
theorem hj_load_κOf (hy : ∀ s, y s ≤ smallB I ε δ s) (zf : Fin (nFree I ε δ) → ℕ) (v : ℕ) :
    ((hjLoad I ε δ (xrOf I ε δ x (κOf I ε δ x y zf)) (xkOf I ε δ y (κOf I ε δ x y zf)) v : ℤ) : ℚ) =
      tLoadG (fun t => (treeAt I ε δ t).1) (fun t => I.m + (treeAt I ε δ t).2.1)
        (forest I ε δ).tree.length
        (baseLoad I ε δ (extendN x) (extendN y) (extendQ zf))
        (hjTV I ε δ x y zf).2 v := by
  rw [hjLoad_eq I ε δ x y hy zf (xrOf I ε δ x (κOf I ε δ x y zf))
    (xkOf I ε δ y (κOf I ε δ x y zf)) (fun _ => rfl) (fun _ => rfl)
    (fun f => by simp [xrOf, κOf, hjLo]) (fun f => by simp [xkOf, κOf, hjLo]) (fun _ => rfl) v]
  exact tm_tLoadG_congr (fun t ht => hj_treeVec_κOf zf t ht) v

/-- INTERNAL: the completed table satisfies every nonroot equation exactly. -/
theorem hj_nonroot (hy : ∀ s, y s ≤ smallB I ε δ s) (zf : Fin (nFree I ε δ) → ℕ) (v : ℕ)
    (hv : v < I.m + I.n) (hr : v ∉ roots I ε δ) :
    hjLoad I ε δ (xrOf I ε δ x (κOf I ε δ x y zf)) (xkOf I ε δ y (κOf I ε δ x y zf)) v =
      tmMargZ I v := by
  have hval := (pseudo_elimOrder_valid I ε δ).1
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 (elim_cover I ε δ v hv hr)
  have h1 := hj_load_κOf (x := x) hy zf e.1
  rw [show (hjTV I ε δ x y zf).2 = (tvFin (fun t => (treeAt I ε δ t).1)
      (fun t => I.m + (treeAt I ε δ t).2.1) (margin I)
      (baseLoad I ε δ (extendN x) (extendN y) (extendQ zf)) (elimOrder I ε δ)).2 from rfl,
    tvFin_nonroot hval _ e he, tm_margin_eq_margZ] at h1
  exact_mod_cast h1

/-- INTERNAL: at a root, the line sum of the completed table is the final leaf-elimination load. -/
theorem hj_root (hy : ∀ s, y s ≤ smallB I ε δ s) (zf : Fin (nFree I ε δ) → ℕ) (r : ℕ)
    (hr : r ∈ roots I ε δ) :
    ((hjLoad I ε δ (xrOf I ε δ x (κOf I ε δ x y zf)) (xkOf I ε δ y (κOf I ε δ x y zf)) r : ℤ) : ℚ) =
      (hjTV I ε δ x y zf).1 r := by
  have hval := (pseudo_elimOrder_valid I ε δ).1
  rw [hj_load_κOf hy zf r]
  simp only [hjTV]
  rw [treeValues_eq_tvFin, tvFin_root hval _ r ((pseudo_elimOrder_valid I ε δ).2 r hr)]

/-- INTERNAL: `(2^{-c})^{|z|} = 2^{-c |z|}`. -/
theorem hj_pow_abs (c : ℝ) (z : ℤ) :
    ((2 : ℝ) ^ (-c)) ^ (|z|).toNat = (2 : ℝ) ^ (-(c * ((|z| : ℤ) : ℝ))) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  have : (((|z|).toNat : ℕ) : ℝ) = ((|z| : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (abs_nonneg z)
  rw [this]; ring

/-- INTERNAL: at `α = 0` the vertex factors of the completed table are the root penalties. -/
theorem hj_vertex_prod_zero (hy : ∀ s, y s ≤ smallB I ε δ s) (j : ℕ)
    (zf : Fin (nFree I ε δ) → ℕ) :
    ∏ v : Fin (I.m + I.n), hjVf I ε δ j 0 v
        (hjLoad I ε δ (xrOf I ε δ x (κOf I ε δ x y zf)) (xkOf I ε δ y (κOf I ε δ x y zf)) v) =
      ∏ r ∈ (roots I ε δ).toFinset, (2 : ℝ) ^ (-(hjRate I ε δ j *
        ((|(hjTV I ε δ x y zf).1 r - margin I r| : ℚ) : ℝ))) := by
  rw [Fin.prod_univ_eq_prod_range (fun v => hjVf I ε δ j 0 v
    (hjLoad I ε δ (xrOf I ε δ x (κOf I ε δ x y zf)) (xkOf I ε δ y (κOf I ε δ x y zf)) v))]
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
    simp only [hjVf, hjVBase, if_pos hr]
    rw [hj_pow_abs]
    congr 3
    have h1 := hj_root (x := x) hy zf v hr
    rw [tm_margin_eq_margZ, ← h1]
    push_cast; rfl
  · rw [if_neg hr]
    simp only [hjVf, hj_nonroot hy zf v (mem_range.1 hv) hr, sub_self, abs_zero,
      Int.toNat_zero, pow_zero]

/-- INTERNAL: the cell factors of the completed table are the tree penalties. -/
theorem hj_psi_prod (j : ℕ) (zf : Fin (nFree I ε δ) → ℕ) :
    ∏ c, hjPsi I ε δ j c (xrOf I ε δ x (κOf I ε δ x y zf) c) =
      ∏ t ∈ range (forest I ε δ).tree.length, (2 : ℝ) ^ (-(hjRate I ε δ j *
        (((boxDist ((hjTV I ε δ x y zf).2 t) ((treeAt I ε δ t).2.2 : ℚ) /
          ((treeAt I ε δ t).2.2 : ℚ)) : ℚ) : ℝ))) := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [hjPsi, prod_const_one, one_mul]
  rw [Finset.prod_range]
  refine prod_congr rfl fun t _ => ?_
  simp only [hjTreePsi]
  have := hj_treeVec_κOf (x := x) (y := y) zf t t.2
  simp only [tmTreeVec, dif_pos t.2, Fin.eta] at this
  rw [this]

/-- INTERNAL: the summand `2^{-jD/H}` of `h_j` factors into root and tree penalties. -/
theorem hj_pen_split (j : ℕ) (zf : Fin (nFree I ε δ) → ℕ) :
    (2 : ℝ) ^ (-((j : ℝ) * (penalty I ε δ (extendN x) (extendN y) (extendQ zf) : ℝ) /
        (HParam I ε δ : ℝ))) =
      (∏ r ∈ (roots I ε δ).toFinset, (2 : ℝ) ^ (-(hjRate I ε δ j *
        ((|(hjTV I ε δ x y zf).1 r - margin I r| : ℚ) : ℝ)))) *
      ∏ t ∈ range (forest I ε δ).tree.length, (2 : ℝ) ^ (-(hjRate I ε δ j *
        (((boxDist ((hjTV I ε δ x y zf).2 t) ((treeAt I ε δ t).2.2 : ℚ) /
          ((treeAt I ε δ t).2.2 : ℚ)) : ℚ) : ℝ))) := by
  rw [← Real.rpow_sum_of_pos (by norm_num), ← Real.rpow_sum_of_pos (by norm_num),
    ← Real.rpow_add (by norm_num)]
  congr 1
  unfold penalty
  rw [← List.sum_toFinset _ (roots_nodup I ε δ)]
  simp only [hjRate, hjTV]
  push_cast
  rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

end hjZero2

section hjZero3

variable {I : Instance} {ε δ : ℚ} {x y : Fin (nSmall I ε δ) → ℕ}

/-- INTERNAL: at `α = 0` the balanced sum is `h_j(x, y)`: the surviving profiles are
exactly the completed tables of the free assignments, each with weight `2^{-jD/H}`.
TEXLINE: sections/integer-signatures.tex:387-396 -/
theorem hj_zero_sum (hx : ∀ s, x s ≤ smallB I ε δ s) (hy : ∀ s, y s ≤ smallB I ε δ s)
    (j : ℕ) :
    ∑ κ ∈ hjBal I ε δ, hjWt I ε δ j 0 x y κ = hWeight I ε δ j (extendN x) (extendN y) := by
  symm
  unfold hWeight
  refine Finset.sum_bij_ne_zero (fun zf _ _ => κOf I ε δ x y zf) ?_ ?_ ?_ ?_
  · intro zf hzf _
    simp only [hjBal, Fintype.mem_piFinset]
    rintro (s | f | t)
    · simp [largeSet, κOf]
    · have h1 := Fintype.mem_piFinset.1 hzf f
      simp only [mem_range] at h1
      simp [largeSet, κOf, hjHi, hjLo, tmEntry]; omega
    · have := hj_abs_tree_lt hx hy zf hzf t t.2
      rw [abs_lt] at this
      simp [largeSet, κOf, hjHi, hjLo]; omega
  · intro z1 _ _ z2 _ _ h
    funext f
    have := congrFun h (Sum.inr (Sum.inl f))
    simp only [κOf, Sum.elim_inr, Sum.elim_inl] at this
    exact_mod_cast this
  · intro κ hκ hw
    simp only [hjBal, Fintype.mem_piFinset] at hκ
    have hL : ∀ v, v < I.m + I.n → v ∉ roots I ε δ →
        hjLoad I ε δ (xrOf I ε δ x κ) (xkOf I ε δ y κ) v = tmMargZ I v := by
      intro v hvV hr
      have h := prod_ne_zero_iff.1 (mul_ne_zero_iff.1 hw).1 ⟨v, hvV⟩ (mem_univ _)
      simp only [hjVf, hjVBase, if_neg hr] at h
      have h0 : (|hjLoad I ε δ (xrOf I ε δ x κ) (xkOf I ε δ y κ) v - tmMargZ I v|).toNat = 0 := by
        by_contra hn; exact h (zero_pow hn)
      rw [Int.toNat_eq_zero, abs_nonpos_iff, sub_eq_zero] at h0
      exact h0
    set zf : Fin (nFree I ε δ) → ℕ := fun f => (κ (Sum.inr (Sum.inl f))).toNat with hzfdef
    have hfree : ∀ f, κ (Sum.inr (Sum.inl f)) = (zf f : ℤ) := fun f => by
      have := hκ (Sum.inr (Sum.inl f))
      simp [largeSet] at this
      simp only [hzfdef]; omega
    have hzf : zf ∈ freeBox I ε δ := by
      simp only [freeBox, Fintype.mem_piFinset, mem_range]
      intro f
      have := hκ (Sum.inr (Sum.inl f))
      simp [largeSet, hjHi, hjLo, tmEntry] at this
      have := hfree f
      omega
    refine ⟨zf, hzf, (Real.rpow_pos_of_pos (by norm_num) _).ne', ?_⟩
    have hval := (pseudo_elimOrder_valid I ε δ).1
    have huniq := tvFin_unique (marg := margin I) hval
      (baseLoad I ε δ (extendN x) (extendN y) (extendQ zf)) (tmTreeVec I ε δ (xrOf I ε δ x κ))
      (fun e he => by
        rw [← hjLoad_eq I ε δ x y hy zf (xrOf I ε δ x κ) (xkOf I ε δ y κ) (fun _ => rfl)
          (fun _ => rfl) (fun f => by simp [xrOf, hjLo, hfree f])
          (fun f => by simp [xkOf, hjLo, hfree f]) (fun _ => rfl) e.1,
          hL e.1 (tm_elim_fst_lt I ε δ he) (tm_elim_fst_not_root I ε δ he), tm_margin_eq_margZ])
    funext c
    rcases c with s | f | t
    · have := hκ (Sum.inl s); simp [largeSet] at this; simp [κOf, this]
    · simp [κOf, hfree f]
    · have h := huniq t t.2
      simp only [tmTreeVec, dif_pos t.2, Fin.eta, xrOf, Sum.elim_inr, hjLo] at h
      simp only [κOf, Sum.elim_inr]
      have : (hjTV I ε δ x y zf).2 t = ((-hjBound I ε δ + κ (Sum.inr (Sum.inr t)) : ℤ) : ℚ) := by
        rw [h]; rfl
      rw [this, Int.floor_intCast]; ring
  · intro zf _ _
    rw [hjWt, hj_vertex_prod_zero hy, hj_psi_prod, hj_pen_split]

end hjZero3

section hjLimit

variable {I : Instance} {ε δ : ℚ}

/-- INTERNAL: the display with small row views `x`, small column views `y`, and zero on
the large cells (`(c, true)` is the `EdgeModel` row view). -/
def dispZ (x y : Fin (nSmall I ε δ) → ℕ) : TmCell I ε δ × Bool → ℤ := fun p =>
  Sum.elim (fun s => if p.2 then (x s : ℤ) else (y s : ℤ)) (fun _ => 0) p.1

/-- INTERNAL: `p = Σ_s b_s`. -/
theorem pSmall_eq_sum : pSmall I ε δ = ∑ s : Fin (nSmall I ε δ), smallB I ε δ s := by
  rw [Fin.sum_univ_eq_sum_range (fun s => smallB I ε δ s)]
  unfold pSmall smallB smallAt nSmall
  exact (sum_range_getD_eq (smallCells I ε δ) (fun e => e.2.2) (0, 0, 0)).symm

/-- INTERNAL: after summing the large cells the remaining total is `p`. -/
theorem hj_rem_total (j : ℕ) (α : ℝ) :
    (hjModel I ε δ j α).Rtot - ∑ c ∈ largeSet I ε δ,
      ((hjModel I ε δ j α).hi c - (hjModel I ε δ j α).lo c) = (pSmall I ε δ : ℤ) := by
  rw [pSmall_eq_sum]
  simp only [EdgeModel.Rtot, largeSet, Finset.sum_filter, Fintype.sum_sum_type, Sum.isRight_inl,
    Sum.isRight_inr, Bool.false_eq_true, if_false, if_true, Finset.sum_const_zero, zero_add]
  push_cast
  simp only [hjModel, hjHi, hjLo, tmEntry, smallB, sub_zero]
  ring

/-- INTERNAL: a box-valid small display is a valid display on the active (small) coordinates. -/
theorem hj_valid_dispZ (j : ℕ) (α : ℝ) (x y : Fin (nSmall I ε δ) → ℕ)
    (hx : ∀ s, x s ≤ smallB I ε δ s) (hy : ∀ s, y s ≤ smallB I ε δ s) (r : ℤ)
    (htot : ∑ s, ((x s : ℤ) + y s) = r) :
    Valid (hjModel I ε δ j α).mE (EdgeModel.actS (largeSet I ε δ)) r (dispZ x y) := by
  refine ⟨fun p => ?_, fun p hp => ?_, fun p hp => ?_, ?_⟩
  · obtain ⟨c, b⟩ := p
    rcases c with s | c <;> cases b <;> simp [dispZ]
  · obtain ⟨c, b⟩ := p
    rcases c with s | c
    · have h1 := hx s; have h2 := hy s
      cases b <;> simp [dispZ, EdgeModel.mE, hjModel, hjHi, hjLo, tmEntry] <;>
        unfold smallB at h1 h2 <;> omega
    · simp [EdgeModel.actS, largeSet] at hp
  · obtain ⟨c, b⟩ := p
    rcases c with s | c
    · simp [EdgeModel.actS, largeSet] at hp
    · simp [dispZ]
  · rw [EdgeModel.sum_prod_bool, Fintype.sum_sum_type]
    simp only [dispZ, Sum.elim_inl, Sum.elim_inr, if_true, Bool.false_eq_true, if_false,
      add_zero, Finset.sum_const_zero]
    exact htot

/-- INTERNAL: the balanced sum at a small display, as the sum of `hjWt` over balanced profiles. -/
theorem hj_WA_eq (j : ℕ) (α : ℝ) (x y : Fin (nSmall I ε δ) → ℕ)
    (hx : ∀ s, x s ≤ smallB I ε δ s) (hy : ∀ s, y s ≤ smallB I ε δ s)
    (htot : ∑ s, ((x s : ℤ) + y s) = pSmall I ε δ) :
    (hjModel I ε δ j α).WA (largeSet I ε δ) (dispZ x y) =
      ∑ κ ∈ hjBal I ε δ, hjWt I ε δ j α x y κ := by
  rw [EdgeModel.WA_eval _ _ _ (hj_valid_dispZ j α x y hx hy _
    (by rw [htot, hj_rem_total]))]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [hjWt, ← hjModel_weight2]
  congr 1 <;> funext c <;> rcases c with s | f | t <;>
    simp [EdgeModel.shift, dispZ, xrOf, xkOf, hjModel, largeSet, hjHi, hjLo, tmEntry, smallB] <;>
    ring

open Filter Topology in
/-- INTERNAL: as `α ↓ 0` the balanced sum at a box-valid small display of total `p`
converges to `h_j(x, y)`.
TEXLINE: sections/integer-signatures.tex:387-396 -/
theorem hj_tendsto (j : ℕ) (x y : Fin (nSmall I ε δ) → ℕ)
    (hx : ∀ s, x s ≤ smallB I ε δ s) (hy : ∀ s, y s ≤ smallB I ε δ s)
    (htot : ∑ s, ((x s : ℤ) + y s) = pSmall I ε δ) :
    Tendsto (fun α => (hjModel I ε δ j α).WA (largeSet I ε δ) (dispZ x y)) (𝓝[>] 0)
      (𝓝 (hWeight I ε δ j (extendN x) (extendN y))) := by
  simp only [hj_WA_eq j _ x y hx hy htot]
  rw [← hj_zero_sum hx hy j]
  have hc : Continuous fun α => ∑ κ ∈ hjBal I ε δ, hjWt I ε δ j α x y κ := by
    refine continuous_finset_sum _ fun κ _ => ?_
    unfold hjWt
    refine Continuous.mul (continuous_finset_prod _ fun v _ => ?_) continuous_const
    unfold hjVf hjVBase
    exact (continuous_const.if_const _ continuous_id).pow _
  exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds

end hjLimit

section final

variable {I : Instance} {ε δ : ℚ}

/-- INTERNAL: the display `n - e_u - e_v` (truncated at zero; only used where valid).
TEXLINE: sections/integer-signatures.tex:20-35 -/
def remDisp {N : ℕ} (n : Fin N × Bool → ℕ) (u v : Fin N × Bool) : Fin N × Bool → ℕ :=
  fun w => n w - (if w = u then 1 else 0) - (if w = v then 1 else 0)

/-- INTERNAL: at a valid removal, `remDisp` is the integer display `n - e_u - e_v`. -/
theorem remDisp_cast {N : ℕ} (n : Fin N × Bool → ℕ) (u v : Fin N × Bool)
    (h : 1 ≤ n u ∧ 1 ≤ n v ∧ (u = v → 2 ≤ n u)) (w : Fin N × Bool) :
    ((remDisp n u v w : ℕ) : ℤ) = n w - (if w = u then 1 else 0) - (if w = v then 1 else 0) := by
  unfold remDisp
  obtain ⟨h1, h2, h3⟩ := h
  by_cases hu : w = u <;> by_cases hv : w = v
  · subst hu; subst hv; have := h3 rfl; simp; omega
  · subst hu; simp [hv]; omega
  · subst hv; simp [hu]; omega
  · simp [hu, hv]

/-- INTERNAL: the small views as `EdgeModel` coordinates: `(s, false)` (row view `x_s`)
is the `EdgeModel` row view `(inl s, true)`. -/
def smallEmb (w : Fin (nSmall I ε δ) × Bool) : TmCell I ε δ × Bool := (Sum.inl w.1, !w.2)

/-- INTERNAL: the embedding of small views is injective. -/
theorem smallEmb_inj : Function.Injective (smallEmb (I := I) (ε := ε) (δ := δ)) := by
  rintro ⟨s, b⟩ ⟨s', b'⟩ h
  simp only [smallEmb, Prod.mk.injEq, Sum.inl.injEq, Bool.not_inj_iff] at h
  rw [h.1, h.2]

/-- INTERNAL: `dispZ` reads a small display back through `smallEmb`. -/
theorem dispZ_emb (g : Fin (nSmall I ε δ) × Bool → ℕ) (w : Fin (nSmall I ε δ) × Bool) :
    dispZ (fun s => g (s, false)) (fun s => g (s, true)) (smallEmb w) = g w := by
  obtain ⟨s, b⟩ := w
  cases b <;> simp [dispZ, smallEmb]

end final

open Filter Topology in
/-- **Removal signature of `h_j`** (`cor:hj-signatures`, first assertion): at every
box-valid display `n` of total `p + 2` on the row/column views of the small cells, the
two-removal matrix of `h_j`, with zero entries for invalid removals, has at most one
positive eigenvalue.  `(s, false)` is the row view `x_s`, `(s, true)` the column view
`y_s`.  (The hypotheses other than `n`'s box and total are not needed: the argument works
for every `j ≥ 0`.)
PAPER: sections/integer-signatures.tex:325-332 -/
theorem hWeight_removal_hyp (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (j : ℕ) (hj : j ≤ HParam I ε δ)
    (n : Fin (nSmall I ε δ) × Bool → ℕ) (hbox : ∀ w, n w ≤ smallB I ε δ w.1)
    (htot : ∑ w, n w = pSmall I ε δ + 2) :
    Hyp (fun u v : Fin (nSmall I ε δ) × Bool =>
      if 1 ≤ n u ∧ 1 ≤ n v ∧ (u = v → 2 ≤ n u) then
        hWeight I ε δ j (extendN fun s => remDisp n u v (s, false))
          (extendN fun s => remDisp n u v (s, true))
      else 0) := by
  classical
  set z := dispZ (fun s => n (s, false)) (fun s => n (s, true)) with hz
  have hztot : ∑ s, ((n (s, false) : ℤ) + n (s, true)) = (pSmall I ε δ : ℤ) + 2 := by
    have : ∑ w, (n w : ℤ) = (pSmall I ε δ : ℤ) + 2 := by exact_mod_cast htot
    rw [← this, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun s _ => by rw [Fintype.sum_bool]; ring
  have hgoodα : ∀ α ∈ Set.Ioo (0 : ℝ) 1, Good (hjModel I ε δ j α).mE
      (EdgeModel.actS (largeSet I ε δ)) (pSmall I ε δ) ((hjModel I ε δ j α).WA (largeSet I ε δ)) := by
    intro α hα
    have := (hjModel I ε δ j α).good_WA (hjModel_hyps I ε δ j hα.1 hα.2.le) (largeSet I ε δ)
    rwa [hj_rem_total] at this
  refine hyp_of_tendsto (l := 𝓝[>] (0 : ℝ))
    (Q := fun α a b => remMat ((hjModel I ε δ j α).WA (largeSet I ε δ)) z (smallEmb a) (smallEmb b))
    ?_ ?_
  · intro a b
    by_cases hc : 1 ≤ n a ∧ 1 ≤ n b ∧ (a = b → 2 ≤ n a)
    · simp only [if_pos hc]
      have heq : z - Pi.single (smallEmb a) 1 - Pi.single (smallEmb b) 1 =
          dispZ (fun s => remDisp n a b (s, false)) (fun s => remDisp n a b (s, true)) := by
        funext p
        obtain ⟨c, bb⟩ := p
        rcases c with s | c
        · have hp : ((Sum.inl s, bb) : TmCell I ε δ × Bool) = smallEmb (s, !bb) := by
            simp [smallEmb]
          rw [hp, dispZ_emb (remDisp n a b), Pi.sub_apply, Pi.sub_apply, hz, dispZ_emb n,
            Pi.single_apply, Pi.single_apply]
          simp only [smallEmb_inj.eq_iff]
          rw [remDisp_cast n a b hc]
        · simp [hz, dispZ, smallEmb]
      simp only [remMat, heq]
      refine hj_tendsto j _ _ (fun s => ?_) (fun s => ?_) ?_
      · exact (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (hbox (s, false)))
      · exact (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (hbox (s, true)))
      · have h1 : ∑ s, (((remDisp n a b (s, false) : ℕ) : ℤ) + ((remDisp n a b (s, true) : ℕ) : ℤ)) =
            ∑ w, ((remDisp n a b w : ℕ) : ℤ) := by
          rw [Fintype.sum_prod_type]
          exact Finset.sum_congr rfl fun s _ => by rw [Fintype.sum_bool]; ring
        rw [h1]
        simp only [remDisp_cast n a b hc, Finset.sum_sub_distrib, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
        have : ∑ w, (n w : ℤ) = (pSmall I ε δ : ℤ) + 2 := by exact_mod_cast htot
        rw [this]; ring
    · simp only [if_neg hc]
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with α hα
      symm
      apply (hgoodα α hα).1
      intro hv
      apply hc
      have h1 := hv.1 (smallEmb a)
      have h2 := hv.1 (smallEmb b)
      simp only [Pi.sub_apply, Pi.single_apply, smallEmb_inj.eq_iff, hz, dispZ_emb n,
        if_true] at h1 h2
      by_cases hab : a = b
      · subst hab; simp only [if_true] at h1; omega
      · rw [if_neg hab] at h1; rw [if_neg (Ne.symm hab)] at h2
        refine ⟨by omega, by omega, fun h => absurd h hab⟩
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with α hα
    exact hyp_comp_inj ((hgoodα α hα).2.2 z (hj_valid_dispZ j α _ _ (fun s => hbox (s, false))
      (fun s => hbox (s, true)) _ hztot)) smallEmb smallEmb_inj

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `hWeight_removal_hyp` via the general-`j` softened `EdgeModel`, balanced summation of the large cells and the limit `α ↓ 0`
-/
