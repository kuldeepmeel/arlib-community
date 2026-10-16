import Cellcounting.Analysis.PenaltyLipschitz
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# The penalty on real free vectors

The paper evaluates the penalty `D` at real points of the cube `[0, B]^e`
(`evaluation.tex:44-51`, "The function `D` is convex") to define the log-concave
density `ϱ_a = 2^{-aD/H}` behind the bin conductance bound. `Pseudocode.penalty` is
defined on rational vectors only, so this file transcribes it over `ℝ`
(`penaltyR`, same formula) and proves:
* `penaltyR_cast`: on rational vectors it is the cast of `Pseudocode.penalty`;
* `penaltyR_convex`: it is convex (leaf elimination is affine in the free vector,
  and `|·|`, `dist(·, [0, b])` are convex);
* `cubePen_continuous`, `cubePen_lipschitz`: in cube coordinates `u ∈ ℝ^e`
  (`z_k = (b_k + 1) u_k / B`) it is continuous and `1/8`-Lipschitz for the sup norm,
  by density of rational vectors and `penalty_lipschitz`.
-/

namespace Cellcounting.Analysis

open Pseudocode

variable (I : Instance) (ε δ : ℚ)

/-- INTERNAL: `Pseudocode.baseLoad` over `ℝ`.
TEXLINE: sections/scales.tex:113-126 -/
noncomputable def baseLoadR (x y : ℕ → ℕ) (z : ℕ → ℝ) (v : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (nSmall I ε δ),
      ((if (smallAt I ε δ k).1 = v then (x k : ℝ) else 0) +
        (if I.m + (smallAt I ε δ k).2.1 = v then (((smallAt I ε δ k).2.2 - y k : ℕ) : ℝ)
          else 0))) +
    ∑ k ∈ Finset.range (nFree I ε δ),
      ((if (freeAt I ε δ k).1 = v then z k else 0) +
        (if I.m + (freeAt I ε δ k).2.1 = v then z k else 0))

/-- INTERNAL: one leaf-elimination step of `Pseudocode.treeValues`, over any field `K`,
with margins `mg`. -/
noncomputable def tvStepF {K : Type*} [Field K] (mg : ℕ → K) (st : (ℕ → K) × (ℕ → K))
    (vt : ℕ × ℕ) : (ℕ → K) × (ℕ → K) :=
  let e := treeAt I ε δ vt.2
  let ztv := mg vt.1 - st.1 vt.1
  let other := if vt.1 = e.1 then I.m + e.2.1 else e.1
  (Function.update st.1 other (st.1 other + ztv), Function.update st.2 vt.2 ztv)

/-- INTERNAL: `Pseudocode.treeValues` over `ℝ`. -/
noncomputable def treeValuesR (x y : ℕ → ℕ) (z : ℕ → ℝ) : (ℕ → ℝ) × (ℕ → ℝ) :=
  (elimOrder I ε δ).foldl (tvStepF I ε δ fun v => (margin I v : ℝ))
    (baseLoadR I ε δ x y z, fun _ => 0)

/-- INTERNAL: `dist(x, [0, b])` over `ℝ`. -/
noncomputable def boxDistR (x b : ℝ) : ℝ :=
  if x < 0 then -x else if b < x then x - b else 0

/-- INTERNAL: `Pseudocode.penalty` over `ℝ`.
TEXLINE: sections/scales.tex:113-126 -/
noncomputable def penaltyR (x y : ℕ → ℕ) (z : ℕ → ℝ) : ℝ :=
  (AParam I ε δ : ℝ) *
    (((roots I ε δ).map fun v => |(treeValuesR I ε δ x y z).1 v - (margin I v : ℝ)|).sum +
      ∑ t ∈ Finset.range (forest I ε δ).tree.length,
        boxDistR ((treeValuesR I ε δ x y z).2 t) ((treeAt I ε δ t).2.2 : ℝ) /
          ((treeAt I ε δ t).2.2 : ℝ))

theorem treeValues_eq_foldl (x y : ℕ → ℕ) (z : ℕ → ℚ) :
    treeValues I ε δ x y z =
      (elimOrder I ε δ).foldl (tvStepF I ε δ (margin I)) (baseLoad I ε δ x y z, fun _ => 0) :=
  rfl

theorem tvStepF_cast (st : (ℕ → ℚ) × (ℕ → ℚ)) (vt : ℕ × ℕ) :
    tvStepF I ε δ (fun v => (margin I v : ℝ)) (fun v => (st.1 v : ℝ), fun v => (st.2 v : ℝ)) vt =
      (fun v => ((tvStepF I ε δ (margin I) st vt).1 v : ℝ),
        fun v => ((tvStepF I ε δ (margin I) st vt).2 v : ℝ)) := by
  unfold tvStepF
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_) <;>
    simp only [Function.update_apply] <;> split_ifs <;> push_cast <;> rfl

theorem foldl_tvStepF_cast (l : List (ℕ × ℕ)) (st : (ℕ → ℚ) × (ℕ → ℚ)) :
    l.foldl (tvStepF I ε δ fun v => (margin I v : ℝ)) (fun v => (st.1 v : ℝ), fun v => (st.2 v : ℝ)) =
      (fun v => ((l.foldl (tvStepF I ε δ (margin I)) st).1 v : ℝ),
        fun v => ((l.foldl (tvStepF I ε δ (margin I)) st).2 v : ℝ)) := by
  induction l generalizing st with
  | nil => rfl
  | cons vt l ih => rw [List.foldl_cons, List.foldl_cons, tvStepF_cast, ih]

theorem baseLoadR_cast (x y : ℕ → ℕ) (z : ℕ → ℚ) (v : ℕ) :
    baseLoadR I ε δ x y (fun k => (z k : ℝ)) v = (baseLoad I ε δ x y z v : ℝ) := by
  unfold baseLoadR baseLoad
  push_cast
  congr 1 <;> refine Finset.sum_congr rfl fun k _ => ?_ <;> split_ifs <;> simp

theorem treeValuesR_cast (x y : ℕ → ℕ) (z : ℕ → ℚ) :
    treeValuesR I ε δ x y (fun k => (z k : ℝ)) =
      (fun v => ((treeValues I ε δ x y z).1 v : ℝ),
        fun v => ((treeValues I ε δ x y z).2 v : ℝ)) := by
  rw [treeValues_eq_foldl, ← foldl_tvStepF_cast]
  unfold treeValuesR
  congr 2
  · exact funext (baseLoadR_cast I ε δ x y z)
  · funext v; simp

theorem boxDistR_cast (a b : ℚ) : boxDistR (a : ℝ) (b : ℝ) = (boxDist a b : ℝ) := by
  unfold boxDistR boxDist
  split_ifs with h1 h2 h3 h4 h3 h4 <;> push_cast <;> first | rfl | (exfalso; norm_cast at *)

/-- INTERNAL: on rational vectors `penaltyR` is the cast of `Pseudocode.penalty`. -/
theorem penaltyR_cast (x y : ℕ → ℕ) (z : ℕ → ℚ) :
    penaltyR I ε δ x y (fun k => (z k : ℝ)) = (penalty I ε δ x y z : ℝ) := by
  unfold penaltyR penalty
  rw [treeValuesR_cast]
  push_cast [Rat.cast_list_sum, List.map_map]
  congr 2
  · congr 1
    refine List.map_congr_left fun v _ => ?_
    simp
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [← boxDistR_cast]; push_cast; rfl

/-! ### Convexity -/

/-- INTERNAL: `dist(w, [0, b]) = max(-w, w - b, 0)` for `b ≥ 0`. -/
theorem boxDistR_eq_max (w b : ℝ) (hb : 0 ≤ b) : boxDistR w b = max (max (-w) (w - b)) 0 := by
  unfold boxDistR
  split_ifs with h1 h2 <;> symm
  · rw [max_eq_left (by linarith : w - b ≤ -w), max_eq_left (by linarith : (0 : ℝ) ≤ -w)]
  · rw [max_eq_right (by linarith : -w ≤ w - b), max_eq_left (by linarith : (0 : ℝ) ≤ w - b)]
  · rw [max_eq_right (max_le (by linarith) (by linarith))]

/-- INTERNAL: `dist(·, [0, b])` is convex for `b ≥ 0`. -/
theorem boxDistR_convex (a a' b lam mu : ℝ) (hb : 0 ≤ b) (hl : 0 ≤ lam) (hm : 0 ≤ mu)
    (hlm : lam + mu = 1) :
    boxDistR (lam * a + mu * a') b ≤ lam * boxDistR a b + mu * boxDistR a' b := by
  have key : ∀ w, -w ≤ boxDistR w b ∧ w - b ≤ boxDistR w b ∧ 0 ≤ boxDistR w b := by
    intro w; rw [boxDistR_eq_max w b hb]
    exact ⟨(le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
      le_max_right _ _⟩
  obtain ⟨k1, k2, k3⟩ := key a
  obtain ⟨k1', k2', k3'⟩ := key a'
  have e1 := mul_le_mul_of_nonneg_left k1 hl
  have e2 := mul_le_mul_of_nonneg_left k2 hl
  have e3 := mul_le_mul_of_nonneg_left k3 hl
  have e1' := mul_le_mul_of_nonneg_left k1' hm
  have e2' := mul_le_mul_of_nonneg_left k2' hm
  have e3' := mul_le_mul_of_nonneg_left k3' hm
  rw [boxDistR_eq_max _ b hb]
  refine max_le (max_le ?_ ?_) ?_
  · linear_combination e1 + e1'
  · linear_combination e2 + e2' + b * hlm
  · linear_combination e3 + e3'

/-- INTERNAL: the pointwise combination `λ st + μ st'` of two elimination states. -/
def combo (lam mu : ℝ) (st st' : (ℕ → ℝ) × (ℕ → ℝ)) : (ℕ → ℝ) × (ℕ → ℝ) :=
  (fun v => lam * st.1 v + mu * st'.1 v, fun v => lam * st.2 v + mu * st'.2 v)

theorem tvStepF_combo (mg : ℕ → ℝ) (lam mu : ℝ) (hlm : lam + mu = 1)
    (st st' : (ℕ → ℝ) × (ℕ → ℝ)) (vt : ℕ × ℕ) :
    tvStepF I ε δ mg (combo lam mu st st') vt =
      combo lam mu (tvStepF I ε δ mg st vt) (tvStepF I ε δ mg st' vt) := by
  obtain rfl : mu = 1 - lam := by linarith
  unfold tvStepF combo
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_) <;>
    simp only [Function.update_apply] <;> split_ifs <;> ring

theorem foldl_tvStepF_combo (mg : ℕ → ℝ) (lam mu : ℝ) (hlm : lam + mu = 1)
    (l : List (ℕ × ℕ)) (st st' : (ℕ → ℝ) × (ℕ → ℝ)) :
    l.foldl (tvStepF I ε δ mg) (combo lam mu st st') =
      combo lam mu (l.foldl (tvStepF I ε δ mg) st) (l.foldl (tvStepF I ε δ mg) st') := by
  induction l generalizing st st' with
  | nil => rfl
  | cons vt l ih => rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, tvStepF_combo I ε δ mg
      lam mu hlm, ih]

theorem baseLoadR_combo (x y : ℕ → ℕ) (z z' : ℕ → ℝ) (lam mu : ℝ) (hlm : lam + mu = 1)
    (v : ℕ) :
    baseLoadR I ε δ x y (fun k => lam * z k + mu * z' k) v =
      lam * baseLoadR I ε δ x y z v + mu * baseLoadR I ε δ x y z' v := by
  unfold baseLoadR
  set S := ∑ k ∈ Finset.range (nSmall I ε δ),
      ((if (smallAt I ε δ k).1 = v then (x k : ℝ) else 0) +
        (if I.m + (smallAt I ε δ k).2.1 = v then (((smallAt I ε δ k).2.2 - y k : ℕ) : ℝ)
          else 0))
  have hsum : ∀ w : ℕ → ℝ, ∑ k ∈ Finset.range (nFree I ε δ),
      ((if (freeAt I ε δ k).1 = v then w k else 0) +
        (if I.m + (freeAt I ε δ k).2.1 = v then w k else 0)) =
      ∑ k ∈ Finset.range (nFree I ε δ), w k *
        ((if (freeAt I ε δ k).1 = v then 1 else 0) +
          (if I.m + (freeAt I ε δ k).2.1 = v then 1 else 0)) := by
    intro w; refine Finset.sum_congr rfl fun k _ => ?_; split_ifs <;> ring
  rw [hsum, hsum, hsum]
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  obtain rfl : mu = 1 - lam := by linarith
  ring

theorem treeValuesR_combo (x y : ℕ → ℕ) (z z' : ℕ → ℝ) (lam mu : ℝ) (hlm : lam + mu = 1) :
    treeValuesR I ε δ x y (fun k => lam * z k + mu * z' k) =
      combo lam mu (treeValuesR I ε δ x y z) (treeValuesR I ε δ x y z') := by
  unfold treeValuesR
  rw [← foldl_tvStepF_combo I ε δ _ lam mu hlm]
  congr 1
  unfold combo
  refine Prod.ext (funext fun v => baseLoadR_combo I ε δ x y z z' lam mu hlm v) ?_
  funext v; simp

/-- INTERNAL: the penalty is convex in the free vector.
TEXLINE: sections/evaluation.tex:51 ("The function `D` is convex") -/
theorem penaltyR_convex (x y : ℕ → ℕ) (z z' : ℕ → ℝ) (lam mu : ℝ) (hl : 0 ≤ lam)
    (hm : 0 ≤ mu) (hlm : lam + mu = 1) :
    penaltyR I ε δ x y (fun k => lam * z k + mu * z' k) ≤
      lam * penaltyR I ε δ x y z + mu * penaltyR I ε δ x y z' := by
  unfold penaltyR
  rw [treeValuesR_combo I ε δ x y z z' lam mu hlm]
  set T := treeValuesR I ε δ x y z
  set T' := treeValuesR I ε δ x y z'
  have hA : (0 : ℝ) ≤ AParam I ε δ := Nat.cast_nonneg _
  rw [show ∀ P Q : ℝ, lam * ((AParam I ε δ : ℝ) * P) + mu * ((AParam I ε δ : ℝ) * Q) =
      (AParam I ε δ : ℝ) * (lam * P + mu * Q) from fun P Q => by ring]
  refine mul_le_mul_of_nonneg_left ?_ hA
  unfold combo
  simp only
  rw [show ∀ P P' Q Q' : ℝ, lam * (P + Q) + mu * (P' + Q') = (lam * P + mu * P') +
      (lam * Q + mu * Q') from fun _ _ _ _ => by ring]
  gcongr
  · rw [← List.sum_map_mul_left, ← List.sum_map_mul_left, ← List.sum_map_add]
    refine List.sum_le_sum fun v _ => ?_
    have hv : lam * T.1 v + mu * T'.1 v - (margin I v : ℝ) =
        lam * (T.1 v - margin I v) + mu * (T'.1 v - margin I v) := by
      linear_combination (margin I v : ℝ) * hlm
    rw [hv]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hl, abs_of_nonneg hm]
  · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun t _ => ?_
    have hb : (0 : ℝ) ≤ ((treeAt I ε δ t).2.2 : ℝ) := Nat.cast_nonneg _
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
    exact div_le_div_of_nonneg_right (boxDistR_convex _ _ _ _ _ hb hl hm hlm) hb

/-! ### Cube coordinates: continuity and the Lipschitz bound -/

/-- INTERNAL: the free vector `z_k = (b_k + 1) u_k / B` of a cube point `u ∈ ℝ^e`.
TEXLINE: sections/evaluation.tex:44-46 -/
noncomputable def cubeZ (u : Fin (nFree I ε δ) → ℝ) : ℕ → ℝ := fun k =>
  if h : k < nFree I ε δ then (((freeAt I ε δ k).2.2 + 1 : ℕ) : ℝ) * u ⟨k, h⟩ / BParam I ε δ
  else 0

/-- INTERNAL: the penalty at a cube point, `D(u)`.
TEXLINE: sections/evaluation.tex:44-51 -/
noncomputable def cubePen (x y : ℕ → ℕ) (u : Fin (nFree I ε δ) → ℝ) : ℝ :=
  penaltyR I ε δ x y (cubeZ I ε δ u)

/-- INTERNAL: the rational free vector of a rational cube point. -/
noncomputable def cubeZQ (q : Fin (nFree I ε δ) → ℚ) : ℕ → ℚ := fun k =>
  if h : k < nFree I ε δ then (((freeAt I ε δ k).2.2 + 1 : ℕ) : ℚ) * q ⟨k, h⟩ / BParam I ε δ
  else 0

theorem cubeZ_cast (q : Fin (nFree I ε δ) → ℚ) :
    cubeZ I ε δ (fun i => (q i : ℝ)) = fun k => (cubeZQ I ε δ q k : ℝ) := by
  funext k; unfold cubeZ cubeZQ; split_ifs <;> push_cast <;> rfl

theorem cubePen_cast (x y : ℕ → ℕ) (q : Fin (nFree I ε δ) → ℚ) :
    cubePen I ε δ x y (fun i => (q i : ℝ)) = (penalty I ε δ x y (cubeZQ I ε δ q) : ℝ) := by
  unfold cubePen; rw [cubeZ_cast, penaltyR_cast]

theorem boxDistR_continuous (b : ℝ) (hb : 0 ≤ b) : Continuous fun w => boxDistR w b := by
  simp_rw [boxDistR_eq_max _ b hb]; fun_prop

theorem foldl_tvStepF_continuous {X : Type*} [TopologicalSpace X] (mg : ℕ → ℝ)
    (l : List (ℕ × ℕ)) (S : X → (ℕ → ℝ) × (ℕ → ℝ))
    (hS : ∀ v, Continuous (fun u => (S u).1 v) ∧ Continuous (fun u => (S u).2 v)) :
    ∀ v, Continuous (fun u => (l.foldl (tvStepF I ε δ mg) (S u)).1 v) ∧
      Continuous (fun u => (l.foldl (tvStepF I ε δ mg) (S u)).2 v) := by
  induction l generalizing S with
  | nil => exact hS
  | cons vt l ih =>
    simp only [List.foldl_cons]
    refine ih (fun u => tvStepF I ε δ mg (S u) vt) fun w => ⟨?_, ?_⟩
    · simp only [tvStepF, Function.update_apply]
      split_ifs <;> first
        | exact ((hS _).1.add (continuous_const.sub (hS _).1))
        | exact (hS w).1
    · simp only [tvStepF, Function.update_apply]
      split_ifs
      · exact continuous_const.sub (hS _).1
      · exact (hS w).2

theorem cubePen_continuous (x y : ℕ → ℕ) : Continuous (cubePen I ε δ x y) := by
  have hz : ∀ k, Continuous fun u => cubeZ I ε δ u k := by
    intro k; unfold cubeZ; split_ifs
    · exact (continuous_const.mul (continuous_apply _)).div_const _
    · exact continuous_const
  have hite : ∀ (P : Prop) [Decidable P] (k : ℕ),
      Continuous fun u => if P then cubeZ I ε δ u k else 0 := by
    intro P _ k; split_ifs; exacts [hz k, continuous_const]
  have hbase : ∀ v, Continuous fun u => baseLoadR I ε δ x y (cubeZ I ε δ u) v := by
    intro v; unfold baseLoadR
    exact continuous_const.add (continuous_finsetSum _ fun k _ => (hite _ k).add (hite _ k))
  have htv := foldl_tvStepF_continuous I ε δ (fun v => (margin I v : ℝ)) (elimOrder I ε δ)
    (fun u => (baseLoadR I ε δ x y (cubeZ I ε δ u), fun _ => 0))
    (fun v => ⟨hbase v, continuous_const⟩)
  unfold cubePen penaltyR treeValuesR
  refine continuous_const.mul (Continuous.add ?_ ?_)
  · exact continuous_list_sum _ fun v _ => ((htv v).1.sub continuous_const).abs
  · exact continuous_finsetSum _ fun t _ =>
      ((boxDistR_continuous _ (Nat.cast_nonneg _)).comp (htv t).2).div_const _

/-- INTERNAL: in cube coordinates the penalty is `1/8`-Lipschitz for the sup norm
(`eq:scaled-penalty-bounds`, at real points).
TEXLINE: sections/evaluation.tex:44-51 -/
theorem cubePen_lipschitz (hε : 0 < ε) (hfeas : feasible I) (x y : ℕ → ℕ)
    (u u' : Fin (nFree I ε δ) → ℝ) :
    |cubePen I ε δ x y u - cubePen I ε δ x y u'| ≤ ‖u - u'‖ / 8 := by
  have hdense : DenseRange (fun q : Fin (nFree I ε δ) → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  refine hdense.induction_on₂ (p := fun u u' =>
      |cubePen I ε δ x y u - cubePen I ε δ x y u'| ≤ ‖u - u'‖ / 8) ?_ ?_ u u'
  · exact isClosed_le
      (((cubePen_continuous I ε δ x y).comp continuous_fst).sub
        ((cubePen_continuous I ε δ x y).comp continuous_snd)).abs
      ((continuous_fst.sub continuous_snd).norm.div_const _)
  intro q q'
  simp only [cubePen_cast]
  refine le_of_forall_lt_rat_imp_le fun r hr => ?_
  have hB : (0 : ℚ) < BParam I ε δ := by
    have := AParam_pos I ε δ hε; have := dParam_ge I
    unfold BParam; positivity
  have hlip := penalty_lipschitz I ε δ hε hfeas x y (cubeZQ I ε δ q) (cubeZQ I ε δ q') (8 * r)
    (by
      have : (0 : ℝ) ≤ ‖(fun i => (q i : ℝ)) - fun i => (q' i : ℝ)‖ / 8 := by positivity
      have : (0 : ℝ) < r := by linarith
      exact_mod_cast (by linarith : (0 : ℝ) ≤ 8 * r))
    (by
      intro k hk
      unfold cubeZQ
      rw [dif_pos hk, dif_pos hk, ← sub_div, abs_div, abs_of_pos hB, ← mul_sub, abs_mul,
        abs_of_nonneg (by positivity)]
      refine div_le_div_of_nonneg_right ?_ hB.le
      push_cast
      rw [mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have h1 : |((q ⟨k, hk⟩ : ℚ) : ℝ) - (q' ⟨k, hk⟩ : ℝ)| ≤
          ‖(fun i => (q i : ℝ)) - fun i => (q' i : ℝ)‖ :=
        norm_le_pi_norm ((fun i => (q i : ℝ)) - fun i => (q' i : ℝ)) ⟨k, hk⟩
      have h2 : |q ⟨k, hk⟩ - q' ⟨k, hk⟩| ≤ 8 * r := by
        have : ((|q ⟨k, hk⟩ - q' ⟨k, hk⟩| : ℚ) : ℝ) ≤ 8 * r := by
          push_cast; linarith
        exact_mod_cast this
      exact h2)
  have : ((|penalty I ε δ x y (cubeZQ I ε δ q) - penalty I ε δ x y (cubeZQ I ε δ q')| : ℚ) : ℝ) ≤
      ((8 * r / 8 : ℚ) : ℝ) := by exact_mod_cast hlip
  push_cast at this
  linarith

end Cellcounting.Analysis
