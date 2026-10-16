import Cellcounting.Analysis.BinChain
import Cellcounting.Analysis.PenaltyReal

/-!
# The continuous bin density

The objects of the proof of `lem:bin-conductance` (`evaluation.tex:214-279`), in cube
coordinates `u ∈ ℝ^e` (`e = nFree`):
* `binPhi`: the scaled penalty `ϕ_a(u) = (a/H) D(u)`, convex, `1/8`-Lipschitz in sup norm
  (`binPhi_convex`, `binPhi_lipschitz`); at a bin corner its floor is `binExp`
  (`binExp_le_binPhi`, `binPhi_lt_binExp`);
* `binRho`: the log-concave density `ϱ_a = 2^{-ϕ_a}`, with values in `(0, 1]`;
* `binBox v = [v, v+1)`, `binCube = [0, B)^e`, `binSide T = ⋃_{v ∈ T} binBox v`, and
  `binNbhd T`, the points of the cube within sup distance `r = 1/(4d)` of `binSide T`;
* `binMass X = ∫_X ϱ_a`;
* `binCutTerm`, `binCutFlow`: the discrete cut quantity `F = Σ min{V_a(v), V_a(w)}` over
  directional moves `v → w` from `T` out of `T`.

Proved here: the density comparisons `V_a(v)/4 ≤ ϱ_a ≤ 2 V_a(v)` near a bin corner
(`binRho_ge`, `binRho_le`), the discrete–continuous side mass comparison
`Σ_{v ∈ T} V_a(v) ≤ 4 μ(binSide T)` (`binV_sum_le_mass`, `eq:bin-density-comparison`)
and finiteness of side masses (`binMass_side_lt_top`).
-/

namespace Cellcounting.Analysis

open Pseudocode MeasureTheory Set
open scoped ENNReal
open Classical

variable (I : Instance) (ε δ : ℚ)

/-- INTERNAL: the scaled penalty `ϕ_a(u) = (a/H) D(u)` at a cube point.
TEXLINE: sections/evaluation.tex:44-51 -/
noncomputable def binPhi (a : ℕ) (x y : ℕ → ℕ) (u : Fin (nFree I ε δ) → ℝ) : ℝ :=
  (a : ℝ) / (HParam I ε δ : ℝ) * cubePen I ε δ x y u

/-- INTERNAL: the continuous density `ϱ_a(u) = 2^{-ϕ_a(u)}`.
TEXLINE: sections/evaluation.tex:214-216 -/
noncomputable def binRho (a : ℕ) (x y : ℕ → ℕ) (u : Fin (nFree I ε δ) → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ (-binPhi I ε δ a x y u))

/-- INTERNAL: the lower corner of a bin, as a cube point. -/
def binCorner (v : ℕ → ℕ) : Fin (nFree I ε δ) → ℝ := fun i => (v i : ℝ)

/-- INTERNAL: the half-open unit bin `[v, v+1)`. -/
def binBox (v : ℕ → ℕ) : Set (Fin (nFree I ε δ) → ℝ) :=
  pi univ fun i => Ico (v i : ℝ) (v i + 1)

/-- INTERNAL: the cube `[0, B)^e`. -/
def binCube : Set (Fin (nFree I ε δ) → ℝ) :=
  pi univ fun _ => Ico (0 : ℝ) (BParam I ε δ)

/-- INTERNAL: the union of the bins of `T`. -/
def binSide (T : Finset (ℕ → ℕ)) : Set (Fin (nFree I ε δ) → ℝ) :=
  ⋃ v ∈ T, binBox I ε δ v

/-- INTERNAL: the radius `r = tB = 1/(4d)`. -/
noncomputable def binRad : ℝ := 1 / (4 * (dParam I : ℝ))

/-- INTERNAL: the cube points within sup distance `r` of `binSide T`; it contains the
dilate `M = (1-t) S + t D₀` of `evaluation.tex:229`.
TEXLINE: sections/evaluation.tex:226-231 -/
def binNbhd (T : Finset (ℕ → ℕ)) : Set (Fin (nFree I ε δ) → ℝ) :=
  binCube I ε δ ∩ {z | ∃ x ∈ binSide I ε δ T, ‖z - x‖ < binRad I}

/-- INTERNAL: unnormalized mass `μ(X) = ∫_X ϱ_a`. -/
noncomputable def binMass (a : ℕ) (x y : ℕ → ℕ) (X : Set (Fin (nFree I ε δ) → ℝ)) : ℝ≥0∞ :=
  ∫⁻ z in X, binRho I ε δ a x y z

/-- INTERNAL: the contribution of proposal pattern `u` from bin `v` to the cut flow of `T`:
`min{V_a(v), V_a(w)}` if it moves to a bin `w ∉ T`. -/
noncomputable def binCutTerm (a : ℕ) (x y : ℕ → ℕ) (T : Finset (ℕ → ℕ)) (v : ℕ → ℕ) (u : ℕ) :
    ℝ :=
  match binProp I ε δ v u with
  | some w => if w ∈ T then 0 else min (binV I ε δ a x y v) (binV I ε δ a x y w)
  | none => 0

/-- INTERNAL: the discrete cut quantity `F = Σ min{V_a(v), V_a(w)}` over moves from `T`
out of `T`.
TEXLINE: sections/evaluation.tex:268-270 -/
noncomputable def binCutFlow (a : ℕ) (x y : ℕ → ℕ) (T : Finset (ℕ → ℕ)) : ℝ :=
  ∑ v ∈ T, ∑ u ∈ Finset.range (2 * nFree I ε δ), binCutTerm I ε δ a x y T v u

theorem binCutTerm_nonneg (a : ℕ) (x y : ℕ → ℕ) (T : Finset (ℕ → ℕ)) (v : ℕ → ℕ) (u : ℕ) :
    0 ≤ binCutTerm I ε δ a x y T v u := by
  unfold binCutTerm
  rcases binProp I ε δ v u with _ | w
  · exact le_rfl
  · dsimp only; split_ifs
    · exact le_rfl
    · exact le_min (binV_pos I ε δ a x y v).le (binV_pos I ε δ a x y w).le

theorem binCutFlow_nonneg (a : ℕ) (x y : ℕ → ℕ) (T : Finset (ℕ → ℕ)) :
    0 ≤ binCutFlow I ε δ a x y T :=
  Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun u _ => binCutTerm_nonneg I ε δ a x y T v u

/-! ### The scaled penalty -/

theorem boxDistR_nonneg (w b : ℝ) : 0 ≤ boxDistR w b := by
  unfold boxDistR; split_ifs <;> linarith

theorem cubePen_nonneg (x y : ℕ → ℕ) (u : Fin (nFree I ε δ) → ℝ) : 0 ≤ cubePen I ε δ x y u := by
  unfold cubePen penaltyR
  refine mul_nonneg (Nat.cast_nonneg _) (add_nonneg ?_ ?_)
  · exact List.sum_nonneg fun c hc => by
      obtain ⟨v, _, rfl⟩ := List.mem_map.1 hc; exact abs_nonneg _
  · exact Finset.sum_nonneg fun t _ => div_nonneg (boxDistR_nonneg _ _) (Nat.cast_nonneg _)

theorem binPhi_nonneg (a : ℕ) (x y : ℕ → ℕ) (u : Fin (nFree I ε δ) → ℝ) :
    0 ≤ binPhi I ε δ a x y u :=
  mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (cubePen_nonneg I ε δ x y u)

/-- INTERNAL: `ϕ_a` is `1/8`-Lipschitz in sup norm, for `a ≤ H`. -/
theorem binPhi_lipschitz (hε : 0 < ε) (hfeas : feasible I) (a : ℕ) (ha : a ≤ HParam I ε δ)
    (x y : ℕ → ℕ) (u u' : Fin (nFree I ε δ) → ℝ) :
    |binPhi I ε δ a x y u - binPhi I ε δ a x y u'| ≤ ‖u - u'‖ / 8 := by
  have hH : (0 : ℝ) < HParam I ε δ := by exact_mod_cast HParam_pos I ε δ hε
  have h0 : (0 : ℝ) ≤ (a : ℝ) / HParam I ε δ := by positivity
  have h1 : (a : ℝ) / HParam I ε δ ≤ 1 := by
    rw [div_le_one hH]; exact_mod_cast ha
  unfold binPhi
  rw [← mul_sub, abs_mul, abs_of_nonneg h0]
  calc (a : ℝ) / HParam I ε δ * |cubePen I ε δ x y u - cubePen I ε δ x y u'|
      ≤ 1 * |cubePen I ε δ x y u - cubePen I ε δ x y u'| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ ≤ ‖u - u'‖ / 8 := by rw [one_mul]; exact cubePen_lipschitz I ε δ hε hfeas x y u u'

theorem cubeZ_combo (lam mu : ℝ) (u u' : Fin (nFree I ε δ) → ℝ) :
    cubeZ I ε δ (lam • u + mu • u') = fun k => lam * cubeZ I ε δ u k + mu * cubeZ I ε δ u' k := by
  funext k; unfold cubeZ; split_ifs
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  · ring

/-- INTERNAL: `ϕ_a` is convex (`evaluation.tex:51`). -/
theorem binPhi_convex (a : ℕ) (x y : ℕ → ℕ) (u u' : Fin (nFree I ε δ) → ℝ) (lam mu : ℝ)
    (hl : 0 ≤ lam) (hm : 0 ≤ mu) (hlm : lam + mu = 1) :
    binPhi I ε δ a x y (lam • u + mu • u') ≤
      lam * binPhi I ε δ a x y u + mu * binPhi I ε δ a x y u' := by
  have h0 : (0 : ℝ) ≤ (a : ℝ) / HParam I ε δ := by positivity
  unfold binPhi cubePen
  rw [cubeZ_combo]
  have := mul_le_mul_of_nonneg_left
    (penaltyR_convex I ε δ x y (cubeZ I ε δ u) (cubeZ I ε δ u') lam mu hl hm hlm) h0
  linarith

/-- INTERNAL: at a bin corner, `ϕ_a` is the rational `a D(v) / H`. -/
theorem binPhi_corner (a : ℕ) (x y : ℕ → ℕ) {v : ℕ → ℕ} (hv : v ∈ binSet I ε δ) :
    binPhi I ε δ a x y (binCorner I ε δ v) =
      (((a : ℚ) * penalty I ε δ x y (binPoint I ε δ v) / (HParam I ε δ : ℚ) : ℚ) : ℝ) := by
  have hc : binCorner I ε δ v = fun i : Fin (nFree I ε δ) => ((v i : ℚ) : ℝ) := by
    funext i; simp [binCorner]
  have hz : cubeZQ I ε δ (fun i : Fin (nFree I ε δ) => (v i : ℚ)) = binPoint I ε δ v := by
    funext k; unfold cubeZQ binPoint
    split_ifs with hk
    · push_cast; ring
    · rw [(mem_binSet_iff I ε δ v).1 hv |>.2 k (not_lt.1 hk)]; simp
  unfold binPhi
  rw [hc, cubePen_cast, hz]
  push_cast; ring

theorem binExp_le_binPhi (a : ℕ) (x y : ℕ → ℕ) {v : ℕ → ℕ} (hv : v ∈ binSet I ε δ) :
    (binExp I ε δ a x y v : ℝ) ≤ binPhi I ε δ a x y (binCorner I ε δ v) := by
  rw [binPhi_corner I ε δ a x y hv]
  unfold binExp levelExp
  exact_mod_cast Int.floor_le _

theorem binPhi_lt_binExp (a : ℕ) (x y : ℕ → ℕ) {v : ℕ → ℕ} (hv : v ∈ binSet I ε δ) :
    binPhi I ε δ a x y (binCorner I ε δ v) < binExp I ε δ a x y v + 1 := by
  rw [binPhi_corner I ε δ a x y hv]
  unfold binExp levelExp
  have h := Int.lt_floor_add_one
    ((a : ℚ) * penalty I ε δ x y (binPoint I ε δ v) / (HParam I ε δ : ℚ))
  exact_mod_cast h

/-! ### The density -/

theorem continuous_binRho (a : ℕ) (x y : ℕ → ℕ) : Continuous (binRho I ε δ a x y) := by
  unfold binRho binPhi
  refine ENNReal.continuous_ofReal.comp ?_
  exact continuous_const.rpow ((continuous_const.mul (cubePen_continuous I ε δ x y)).neg)
    fun _ => Or.inl two_ne_zero

theorem measurable_binRho (a : ℕ) (x y : ℕ → ℕ) : Measurable (binRho I ε δ a x y) :=
  (continuous_binRho I ε δ a x y).measurable

theorem binRho_le_one (a : ℕ) (x y : ℕ → ℕ) (u : Fin (nFree I ε δ) → ℝ) :
    binRho I ε δ a x y u ≤ 1 := by
  unfold binRho
  rw [ENNReal.ofReal_le_one]
  exact Real.rpow_le_one_of_one_le_of_nonpos one_le_two
    (neg_nonpos.2 (binPhi_nonneg I ε δ a x y u))

theorem binV_eq_rpow (a : ℕ) (x y v : ℕ → ℕ) :
    binV I ε δ a x y v = (2 : ℝ) ^ (-(binExp I ε δ a x y v : ℝ)) := by
  unfold binV; rw [← Real.rpow_intCast]; push_cast; rfl

/-- INTERNAL: `ϱ_a ≤ 2 V_a(v)` within sup distance `8` of the corner of `v`. -/
theorem binRho_le (hε : 0 < ε) (hfeas : feasible I) (a : ℕ) (ha : a ≤ HParam I ε δ)
    (x y : ℕ → ℕ) {v : ℕ → ℕ} (hv : v ∈ binSet I ε δ) (z : Fin (nFree I ε δ) → ℝ)
    (hz : ‖z - binCorner I ε δ v‖ ≤ 8) :
    binRho I ε δ a x y z ≤ ENNReal.ofReal (2 * binV I ε δ a x y v) := by
  unfold binRho
  refine ENNReal.ofReal_le_ofReal ?_
  have hl := binPhi_lipschitz I ε δ hε hfeas a ha x y z (binCorner I ε δ v)
  have he := binExp_le_binPhi I ε δ a x y hv
  have hab := (abs_le.1 hl).1
  rw [binV_eq_rpow, show (2 : ℝ) * 2 ^ (-(binExp I ε δ a x y v : ℝ)) =
      2 ^ (1 + -(binExp I ε δ a x y v : ℝ)) by
    rw [Real.rpow_add two_pos, Real.rpow_one]]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)

/-- INTERNAL: `ϱ_a ≥ V_a(v)/4` within sup distance `8` of the corner of `v`
(`eq:bin-density-comparison`). -/
theorem binRho_ge (hε : 0 < ε) (hfeas : feasible I) (a : ℕ) (ha : a ≤ HParam I ε δ)
    (x y : ℕ → ℕ) {v : ℕ → ℕ} (hv : v ∈ binSet I ε δ) (z : Fin (nFree I ε δ) → ℝ)
    (hz : ‖z - binCorner I ε δ v‖ ≤ 8) :
    ENNReal.ofReal (binV I ε δ a x y v / 4) ≤ binRho I ε δ a x y z := by
  unfold binRho
  refine ENNReal.ofReal_le_ofReal ?_
  have hl := binPhi_lipschitz I ε δ hε hfeas a ha x y z (binCorner I ε δ v)
  have he := binPhi_lt_binExp I ε δ a x y hv
  have hab := (abs_le.1 hl).2
  rw [binV_eq_rpow, show (2 : ℝ) ^ (-(binExp I ε δ a x y v : ℝ)) / 4 =
      2 ^ (-(binExp I ε δ a x y v : ℝ) + -2) by
    rw [Real.rpow_add two_pos, Real.rpow_neg two_pos.le 2, Real.rpow_two]; ring]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)

/-! ### Bins and side masses -/

theorem measurableSet_binBox (v : ℕ → ℕ) : MeasurableSet (binBox I ε δ v) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem volume_binBox (v : ℕ → ℕ) : volume (binBox I ε δ v) = 1 := by
  unfold binBox
  rw [Real.volume_pi_Ico]
  simp

theorem binBox_disjoint {v w : ℕ → ℕ} (hv : v ∈ binSet I ε δ) (hw : w ∈ binSet I ε δ)
    (hvw : v ≠ w) : Disjoint (binBox I ε δ v) (binBox I ε δ w) := by
  rw [Set.disjoint_left]
  intro z hzv hzw
  apply hvw
  funext k
  by_cases hk : k < nFree I ε δ
  · have h1 := hzv ⟨k, hk⟩ (mem_univ _)
    have h2 := hzw ⟨k, hk⟩ (mem_univ _)
    simp only [mem_Ico] at h1 h2
    have a1 : (v k : ℝ) < w k + 1 := by linarith
    have a2 : (w k : ℝ) < v k + 1 := by linarith
    have b1 : v k < w k + 1 := by exact_mod_cast a1
    have b2 : w k < v k + 1 := by exact_mod_cast a2
    omega
  · rw [((mem_binSet_iff I ε δ v).1 hv).2 k (not_lt.1 hk),
      ((mem_binSet_iff I ε δ w).1 hw).2 k (not_lt.1 hk)]

theorem binBox_norm_le {v : ℕ → ℕ} {z : Fin (nFree I ε δ) → ℝ} (hz : z ∈ binBox I ε δ v) :
    ‖z - binCorner I ε δ v‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  have h := hz i (mem_univ _)
  simp only [mem_Ico] at h
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  simp only [binCorner]
  constructor <;> linarith

theorem binSide_subset_cube {T : Finset (ℕ → ℕ)} (hT : T ⊆ binSet I ε δ) :
    binSide I ε δ T ⊆ binCube I ε δ := by
  intro z hz
  simp only [binSide, mem_iUnion] at hz
  obtain ⟨v, hv, hz⟩ := hz
  intro i _
  have h := hz i (mem_univ _)
  have hb := ((mem_binSet_iff I ε δ v).1 (hT hv)).1 i i.isLt
  simp only [mem_Ico] at h ⊢
  refine ⟨le_trans (Nat.cast_nonneg _) h.1, lt_of_lt_of_le h.2 ?_⟩
  exact_mod_cast hb

theorem binMass_le_volume (a : ℕ) (x y : ℕ → ℕ) (X : Set (Fin (nFree I ε δ) → ℝ)) :
    binMass I ε δ a x y X ≤ volume X := by
  unfold binMass
  calc ∫⁻ z in X, binRho I ε δ a x y z ≤ ∫⁻ _ in X, 1 :=
        lintegral_mono fun z => binRho_le_one I ε δ a x y z
    _ = volume X := setLIntegral_one X

theorem volume_binCube_lt_top : volume (binCube I ε δ) < ⊤ := by
  unfold binCube
  rw [Real.volume_pi_Ico]
  exact ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top

theorem binMass_side_lt_top (a : ℕ) (x y : ℕ → ℕ) {T : Finset (ℕ → ℕ)}
    (hT : T ⊆ binSet I ε δ) : binMass I ε δ a x y (binSide I ε δ T) < ⊤ :=
  lt_of_le_of_lt ((binMass_le_volume I ε δ a x y _).trans (measure_mono
    (binSide_subset_cube I ε δ hT))) (volume_binCube_lt_top I ε δ)

theorem binMass_side_eq (a : ℕ) (x y : ℕ → ℕ) {T : Finset (ℕ → ℕ)} (hT : T ⊆ binSet I ε δ) :
    binMass I ε δ a x y (binSide I ε δ T) = ∑ v ∈ T, binMass I ε δ a x y (binBox I ε δ v) := by
  unfold binMass binSide
  refine lintegral_biUnion_finset (fun v hv w hw hvw => ?_)
    (fun v _ => measurableSet_binBox I ε δ v) _
  exact binBox_disjoint I ε δ (hT hv) (hT hw) hvw

/-- INTERNAL: the discrete–continuous comparison `Σ_{v ∈ T} V_a(v) ≤ 4 μ(binSide T)`.
TEXLINE: sections/evaluation.tex:271-275 (`eq:bin-density-comparison`) -/
theorem binV_sum_le_mass (hε : 0 < ε) (hfeas : feasible I) (a : ℕ) (ha : a ≤ HParam I ε δ)
    (x y : ℕ → ℕ) {T : Finset (ℕ → ℕ)} (hT : T ⊆ binSet I ε δ) :
    ENNReal.ofReal (∑ v ∈ T, binV I ε δ a x y v) ≤ 4 * binMass I ε δ a x y (binSide I ε δ T) := by
  rw [binMass_side_eq I ε δ a x y hT, Finset.mul_sum,
    ENNReal.ofReal_sum_of_nonneg fun v _ => (binV_pos I ε δ a x y v).le]
  refine Finset.sum_le_sum fun v hv => ?_
  have h : ENNReal.ofReal (binV I ε δ a x y v / 4) ≤ binMass I ε δ a x y (binBox I ε δ v) := by
    calc ENNReal.ofReal (binV I ε δ a x y v / 4)
        = ∫⁻ _ in binBox I ε δ v, ENNReal.ofReal (binV I ε δ a x y v / 4) := by
          rw [setLIntegral_const, volume_binBox, mul_one]
      _ ≤ binMass I ε δ a x y (binBox I ε δ v) :=
          setLIntegral_mono (measurable_binRho I ε δ a x y) fun z hz =>
            binRho_ge I ε δ hε hfeas a ha x y (hT hv) z
              ((binBox_norm_le I ε δ hz).trans (by norm_num))
  calc ENNReal.ofReal (binV I ε δ a x y v)
      = 4 * ENNReal.ofReal (binV I ε δ a x y v / 4) := by
        rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]; ring_nf
    _ ≤ 4 * binMass I ε δ a x y (binBox I ε δ v) := by gcongr

end Cellcounting.Analysis
