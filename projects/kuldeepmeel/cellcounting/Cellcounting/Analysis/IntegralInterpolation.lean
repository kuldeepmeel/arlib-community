import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.MeanInequalities

/-!
# Integral interpolation (`lem:integral-interpolation`, Prékopa–Leindler)

`Cellcounting.Analysis.integral_interpolation_pi`: for `0 < t < 1` and measurable
`f g h : ℝ^n → [0, ∞]` with `f, g` bounded and supported in a common cube, if
`h((1-t)x + ty) ≥ f(x)^{1-t} g(y)^t` for all `x, y`, then
`∫ h ≥ (∫ f)^{1-t} (∫ g)^t`.

This is `evaluation.tex:147-203`, in functional form: the paper's finite unions of boxes
`S₀, S₁, S₂` enter as indicator factors of `f₀, f₁, f₂`. The proof follows the paper's
induction on dimension (Fubini over the first coordinate), but the one-dimensional case
is argued through superlevel sets instead of quantile transport:
* `bm_compact`, `bm_measurable`: the one-dimensional Brunn–Minkowski inequality
  `|(1-t)A + tB| ≥ (1-t)|A| + t|B|` (inner regularity reduces to compact sets);
* `pl1_norm`: for `f, g ≤ 1` with supremum `1`, the layer-cake formula and
  Brunn–Minkowski on the level sets give `∫ h ≥ (1-t)∫ f + t ∫ g`;
* `pl1`: normalising by the suprema and the weighted AM–GM inequality (`amgm_ennreal`).
Mathlib has no Prékopa–Leindler or Brunn–Minkowski inequality.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Cellcounting.Analysis

/-- INTERNAL: one-dimensional Brunn–Minkowski for nonempty compact sets.
TEXLINE: sections/evaluation.tex:153-170 -/
theorem bm_compact {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {K L E : Set ℝ}
    (hK : IsCompact K) (hL : IsCompact L) (hK0 : K.Nonempty) (hL0 : L.Nonempty)
    (hE : ∀ x ∈ K, ∀ y ∈ L, (1 - t) * x + t * y ∈ E) :
    ENNReal.ofReal (1 - t) * volume K + ENNReal.ofReal t * volume L ≤ volume E := by
  set α := sSup K
  set β := sInf L
  have hα : α ∈ K := hK.sSup_mem hK0
  have hβ : β ∈ L := hL.sInf_mem hL0
  set P := AffineMap.homothety β (1 - t) '' K
  set Q := AffineMap.homothety α t '' L
  have hP : ∀ z ∈ P, z ≤ (1 - t) * α + t * β := by
    rintro _ ⟨x, hx, rfl⟩
    have : x ≤ α := le_csSup hK.bddAbove hx
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    nlinarith
  have hQ : ∀ z ∈ Q, (1 - t) * α + t * β ≤ z := by
    rintro _ ⟨y, hy, rfl⟩
    have : β ≤ y := csInf_le hL.bddBelow hy
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    nlinarith
  have hPE : P ⊆ E := by
    rintro _ ⟨x, hx, rfl⟩
    have := hE x hx β hβ
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    convert this using 1; ring
  have hQE : Q ⊆ E := by
    rintro _ ⟨y, hy, rfl⟩
    have := hE α hα y hy
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    convert this using 1; ring
  have hvP : volume P = ENNReal.ofReal (1 - t) * volume K := by
    simp only [P, Measure.addHaar_image_homothety, Module.finrank_self, pow_one,
      abs_of_pos (by linarith : (0:ℝ) < 1 - t)]
  have hvQ : volume Q = ENNReal.ofReal t * volume L := by
    simp only [Q, Measure.addHaar_image_homothety, Module.finrank_self, pow_one, abs_of_pos ht0]
  have hQm : MeasurableSet (Q \ {(1 - t) * α + t * β}) :=
    ((hL.image (AffineMap.homothety α t).continuous_of_finiteDimensional).isClosed.measurableSet).diff
      (measurableSet_singleton _)
  have hdisj : Disjoint P (Q \ {(1 - t) * α + t * β}) := by
    rw [Set.disjoint_left]
    rintro z hzP ⟨hzQ, hzm⟩
    exact hzm (le_antisymm (hP z hzP) (hQ z hzQ))
  rw [← hvP, ← hvQ, ← measure_sdiff_null (s := Q) (measure_singleton ((1 - t) * α + t * β)),
    ← measure_union hdisj hQm]
  exact measure_mono (union_subset hPE (sdiff_subset.trans hQE))

/-- INTERNAL: inner regularity of Lebesgue measure on `ℝ`, as a supremum over a subtype. -/
theorem vol_eq_iSup_compact {A : Set ℝ} (hA : MeasurableSet A) :
    volume A = ⨆ K : {K : Set ℝ // K ⊆ A ∧ IsCompact K}, volume K.1 := by
  rw [hA.measure_eq_iSup_isCompact, iSup_subtype']
  simp only [iSup_subtype, iSup_and]

/-- INTERNAL: one-dimensional Brunn–Minkowski for nonempty measurable sets: a set
containing `(1-t)A + tB` has measure at least `(1-t)|A| + t|B|`.
TEXLINE: sections/evaluation.tex:153-170 -/
theorem bm_measurable {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {A B E : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hA0 : A.Nonempty) (hB0 : B.Nonempty)
    (hE : ∀ x ∈ A, ∀ y ∈ B, (1 - t) * x + t * y ∈ E) :
    ENNReal.ofReal (1 - t) * volume A + ENNReal.ofReal t * volume B ≤ volume E := by
  obtain ⟨a0, ha0⟩ := hA0
  obtain ⟨b0, hb0⟩ := hB0
  have : Nonempty {K : Set ℝ // K ⊆ A ∧ IsCompact K} := ⟨⟨∅, empty_subset _, isCompact_empty⟩⟩
  have : Nonempty {K : Set ℝ // K ⊆ B ∧ IsCompact K} := ⟨⟨∅, empty_subset _, isCompact_empty⟩⟩
  rw [vol_eq_iSup_compact hA, vol_eq_iSup_compact hB, ENNReal.mul_iSup, ENNReal.mul_iSup]
  refine ENNReal.iSup_add_iSup_le fun K L => ?_
  calc ENNReal.ofReal (1 - t) * volume K.1 + ENNReal.ofReal t * volume L.1
      ≤ ENNReal.ofReal (1 - t) * volume (insert a0 K.1) +
          ENNReal.ofReal t * volume (insert b0 L.1) := by
        gcongr <;> exact subset_insert _ _
    _ ≤ volume E :=
        bm_compact ht0 ht1 (K.2.2.insert a0) (L.2.2.insert b0) (insert_nonempty _ _)
          (insert_nonempty _ _) (fun x hx y hy =>
            hE x (insert_subset ha0 K.2.1 hx) y (insert_subset hb0 L.2.1 hy))

/-- INTERNAL: one-dimensional Prékopa–Leindler, normalised: `f, g ≤ 1` with supremum `1`
give `(1-t)∫f + t∫g ≤ ∫h`.
TEXLINE: sections/evaluation.tex:153-170 -/
theorem pl1_norm {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ y, g y ≤ 1)
    (hfs : ∀ s : ℝ≥0∞, s < 1 → ∃ x, s < f x) (hgs : ∀ s : ℝ≥0∞, s < 1 → ∃ y, s < g y)
    (hfgh : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) * x + t * y)) :
    ENNReal.ofReal (1 - t) * (∫⁻ x, f x) + ENNReal.ofReal t * ∫⁻ y, g y ≤ ∫⁻ z, h z := by
  have hfin : ∀ {u : ℝ≥0∞}, u ≤ 1 → u ≠ ⊤ := fun hu => ne_top_of_le_ne_top ENNReal.one_ne_top hu
  have hlc : ∀ (u : ℝ → ℝ≥0∞), Measurable u → (∀ x, u x ≤ 1) →
      lintegral volume u = ∫⁻ s in Ioi 0, volume {x | s < (u x).toReal} := by
    intro u hu hu1
    rw [← lintegral_eq_lintegral_meas_lt volume (ae_of_all _ fun x => ENNReal.toReal_nonneg)
      hu.ennreal_toReal.aemeasurable]
    exact lintegral_congr fun x => (ENNReal.ofReal_toReal (hfin (hu1 x))).symm
  have hmono : ∀ (u : ℝ → ℝ≥0∞), Measurable fun s : ℝ => volume {x | s < (u x).toReal} := by
    intro u
    refine Antitone.measurable fun a b hab => measure_mono fun x hx => ?_
    exact lt_of_le_of_lt hab hx
  have hh' : Measurable fun z => min (h z) 1 := hh.min measurable_const
  calc ENNReal.ofReal (1 - t) * (∫⁻ x, f x) + ENNReal.ofReal t * ∫⁻ y, g y
      = ∫⁻ s in Ioi 0, (ENNReal.ofReal (1 - t) * volume {x | s < (f x).toReal} +
          ENNReal.ofReal t * volume {y | s < (g y).toReal}) := by
        rw [hlc f hf hf1, hlc g hg hg1, lintegral_add_left ((hmono f).const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ s in Ioi 0, volume {z | s < (min (h z) 1).toReal} := by
        refine setLIntegral_mono (hmono _) fun s hs => ?_
        have hs0 : 0 < s := hs
        rcases le_or_gt 1 s with hs1 | hs1
        · have he : ∀ (u : ℝ → ℝ≥0∞), (∀ x, u x ≤ 1) → {x | s < (u x).toReal} = ∅ := by
            intro u hu1
            ext x
            simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
            have : (u x).toReal ≤ 1 := by
              have := ENNReal.toReal_mono ENNReal.one_ne_top (hu1 x); simpa using this
            linarith
          rw [he f hf1, he g hg1]; simp
        · have hsr : ENNReal.ofReal s < 1 := ENNReal.ofReal_lt_one.2 hs1
          have hlvl : ∀ (u : ℝ → ℝ≥0∞), (∀ x, u x ≤ 1) → ∀ x,
              (s < (u x).toReal ↔ ENNReal.ofReal s < u x) := fun u hu1 x =>
            (ENNReal.ofReal_lt_iff_lt_toReal hs0.le (hfin (hu1 x))).symm
          refine bm_measurable ht0 ht1 (measurableSet_lt measurable_const hf.ennreal_toReal)
            (measurableSet_lt measurable_const hg.ennreal_toReal) ?_ ?_ ?_
          · obtain ⟨x, hx⟩ := hfs _ hsr
            exact ⟨x, (hlvl f hf1 x).2 hx⟩
          · obtain ⟨y, hy⟩ := hgs _ hsr
            exact ⟨y, (hlvl g hg1 y).2 hy⟩
          · intro x hx y hy
            have hx' := (hlvl f hf1 x).1 hx
            have hy' := (hlvl g hg1 y).1 hy
            show s < (min (h ((1 - t) * x + t * y)) 1).toReal
            rw [← ENNReal.ofReal_lt_iff_lt_toReal hs0.le (hfin (min_le_right _ _))]
            refine lt_min ?_ hsr
            have hpos : ENNReal.ofReal s ≠ 0 := by simpa using hs0
            calc ENNReal.ofReal s = ENNReal.ofReal s ^ ((1 - t) + t) := by simp
              _ = ENNReal.ofReal s ^ (1 - t) * ENNReal.ofReal s ^ t :=
                  ENNReal.rpow_add _ _ hpos ENNReal.ofReal_ne_top
              _ < f x ^ (1 - t) * g y ^ t :=
                  ENNReal.mul_lt_mul (ENNReal.rpow_lt_rpow hx' (by linarith))
                    (ENNReal.rpow_lt_rpow hy' ht0)
              _ ≤ _ := hfgh x y
    _ = ∫⁻ z, min (h z) 1 := by
        rw [hlc _ hh' fun z => min_le_right _ _]
    _ ≤ ∫⁻ z, h z := lintegral_mono fun z => min_le_left _ _

/-- INTERNAL: weighted AM–GM in `[0, ∞]`. -/
theorem amgm_ennreal {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (x y : ℝ≥0∞) :
    x ^ (1 - t) * y ^ t ≤ ENNReal.ofReal (1 - t) * x + ENNReal.ofReal t * y := by
  have h1t : 0 < 1 - t := by linarith
  rcases eq_or_ne x ⊤ with rfl | hx
  · rcases eq_or_ne y 0 with rfl | hy
    · simp [ENNReal.zero_rpow_of_pos ht0]
    · rw [ENNReal.mul_top (by simpa using h1t)]; simp
  rcases eq_or_ne y ⊤ with rfl | hy
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp [ENNReal.zero_rpow_of_pos h1t]
    · rw [ENNReal.mul_top (by simpa using ht0)]; simp
  lift x to NNReal using hx
  lift y to NNReal using hy
  rw [← ENNReal.coe_rpow_of_nonneg _ h1t.le, ← ENNReal.coe_rpow_of_nonneg _ ht0.le,
    ← ENNReal.coe_mul, ENNReal.ofReal, ENNReal.ofReal, ← ENNReal.coe_mul, ← ENNReal.coe_mul,
    ← ENNReal.coe_add, ENNReal.coe_le_coe]
  have := NNReal.geom_mean_le_arith_mean2_weighted (Real.toNNReal (1 - t)) (Real.toNNReal t) x y
    (by rw [← Real.toNNReal_add h1t.le ht0.le]; simp)
  rwa [Real.coe_toNNReal _ h1t.le, Real.coe_toNNReal _ ht0.le] at this

/-- INTERNAL: one-dimensional Prékopa–Leindler for bounded `f, g`.
TEXLINE: sections/evaluation.tex:153-170 -/
theorem pl1 {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hfC : ∀ x, f x ≤ C) (hgC : ∀ y, g y ≤ C)
    (hfgh : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) * x + t * y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t ≤ ∫⁻ z, h z := by
  have h1t : 0 < 1 - t := by linarith
  set a := ⨆ x, f x with ha
  set b := ⨆ y, g y with hb
  have haT : a ≠ ⊤ := ne_top_of_le_ne_top hC (iSup_le hfC)
  have hbT : b ≠ ⊤ := ne_top_of_le_ne_top hC (iSup_le hgC)
  rcases eq_or_ne a 0 with ha0 | ha0
  · have : ∫⁻ x, f x = 0 := by
      rw [lintegral_eq_zero_iff hf]
      exact Filter.Eventually.of_forall fun x => le_antisymm ((le_iSup f x).trans ha0.le) bot_le
    rw [this, ENNReal.zero_rpow_of_pos h1t, zero_mul]; exact bot_le
  rcases eq_or_ne b 0 with hb0 | hb0
  · have : ∫⁻ y, g y = 0 := by
      rw [lintegral_eq_zero_iff hg]
      exact Filter.Eventually.of_forall fun y => le_antisymm ((le_iSup g y).trans hb0.le) bot_le
    rw [this, ENNReal.zero_rpow_of_pos ht0, mul_zero]; exact bot_le
  set c := a ^ (1 - t) * b ^ t with hc
  have hc0 : c ≠ 0 := mul_ne_zero (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) haT).ne'
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 hb0) hbT).ne'
  have hcT : c ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg h1t.le haT)
    (ENNReal.rpow_ne_top_of_nonneg ht0.le hbT)
  have hnorm1 : ∀ (u : ℝ → ℝ≥0∞) (m : ℝ≥0∞), m = ⨆ x, u x → m ≠ 0 → m ≠ ⊤ →
      (∀ x, u x * m⁻¹ ≤ 1) ∧ ∀ s : ℝ≥0∞, s < 1 → ∃ x, s < u x * m⁻¹ := by
    intro u m hm hm0 hmT
    refine ⟨fun x => ?_, fun s hs => ?_⟩
    · calc u x * m⁻¹ ≤ m * m⁻¹ := by gcongr; exact hm ▸ le_iSup u x
        _ = 1 := ENNReal.mul_inv_cancel hm0 hmT
    · have hsm : s * m < m := by
        calc s * m < 1 * m := ENNReal.mul_lt_mul_left hm0 hmT hs
          _ = m := one_mul m
      rw [hm] at hsm
      obtain ⟨x, hx⟩ := lt_iSup_iff.1 hsm
      refine ⟨x, ?_⟩
      rw [← hm] at hx
      calc s = s * m * m⁻¹ := by rw [mul_assoc, ENNReal.mul_inv_cancel hm0 hmT, mul_one]
        _ < u x * m⁻¹ := ENNReal.mul_lt_mul_left (ENNReal.inv_ne_zero.2 hmT)
            (ENNReal.inv_ne_top.2 hm0) hx
  obtain ⟨hf1, hfs⟩ := hnorm1 f a ha ha0 haT
  obtain ⟨hg1, hgs⟩ := hnorm1 g b hb hb0 hbT
  have key := pl1_norm ht0 ht1 (fun x => f x * a⁻¹) (fun y => g y * b⁻¹) (fun z => h z * c⁻¹)
    (hf.mul_const _) (hg.mul_const _) (hh.mul_const _) hf1 hg1 hfs hgs (by
      intro x y
      rw [ENNReal.mul_rpow_of_nonneg _ _ h1t.le, ENNReal.mul_rpow_of_nonneg _ _ ht0.le,
        ENNReal.inv_rpow, ENNReal.inv_rpow, hc,
        ENNReal.mul_inv (Or.inr (ENNReal.rpow_ne_top_of_nonneg ht0.le hbT))
          (Or.inr (ENNReal.rpow_pos (pos_iff_ne_zero.2 hb0) hbT).ne')]
      calc f x ^ (1 - t) * (a ^ (1 - t))⁻¹ * (g y ^ t * (b ^ t)⁻¹)
          = f x ^ (1 - t) * g y ^ t * ((a ^ (1 - t))⁻¹ * (b ^ t)⁻¹) := by ring
        _ ≤ _ := by gcongr; exact hfgh x y)
  rw [lintegral_mul_const _ hf, lintegral_mul_const _ hg, lintegral_mul_const _ hh] at key
  have hamgm := (amgm_ennreal ht0 ht1 ((∫⁻ x, f x) * a⁻¹) ((∫⁻ y, g y) * b⁻¹)).trans key
  rw [ENNReal.mul_rpow_of_nonneg _ _ h1t.le, ENNReal.mul_rpow_of_nonneg _ _ ht0.le,
    ENNReal.inv_rpow, ENNReal.inv_rpow] at hamgm
  have : (∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t * c⁻¹ ≤ (∫⁻ z, h z) * c⁻¹ := by
    refine le_of_eq_of_le ?_ hamgm
    rw [hc, ENNReal.mul_inv (Or.inr (ENNReal.rpow_ne_top_of_nonneg ht0.le hbT))
          (Or.inr (ENNReal.rpow_pos (pos_iff_ne_zero.2 hb0) hbT).ne')]
    ring
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.inv_ne_zero.2 hcT) (ENNReal.inv_ne_top.2 hc0)).1 this

/-- INTERNAL: splitting off the first coordinate is `Fin.cons`. -/
theorem piFinSuccAbove_zero_symm_apply (n : ℕ) (x1 : ℝ) (x' : Fin n → ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm (x1, x') =
      Fin.cons x1 x' := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]; rfl

/-- **Integral interpolation** (`lem:integral-interpolation`, Prékopa–Leindler): if
`h((1-t)x + ty) ≥ f(x)^{1-t} g(y)^t`, with `f, g` bounded and supported in the cube
`[-R, R]^n`, then `(∫f)^{1-t} (∫g)^t ≤ ∫h`.
PAPER: sections/evaluation.tex:147-203 -/
theorem integral_interpolation_pi (n : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (f g h : (Fin n → ℝ) → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hfC : ∀ x, f x ≤ C) (hgC : ∀ y, g y ≤ C) {R : ℝ}
    (hfR : ∀ x, f x ≠ 0 → ∀ i, |x i| ≤ R) (hgR : ∀ y, g y ≠ 0 → ∀ i, |y i| ≤ R)
    (hfgh : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t ≤ ∫⁻ z, h z := by
  induction n generalizing C with
  | zero =>
    have hu : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by simp [volume_pi]
    simp only [lintegral_unique, hu, mul_one]
    have := hfgh default default
    convert this using 2 <;> exact congrArg (· ^ _) (congrArg _ (Subsingleton.elim _ _))
  | succ n ih =>
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hmp : MeasurePreserving e.symm (volume.prod volume) volume :=
      (volume_preserving_piFinSuccAbove (fun _ => ℝ) 0).symm
    have hcons : ∀ x1 x', e.symm (x1, x') = Fin.cons x1 x' := piFinSuccAbove_zero_symm_apply n
    have hfub : ∀ u : (Fin (n + 1) → ℝ) → ℝ≥0∞, Measurable u →
        ∫⁻ x, u x = ∫⁻ x1, ∫⁻ x', u (e.symm (x1, x')) := by
      intro u hu
      rw [← hmp.lintegral_comp_emb e.symm.measurableEmbedding,
        lintegral_prod (fun z => u (e.symm z)) (hu.comp e.symm.measurable).aemeasurable]
    have hsl : ∀ u : (Fin (n + 1) → ℝ) → ℝ≥0∞, Measurable u → ∀ x1,
        Measurable fun x' => u (e.symm (x1, x')) :=
      fun u hu x1 => hu.comp (e.symm.measurable.comp measurable_prodMk_left)
    have hmarg : ∀ u : (Fin (n + 1) → ℝ) → ℝ≥0∞, Measurable u →
        Measurable fun x1 => ∫⁻ x', u (e.symm (x1, x')) :=
      fun u hu => (hu.comp e.symm.measurable).lintegral_prod_right'
    have hlin : ∀ x1 y1 (x' y' : Fin n → ℝ), (1 - t) • e.symm (x1, x') + t • e.symm (y1, y') =
        e.symm ((1 - t) * x1 + t * y1, (1 - t) • x' + t • y') := by
      intro x1 y1 x' y'
      rw [hcons, hcons, hcons]
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    -- the box carrying the slices
    set box : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Set.Icc (-R) R
    have hbox : volume box ≠ ⊤ :=
      (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top.ne
    have hsupp : ∀ u : (Fin (n + 1) → ℝ) → ℝ≥0∞, (∀ x, u x ≠ 0 → ∀ i, |x i| ≤ R) →
        (∀ x, u x ≤ C) → ∀ x1, ∫⁻ x', u (e.symm (x1, x')) ≤ C * volume box := by
      intro u hR hu x1
      calc ∫⁻ x', u (e.symm (x1, x')) ≤ ∫⁻ x', box.indicator (fun _ => C) x' := by
            refine lintegral_mono fun x' => ?_
            by_cases hx : x' ∈ box
            · rw [Set.indicator_of_mem hx]; exact hu _
            · rw [Set.indicator_of_notMem hx]
              by_contra hne
              have hne' : u (e.symm (x1, x')) ≠ 0 := fun h0 => hne (h0 ▸ le_rfl)
              refine hx fun i _ => ?_
              have := hR _ hne' i.succ
              rw [hcons, Fin.cons_succ] at this
              exact abs_le.1 this
        _ = C * volume box := by
            rw [lintegral_indicator_const (MeasurableSet.univ_pi fun _ => measurableSet_Icc)]
    have hslR : ∀ u : (Fin (n + 1) → ℝ) → ℝ≥0∞, (∀ x, u x ≠ 0 → ∀ i, |x i| ≤ R) → ∀ x1,
        ∀ x', u (e.symm (x1, x')) ≠ 0 → ∀ i, |x' i| ≤ R := by
      intro u hR x1 x' hne i
      have := hR _ hne i.succ
      rwa [hcons, Fin.cons_succ] at this
    rw [hfub f hf, hfub g hg, hfub h hh]
    refine pl1 ht0 ht1 _ _ _ (hmarg f hf) (hmarg g hg) (hmarg h hh)
      (ENNReal.mul_ne_top hC hbox) (hsupp f hfR hfC) (hsupp g hgR hgC) fun x1 y1 => ?_
    refine ih _ _ _ (hsl f hf x1) (hsl g hg y1) (hsl h hh _) hC (fun x' => hfC _)
      (fun y' => hgC _) (hslR f hfR x1) (hslR g hgR y1) fun x' y' => ?_
    rw [← hlin]
    exact hfgh _ _

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · Prékopa–Leindler on `ℝ^n` for bounded, boxed functions; no `sorry`
-/

