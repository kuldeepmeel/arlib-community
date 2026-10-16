import Cellcounting.Analysis.RefStationary
import Cellcounting.Analysis.TransMassEqCpart

/-!
# The edge energy `𝔇(g)` and the transversal/defect means (`transport.tex:86-96, 318-440`)

The objects in which `prop:transversal-variance`, `lem:defect-mean` and
`prop:observable-variance` are phrased, for the exact Metropolis chain `P_{j, w}` on
`X = chainStates`:

* `exchNbr` — two states differ by one exchange (one element out, one element in);
* `refDir` — `𝔇(g) = Σ_{{S, S'}} min{λ(S), λ(S')} (g(S) - g(S'))²`, the sum over
  unordered exchange edges of `X` (`eq:energy`), written as half the ordered sum;
* `refMuMean`, `refMuVar` — mean and variance under `μ = f_j / C(j)` on transversals;
* `refDefMean` — `ḡ_il = c_il⁻¹ Σ_{A_il} f_j g`, the `f_j`-mean on a defect type.

Also proved here: the labels of a defect type are distinct and below `p`, `𝔇 ≥ 0`,
and the total mass bound `Λ ≤ 5 p² C(j)` of `eq:type-mass-bounds`.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: `S'` is obtained from `S` by one exchange: exactly one element of `S`
leaves and exactly one new element enters.
TEXLINE: sections/transport.tex:64-69 -/
def exchNbr (S S' : Finset ℕ) : Prop := (S \ S').card = 1 ∧ (S' \ S).card = 1

open Classical in
/-- INTERNAL: the edge energy `𝔇(g)` of `eq:energy`: the sum over unordered exchange
edges `{S, S'}` of `X` of `min{λ(S), λ(S')} (g(S) - g(S'))²`, written as half the sum
over ordered pairs.
TEXLINE: sections/transport.tex:86-96 -/
noncomputable def refDir (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (g : Finset ℕ → ℝ) : ℝ :=
  (∑ S ∈ chainStates I ε δ, ∑ S' ∈ chainStates I ε δ,
    if exchNbr S S' then
      min (refLam I ε δ S j w) (refLam I ε δ S' j w) * (g S - g S') ^ 2
    else 0) / 2

/-- INTERNAL: the mean `E_μ g` under `μ = f_j / C(j)` on transversals.
TEXLINE: sections/transport.tex:320-329 -/
noncomputable def refMuMean (I : Instance) (ε δ : ℚ) (j : ℕ) (g : Finset ℕ → ℝ) : ℝ :=
  ∑ S ∈ transStates I ε δ, refMu I ε δ j S * g S

/-- INTERNAL: the variance `Var_μ g` of the restriction of `g` to transversals.
TEXLINE: sections/transport.tex:320-329 -/
noncomputable def refMuVar (I : Instance) (ε δ : ℚ) (j : ℕ) (g : Finset ℕ → ℝ) : ℝ :=
  ∑ S ∈ transStates I ε δ, refMu I ε δ j S * (g S - refMuMean I ε δ j g) ^ 2

open Classical in
/-- INTERNAL: the defect mean `ḡ_il = c_il⁻¹ Σ_{S ∈ A_il} f_j(S) g(S)`.
TEXLINE: sections/transport.tex:436-438 -/
noncomputable def refDefMean (I : Instance) (ε δ : ℚ) (j i l : ℕ) (g : Finset ℕ → ℝ) : ℝ :=
  (∑ S ∈ (refStates I ε δ).filter (fun S => kind I ε δ S = .defect i l),
      fWeight I ε δ j S * g S) / cDef I ε δ j i l

/-- INTERNAL: the labels of a defect type are distinct and below `p`.
TEXLINE: sections/signatures.tex:13-41 -/
theorem kind_defect_lt (I : Instance) (ε δ : ℚ) (S : Finset ℕ) (i l : ℕ)
    (h : kind I ε δ S = .defect i l) :
    i < pSmall I ε δ ∧ l < pSmall I ε δ ∧ i ≠ l := by
  unfold kind at h
  simp only at h
  split_ifs at h with hE hF hEF
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := And.intro (Finset.card_eq_one.1 hEF.1) (Finset.card_eq_one.1 hEF.2)
  rw [ha, hb] at h
  simp only [Finset.sup_singleton, id, Program.Kind.defect.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have ha' : a ∈ (Finset.range (pSmall I ε δ)).filter fun i => 2 * i ∉ S ∧ 2 * i + 1 ∉ S := by
    rw [ha]; exact Finset.mem_singleton_self a
  have hb' : b ∈ (Finset.range (pSmall I ε δ)).filter fun i => 2 * i ∈ S ∧ 2 * i + 1 ∈ S := by
    rw [hb]; exact Finset.mem_singleton_self b
  simp only [Finset.mem_filter, Finset.mem_range] at ha' hb'
  refine ⟨ha'.1, hb'.1, ?_⟩
  rintro rfl
  exact ha'.2.1 hb'.2.1

/-- INTERNAL: `f_j(S) > 0` (a local copy of `refPhase_fWeight_pos`, whose module sits
downstream of this one). -/
theorem td_fWeight_pos (I : Instance) (ε δ : ℚ) (j : ℕ) (S : Finset ℕ) :
    0 < fWeight I ε δ j S := by
  unfold fWeight
  refine mul_pos ?_ (Finset.prod_pos fun s _ => by positivity)
  exact Finset.sum_pos (fun z _ => by positivity) ⟨fun _ => 0, by simp [freeBox]⟩

/-- INTERNAL: `C(j) > 0` (a local copy of `refPhase_Cpart_pos`). -/
theorem td_Cpart_pos (I : Instance) (ε δ : ℚ) (j : ℕ) : 0 < Cpart I ε δ j :=
  Finset.sum_pos (fun _ _ => Finset.sum_pos (fun _ _ => by positivity)
    ⟨fun _ => 0, by simp [freeBox]⟩) ⟨fun _ => 0, by simp [smallBox]⟩

/-- INTERNAL: `c_il(j) ≥ 0`. -/
theorem td_cDef_nonneg (I : Instance) (ε δ : ℚ) (j i l : ℕ) : 0 ≤ cDef I ε δ j i l := by
  classical
  unfold cDef
  exact Finset.sum_nonneg fun S _ => (td_fWeight_pos I ε δ j S).le

/-- INTERNAL: good multipliers are nonnegative.
TEXLINE: sections/transport.tex:50-54 -/
theorem td_w_nonneg (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ j w) (i l : ℕ) (hi : i < pSmall I ε δ) (hl : l < pSmall I ε δ)
    (hil : i ≠ l) : 0 ≤ (w i l : ℝ) :=
  le_trans (div_nonneg (td_Cpart_pos I ε δ j).le
    (mul_nonneg (by norm_num) (td_cDef_nonneg I ε δ j i l))) (hgood i hi l hl hil).1

/-- INTERNAL: `λ(S) = f_j(S) w_il` on `A_il` and `f_j(S)` otherwise. -/
theorem td_refLam_eq (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ) (S : Finset ℕ) :
    refLam I ε δ S j w = match kind I ε δ S with
      | .defect i l => fWeight I ε δ j S * (w i l : ℝ)
      | _ => fWeight I ε δ j S := rfl

/-- INTERNAL: `λ ≥ 0` for good multipliers.
TEXLINE: sections/transport.tex:36-54 -/
theorem td_refLam_nonneg (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ j w) (S : Finset ℕ) : 0 ≤ refLam I ε δ S j w := by
  rw [td_refLam_eq]
  cases hk : kind I ε δ S with
  | defect i l =>
    obtain ⟨hi, hl, hil⟩ := kind_defect_lt I ε δ S i l hk
    exact mul_nonneg (td_fWeight_pos I ε δ j S).le (td_w_nonneg I ε δ j w hgood i l hi hl hil)
  | transversal => exact (td_fWeight_pos I ε δ j S).le
  | outside => exact (td_fWeight_pos I ε δ j S).le

open Classical in
/-- INTERNAL: the transversals of `X` are `A`. -/
theorem td_chainStates_filter_trans (I : Instance) (ε δ : ℚ) :
    (chainStates I ε δ).filter (fun S => kind I ε δ S = .transversal) = transStates I ε δ := by
  unfold chainStates transStates
  rw [Finset.filter_filter]
  refine Finset.filter_congr fun S _ => ?_
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by rw [h]; simp, h⟩

open Classical in
/-- INTERNAL: `Λ = C(j) + Σ_{S ∈ X \ A} λ(S)`.
TEXLINE: sections/transport.tex:36-62 -/
theorem td_refLamTot_eq (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ) :
    refLamTot I ε δ j w = Cpart I ε δ j +
      ∑ S ∈ (chainStates I ε δ).filter (fun S => ¬ kind I ε δ S = .transversal),
        refLam I ε δ S j w := by
  unfold refLamTot
  rw [← Finset.sum_filter_add_sum_filter_not (chainStates I ε δ)
    (fun S => kind I ε δ S = .transversal), td_chainStates_filter_trans,
    ← transMass_eq_Cpart]
  congr 1
  unfold transMass
  refine Finset.sum_congr rfl fun S hS => ?_
  have hk : kind I ε δ S = .transversal := (Finset.mem_filter.1 hS).2
  rw [td_refLam_eq, hk]

open Classical in
/-- INTERNAL: `C(j) ≤ Λ` for good multipliers.
TEXLINE: sections/transport.tex:56-62 -/
theorem td_Cpart_le_refLamTot (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ j w) : Cpart I ε δ j ≤ refLamTot I ε δ j w := by
  rw [td_refLamTot_eq]
  have := Finset.sum_nonneg (s := (chainStates I ε δ).filter
    (fun S => ¬ kind I ε δ S = .transversal))
    fun S _ => td_refLam_nonneg I ε δ j w hgood S
  linarith

open Classical in
/-- INTERNAL: `Λ ≤ (1 + 4 p²) C(j) ≤ 5 p² C(j)` for good multipliers: each defect
type carries multiplied mass `w_il c_il ≤ 4 C(j)` (`eq:type-mass-bounds`).
TEXLINE: sections/transport.tex:56-62 -/
theorem td_refLamTot_le (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (j : ℕ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) :
    refLamTot I ε δ j w ≤ 5 * (pSmall I ε δ : ℝ) ^ 2 * Cpart I ε δ j := by
  set p := pSmall I ε δ with hpdef
  set C := Cpart I ε δ j
  have hC := td_Cpart_pos I ε δ j
  set R := Finset.range p ×ˢ Finset.range p
  have hsplit : ∀ S ∈ (chainStates I ε δ).filter (fun S => ¬ kind I ε δ S = .transversal),
      refLam I ε δ S j w = ∑ il ∈ R,
        (if kind I ε δ S = .defect il.1 il.2 then fWeight I ε δ j S * (w il.1 il.2 : ℝ)
          else 0) := by
    intro S hS
    obtain ⟨hSX, hnt⟩ := Finset.mem_filter.1 hS
    have hno : kind I ε δ S ≠ .outside := (Finset.mem_filter.1 hSX).2
    rw [td_refLam_eq]
    cases hk : kind I ε δ S with
    | transversal => exact absurd hk hnt
    | outside => exact absurd hk hno
    | defect a b =>
      obtain ⟨ha, hb, _⟩ := kind_defect_lt I ε δ S a b hk
      rw [Finset.sum_eq_single (a, b)]
      · simp
      · rintro ⟨i, l⟩ _ hne
        simp only [Program.Kind.defect.injEq]
        rw [if_neg]
        rintro ⟨rfl, rfl⟩
        exact hne rfl
      · intro h
        exact absurd (Finset.mem_product.2 ⟨Finset.mem_range.2 ha, Finset.mem_range.2 hb⟩) h
  have hpair : ∀ il ∈ R,
      ∑ S ∈ (chainStates I ε δ).filter (fun S => ¬ kind I ε δ S = .transversal),
        (if kind I ε δ S = .defect il.1 il.2 then fWeight I ε δ j S * (w il.1 il.2 : ℝ)
          else 0) ≤ 4 * C := by
    rintro ⟨i, l⟩ hil
    obtain ⟨hi, hl⟩ := Finset.mem_product.1 hil
    rw [Finset.mem_range] at hi hl
    by_cases heq : i = l
    · subst heq
      refine le_of_eq_of_le (Finset.sum_eq_zero fun S _ => ?_) (by linarith)
      rw [if_neg]
      intro hk
      exact (kind_defect_lt I ε δ S i i hk).2.2 rfl
    · have hc : ∑ S ∈ (chainStates I ε δ).filter (fun S => ¬ kind I ε δ S = .transversal),
          (if kind I ε δ S = .defect i l then fWeight I ε δ j S else 0) = cDef I ε δ j i l := by
        unfold cDef chainStates
        rw [Finset.filter_filter, Finset.sum_filter, Finset.sum_filter]
        refine Finset.sum_congr rfl fun S _ => ?_
        by_cases hk : kind I ε δ S = .defect i l
        · simp [hk]
        · simp [hk]
      have hcalc : ∑ S ∈ (chainStates I ε δ).filter (fun S => ¬ kind I ε δ S = .transversal),
          (if kind I ε δ S = .defect i l then fWeight I ε δ j S * (w i l : ℝ) else 0) =
            (w i l : ℝ) * cDef I ε δ j i l := by
        rw [← hc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ => ?_
        split_ifs <;> ring
      simp only
      rw [hcalc]
      have hw := (hgood i hi l hl heq).2
      rcases (td_cDef_nonneg I ε δ j i l).eq_or_lt with h0 | hpos
      · rw [← h0, mul_zero]; linarith
      · rw [le_div_iff₀ hpos] at hw
        linarith
  have hbound := Finset.sum_le_sum hpair
  rw [Finset.sum_comm] at hbound
  rw [Finset.sum_congr rfl hsplit |>.symm] at hbound
  have hR : R.card = p * p := by simp [R]
  simp only [Finset.sum_const, nsmul_eq_mul, hR] at hbound
  rw [td_refLamTot_eq]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hp
  have hCC : Cpart I ε δ j = C := rfl
  push_cast at hbound
  rw [hCC]
  have hC' : 0 < C := hC
  have hpp : (1 : ℝ) ≤ p * p := by nlinarith
  have := mul_le_mul_of_nonneg_right hpp hC'.le
  nlinarith

/-- INTERNAL: `π ≥ 0` for good multipliers. -/
theorem td_refPi_nonneg (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ j w) (S : Finset ℕ) : 0 ≤ refPi I ε δ j w S := by
  unfold refPi
  split
  · exact div_nonneg (td_refLam_nonneg I ε δ j w hgood S)
      (Finset.sum_nonneg fun S _ => td_refLam_nonneg I ε δ j w hgood S)
  · exact le_refl 0

open Classical in
/-- INTERNAL: `𝔇(g) ≥ 0` for good multipliers. -/
theorem td_refDir_nonneg (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ j w) (g : Finset ℕ → ℝ) : 0 ≤ refDir I ε δ j w g := by
  unfold refDir
  refine div_nonneg (Finset.sum_nonneg fun S _ => Finset.sum_nonneg fun S' _ => ?_) (by norm_num)
  split
  · exact mul_nonneg (le_min (td_refLam_nonneg I ε δ j w hgood S)
      (td_refLam_nonneg I ε δ j w hgood S')) (sq_nonneg _)
  · exact le_refl 0

end Cellcounting.Analysis
