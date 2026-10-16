import Cellcounting.Analysis.PmfClose

/-!
# Approximate couplings of probability laws

`ACouple μ ν R ε` says there is a joint law of `μ` and `ν` under which the
relation `R` fails with probability at most `ε`.  This is the device of the
coupling clause of `lem:bounded-implementation` (`algorithm.tex:519-576`):
expose the joint history before each draw, couple the new draws, and charge a
union bound over the discrepancies.

The calculus: `ACouple.pure`, `ACouple.bind` (costs add; the second kernel is
needed only on related pairs), `ACouple.map`, `ACouple.loop` (along
`Pseudocode.loop`, with an index-dependent relation), `ACouple.mono`,
`ACouple.bind_left` (a draw on one side only, charged by the probability of
leaving a good set), `ACouple.support_right`, and `ACouple.of_pclose`: a
one-sided total-variation bound `PClose μ ν ζ` gives an equality coupling at
cost `ζ` (the maximal coupling).
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal

/-- INTERNAL: an approximate relational coupling: a joint law with marginals `μ`
and `ν` under which `R` fails with probability at most `ε`.
TEXLINE: sections/algorithm.tex:519-576 -/
def ACouple {α β : Type*} (μ : PMF α) (ν : PMF β) (R : α → β → Prop) (ε : ℝ≥0∞) : Prop :=
  ∃ π : PMF (α × β), π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
    π.toOuterMeasure {q | ¬ R q.1 q.2} ≤ ε

section
variable {α β γ δ : Type*}

/-- INTERNAL: the independent coupling. -/
noncomputable def prodLaw (μ : PMF α) (ν : PMF β) : PMF (α × β) :=
  μ.bind fun a => ν.map fun b => (a, b)

theorem pmf_map_id' (μ : PMF α) : μ.map (fun a => a) = μ := PMF.map_id μ

theorem pmf_map_const' (μ : PMF α) (b : β) : μ.map (fun _ => b) = PMF.pure b :=
  PMF.map_const μ b

/-- INTERNAL: event probabilities are at most one. -/
theorem outer_le_one (μ : PMF α) (s : Set α) : μ.toOuterMeasure s ≤ 1 := by
  rw [outer_eq_pexp]
  exact pexp_le_one _ _ fun a => by by_cases ha : a ∈ s <;> simp [ha]

theorem prodLaw_fst (μ : PMF α) (ν : PMF β) : (prodLaw μ ν).map Prod.fst = μ := by
  simp only [prodLaw, PMF.map_bind, PMF.map_comp, Function.comp_def, pmf_map_const']
  exact PMF.bind_pure μ

theorem prodLaw_snd (μ : PMF α) (ν : PMF β) : (prodLaw μ ν).map Prod.snd = ν := by
  simp [prodLaw, PMF.map_bind, PMF.map_comp, Function.comp_def, pmf_map_id']

theorem ACouple.mono {μ : PMF α} {ν : PMF β} {R S : α → β → Prop} {ε ε' : ℝ≥0∞}
    (h : ACouple μ ν R ε) (hRS : ∀ a b, R a b → S a b) (hε : ε ≤ ε') : ACouple μ ν S ε' := by
  obtain ⟨π, h1, h2, h3⟩ := h
  refine ⟨π, h1, h2, le_trans (PMF.toOuterMeasure_mono _ ?_) (h3.trans hε)⟩
  intro q hq
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, PMF.mem_support_iff] at hq ⊢
  exact fun hR => hq.1 (hRS _ _ hR)

theorem ACouple.top (μ : PMF α) (ν : PMF β) (R : α → β → Prop) : ACouple μ ν R 1 :=
  ⟨prodLaw μ ν, prodLaw_fst μ ν, prodLaw_snd μ ν, outer_le_one _ _⟩

theorem ACouple.pure {a : α} {b : β} {R : α → β → Prop} (h : R a b) :
    ACouple (PMF.pure a) (PMF.pure b) R 0 := by
  refine ⟨PMF.pure (a, b), PMF.pure_map _ _, PMF.pure_map _ _, ?_⟩
  rw [PMF.toOuterMeasure_pure_apply]
  simp [h]

theorem ACouple.refl (μ : PMF α) : ACouple μ μ (· = ·) 0 := by
  refine ⟨μ.map fun a => (a, a), by simp [PMF.map_comp, Function.comp_def, pmf_map_id'],
    by simp [PMF.map_comp, Function.comp_def, pmf_map_id'], ?_⟩
  rw [PMF.toOuterMeasure_map_apply]
  simp

theorem ACouple.bind {μ : PMF α} {ν : PMF β} {f : α → PMF γ} {g : β → PMF δ}
    {R : α → β → Prop} {S : γ → δ → Prop} {ε₁ ε₂ : ℝ≥0∞} (h : ACouple μ ν R ε₁)
    (hK : ∀ a b, R a b → ACouple (f a) (g b) S ε₂) :
    ACouple (μ.bind f) (ν.bind g) S (ε₁ + ε₂) := by
  classical
  obtain ⟨π, h1, h2, h3⟩ := h
  let K : α × β → PMF (γ × δ) := fun q =>
    if hq : R q.1 q.2 then Classical.choose (hK q.1 q.2 hq) else prodLaw (f q.1) (g q.2)
  have hK1 : ∀ q, (K q).map Prod.fst = f q.1 := by
    intro q; by_cases hq : R q.1 q.2
    · simp only [K, dif_pos hq]; exact (Classical.choose_spec (hK q.1 q.2 hq)).1
    · simp only [K, dif_neg hq]; exact prodLaw_fst _ _
  have hK2 : ∀ q, (K q).map Prod.snd = g q.2 := by
    intro q; by_cases hq : R q.1 q.2
    · simp only [K, dif_pos hq]; exact (Classical.choose_spec (hK q.1 q.2 hq)).2.1
    · simp only [K, dif_neg hq]; exact prodLaw_snd _ _
  have hK3 : ∀ q, (K q).toOuterMeasure {r | ¬ S r.1 r.2} ≤
      ε₂ + ({q | ¬ R q.1 q.2} : Set (α × β)).indicator 1 q := by
    intro q; by_cases hq : R q.1 q.2
    · simp only [K, dif_pos hq]
      exact (Classical.choose_spec (hK q.1 q.2 hq)).2.2.trans le_self_add
    · simp only [K, dif_neg hq]
      rw [Set.indicator_of_mem (by simpa using hq)]
      exact (outer_le_one _ _).trans le_add_self
  refine ⟨π.bind K, ?_, ?_, ?_⟩
  · rw [PMF.map_bind]; simp_rw [hK1]; rw [← h1, PMF.bind_map]; rfl
  · rw [PMF.map_bind]; simp_rw [hK2]; rw [← h2, PMF.bind_map]; rfl
  · rw [PMF.toOuterMeasure_bind_apply]
    calc ∑' q, π q * (K q).toOuterMeasure {r | ¬ S r.1 r.2}
        ≤ ∑' q, π q * (({q | ¬ R q.1 q.2} : Set (α × β)).indicator 1 q + ε₂) :=
          ENNReal.tsum_le_tsum fun q => by gcongr; rw [add_comm]; exact hK3 q
      _ = pexp π (({q | ¬ R q.1 q.2} : Set (α × β)).indicator 1) + ε₂ :=
          pexp_add_const π _ ε₂
      _ ≤ ε₁ + ε₂ := by rw [← outer_eq_pexp]; gcongr

theorem ACouple.map {μ : PMF α} {ν : PMF β} {R : α → β → Prop} {S : γ → δ → Prop}
    {ε : ℝ≥0∞} (h : ACouple μ ν R ε) (f : α → γ) (g : β → δ)
    (hfg : ∀ a b, R a b → S (f a) (g b)) : ACouple (μ.map f) (ν.map g) S ε := by
  rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  simpa [Function.comp_def] using h.bind (S := S) (ε₂ := 0) fun a b hab => ACouple.pure (hfg a b hab)

/-- INTERNAL: a draw on the left only, charged by the probability of leaving `P`. -/
theorem ACouple.bind_left {μ : PMF α} {f : α → PMF γ} {ν : PMF δ} {P : α → Prop}
    {S : γ → δ → Prop} {ε₁ ε₂ : ℝ≥0∞} (hμ : μ.toOuterMeasure {a | ¬ P a} ≤ ε₁)
    (hK : ∀ a, P a → ACouple (f a) ν S ε₂) : ACouple (μ.bind f) ν S (ε₁ + ε₂) := by
  have h0 : ACouple μ (PMF.pure ()) (fun a _ => P a) ε₁ := by
    refine ⟨μ.map fun a => (a, ()), by simp [PMF.map_comp, Function.comp_def, pmf_map_id'],
      by simp [PMF.map_comp, Function.comp_def, pmf_map_const'], ?_⟩
    rw [PMF.toOuterMeasure_map_apply]; exact hμ
  simpa using h0.bind (g := fun _ => ν) fun a _ ha => hK a ha

/-- INTERNAL: the right-hand outcome may be assumed in the support. -/
theorem ACouple.support_right {μ : PMF α} {ν : PMF β} {R : α → β → Prop} {ε : ℝ≥0∞}
    (h : ACouple μ ν R ε) : ACouple μ ν (fun a b => R a b ∧ b ∈ ν.support) ε := by
  obtain ⟨π, h1, h2, h3⟩ := h
  refine ⟨π, h1, h2, ?_⟩
  have hsub : {q : α × β | ¬ (R q.1 q.2 ∧ q.2 ∈ ν.support)} ⊆
      {q | ¬ R q.1 q.2} ∪ Prod.snd ⁻¹' {b | b ∉ ν.support} := by
    intro q hq; by_cases hR : R q.1 q.2
    · exact Or.inr fun hb => hq ⟨hR, hb⟩
    · exact Or.inl hR
  have hzero : π.toOuterMeasure (Prod.snd ⁻¹' {b | b ∉ ν.support}) = 0 := by
    rw [← PMF.toOuterMeasure_map_apply, h2, PMF.toOuterMeasure_apply_eq_zero_iff]
    exact Set.disjoint_left.2 fun b hb hb' => hb' hb
  calc π.toOuterMeasure _ ≤ π.toOuterMeasure ({q | ¬ R q.1 q.2} ∪ _) :=
        PMF.toOuterMeasure_mono _ (by
          intro q hq; exact hsub hq.1)
    _ ≤ π.toOuterMeasure {q | ¬ R q.1 q.2} + π.toOuterMeasure _ := MeasureTheory.measure_union_le _ _
    _ ≤ ε := by rw [hzero, add_zero]; exact h3

end

/-- INTERNAL: couplings compose along `loop`, with an index-dependent relation;
the costs add. -/
theorem ACouple.loop {β γ : Type} {f : ℕ → β → PMF β} {g : ℕ → γ → PMF γ}
    {R : ℕ → β → γ → Prop} {ζ : ℕ → ℝ≥0∞} (k : ℕ)
    (h : ∀ i < k, ∀ x y, R i x y → ACouple (f i x) (g i y) (R (i + 1)) (ζ i))
    {x : β} {y : γ} (h0 : R 0 x y) :
    ACouple (Pseudocode.loop f k x) (Pseudocode.loop g k y) (R k)
      (∑ i ∈ Finset.range k, ζ i) := by
  induction k with
  | zero => simpa using ACouple.pure h0
  | succ k ih =>
    rw [loop_succ, loop_succ, Finset.sum_range_succ]
    exact (ih fun i hi => h i (by omega)).bind fun a b hab => h k (by omega) a b hab

/-- INTERNAL: the maximal coupling: one-sided total variation `ζ` gives an equality
coupling failing with probability at most `ζ`. -/
theorem ACouple.of_pclose {α : Type*} {μ ν : PMF α} {ζ : ℝ≥0∞} (h : PClose μ ν ζ) :
    ACouple μ ν (· = ·) ζ := by
  classical
  set m : α → ℝ≥0∞ := fun a => min (μ a) (ν a) with hm
  set dμ : α → ℝ≥0∞ := fun a => μ a - m a with hdμ
  set dν : α → ℝ≥0∞ := fun a => ν a - m a with hdν
  set c : ℝ≥0∞ := ∑' a, dμ a with hc
  have hμsplit : ∀ a, m a + dμ a = μ a := fun a => add_tsub_cancel_of_le (min_le_left _ _)
  have hνsplit : ∀ a, m a + dν a = ν a := fun a => add_tsub_cancel_of_le (min_le_right _ _)
  have hM1 : ∑' a, m a + c = 1 := by
    rw [hc, ← ENNReal.tsum_add]; simp_rw [hμsplit]; exact μ.tsum_coe
  have hM2 : ∑' a, m a + ∑' a, dν a = 1 := by
    rw [← ENNReal.tsum_add]; simp_rw [hνsplit]; exact ν.tsum_coe
  have hMtop : ∑' a, m a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hM1 ▸ le_self_add)
  have hcν : ∑' a, dν a = c := (ENNReal.add_right_inj hMtop).1 (hM2.trans hM1.symm)
  have hctop : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hM1 ▸ le_add_self)
  have hcancel : ∀ x, x ≤ c → x * c * c⁻¹ = x := by
    intro x hx
    by_cases hc0 : c = 0
    · have : x = 0 := le_antisymm (hc0 ▸ hx) zero_le
      simp [this]
    · rw [mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, mul_one]
  have hcancel' : ∀ x, x ≤ c → c * x * c⁻¹ = x := by
    intro x hx; rw [mul_comm c x]; exact hcancel x hx
  set f : α × α → ℝ≥0∞ := fun q => (if q.1 = q.2 then m q.1 else 0) + dμ q.1 * dν q.2 * c⁻¹
    with hf
  have hrow : ∀ a, ∑' b, f (a, b) = μ a := by
    intro a
    simp only [hf]
    rw [ENNReal.tsum_add, tsum_eq_single a (fun x hx => by simp [Ne.symm hx]), if_pos rfl,
      ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, hcν,
      hcancel _ (ENNReal.le_tsum a), hμsplit]
  have hcol : ∀ b, ∑' a, f (a, b) = ν b := by
    intro b
    simp only [hf]
    rw [ENNReal.tsum_add, tsum_eq_single b (fun x hx => by simp [hx]), if_pos rfl,
      ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, ← hc,
      hcancel' _ (hcν ▸ ENNReal.le_tsum b), hνsplit]
  have htot : ∑' q, f q = 1 := by
    rw [ENNReal.tsum_prod']; simp_rw [hrow]; exact μ.tsum_coe
  let π : PMF (α × α) := ⟨f, ENNReal.summable.hasSum_iff.2 htot⟩
  have hπ : ∀ q, π q = f q := fun _ => rfl
  refine ⟨π, ?_, ?_, ?_⟩
  · ext a
    rw [PMF.map_apply, ENNReal.tsum_prod']
    simp_rw [hπ]
    rw [tsum_eq_single a (fun x hx => by simp [Ne.symm hx])]
    simp [hrow]
  · ext b
    rw [PMF.map_apply, ENNReal.tsum_prod', ENNReal.tsum_comm]
    simp_rw [hπ]
    rw [tsum_eq_single b (fun x hx => by simp [Ne.symm hx])]
    simp [hcol]
  · -- off-diagonal mass is at most `c`, and `c ≤ ζ`
    have hoff : π.toOuterMeasure {q | ¬ q.1 = q.2} ≤ c := by
      rw [PMF.toOuterMeasure_apply]
      calc ∑' q, ({q : α × α | ¬ q.1 = q.2}.indicator π q)
          ≤ ∑' q : α × α, dμ q.1 * dν q.2 * c⁻¹ := by
            refine ENNReal.tsum_le_tsum fun q => ?_
            by_cases hq : q.1 = q.2
            · simp [hq]
            · rw [Set.indicator_of_mem (by simpa using hq), hπ]; simp [hf, hq]
        _ = c * c * c⁻¹ := by
            rw [ENNReal.tsum_prod']
            simp_rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, hcν]
            rw [ENNReal.tsum_mul_right, ← hc]
        _ = c := hcancel c le_rfl
    have hcζ : c ≤ ζ := by
      set A : Set α := {a | ν a < μ a}
      have hA := h (A.indicator 1) fun a => by by_cases ha : a ∈ A <;> simp [ha]
      have hsplitA : pexp μ (A.indicator 1) = pexp ν (A.indicator 1) + c := by
        simp only [pexp, hc]
        rw [← ENNReal.tsum_add]
        congr 1; funext a
        by_cases ha : a ∈ A
        · have ha' : ν a < μ a := ha
          have : m a = ν a := min_eq_right ha'.le
          simp only [Set.indicator_of_mem ha, Pi.one_apply, mul_one, hdμ, this]
          exact (add_tsub_cancel_of_le ha'.le).symm
        · have ha' : μ a ≤ ν a := not_lt.1 ha
          have : m a = μ a := min_eq_left ha'
          simp [Set.indicator_of_notMem ha, hdμ, this]
      rw [hsplitA] at hA
      have hfin : pexp ν (A.indicator 1) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top
          (pexp_le_one _ _ fun a => by by_cases ha : a ∈ A <;> simp [ha])
      exact (ENNReal.add_le_add_iff_left hfin).1 hA
    exact hoff.trans hcζ
end Cellcounting.Analysis
