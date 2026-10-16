import Cellcounting.Analysis.RefStationary

/-!
# Detailed balance of the exact Metropolis chain `P_{j, w}` (`transport.tex:70-84`)

Every pair of states of `X` satisfies `π(S) P(S, S') = π(S') P(S', S)`.  For distinct
states, `P(S, S') = N(S, S') / (2 p²) · clip(λ(S')/λ(S))`, where `N(S, S')` counts the
pairs of uniform draws whose exchange turns `S` into `S'` and `clip = max 0 (min 1 ·)`
(`rsr_refStep_apply`).  A state of `X` has exactly `p` elements inside `[0, 2p)` and
`p` outside, so the draws biject with the exchanges `(a, b) ∈ S × ([0, 2p) \ S)` and
`N(S, S') = N(S', S)` (`rsr_count_symm`); and `λ(S) clip(λ(S')/λ(S))` is symmetric
(`rsr_acc_symm`), equal to `min{λ(S), λ(S')}` when both are nonnegative.  The
symmetry holds for arbitrary real `λ`, so goodness of the multipliers is not used.
-/

namespace Cellcounting.Analysis

open Pseudocode


/-- INTERNAL: the mass function of the exact uniform draw on `{0, …, k-1}`. -/
theorem rsr_uniformBelow_apply {k : ℕ} (hk : 0 < k) (u : ℕ) :
    uniformBelow k u = if u < k then (k : ENNReal)⁻¹ else 0 := by
  unfold uniformBelow
  rw [dif_pos hk]
  erw [PMF.uniformOfFinset_apply]
  simp [Finset.mem_range]

/-- INTERNAL: averaging over an exact uniform draw is a finite average. -/
theorem rsr_tsum_uniformBelow {k : ℕ} (hk : 0 < k) (f : ℕ → ENNReal) :
    ∑' u, uniformBelow k u * f u = ∑ u ∈ Finset.range k, (k : ENNReal)⁻¹ * f u := by
  rw [tsum_eq_sum (s := Finset.range k)]
  · refine Finset.sum_congr rfl fun u hu => ?_
    rw [rsr_uniformBelow_apply hk, if_pos (Finset.mem_range.1 hu)]
  · intro u hu
    rw [rsr_uniformBelow_apply hk, if_neg (by simpa using hu), zero_mul]

/-- INTERNAL: `do`-notation bind in `PMF` is `PMF.bind`. -/
theorem rsr_bind_eq {α β : Type} (p : PMF α) (f : α → PMF β) : (p >>= f) = p.bind f := rfl
/-- INTERNAL: `pure` in `PMF` is `PMF.pure`. -/
theorem rsr_pure_eq {α : Type} (a : α) : (pure a : PMF α) = PMF.pure a := rfl

/-- INTERNAL: the acceptance coin accepts with probability `max 0 (min 1 r)`. -/
theorem rsr_refAccept_true (r : ℝ) :
    refAccept r true = ((Real.toNNReal (min 1 r) : NNReal) : ENNReal) := by
  unfold refAccept; simp [PMF.bernoulli_apply]

/-- INTERNAL: the off-diagonal mass `P(S, T)` of `refStep` into a state `T ∈ X`: half (the
non-hold coin) times the average over the two uniform draws of the acceptance probability
of those draws that propose `T`.
TEXLINE: sections/transport.tex:60-69 -/
theorem rsr_refStep_apply (I : Instance) (ε δ : ℚ) (a : ℕ) (w : ℕ → ℕ → ℚ) (S T : Finset ℕ) (hTS : T ≠ S)
    (hT : kind I ε δ T ≠ .outside) (hp : pSmall I ε δ ≠ 0) :
    refStep I ε δ a w S T = 2⁻¹ * ∑ u1 ∈ Finset.range (pSmall I ε δ), ∑ u2 ∈ Finset.range (pSmall I ε δ),
      ((pSmall I ε δ : ENNReal)⁻¹ * ((pSmall I ε δ : ENNReal)⁻¹ *
        if insert (nthWith I ε δ S false u2) (S.erase (nthWith I ε δ S true u1)) = T then
          ((Real.toNNReal (min 1 (refLam I ε δ T a w / refLam I ε δ S a w)) : NNReal) : ENNReal) else 0)) := by
  have hp' : 0 < pSmall I ε δ := Nat.pos_of_ne_zero hp
  unfold refStep
  simp only [rsr_bind_eq, rsr_pure_eq]
  rw [PMF.bind_apply, tsum_bool]
  simp only [Arlib.Computation.ProbRAM.fair_apply, Bool.false_eq_true, ↓reduceIte, PMF.pure_apply, hTS,
    mul_zero, add_zero, PMF.bind_apply, rsr_tsum_uniformBelow hp', one_div]
  congr 1
  refine Finset.sum_congr rfl fun u1 _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u2 _ => ?_
  congr 2
  generalize insert (nthWith I ε δ S false u2) (S.erase (nthWith I ε δ S true u1)) = S'
  by_cases h : S' = T
  · subst h
    rw [if_pos rfl]
    split
    · exact absurd ‹_› hT
    · rw [PMF.bind_apply, tsum_bool]
      simp [PMF.pure_apply, hTS, rsr_refAccept_true]
  · rw [if_neg h]
    split
    · simp [PMF.pure_apply, hTS]
    · rw [PMF.bind_apply, tsum_bool]
      simp [PMF.pure_apply, hTS, Ne.symm h]


/-- INTERNAL: a sum over `[0, 2n)` grouped by pairs `{2i, 2i+1}`. -/
theorem rsr_sum_range_two_mul (f : ℕ → ℕ) (n : ℕ) :
    ∑ e ∈ Finset.range (2 * n), f e = ∑ i ∈ Finset.range n, (f (2 * i) + f (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

/-- INTERNAL: a state of `X` has exactly `p` elements (transversals have one per pair;
a defect state has one empty pair and one full pair).
TEXLINE: sections/signatures.tex:13-41 -/
theorem rsr_card_of_chain (I : Instance) (ε δ : ℚ) (S : Finset ℕ) (hS : S ∈ chainStates I ε δ) :
    S.card = pSmall I ε δ := by
  simp only [chainStates, refStates, Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨hsub, hk⟩ := hS
  set E := (Finset.range (pSmall I ε δ)).filter fun i => 2 * i ∉ S ∧ 2 * i + 1 ∉ S with hE
  set F := (Finset.range (pSmall I ε δ)).filter fun i => 2 * i ∈ S ∧ 2 * i + 1 ∈ S with hF
  have hEF : E.card = F.card := by
    have : kind I ε δ S = if E.card = 0 then (if F.card = 0 then .transversal else .outside)
        else if E.card = 1 ∧ F.card = 1 then .defect (E.sup id) (F.sup id) else .outside := rfl
    rw [this] at hk
    split_ifs at hk with h1 h2 h3 <;> first | exact absurd rfl hk | omega
  have hSc : S.card = ∑ e ∈ Finset.range (2 * pSmall I ε δ), if e ∈ S then 1 else 0 := by
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hsub]
  have hcount : S.card + E.card = pSmall I ε δ + F.card := by
    rw [hSc, rsr_sum_range_two_mul, hE, hF, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    rw [show ∀ g : ℕ → ℕ, pSmall I ε δ + ∑ i ∈ Finset.range (pSmall I ε δ), g i =
        ∑ i ∈ Finset.range (pSmall I ε δ), (1 + g i) from fun g => by
      rw [Finset.sum_add_distrib]; simp]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : 2 * i ∈ S <;> by_cases h2 : 2 * i + 1 ∈ S <;> simp [h1, h2]
  omega

/-- INTERNAL: `a · clip(b/a)` is symmetric in `a, b`, where `clip` is the clipped
acceptance probability `max 0 (min 1 ·)`; for `a, b ≥ 0` both sides are `min a b`.
TEXLINE: sections/transport.tex:78-84 -/
theorem rsr_acc_symm (a b : ℝ) :
    a * max (min 1 (b / a)) 0 = b * max (min 1 (a / b)) 0 := by
  rcases lt_trichotomy a 0 with ha | rfl | ha <;> rcases lt_trichotomy b 0 with hb | rfl | hb
  · rcases le_total a b with hab | hab
    · rw [min_eq_right ((div_le_one_of_neg ha).2 hab), min_eq_left ((one_le_div_of_neg hb).2 hab),
        max_eq_left zero_le_one, max_eq_left (div_nonneg_of_nonpos hb.le ha.le)]
      field_simp [ha.ne, hb.ne]
    · rw [min_eq_left ((one_le_div_of_neg ha).2 hab), min_eq_right ((div_le_one_of_neg hb).2 hab),
        max_eq_left zero_le_one, max_eq_left (div_nonneg_of_nonpos ha.le hb.le)]
      field_simp [ha.ne, hb.ne]
  · simp
  · rw [max_eq_right (min_le_of_right_le (div_nonpos_of_nonneg_of_nonpos hb.le ha.le)),
      max_eq_right (min_le_of_right_le (div_nonpos_of_nonpos_of_nonneg ha.le hb.le))]
    simp
  · simp
  · simp
  · simp
  · rw [max_eq_right (min_le_of_right_le (div_nonpos_of_nonpos_of_nonneg hb.le ha.le)),
      max_eq_right (min_le_of_right_le (div_nonpos_of_nonneg_of_nonpos ha.le hb.le))]
    simp
  · simp
  · rcases le_total a b with hab | hab
    · rw [min_eq_left ((one_le_div ha).2 hab), min_eq_right ((div_le_one hb).2 hab),
        max_eq_left zero_le_one, max_eq_left (div_nonneg ha.le hb.le)]
      field_simp [ha.ne, hb.ne]
    · rw [min_eq_right ((div_le_one ha).2 hab), min_eq_left ((one_le_div hb).2 hab),
        max_eq_left zero_le_one, max_eq_left (div_nonneg hb.le ha.le)]
      field_simp [ha.ne, hb.ne]

/-- INTERNAL: states of `X` lie in `[0, 2p)`. -/
theorem rsr_sub_of_chain (I : Instance) (ε δ : ℚ) (S : Finset ℕ) (hS : S ∈ chainStates I ε δ) :
    S ⊆ Finset.range (2 * pSmall I ε δ) := by
  simp only [chainStates, refStates, Finset.mem_filter, Finset.mem_powerset] at hS
  exact hS.1

/-- INTERNAL: `nthWith S v` indexes a duplicate-free list of length `p` listing the
elements of `[0, 2p)` whose membership in `S` is `v`. -/
theorem rsr_nthWith_list (I : Instance) (ε δ : ℚ) (S : Finset ℕ) (hS : S ∈ chainStates I ε δ)
    (v : Bool) : ∃ L : List ℕ, L.Nodup ∧ L.length = pSmall I ε δ ∧
      (∀ e, e ∈ L ↔ e < 2 * pSmall I ε δ ∧ (e ∈ S ↔ v = true)) ∧
      ∀ u, nthWith I ε δ S v u = L.getD u 0 := by
  have hsub := rsr_sub_of_chain I ε δ S hS
  have hcard := rsr_card_of_chain I ε δ S hS
  set L := (List.range (2 * pSmall I ε δ)).filter fun e => decide (e ∈ S) == v with hL
  have hnd : L.Nodup := List.nodup_range.filter _
  have hmem : ∀ e, e ∈ L ↔ e < 2 * pSmall I ε δ ∧ (e ∈ S ↔ v = true) := by
    intro e
    rw [hL, List.mem_filter, List.mem_range]
    cases v <;> simp
  refine ⟨L, hnd, ?_, hmem, fun u => rfl⟩
  rw [← List.toFinset_card_of_nodup hnd]
  cases v
  · have : L.toFinset = Finset.range (2 * pSmall I ε δ) \ S := by
      ext e; simp [List.mem_toFinset, hmem]
    rw [this, Finset.card_sdiff_of_subset hsub, Finset.card_range, hcard]; omega
  · have : L.toFinset = S := by
      ext e; rw [List.mem_toFinset, hmem]
      simp only [iff_true]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_range.1 (hsub h), h⟩⟩
    rw [this, hcard]

/-- INTERNAL: `getD` inside the bounds is indexing. -/
theorem rsr_getD {l : List ℕ} {n : ℕ} (h : n < l.length) : l.getD n 0 = l[n] := by simp [h]

/-- INTERNAL: the pairs of draws proposing `T` from `S` are in bijection with the
exchanges `(a, b) ∈ S × ([0, 2p) \ S)` with `S - a + b = T`. -/
theorem rsr_count_eq (I : Instance) (ε δ : ℚ) (S T : Finset ℕ) (hS : S ∈ chainStates I ε δ) :
    ((Finset.range (pSmall I ε δ) ×ˢ Finset.range (pSmall I ε δ)).filter fun u =>
        insert (nthWith I ε δ S false u.2) (S.erase (nthWith I ε δ S true u.1)) = T).card =
      ((S ×ˢ (Finset.range (2 * pSmall I ε δ) \ S)).filter fun x =>
        insert x.2 (S.erase x.1) = T).card := by
  obtain ⟨L1, hnd1, hlen1, hmem1, hn1⟩ := rsr_nthWith_list I ε δ S hS true
  obtain ⟨L2, hnd2, hlen2, hmem2, hn2⟩ := rsr_nthWith_list I ε δ S hS false
  refine Finset.card_nbij (fun u => (nthWith I ε δ S true u.1, nthWith I ε δ S false u.2))
    ?_ ?_ ?_
  · intro u hu
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product, Finset.mem_range] at hu ⊢
    obtain ⟨⟨h1, h2⟩, he⟩ := hu
    rw [hn1, rsr_getD (hlen1 ▸ h1)] at he ⊢
    rw [hn2, rsr_getD (hlen2 ▸ h2)] at he ⊢
    refine ⟨⟨?_, ?_⟩, he⟩
    · exact ((hmem1 _).1 (List.getElem_mem _)).2.2 rfl
    · have := (hmem2 _).1 (List.getElem_mem (hlen2 ▸ h2))
      exact Finset.mem_sdiff.2 ⟨Finset.mem_range.2 this.1, fun h => by simpa using this.2.1 h⟩
  · rintro ⟨u1, u2⟩ hu ⟨u1', u2'⟩ hu' heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product, Finset.mem_range] at hu hu'
    simp only [Prod.mk.injEq, hn1, hn2] at heq
    rw [rsr_getD (hlen1 ▸ hu.1.1), rsr_getD (hlen1 ▸ hu'.1.1),
      rsr_getD (hlen2 ▸ hu.1.2), rsr_getD (hlen2 ▸ hu'.1.2),
      hnd1.getElem_inj_iff, hnd2.getElem_inj_iff] at heq
    rw [heq.1, heq.2]
  · rintro ⟨a, b⟩ hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product, Finset.mem_sdiff,
      Finset.mem_range] at hx
    obtain ⟨⟨ha, hb, hbS⟩, he⟩ := hx
    obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.1 ((hmem1 a).2 ⟨by
      have := rsr_sub_of_chain I ε δ S hS ha; simpa using this, by simp [ha]⟩)
    obtain ⟨k, hk, hkb⟩ := List.mem_iff_getElem.1 ((hmem2 b).2 ⟨hb, by simp [hbS]⟩)
    refine ⟨(i, k), ?_, ?_⟩
    · simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product, Finset.mem_range]
      rw [hn1, hn2, rsr_getD hi, rsr_getD hk, hia, hkb]
      exact ⟨⟨hlen1 ▸ hi, hlen2 ▸ hk⟩, he⟩
    · simp only [hn1, hn2, rsr_getD hi, rsr_getD hk, hia, hkb]

/-- INTERNAL: an exchange `S - a + b = T` reverses to `T - b + a = S`. -/
theorem rsr_swap_mem (S T R : Finset ℕ) (hsub : S ⊆ R) (x : ℕ × ℕ)
    (hx : x ∈ (S ×ˢ (R \ S)).filter fun x => insert x.2 (S.erase x.1) = T) :
    x.swap ∈ (T ×ˢ (R \ T)).filter fun x => insert x.2 (T.erase x.1) = S := by
  obtain ⟨a, b⟩ := x
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff, Prod.swap_prod_mk] at hx ⊢
  obtain ⟨⟨ha, hbR, hbS⟩, rfl⟩ := hx
  have hab : a ≠ b := fun h => hbS (h ▸ ha)
  refine ⟨⟨Finset.mem_insert_self _ _, hsub ha, ?_⟩, ?_⟩
  · simp [hab]
  · rw [Finset.erase_insert (fun h => hbS (Finset.mem_of_mem_erase h)), Finset.insert_erase ha]

/-- INTERNAL: the number of draws proposing `T` from `S` equals the number proposing `S`
from `T`: the proposal kernel is symmetric on `X`.
TEXLINE: sections/transport.tex:78-84 -/
theorem rsr_count_symm (I : Instance) (ε δ : ℚ) (S T : Finset ℕ) (hS : S ∈ chainStates I ε δ)
    (hT : T ∈ chainStates I ε δ) :
    ((Finset.range (pSmall I ε δ) ×ˢ Finset.range (pSmall I ε δ)).filter fun u =>
        insert (nthWith I ε δ S false u.2) (S.erase (nthWith I ε δ S true u.1)) = T).card =
      ((Finset.range (pSmall I ε δ) ×ˢ Finset.range (pSmall I ε δ)).filter fun u =>
        insert (nthWith I ε δ T false u.2) (T.erase (nthWith I ε δ T true u.1)) = S).card := by
  rw [rsr_count_eq I ε δ S T hS, rsr_count_eq I ε δ T S hT]
  exact Finset.card_nbij' Prod.swap Prod.swap
    (fun x hx => rsr_swap_mem S T _ (rsr_sub_of_chain I ε δ S hS) x hx)
    (fun x hx => rsr_swap_mem T S _ (rsr_sub_of_chain I ε δ T hT) x hx)
    (fun x _ => Prod.swap_swap x) (fun x _ => Prod.swap_swap x)

/-- INTERNAL: `P(S, T)` as a real number, for `T ≠ S` in `X`.
TEXLINE: sections/transport.tex:60-69 -/
theorem rsr_refPk_ne (I : Instance) (ε δ : ℚ) (a : ℕ) (w : ℕ → ℕ → ℚ) (S T : Finset ℕ)
    (hTS : T ≠ S) (hT : kind I ε δ T ≠ .outside) (hp : pSmall I ε δ ≠ 0) :
    refPk I ε δ a w S T =
      2⁻¹ * ((pSmall I ε δ : ℝ)⁻¹ * ((pSmall I ε δ : ℝ)⁻¹ *
        (((Finset.range (pSmall I ε δ) ×ˢ Finset.range (pSmall I ε δ)).filter fun u =>
          insert (nthWith I ε δ S false u.2) (S.erase (nthWith I ε δ S true u.1)) = T).card : ℝ))) *
        max (min 1 (refLam I ε δ T a w / refLam I ε δ S a w)) 0 := by
  unfold refPk
  rw [rsr_refStep_apply I ε δ a w S T hTS hT hp, ← Finset.sum_product']
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_ofNat,
    ENNReal.coe_toReal, Real.coe_toNNReal']
  ring

/-- **Reversibility of `P_{j, w}`** (`transport.tex:78-84`): detailed balance
`π(S) P(S, S') = π(S') P(S', S)` on `X`, for good multipliers.
PAPER: sections/transport.tex:78-84 -/
theorem refStep_reversible (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (j : ℕ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) (S S' : Finset ℕ)
    (hS : S ∈ chainStates I ε δ) (hS' : S' ∈ chainStates I ε δ) :
    refPi I ε δ j w S * refPk I ε δ j w S S' = refPi I ε δ j w S' * refPk I ε δ j w S' S := by
  by_cases hSS : S = S'
  · subst hSS; rfl
  have hk : kind I ε δ S ≠ .outside := by
    simp only [chainStates, Finset.mem_filter] at hS; exact hS.2
  have hk' : kind I ε δ S' ≠ .outside := by
    simp only [chainStates, Finset.mem_filter] at hS'; exact hS'.2
  rw [refPi, refPi, if_pos hS, if_pos hS', rsr_refPk_ne I ε δ j w S S' (Ne.symm hSS) hk' hp,
    rsr_refPk_ne I ε δ j w S' S hSS hk hp, rsr_count_symm I ε δ S S' hS hS']
  have := rsr_acc_symm (refLam I ε δ S j w) (refLam I ε δ S' j w)
  calc _ = 2⁻¹ * ((pSmall I ε δ : ℝ)⁻¹ * ((pSmall I ε δ : ℝ)⁻¹ *
        (((Finset.range (pSmall I ε δ) ×ˢ Finset.range (pSmall I ε δ)).filter fun u =>
          insert (nthWith I ε δ S' false u.2) (S'.erase (nthWith I ε δ S' true u.1)) = S).card : ℝ)))
        / refLamTot I ε δ j w * (refLam I ε δ S j w *
          max (min 1 (refLam I ε δ S' j w / refLam I ε δ S j w)) 0) := by ring
    _ = _ := by rw [this]; ring

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `refStep_reversible` via explicit `P(S, T)` formula, proposal-count symmetry, `rsr_acc_symm`
-/
