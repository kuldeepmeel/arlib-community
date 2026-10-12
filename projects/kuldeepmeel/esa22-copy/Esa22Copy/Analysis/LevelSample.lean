import Esa22Copy.Interface.Pseudocode

/-!
# Level samples: Algorithm 3's `Y_k`, in law

`levelSample q S` keeps each element of `S` independently with probability
`2⁻q`: it is `q` successive fair throws (`Pseudocode.throw`, one fair coin per
element each time).  It is the law the paper's Claim `cl:loop`
(esa22-final.tex:624-678) assigns to Algorithm 3's set `Y_{q,j}` when
`S = S_j = {a₁,…,a_j}`: "every element of `S_j` is in `Y_q` independently with
probability `2⁻q`".

Its closed form (`levelSample_apply`) is `Pr[T] = 2^{-q|T|}(1-2^{-q})^{|S|-|T|}` for
`T ⊆ S`, with `1 - 2^{-q}` written subtraction-free as `levelMiss q`.  The
inductive step of `cl:loop` is `levelSample_bind_pick`: drop `a` and re-pick it at
level `q ≤ w` from a `w`-bit block.

The analysis never builds Algorithm 3's joint process over all levels.  It
uses only this per-level law, through a domination invariant for Algorithm 2
(`RelaxedDomination.lean`) that replaces the pathwise coupling
`(p_j, X_j) = (p_j, Y_{k,j})` of esa22-final.tex:684.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Esa22Copy.Analysis

open Esa22Copy.Interface.Pseudocode

variable {α : Type} [DecidableEq α] [Fintype α]

/-- **The law of `Y_{q,j}`** (Claim `cl:loop`, esa22-final.tex:624-678): every
element of `S` kept independently with probability `2⁻q`, as `q` successive fair
throws.

PAPER: esa22-final.tex:624-678 -/
noncomputable def levelSample : ℕ → Finset α → PMF (Finset α)
  | 0, S => PMF.pure S
  | q + 1, S => (throw S).bind (levelSample q)

/-- INTERNAL: unfolding equation at level `0`. -/
theorem levelSample_zero (S : Finset α) : levelSample 0 S = PMF.pure S := rfl

/-- INTERNAL: unfolding equation at level `q + 1`. -/
theorem levelSample_succ (q : ℕ) (S : Finset α) :
    levelSample (q + 1) S = (throw S).bind (levelSample q) := rfl

/-- INTERNAL: a level sample of `S` is a subset of `S`. -/
theorem levelSample_subset (q : ℕ) (S T : Finset α) (hT : T ∈ (levelSample q S).support) :
    T ⊆ S := by
  induction q generalizing S with
  | zero =>
    rw [levelSample_zero, PMF.support_pure] at hT
    exact (Set.mem_singleton_iff.1 hT).le
  | succ q ih =>
    rw [levelSample_succ, PMF.mem_support_bind_iff] at hT
    obtain ⟨U, hU, hTU⟩ := hT
    rw [Esa22Copy.Interface.Pseudocode.throw, PMF.support_map] at hU
    obtain ⟨R, -, rfl⟩ := hU
    exact (ih _ hTU).trans (Finset.filter_subset _ _)

open Arlib.Computation (Block)

/-- INTERNAL: the number of subsets `R` with `X ∩ R = U`, for `U ⊆ X`. -/
theorem card_filter_inter_eq (X U : Finset α) (hU : U ⊆ X) :
    (Finset.univ.filter (fun R : Finset α => X.filter (· ∈ R) = U)).card =
      2 ^ (Fintype.card α - X.card) := by
  rw [← Finset.card_compl, ← Finset.card_powerset]
  refine Finset.card_nbij' (fun R => R \ X) (fun V => U ∪ V) ?_ ?_ ?_ ?_
  · intro R _
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
    intro x hx
    simp only [Finset.mem_sdiff] at hx
    simpa using hx.2
  · intro V hV
    simp only [Finset.coe_powerset, Set.mem_powerset_iff, Finset.coe_subset] at hV
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    ext x
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hxX, hxU | hxV⟩
      · exact hxU
      · exact absurd hxX (Finset.mem_compl.1 (hV hxV))
    · rintro hxU
      exact ⟨hU hxU, Or.inl hxU⟩
  · intro R hR
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hR
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hxU | ⟨hxR, -⟩)
      · rw [← hR] at hxU; exact (Finset.mem_filter.1 hxU).2
      · exact hxR
    · intro hxR
      by_cases hxX : x ∈ X
      · left; rw [← hR]; exact Finset.mem_filter.2 ⟨hxX, hxR⟩
      · right; exact ⟨hxR, hxX⟩
  · intro V hV
    simp only [Finset.coe_powerset, Set.mem_powerset_iff, Finset.coe_subset] at hV
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hxU | hxV, hxX⟩
      · exact absurd (hU hxU) hxX
      · exact hxV
    · intro hxV
      exact ⟨Or.inr hxV, Finset.mem_compl.1 (hV hxV)⟩

/-- INTERNAL: the throw keeps exactly `U ⊆ X` with probability `2^{-|X|}`. -/
theorem throw_apply (X U : Finset α) :
    throw X U = if U ⊆ X then (2⁻¹ : ℝ≥0∞) ^ X.card else 0 := by
  rw [← PMF.toOuterMeasure_apply_singleton, Esa22Copy.Interface.Pseudocode.throw,
    PMF.toOuterMeasure_map_apply,
    show (fun R : Finset α => X.filter (· ∈ R)) ⁻¹' {U} = {R | X.filter (· ∈ R) = U} from rfl]
  split_ifs with hU
  · have hc : Fintype.card {R : Finset α | X.filter (· ∈ R) = U} =
        2 ^ (Fintype.card α - X.card) := by
      rw [Fintype.card_subtype]; exact card_filter_inter_eq X U hU
    rw [PMF.toOuterMeasure_uniformOfFintype_apply, hc, Fintype.card_finset]
    have hk : X.card ≤ Fintype.card α := Finset.card_le_univ X
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
    rw [hd, Nat.add_sub_cancel_left, pow_add]
    push_cast
    rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
      ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, ENNReal.inv_pow]
  · rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
    intro R _ hR
    exact hU (by rw [← hR]; exact Finset.filter_subset _ _)

/-- INTERNAL: `1 - 2^{-q}` without subtraction: `c₀ = 0`, `c_{q+1} = (1 + c_q)/2`. -/
noncomputable def levelMiss : ℕ → ℝ≥0∞
  | 0 => 0
  | q + 1 => 2⁻¹ * (1 + levelMiss q)

/-- INTERNAL: a sum over the sets between `T` and `S` reindexed by `U \ T`. -/
theorem sum_between (T S : Finset α) (hTS : T ⊆ S) (f : ℕ → ℝ≥0∞) :
    ∑ U : Finset α, (if U ⊆ S ∧ T ⊆ U then f (U.card - T.card) else 0) =
      ∑ V ∈ (S \ T).powerset, f V.card := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun U => U \ T) (fun V => T ∪ V) ?_ ?_ ?_ ?_ ?_
  · intro U hU
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
    exact Finset.mem_powerset.2 (Finset.sdiff_subset_sdiff hU.1 le_rfl)
  · intro V hV
    have hV' := Finset.mem_powerset.1 hV
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Finset.union_subset hTS (hV'.trans Finset.sdiff_subset), Finset.subset_union_left⟩
  · intro U hU
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
    exact Finset.union_sdiff_of_subset hU.2
  · intro V hV
    have hV' := Finset.mem_powerset.1 hV
    rw [Finset.union_sdiff_left]
    exact Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_of_subset_left hV'
      Finset.sdiff_disjoint)
  · intro U hU
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
    rw [Finset.card_sdiff_of_subset hU.2]

/-- INTERNAL: the closed form of a level sample: `T ⊆ S` with probability
`p^{|T|} (1-p)^{|S|-|T|}`, `p = 2^{-q}`.
TEXLINE: esa22-final.tex:624-678 -/
theorem levelSample_apply (q : ℕ) (S T : Finset α) :
    levelSample q S T =
      if T ⊆ S then ((2⁻¹ : ℝ≥0∞) ^ q) ^ T.card * levelMiss q ^ (S.card - T.card) else 0 := by
  induction q generalizing S T with
  | zero =>
    rw [levelSample_zero, PMF.pure_apply]
    by_cases hTS : T = S
    · subst hTS; simp [levelMiss]
    · rw [if_neg hTS]
      split_ifs with h
      · have hlt : T.card < S.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨h, hTS⟩)
        simp [levelMiss, Nat.sub_ne_zero_of_lt hlt]
      · rfl
  | succ q ih =>
    rw [levelSample_succ, PMF.bind_apply, tsum_fintype]
    simp only [throw_apply, ih, ite_mul, zero_mul, mul_ite, mul_zero]
    split_ifs with hTS
    · have : ∀ U : Finset α, (if T ⊆ U then (if U ⊆ S then (2⁻¹ : ℝ≥0∞) ^ S.card *
            (((2⁻¹ : ℝ≥0∞) ^ q) ^ T.card * levelMiss q ^ (U.card - T.card)) else 0) else 0) =
          (2⁻¹ : ℝ≥0∞) ^ S.card * ((2⁻¹ : ℝ≥0∞) ^ q) ^ T.card *
            (if U ⊆ S ∧ T ⊆ U then levelMiss q ^ (U.card - T.card) else 0) := by
        intro U
        by_cases h1 : U ⊆ S <;> by_cases h2 : T ⊆ U <;> simp [h1, h2, mul_assoc]
      simp only [this]
      rw [← Finset.mul_sum, sum_between T S hTS]
      have hsum : ∑ V ∈ (S \ T).powerset, levelMiss q ^ V.card =
          (levelMiss q + 1) ^ (S \ T).card := by
        simpa using Finset.sum_pow_mul_eq_add_pow (levelMiss q) (1 : ℝ≥0∞) (S \ T)
      rw [hsum, Finset.card_sdiff_of_subset hTS, levelMiss, mul_pow, pow_succ, mul_pow,
        add_comm (levelMiss q) 1]
      rw [show (2⁻¹ : ℝ≥0∞) ^ S.card = 2⁻¹ ^ T.card * 2⁻¹ ^ (S.card - T.card) by
        rw [← pow_add, Nat.add_sub_cancel' (Finset.card_le_card hTS)]]
      ring
    · refine Finset.sum_eq_zero fun U _ => ?_
      by_cases h1 : U ⊆ S
      · by_cases h2 : T ⊆ U
        · exact absurd (h2.trans h1) hTS
        · simp [h1, h2]
      · simp [h1]

open Arlib.Computation (Block)

/-- INTERNAL: the pick accepts iff the first `q` bits of its block are all one. -/
theorem acceptsAt_ofFun_iff {w q : ℕ} (hq : q ≤ w) (f : Fin w → Bool) :
    Esa22Copy.Interface.acceptsAt q (Block.ofFun f) = true ↔
      ∀ i : Fin w, (i : ℕ) < q → f i = true := by
  simp only [Esa22Copy.Interface.acceptsAt, hq, if_true, List.all_eq_true, id]
  constructor
  · intro h i hi
    have hmem : f i ∈ (List.ofFn (Block.ofFun f).get).take q := by
      rw [List.mem_iff_getElem]
      refine ⟨i, by simp; omega, ?_⟩
      simp [Block.ofFun, Arlib.Computation.Block.get]
    exact h _ hmem
  · intro h x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    simp only [List.length_take, List.length_ofFn] at hj
    simp only [List.getElem_take, List.getElem_ofFn]
    exact h ⟨j, by omega⟩ (by simp; omega)

/-- INTERNAL: `2^{w-q}` blocks of width `w` are accepted at level `q ≤ w`. -/
theorem card_accept {w q : ℕ} (hq : q ≤ w) :
    (Finset.univ.filter (fun f : Fin w → Bool =>
      Esa22Copy.Interface.acceptsAt q (Block.ofFun f) = true)).card = 2 ^ (w - q) := by
  have hset : Finset.univ.filter (fun f : Fin w → Bool =>
      Esa22Copy.Interface.acceptsAt q (Block.ofFun f) = true) =
      Fintype.piFinset (fun i : Fin w => if (i : ℕ) < q then ({true} : Finset Bool)
        else Finset.univ) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      acceptsAt_ofFun_iff hq]
    refine forall_congr' fun i => ?_
    split_ifs with h <;> simp [h]
  rw [hset, Fintype.card_piFinset]
  simp only [apply_ite Finset.card]
  rw [Finset.prod_ite]
  simp only [Finset.card_singleton, Finset.prod_const_one, one_mul, Finset.card_univ,
    Fintype.card_bool, Finset.prod_const]
  congr 1
  have h1 := Fin.card_filter_val_lt (n := w) (m := q)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin w))) (fun i : Fin w => (i : ℕ) < q)
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  omega


/-- INTERNAL: `levelMiss q = 1 - 2^{-q}`. -/
theorem levelMiss_add (q : ℕ) : levelMiss q + (2⁻¹ : ℝ≥0∞) ^ q = 1 := by
  induction q with
  | zero => simp [levelMiss]
  | succ q ih =>
    rw [levelMiss, pow_succ, mul_comm ((2⁻¹ : ℝ≥0∞) ^ q), ← mul_add, add_assoc, ih,
      one_add_one_eq_two, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

/-- INTERNAL: the pick at level `q ≤ w` accepts with probability `2^{-q}`.
TEXLINE: esa22-final.tex:672 -/
theorem prob_accept {w q : ℕ} (hq : q ≤ w) :
    (PMF.uniformOfFintype (Fin w → Bool)).toOuterMeasure
      {f | Esa22Copy.Interface.acceptsAt q (Block.ofFun f) = true} = (2⁻¹ : ℝ≥0∞) ^ q := by
  have hc : Fintype.card {f : Fin w → Bool |
      Esa22Copy.Interface.acceptsAt q (Block.ofFun f) = true} = 2 ^ (w - q) := by
    rw [Fintype.card_subtype]; exact card_accept hq
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, hc]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hq
  rw [hd, Nat.add_sub_cancel_left, pow_add]
  push_cast
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, ENNReal.inv_pow]

/-- INTERNAL: the pick at level `q ≤ w` rejects with probability `1 - 2^{-q}`. -/
theorem prob_reject {w q : ℕ} (hq : q ≤ w) :
    (PMF.uniformOfFintype (Fin w → Bool)).toOuterMeasure
      {f | Esa22Copy.Interface.acceptsAt q (Block.ofFun f) = false} = levelMiss q := by
  set μ := PMF.uniformOfFintype (Fin w → Bool)
  set A := {f : Fin w → Bool | Esa22Copy.Interface.acceptsAt q (Block.ofFun f) = true}
  have hsum : μ.toOuterMeasure A + μ.toOuterMeasure Aᶜ = 1 := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
    simp only [Set.indicator_self_add_compl_apply]
    exact μ.tsum_coe
  have hAc : Aᶜ = {f | Esa22Copy.Interface.acceptsAt q (Block.ofFun f) = false} := by
    ext f; simp [A]
  rw [← hAc]
  have h2 := levelMiss_add q
  rw [prob_accept hq] at hsum
  have hne : (2⁻¹ : ℝ≥0∞) ^ q ≠ ⊤ := by simp
  rw [add_comm] at hsum
  exact (ENNReal.add_left_inj hne).1 (hsum.trans h2.symm)

/-- INTERNAL: the law of the pick of a fresh element: add it w.p. `2^{-q}`. -/
theorem pick_apply {w q : ℕ} (hq : q ≤ w) (a : α) (X Y : Finset α) (ha : a ∉ X) :
    pick w q a X Y = (if Y = insert a X then (2⁻¹ : ℝ≥0∞) ^ q else 0) +
      (if Y = X then levelMiss q else 0) := by
  rw [← PMF.toOuterMeasure_apply_singleton, pick, PMF.toOuterMeasure_map_apply]
  have hne : insert a X ≠ X := fun h => ha (h ▸ Finset.mem_insert_self a X)
  by_cases h1 : Y = insert a X
  · subst h1
    rw [if_pos rfl, if_neg hne, add_zero, ← prob_accept hq]
    congr 1
    ext f
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    split_ifs with h <;> simp [h, hne.symm]
  · by_cases h2 : Y = X
    · subst h2
      rw [if_neg h1, if_pos rfl, zero_add, ← prob_reject hq]
      congr 1
      ext f
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      split_ifs with h <;> simp [h, hne]
    · rw [if_neg h1, if_neg h2, add_zero]
      rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
      intro f _ hf
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hf
      split_ifs at hf
      · exact h1 hf.symm
      · exact h2 hf.symm


omit [Fintype α] in
/-- INTERNAL: sets with the same erasure of `a` differ at most in `a`. -/
theorem eq_of_erase_eq {a : α} {U V : Finset α} (h : U.erase a = V.erase a) :
    U = V.erase a ∨ U = insert a (V.erase a) := by
  by_cases ha : a ∈ U
  · right; rw [← h, Finset.insert_erase ha]
  · left; rw [← h, Finset.erase_eq_of_notMem ha]

/-- **Claim `cl:loop`, inductive step** (esa22-final.tex:664-676): if every
element of `S` is in `Y_q` independently with probability `2⁻q`, then after
line `cfinal-drop` (`Y_q ← Y_q ∖ {a}`) and line `cfinal-pick` (add `a` with
probability `2⁻q`, a fresh draw), every element of `S ∪ {a}` is.  Needs
`q ≤ w`, so the pick's `w`-bit block yields a true Bernoulli(`2⁻q`).

PAPER: esa22-final.tex:664-676 -/
theorem levelSample_bind_pick (w q : ℕ) (hq : q ≤ w) (a : α) (S : Finset α) :
    (levelSample q S).bind (fun U => pick w q a (drop a U)) = levelSample q (insert a S) := by
  ext T
  rw [PMF.bind_apply, tsum_fintype]
  simp only [drop, pick_apply hq a _ _ (Finset.notMem_erase a _)]
  set p : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ q
  set c : ℝ≥0∞ := levelMiss q
  have hcp : c + p = 1 := levelMiss_add q
  by_cases haT : a ∈ T
  · have hne : T.erase a ≠ T := fun h => (Finset.notMem_erase a T) (by rw [h]; exact haT)
    rw [Finset.sum_eq_add (T.erase a) T hne]
    rotate_left
    · intro U _ hU
      have h1 : T ≠ U.erase a := fun h => Finset.notMem_erase a U (by rw [← h]; exact haT)
      have h2 : T ≠ insert a (U.erase a) := by
        intro h
        have : U.erase a = T.erase a := by rw [h, Finset.erase_insert (Finset.notMem_erase a U)]
        rcases eq_of_erase_eq this with h' | h'
        · exact hU.1 h'
        · exact hU.2 (h'.trans (Finset.insert_erase haT))
      simp [h1, h2]
    · simp
    · simp
    have e1 : (if T = insert a ((T.erase a).erase a) then p else 0) +
        (if T = (T.erase a).erase a then c else 0) = p := by
      rw [Finset.erase_idem, Finset.insert_erase haT, if_pos rfl, if_neg (Ne.symm hne), add_zero]
    have e2 : (if T = insert a (T.erase a) then p else 0) + (if T = T.erase a then c else 0) = p := by
      rw [Finset.insert_erase haT, if_pos rfl, if_neg (Ne.symm hne), add_zero]
    rw [e1, e2]
    rw [levelSample_apply, levelSample_apply, levelSample_apply]
    simp only [show ((2⁻¹ : ℝ≥0∞) ^ q) = p from rfl, show levelMiss q = c from rfl]
    have hk : 1 ≤ T.card := Finset.card_pos.2 ⟨a, haT⟩
    rw [Finset.card_erase_of_mem haT]
    by_cases haS : a ∈ S
    · rw [Finset.insert_eq_of_mem haS]
      by_cases hTS : T ⊆ S
      · have hTS' : T.erase a ⊆ S := (Finset.erase_subset a T).trans hTS
        rw [if_pos hTS', if_pos hTS]
        have hkn : T.card ≤ S.card := Finset.card_le_card hTS
        obtain ⟨k, hk'⟩ : ∃ k, T.card = k + 1 := ⟨T.card - 1, by omega⟩
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hkn
        rw [hd, hk', Nat.add_sub_cancel, show k + 1 + d - k = d + 1 by omega,
          Nat.add_sub_cancel_left]
        calc p ^ k * c ^ (d + 1) * p + p ^ (k + 1) * c ^ d * p
            = p ^ (k + 1) * c ^ d * (c + p) := by ring
          _ = p ^ (k + 1) * c ^ d := by rw [hcp, mul_one]
      · have hTS' : ¬ T.erase a ⊆ S := by
          intro h; apply hTS; intro x hx
          by_cases hxa : x = a
          · exact hxa ▸ haS
          · exact h (Finset.mem_erase.2 ⟨hxa, hx⟩)
        rw [if_neg hTS', if_neg hTS]; simp
    · have hTS : ¬ T ⊆ S := fun h => haS (h haT)
      simp only [if_neg hTS, zero_mul, add_zero]
      rw [Finset.card_insert_of_notMem haS]
      by_cases hTS' : T.erase a ⊆ S
      · have hTi : T ⊆ insert a S := by
          intro x hx
          by_cases hxa : x = a
          · exact hxa ▸ Finset.mem_insert_self a S
          · exact Finset.mem_insert_of_mem (hTS' (Finset.mem_erase.2 ⟨hxa, hx⟩))
        rw [if_pos hTS', if_pos hTi]
        have hkn : T.card - 1 ≤ S.card := by
          have := Finset.card_le_card hTS'; rwa [Finset.card_erase_of_mem haT] at this
        obtain ⟨k, hk'⟩ : ∃ k, T.card = k + 1 := ⟨T.card - 1, by omega⟩
        rw [hk', Nat.add_sub_cancel] at hkn ⊢
        rw [show S.card + 1 - (k + 1) = S.card - k by omega]
        ring
      · have hTi : ¬ T ⊆ insert a S := by
          intro h; apply hTS'; intro x hx
          have hx' := Finset.mem_erase.1 hx
          rcases Finset.mem_insert.1 (h hx'.2) with h' | h'
          · exact absurd h' hx'.1
          · exact h'
        rw [if_neg hTS', if_neg hTi]; simp
  · have hne : T ≠ insert a T := fun h => haT (h ▸ Finset.mem_insert_self a T)
    rw [Finset.sum_eq_add T (insert a T) hne]
    rotate_left
    · intro U _ hU
      have h1 : T ≠ insert a (U.erase a) := fun h => haT (h ▸ Finset.mem_insert_self _ _)
      have h2 : T ≠ U.erase a := by
        intro h
        have : U.erase a = T.erase a := by rw [← h, Finset.erase_eq_of_notMem haT]
        rcases eq_of_erase_eq this with h' | h'
        · exact hU.1 (h'.trans (Finset.erase_eq_of_notMem haT))
        · exact hU.2 (h'.trans (by rw [Finset.erase_eq_of_notMem haT]))
      simp [h1, h2]
    · simp
    · simp
    have e1 : (if T = insert a (T.erase a) then p else 0) + (if T = T.erase a then c else 0) = c := by
      rw [Finset.erase_eq_of_notMem haT, if_neg hne, if_pos rfl, zero_add]
    have e2 : (if T = insert a ((insert a T).erase a) then p else 0) +
        (if T = (insert a T).erase a then c else 0) = c := by
      rw [Finset.erase_insert haT, if_neg hne, if_pos rfl, zero_add]
    rw [e1, e2]
    rw [levelSample_apply, levelSample_apply, levelSample_apply,
      Finset.card_insert_of_notMem haT]
    simp only [show ((2⁻¹ : ℝ≥0∞) ^ q) = p from rfl, show levelMiss q = c from rfl]
    by_cases haS : a ∈ S
    · rw [Finset.insert_eq_of_mem haS]
      by_cases hTS : T ⊆ S
      · have hTS' : insert a T ⊆ S := Finset.insert_subset haS hTS
        rw [if_pos hTS, if_pos hTS']
        have hlt : T.card < S.card := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.2 ⟨hTS, fun h => haT (h ▸ haS)⟩)
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hlt
        rw [hd, show T.card + d + 1 - T.card = d + 1 by omega,
          show T.card + d + 1 - (T.card + 1) = d by omega]
        calc p ^ T.card * c ^ (d + 1) * c + p ^ (T.card + 1) * c ^ d * c
            = p ^ T.card * c ^ (d + 1) * (c + p) := by ring
          _ = p ^ T.card * c ^ (d + 1) := by rw [hcp, mul_one]
      · have hTS' : ¬ insert a T ⊆ S := fun h => hTS ((Finset.subset_insert a T).trans h)
        rw [if_neg hTS, if_neg hTS']; simp
    · have hTS' : ¬ insert a T ⊆ S := fun h => haS (h (Finset.mem_insert_self a T))
      simp only [if_neg hTS', zero_mul, add_zero]
      rw [Finset.card_insert_of_notMem haS]
      by_cases hTS : T ⊆ S
      · have hTi : T ⊆ insert a S := hTS.trans (Finset.subset_insert a S)
        rw [if_pos hTS, if_pos hTi]
        have hkn : T.card ≤ S.card := Finset.card_le_card hTS
        rw [show S.card + 1 - T.card = S.card - T.card + 1 by omega, pow_succ]
        ring
      · have hTi : ¬ T ⊆ insert a S := by
          intro h; apply hTS; intro x hx
          rcases Finset.mem_insert.1 (h hx) with h' | h'
          · exact absurd (h' ▸ hx) haT
          · exact h'
        rw [if_neg hTS, if_neg hTi]; simp


end Esa22Copy.Analysis
