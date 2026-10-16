import Cellcounting.Analysis.ForestPenaltyBound

/-!
# The penalty is `1/8`-Lipschitz in cube coordinates (`eq:scaled-penalty-bounds`)

`Cellcounting.Analysis.penalty_lipschitz`: on a feasible instance, if two free
vectors differ by at most `t (b_k + 1)/B` in every free coordinate `k` (`t` units of
the cube `[0, B]^e`), their penalties differ by at most `t/8`.

The argument is the cut argument of `lem:forest` (`scales.tex:136-158`), applied
to the difference of two free vectors.  For a tree edge `t₀` with subtree `S`,
the signed deviation sum over `S` vanishes for both vectors, so the change of
`z_{t₀}` equals the change of the free cells leaving `S`, each of which has
`b_e ≤ b_{t₀}`: `|Δz_{t₀}| ≤ e τ (b_{t₀} + 1)`.  A root's deviation does not
depend on the free vector at all (no free cell leaves a component).  Since
`dist(·, [0, b])` is `1`-Lipschitz, `|ΔD| ≤ A Σ_t e τ (b_t + 1)/b_t ≤ 2 A d² τ`,
and `τ = t/B`, `B = 16 A d²` gives `t/8`.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Pseudocode

variable (I : Instance) (ε δ : ℚ)

/-- INTERNAL: propositional bookkeeping for cut membership. -/
theorem iff_not_of_not_iff {a b : Prop} (h : ¬(a ↔ b)) : (a ↔ ¬b) := by tauto

/-- INTERNAL: propositional bookkeeping for cut membership. -/
theorem not_iff_of_iff_not {a b : Prop} (h : a ↔ ¬b) : ¬(a ↔ b) := by tauto

/-- INTERNAL: the difference of two cut terms for one cell. -/
theorem crossTerm_sub (S : Finset ℕ) (ρ κ : ℕ) (a a' : ℚ) :
    crossTerm S ρ κ a a - crossTerm S ρ κ a' a' = crossTerm S ρ κ (a - a') (a - a') := by
  unfold crossTerm; split_ifs <;> ring

/-- INTERNAL: a tree value moves by at most `e τ (b_{t₀} + 1)` when every free
coordinate moves by at most `τ (b_k + 1)`.
TEXLINE: sections/scales.tex:141-152 -/
theorem tree_value_lip {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) (x y : ℕ → ℕ)
    (z z' : ℕ → ℚ) (τ : ℚ) (hτ : 0 ≤ τ)
    (hzz : ∀ k < nFree I ε δ, |z k - z' k| ≤ τ * (((freeAt I ε δ k).2.2 : ℚ) + 1))
    {t₀ : ℕ} (ht₀ : t₀ < (forest I ε δ).tree.length) :
    |(treeValues I ε δ x y z).2 t₀ - (treeValues I ε δ x y z').2 t₀| ≤
      nFree I ε δ * (τ * (((treeAt I ε δ t₀).2.2 : ℚ) + 1)) := by
  classical
  have hv := elimValid_ft I ε δ
  obtain ⟨p, hp, hpt⟩ := List.mem_map.1 (hv.cover t₀ ht₀)
  set D := EDesc (ftR I ε δ) (ftC I ε δ) (elimOrder I ε δ) with hD
  set S := (Finset.range (I.m + I.n)).filter (fun u => D u p.1) with hSdef
  have hmemS : ∀ u, u < I.m + I.n → (u ∈ S ↔ D u p.1) := fun u hu => by
    simp [hSdef, Finset.mem_filter, Finset.mem_range, hu]
  have hRS : ∀ t < (forest I ε δ).tree.length, (ftR I ε δ t ∈ S ↔ D (ftR I ε δ t) p.1) :=
    fun t ht => hmemS _ (by have := ftR_lt I ε δ ht; omega)
  have hCS : ∀ t < (forest I ε δ).tree.length, (ftC I ε δ t ∈ S ↔ D (ftC I ε δ t) p.1) :=
    fun t ht => hmemS _ (ftC_lt I ε δ ht)
  -- every vertex of the subtree satisfies its margin equation, for both vectors
  have hΦ : ∀ w : ℕ → ℚ, ∑ u ∈ S, sgnQ I.m u * devQ I ε δ x y w u = 0 := by
    intro w
    refine Finset.sum_eq_zero fun u hu => ?_
    have hd := (Finset.mem_filter.1 hu).2
    rcases desc_mem hv hd with rfl | hm
    · rw [devQ_nonroot I ε δ x y w (List.mem_map_of_mem hp), mul_zero]
    · rw [devQ_nonroot I ε δ x y w hm, mul_zero]
  have hother : ∀ t < (forest I ε δ).tree.length, t ≠ t₀ →
      (ftR I ε δ t ∈ S ↔ ftC I ε δ t ∈ S) := by
    intro t ht hne
    rw [hRS t ht, hCS t ht]
    exact desc_edge_iff hv ht (fun q hq hqt hqv => hne (by
      rw [← hqt, eq_of_fst_eq hv hq hp hqv, hpt]))
  have htree : ∀ w : ℕ → ℚ, ∑ t ∈ Finset.range (forest I ε δ).tree.length,
      crossTerm S (ftR I ε δ t) (ftC I ε δ t) (trD I ε δ X x y w t) (trD I ε δ X x y w t) =
      crossTerm S (ftR I ε δ t₀) (ftC I ε δ t₀) (trD I ε δ X x y w t₀) (trD I ε δ X x y w t₀) :=
    fun w => Finset.sum_eq_single t₀ (fun t ht hne => crossTerm_eq_zero
      (hother t (Finset.mem_range.1 ht) hne) _) (fun h => absurd (Finset.mem_range.2 ht₀) h)
  have hcross : ftR I ε δ t₀ ∈ S ↔ ¬ ftC I ε δ t₀ ∈ S := by
    have hin : D p.1 p.1 := Relation.ReflTransGen.refl
    have hout := not_desc_oth hv hp
    have hne := hv.ne t₀ ht₀
    rw [hRS t₀ ht₀, hCS t₀ ht₀]
    unfold oth at hout
    rw [hpt] at hout
    rcases hv.inc p hp with h | h <;> rw [hpt] at h
    · rw [if_pos h] at hout; rw [← h]; tauto
    · rw [if_neg (by rw [h]; exact Ne.symm hne)] at hout; rw [← h]; tauto
  have hz := hΦ z
  have hz' := hΦ z'
  rw [signed_dev I ε δ hX, htree] at hz hz'
  -- the change of the tree value is the change of the crossing free cells
  have hdiff : (treeValues I ε δ x y z).2 t₀ - (treeValues I ε δ x y z').2 t₀ =
      trD I ε δ X x y z t₀ - trD I ε δ X x y z' t₀ := by unfold trD; ring
  have hfr : ∀ k, frC I ε δ X z' k - frC I ε δ X z k = z' k - z k := fun k => by
    unfold frC; ring
  rw [hdiff, ← abs_crossTerm_cross hcross, ← crossTerm_sub,
    show crossTerm S (ftR I ε δ t₀) (ftC I ε δ t₀) (trD I ε δ X x y z t₀) (trD I ε δ X x y z t₀) -
      crossTerm S (ftR I ε δ t₀) (ftC I ε δ t₀) (trD I ε δ X x y z' t₀) (trD I ε δ X x y z' t₀) =
      ∑ k ∈ Finset.range (nFree I ε δ), (crossTerm S (freeAt I ε δ k).1
          (I.m + (freeAt I ε δ k).2.1) (frC I ε δ X z' k) (frC I ε δ X z' k) -
        crossTerm S (freeAt I ε δ k).1
          (I.m + (freeAt I ε δ k).2.1) (frC I ε δ X z k) (frC I ε δ X z k)) by
      rw [Finset.sum_sub_distrib]; linarith]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ k ∈ Finset.range (nFree I ε δ), |crossTerm S (freeAt I ε δ k).1
      (I.m + (freeAt I ε δ k).2.1) (frC I ε δ X z' k) (frC I ε δ X z' k) -
        crossTerm S (freeAt I ε δ k).1
          (I.m + (freeAt I ε δ k).2.1) (frC I ε δ X z k) (frC I ε δ X z k)| ≤
      τ * (((treeAt I ε δ t₀).2.2 : ℚ) + 1) := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    rw [crossTerm_sub, hfr]
    by_cases hc : (freeAt I ε δ k).1 ∈ S ↔ I.m + (freeAt I ε δ k).2.1 ∈ S
    · rw [crossTerm_eq_zero hc, abs_zero]; positivity
    · have hc' : (freeAt I ε δ k).1 ∈ S ↔ ¬ I.m + (freeAt I ε δ k).2.1 ∈ S :=
        iff_not_of_not_iff hc
      obtain ⟨t', ht', hb, hcut⟩ := free_cross_edge I ε δ hk' S hc'
      have ht'0 : t' = t₀ := by
        by_contra hne
        exact not_iff_of_iff_not hcut (hother t' ht' hne)
      subst ht'0
      rw [abs_crossTerm_cross hc', abs_sub_comm]
      refine (hzz k hk').trans ?_
      have : ((freeAt I ε δ k).2.2 : ℚ) ≤ (treeAt I ε δ t').2.2 := by exact_mod_cast hb
      gcongr
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- INTERNAL: a root's deviation does not depend on the free vector.
TEXLINE: sections/scales.tex:141-152 -/
theorem root_dev_indep {X : Fin I.m → Fin I.n → ℕ} (hX : X ∈ I.Omega) (x y : ℕ → ℕ)
    (z z' : ℕ → ℚ) {r : ℕ} (hr : r ∈ roots I ε δ) :
    devQ I ε δ x y z r = devQ I ε δ x y z' r := by
  classical
  have hv := elimValid_ft I ε δ
  have hrl := (pseudo_elimOrder_valid I ε δ).2 r hr
  have hrV := ((mem_roots_iff I ε δ r).1 hr).1
  set D := EDesc (ftR I ε δ) (ftC I ε δ) (elimOrder I ε δ) with hD
  set S := (Finset.range (I.m + I.n)).filter (fun u => D u r) with hSdef
  have hmemS : ∀ u, u < I.m + I.n → (u ∈ S ↔ D u r) := fun u hu => by
    simp [hSdef, Finset.mem_filter, Finset.mem_range, hu]
  have hrS : r ∈ S := (hmemS r hrV).2 Relation.ReflTransGen.refl
  have hall : ∀ t < (forest I ε δ).tree.length, (ftR I ε δ t ∈ S ↔ ftC I ε δ t ∈ S) := by
    intro t ht
    rw [hmemS _ (by have := ftR_lt I ε δ ht; omega), hmemS _ (ftC_lt I ε δ ht)]
    exact desc_edge_iff hv ht (fun q hq _ hqr => hrl (hqr ▸ List.mem_map_of_mem hq))
  have key : ∀ w : ℕ → ℚ, sgnQ I.m r * devQ I ε δ x y w r =
      ∑ k ∈ Finset.range (nSmall I ε δ), crossTerm S (smallAt I ε δ k).1
          (I.m + (smallAt I ε δ k).2.1) (smA I ε δ X x k) (smB I ε δ X y k) := by
    intro w
    have hΦ : ∑ u ∈ S, sgnQ I.m u * devQ I ε δ x y w u = sgnQ I.m r * devQ I ε δ x y w r := by
      refine Finset.sum_eq_single r (fun u hu hne => ?_) (fun h => absurd hrS h)
      rcases desc_mem hv (Finset.mem_filter.1 hu).2 with h | h
      · exact absurd h hne
      · rw [devQ_nonroot I ε δ x y w h, mul_zero]
    rw [← hΦ, signed_dev I ε δ hX]
    have htree : ∑ t ∈ Finset.range (forest I ε δ).tree.length, crossTerm S (ftR I ε δ t)
        (ftC I ε δ t) (trD I ε δ X x y w t) (trD I ε δ X x y w t) = 0 :=
      Finset.sum_eq_zero fun t ht => crossTerm_eq_zero (hall t (Finset.mem_range.1 ht)) _
    have hfree : ∑ k ∈ Finset.range (nFree I ε δ), crossTerm S (freeAt I ε δ k).1
        (I.m + (freeAt I ε δ k).2.1) (frC I ε δ X w k) (frC I ε δ X w k) = 0 := by
      refine Finset.sum_eq_zero fun k hk => crossTerm_eq_zero ?_ _
      by_contra hc
      obtain ⟨t', ht', -, hcut⟩ :=
        free_cross_edge I ε δ (Finset.mem_range.1 hk) S (iff_not_of_not_iff hc)
      exact not_iff_of_iff_not hcut (hall t' ht')
    rw [htree, hfree, add_zero, add_zero]
  have hsgn : sgnQ I.m r ≠ 0 := by unfold sgnQ; split_ifs <;> norm_num
  exact mul_left_cancel₀ hsgn ((key z).trans (key z').symm)

/-- INTERNAL: `dist(·, [0, b])` is `1`-Lipschitz. -/
theorem boxDist_lip (a a' b : ℚ) (hb : 0 ≤ b) : |boxDist a b - boxDist a' b| ≤ |a - a'| := by
  unfold boxDist
  rw [abs_le]
  constructor <;> split_ifs <;> linarith [le_abs_self (a - a'), neg_abs_le (a - a')]

/-- **Lipschitz bound for the penalty** (`eq:scaled-penalty-bounds`): free vectors
`t` cube units apart (`|z_k - z'_k| ≤ t (b_k + 1)/B`) have penalties at most `t/8`
apart.
PAPER: sections/evaluation.tex:44-51 -/
theorem penalty_lipschitz (hε : 0 < ε) (hfeas : feasible I) (x y : ℕ → ℕ) (z z' : ℕ → ℚ)
    (t : ℚ) (ht : 0 ≤ t)
    (hzz : ∀ k < nFree I ε δ, |z k - z' k| ≤ t * (((freeAt I ε δ k).2.2 : ℚ) + 1) / BParam I ε δ) :
    |penalty I ε δ x y z - penalty I ε δ x y z'| ≤ t / 8 := by
  obtain ⟨X, hX⟩ := hfeas
  have hA : (0 : ℚ) < AParam I ε δ := by exact_mod_cast AParam_pos I ε δ hε
  have hd : (2 : ℚ) ≤ dParam I := by exact_mod_cast dParam_ge I
  have hBdef : (BParam I ε δ : ℚ) = 16 * AParam I ε δ * (dParam I : ℚ) ^ 2 := by
    unfold BParam; push_cast; ring
  have hB : (0 : ℚ) < BParam I ε δ := by rw [hBdef]; positivity
  set τ : ℚ := t / BParam I ε δ with hτdef
  have hτ : 0 ≤ τ := by positivity
  have hzz' : ∀ k < nFree I ε δ, |z k - z' k| ≤ τ * (((freeAt I ε δ k).2.2 : ℚ) + 1) := by
    intro k hk
    rw [hτdef, div_mul_eq_mul_div]
    exact hzz k hk
  have hW1 : (1 : ℚ) ≤ WParam I ε δ := by exact_mod_cast WParam_pos I ε δ hε
  -- roots contribute nothing to the difference
  have hroots : ((roots I ε δ).map fun v => |(treeValues I ε δ x y z).1 v - margin I v|).sum =
      ((roots I ε δ).map fun v => |(treeValues I ε δ x y z').1 v - margin I v|).sum := by
    congr 1
    refine List.map_congr_left fun r hr => ?_
    rw [devQ_root I ε δ x y z hr, devQ_root I ε δ x y z' hr, root_dev_indep I ε δ hX x y z z' hr]
  set nT := (forest I ε δ).tree.length
  set e := (nFree I ε δ : ℚ)
  -- each tree term moves by at most `2 e τ`
  have hterm : ∀ s ∈ Finset.range nT,
      |boxDist ((treeValues I ε δ x y z).2 s) ((treeAt I ε δ s).2.2 : ℚ) /
          ((treeAt I ε δ s).2.2 : ℚ) -
        boxDist ((treeValues I ε δ x y z').2 s) ((treeAt I ε δ s).2.2 : ℚ) /
          ((treeAt I ε δ s).2.2 : ℚ)| ≤ 2 * (e * τ) := by
    intro s hs
    have hs' := Finset.mem_range.1 hs
    have hbW : (WParam I ε δ : ℚ) ≤ (treeAt I ε δ s).2.2 := by
      exact_mod_cast (large_mem I ε δ (Or.inl (treeAt_mem I ε δ hs'))).2
    have hb : (0 : ℚ) < (treeAt I ε δ s).2.2 := by linarith
    rw [← sub_div, abs_div, abs_of_pos hb, div_le_iff₀ hb]
    refine (boxDist_lip _ _ _ hb.le).trans ?_
    refine (tree_value_lip I ε δ hX x y z z' τ hτ hzz' hs').trans ?_
    have he0 : 0 ≤ e := by positivity
    nlinarith [mul_nonneg he0 hτ]
  -- the count of tree and free cells
  have hcount : e * nT ≤ (dParam I : ℚ) ^ 2 := by
    have h := cells_count_le I ε δ
    have h1 : (nFree I ε δ : ℚ) + nT ≤ dParam I := by
      unfold dParam; push_cast
      have : ((nFree I ε δ + nT : ℕ) : ℚ) ≤ (I.m * I.n : ℕ) := by exact_mod_cast (by omega)
      push_cast at this; nlinarith [(Nat.cast_nonneg I.m : (0 : ℚ) ≤ I.m),
        (Nat.cast_nonneg I.n : (0 : ℚ) ≤ I.n)]
    have h0 : (0 : ℚ) ≤ e := by positivity
    have h0' : (0 : ℚ) ≤ nT := by positivity
    nlinarith
  unfold penalty
  rw [hroots, ← mul_sub, abs_mul, abs_of_pos hA, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  calc (AParam I ε δ : ℚ) * |∑ s ∈ Finset.range nT,
          (boxDist ((treeValues I ε δ x y z).2 s) ((treeAt I ε δ s).2.2 : ℚ) /
            ((treeAt I ε δ s).2.2 : ℚ) -
          boxDist ((treeValues I ε δ x y z').2 s) ((treeAt I ε δ s).2.2 : ℚ) /
            ((treeAt I ε δ s).2.2 : ℚ))|
      ≤ AParam I ε δ * ∑ s ∈ Finset.range nT, 2 * (e * τ) := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = 2 * AParam I ε δ * (e * nT) * τ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ 2 * AParam I ε δ * (dParam I : ℚ) ^ 2 * τ := by gcongr
    _ = t / 8 := by
        rw [hτdef, hBdef]; field_simp; ring

end Cellcounting.Analysis
