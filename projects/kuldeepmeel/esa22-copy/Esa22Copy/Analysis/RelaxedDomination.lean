import Esa22Copy.Analysis.RelaxedAlgorithm
import Esa22Copy.Analysis.LevelSample

/-!
# Algorithm 2 is dominated by the level samples

The paper identifies Algorithm 2's `(p_j, X_j)` with Algorithm 3's
`(p_j, Y_{k,j})` when `p_j = 2⁻ᵏ` (esa22-final.tex:684), and then uses only that
`X_j = Y_{k_j, j}` with `Y_{q,j}` distributed as in Claim `cl:loop`.  This file
states the consequence of that coupling the analysis actually needs, as an
inequality between laws that can be proved by induction over the stream without
constructing Algorithm 3 at all:

  `Σ_{st} Pr[X_j-state = st] · [k ≤ q] · Pr[levelSample (q - k) X = T]
     ≤ Pr[levelSample q S_j = T]`  (with `k = st.level`, `X = st.sample`).

Read through the coupling, the left side is `Pr[k_j ≤ q ∧ Y_{q,j} = T]`: an
element of `X_j = Y_{k_j,j}` is in `Y_{q,j}` independently with probability
`2^{-(q-k_j)}`.  The term `k = q` gives `Pr[k_j = q ∧ X_j = T] ≤ Pr[Y_{q,j} = T]`,
which is what bounds `Error_{2,q}` and `Bad_j` in Claim `lm:error-fail`.

Proof (induction on `j`, appending one stream element `a`; `relaxedStep_domination`
is one step):
* no throw at level `k < q`, or throw from `k` to `k + 1 ≤ q`: both continue
  as `levelSample (q - k)` of the picked set, since one throw then
  `levelSample r` is `levelSample (r + 1)`;
* no throw at level `k = q`: bounded by dropping the `[|X'| ≠ thresh]` factor;
* commutation (`pick_bind_levelSample`): picking at level `k` then sampling down
  `r` levels equals sampling down `r` levels then picking at level `k + r` (needs
  `k + r ≤ w`, so `acceptsAt` is a true Bernoulli(`2^{-(k+r)}`));
* `levelSample q S` followed by a level-`q` pick of `a` is `levelSample q (insert a S)`
  (`levelSample_bind_pick`).
-/

set_option autoImplicit false

open scoped ENNReal

namespace Esa22Copy.Analysis

open Esa22Copy.Interface (Snapshot)
open Esa22Copy.Interface.Pseudocode

variable {α : Type} [DecidableEq α] [Fintype α]

/-- INTERNAL: picking `a` at level `q` after any law `μ`, evaluated at `T`. -/
theorem bind_pick_apply (w q : ℕ) (hq : q ≤ w) (a : α) (μ : PMF (Finset α)) (T : Finset α) :
    (μ.bind fun U => pick w q a (drop a U)) T =
      if a ∈ T then (μ (T.erase a) + μ T) * (2⁻¹ : ℝ≥0∞) ^ q
      else (μ T + μ (insert a T)) * levelMiss q := by
  rw [PMF.bind_apply, tsum_fintype]
  simp only [drop, pick_apply hq a _ _ (Finset.notMem_erase a _)]
  by_cases haT : a ∈ T
  · rw [if_pos haT]
    have hne : T.erase a ≠ T := fun h => (Finset.notMem_erase a T) (by rw [h]; exact haT)
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
    rw [Finset.erase_idem, Finset.insert_erase haT, if_pos rfl, if_neg (Ne.symm hne), add_zero,
      add_mul]
  · rw [if_neg haT]
    have hne : T ≠ insert a T := fun h => haT (h ▸ Finset.mem_insert_self a T)
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
    rw [Finset.erase_eq_of_notMem haT, Finset.erase_insert haT, if_neg hne, if_pos rfl, zero_add,
      add_mul]

/-- INTERNAL: a level sample taken after a pick at level `k`, evaluated at `T`. -/
theorem pick_bind_apply (w k r : ℕ) (hk : k ≤ w) (a : α) (X T : Finset α) :
    ((pick w k a (drop a X)).bind (levelSample r)) T =
      (2⁻¹ : ℝ≥0∞) ^ k * levelSample r (insert a (X.erase a)) T +
        levelMiss k * levelSample r (X.erase a) T := by
  rw [PMF.bind_apply, tsum_fintype]
  simp only [drop, pick_apply hk a _ _ (Finset.notMem_erase a X), add_mul, ite_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

omit [DecidableEq α] [Fintype α] in
/-- INTERNAL: `1 - 2^{-(k+r)} = 2^{-k}(1 - 2^{-r}) + (1 - 2^{-k})`. -/
theorem levelMiss_add_levels (k r : ℕ) :
    levelMiss (k + r) = (2⁻¹ : ℝ≥0∞) ^ k * levelMiss r + levelMiss k := by
  have h1 := levelMiss_add (k + r)
  have h2 : (2⁻¹ : ℝ≥0∞) ^ k * levelMiss r + levelMiss k + (2⁻¹ : ℝ≥0∞) ^ (k + r) = 1 := by
    rw [pow_add, add_comm ((2⁻¹ : ℝ≥0∞) ^ k * levelMiss r), add_assoc, ← mul_add,
      levelMiss_add r, mul_one, levelMiss_add k]
  exact (ENNReal.add_left_inj (by simp)).1 (h1.trans h2.symm)

/-- INTERNAL: **commutation of pick and level sampling**.  Picking `a` at level
`k` and then keeping each element with probability `2^{-r}` has the same law as
keeping each element with probability `2^{-r}` and then picking `a` at level
`k + r`: both keep `a` with probability `2^{-(k+r)}` and every other element with
probability `2^{-r}`, independently.  Needs `k + r ≤ w`.
TEXLINE: esa22-final.tex:684 -/
theorem pick_bind_levelSample (w k r : ℕ) (hkr : k + r ≤ w) (a : α) (X : Finset α) :
    (pick w k a (drop a X)).bind (levelSample r) =
      (levelSample r X).bind (fun U => pick w (k + r) a (drop a U)) := by
  ext T
  rw [pick_bind_apply w k r (by omega), bind_pick_apply w (k + r) hkr]
  simp only [levelSample_apply]
  rw [levelMiss_add_levels, pow_add]
  set pk : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ k
  set pr : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ r
  set ck : ℝ≥0∞ := levelMiss k
  set cr : ℝ≥0∞ := levelMiss r
  have hr : cr + pr = 1 := levelMiss_add r
  by_cases haT : a ∈ T
  · rw [if_pos haT]
    have hTe : ¬ T ⊆ X.erase a := fun h => Finset.notMem_erase a X (h haT)
    rw [if_neg hTe, mul_zero, add_zero, Finset.card_erase_of_mem haT]
    obtain ⟨s, hs⟩ : ∃ s, T.card = s + 1 := ⟨T.card - 1, by
      have := Finset.card_pos.2 ⟨a, haT⟩; omega⟩
    rw [hs, Nat.add_sub_cancel]
    by_cases haX : a ∈ X
    · rw [Finset.insert_erase haX]
      have hiff : T.erase a ⊆ X ↔ T ⊆ X := by
        constructor
        · intro h x hx
          by_cases hxa : x = a
          · exact hxa ▸ haX
          · exact h (Finset.mem_erase.2 ⟨hxa, hx⟩)
        · exact fun h => (Finset.erase_subset a T).trans h
      by_cases hTX : T ⊆ X
      · rw [if_pos hTX, if_pos (hiff.2 hTX)]
        have hn : T.card ≤ X.card := Finset.card_le_card hTX
        obtain ⟨d, hd⟩ : ∃ d, X.card = s + 1 + d := ⟨X.card - (s + 1), by omega⟩
        rw [hd, show s + 1 + d - s = d + 1 by omega, show s + 1 + d - (s + 1) = d by omega]
        calc pk * (pr ^ (s + 1) * cr ^ d) = pk * (pr ^ (s + 1) * cr ^ d) * (cr + pr) := by
              rw [hr, mul_one]
          _ = _ := by ring
      · rw [if_neg hTX, if_neg (fun h => hTX (hiff.1 h))]; simp
    · rw [Finset.erase_eq_of_notMem haX, Finset.card_insert_of_notMem haX]
      have hTX : ¬ T ⊆ X := fun h => haX (h haT)
      rw [if_neg hTX, add_zero]
      have hiff : T ⊆ insert a X ↔ T.erase a ⊆ X := by
        constructor
        · intro h x hx
          have hx' := Finset.mem_erase.1 hx
          rcases Finset.mem_insert.1 (h hx'.2) with h' | h'
          · exact absurd h' hx'.1
          · exact h'
        · intro h x hx
          by_cases hxa : x = a
          · exact hxa ▸ Finset.mem_insert_self a X
          · exact Finset.mem_insert_of_mem (h (Finset.mem_erase.2 ⟨hxa, hx⟩))
      by_cases hTe' : T.erase a ⊆ X
      · rw [if_pos (hiff.2 hTe'), if_pos hTe']
        rw [show X.card + 1 - (s + 1) = X.card - s by omega]
        ring
      · rw [if_neg (fun h => hTe' (hiff.1 h)), if_neg hTe']; simp
  · rw [if_neg haT]
    by_cases haX : a ∈ X
    · rw [Finset.insert_erase haX, Finset.card_erase_of_mem haX]
      have hiff1 : T ⊆ X.erase a ↔ T ⊆ X := by
        constructor
        · exact fun h => h.trans (Finset.erase_subset a X)
        · intro h x hx
          exact Finset.mem_erase.2 ⟨fun hxa => haT (hxa ▸ hx), h hx⟩
      have hiff2 : insert a T ⊆ X ↔ T ⊆ X := by
        constructor
        · exact fun h => (Finset.subset_insert a T).trans h
        · exact fun h => Finset.insert_subset haX h
      by_cases hTX : T ⊆ X
      · rw [if_pos hTX, if_pos (hiff1.2 hTX), if_pos (hiff2.2 hTX),
          Finset.card_insert_of_notMem haT]
        have hlt : T.card < X.card := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.2 ⟨hTX, fun h => haT (h ▸ haX)⟩)
        obtain ⟨d, hd⟩ : ∃ d, X.card = T.card + 1 + d := ⟨X.card - (T.card + 1), by omega⟩
        rw [hd, show T.card + 1 + d - T.card = d + 1 by omega,
          show T.card + 1 + d - 1 - T.card = d by omega,
          show T.card + 1 + d - (T.card + 1) = d by omega]
        calc pk * (pr ^ T.card * cr ^ (d + 1)) + ck * (pr ^ T.card * cr ^ d)
            = pr ^ T.card * cr ^ d * (pk * cr + ck) := by ring
          _ = pr ^ T.card * cr ^ d * (pk * cr + ck) * (cr + pr) := by rw [hr, mul_one]
          _ = _ := by ring
      · rw [if_neg hTX, if_neg (fun h => hTX (hiff1.1 h)), if_neg (fun h => hTX (hiff2.1 h))]
        simp
    · rw [Finset.erase_eq_of_notMem haX, Finset.card_insert_of_notMem haX]
      have hiff : T ⊆ insert a X ↔ T ⊆ X := by
        constructor
        · intro h x hx
          rcases Finset.mem_insert.1 (h hx) with h' | h'
          · exact absurd (h' ▸ hx) haT
          · exact h'
        · exact fun h => h.trans (Finset.subset_insert a X)
      have hTi : ¬ insert a T ⊆ X := fun h => haX (h (Finset.mem_insert_self a T))
      rw [if_neg hTi, add_zero]
      by_cases hTX : T ⊆ X
      · rw [if_pos (hiff.2 hTX), if_pos hTX]
        have hn : T.card ≤ X.card := Finset.card_le_card hTX
        obtain ⟨d, hd⟩ : ∃ d, X.card = T.card + d := ⟨X.card - T.card, by omega⟩
        rw [hd, show T.card + d + 1 - T.card = d + 1 by omega, Nat.add_sub_cancel_left]
        ring
      · rw [if_neg (fun h => hTX (hiff.1 h)), if_neg hTX]; simp

omit [DecidableEq α] [Fintype α] in
/-- INTERNAL: integrating against a pushforward. -/
theorem tsum_map_mul {β γ : Type} (μ : PMF β) (f : β → γ) (g : γ → ℝ≥0∞) :
    ∑' c, μ.map f c * g c = ∑' b, μ b * g (f b) := by
  simp only [PMF.map_apply, ENNReal.tsum_mul_right.symm]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun b => ?_
  rw [tsum_eq_single (f b)]
  · simp
  · intro c hc; simp [hc]

/-- INTERNAL: one iteration of Algorithm 2, weighted by the domination integrand,
is at most a level-`q` pick after the level sample of the current set.
TEXLINE: esa22-final.tex:572-581 -/
theorem relaxedStep_domination (thr w q : ℕ) (hq : q ≤ w) (st : Snapshot α) (a : α)
    (T : Finset α) :
    ∑' st', relaxedStep thr w st a st' *
        (if st'.level ≤ q then levelSample (q - st'.level) st'.sample T else 0) ≤
      if st.level ≤ q then
        ((levelSample (q - st.level) st.sample).bind fun U => pick w q a (drop a U)) T
      else 0 := by
  set g : Snapshot α → ℝ≥0∞ := fun st' =>
    if st'.level ≤ q then levelSample (q - st'.level) st'.sample T else 0
  simp only [relaxedStep, PMF.bind_apply, ENNReal.tsum_mul_right.symm]
  rw [ENNReal.tsum_comm]
  simp only [mul_assoc, ENNReal.tsum_mul_left]
  have hinner : ∀ X : Finset α,
      ∑' st', (if full thr X then (throw X).map (fun Y => (⟨Y, halve st.level⟩ : Snapshot α))
          else PMF.pure ⟨X, st.level⟩) st' * g st' ≤
        if st.level ≤ q then levelSample (q - st.level) X T else 0 := by
    intro X
    by_cases hk : st.level ≤ q
    · rw [if_pos hk]
      by_cases hfull : full thr X = true
      · rw [if_pos hfull, tsum_map_mul]
        simp only [g, halve]
        by_cases hk1 : st.level + 1 ≤ q
        · simp only [hk1, if_true]
          have : q - st.level = (q - (st.level + 1)) + 1 := by omega
          rw [this, levelSample_succ, PMF.bind_apply]
        · simp only [hk1, if_false, mul_zero, tsum_zero]
          exact bot_le
      · rw [if_neg hfull, tsum_eq_single ⟨X, st.level⟩]
        · simp [g, hk]
        · intro b hb; simp [PMF.pure_apply, hb]
    · rw [if_neg hk]
      by_cases hfull : full thr X = true
      · rw [if_pos hfull, tsum_map_mul]
        simp only [g, halve]
        have : ¬ st.level + 1 ≤ q := by omega
        simp [this]
      · rw [if_neg hfull, tsum_eq_single ⟨X, st.level⟩]
        · simp [g, hk]
        · intro b hb; simp [PMF.pure_apply, hb]
  calc _ ≤ ∑' X, pick w st.level a (drop a st.sample) X *
        (if st.level ≤ q then levelSample (q - st.level) X T else 0) :=
        ENNReal.tsum_le_tsum fun X => mul_le_mul' le_rfl (hinner X)
    _ = _ := by
        split_ifs with hk
        · rw [← PMF.bind_apply, pick_bind_levelSample w st.level (q - st.level) (by omega),
            Nat.add_sub_cancel' hk, PMF.bind_apply]
        · simp

/-- **Algorithm 2 is dominated by the level samples** — the form in which the
coupling `(p_j, X_j) = (p_j, Y_{k,j})` (esa22-final.tex:684) and Claim `cl:loop`
(esa22-final.tex:624-678) enter the proof of Claim `lm:error-fail`.

PAPER: esa22-final.tex:684 -/
theorem relaxed_domination (thr w : ℕ) (l : List α) (q : ℕ) (hq : q ≤ w) (T : Finset α) :
    ∑' st : Snapshot α, relaxedLoop thr w l init st *
        (if st.level ≤ q then levelSample (q - st.level) st.sample T else 0)
      ≤ levelSample q l.toFinset T := by
  induction l using List.reverseRecOn generalizing T with
  | nil =>
    simp only [relaxedLoop, List.toFinset_nil]
    rw [tsum_eq_single init]
    · simp [PMF.pure_apply, init]
    · intro st hst; simp [PMF.pure_apply, hst]
  | append_singleton l a ih =>
    have hloop : relaxedLoop thr w (l ++ [a]) init =
        (relaxedLoop thr w l init).bind fun st => relaxedStep thr w st a := by
      rw [relaxedLoop_append]
      congr 1
      funext st
      rw [relaxedLoop_cons]
      exact PMF.bind_pure _
    set P := relaxedLoop thr w l init
    set f : Finset α → ℝ≥0∞ := fun U => pick w q a (drop a U) T
    -- the induction hypothesis, integrated against `f`
    have ihf : ∑' st : Snapshot α, P st *
        (if st.level ≤ q then ∑' U, levelSample (q - st.level) st.sample U * f U else 0) ≤
          ∑' U, levelSample q l.toFinset U * f U := by
      calc _ = ∑' st : Snapshot α, ∑' U, P st *
            ((if st.level ≤ q then levelSample (q - st.level) st.sample U else 0) * f U) := by
            refine tsum_congr fun st => ?_
            split_ifs
            · rw [ENNReal.tsum_mul_left]
            · simp
        _ = ∑' U, (∑' st : Snapshot α, P st *
            (if st.level ≤ q then levelSample (q - st.level) st.sample U else 0)) * f U := by
            rw [ENNReal.tsum_comm]
            refine tsum_congr fun U => ?_
            rw [← ENNReal.tsum_mul_right]
            exact tsum_congr fun st => (mul_assoc _ _ _).symm
        _ ≤ _ := ENNReal.tsum_le_tsum fun U => mul_le_mul' (ih U) le_rfl
    have hins : (l ++ [a]).toFinset = insert a l.toFinset := by ext x; simp
    rw [hloop, hins, ← levelSample_bind_pick w q hq a, PMF.bind_apply]
    simp only [PMF.bind_apply, ENNReal.tsum_mul_right.symm]
    rw [ENNReal.tsum_comm]
    simp only [mul_assoc, ENNReal.tsum_mul_left]
    refine le_trans (ENNReal.tsum_le_tsum fun st => mul_le_mul' le_rfl
      (relaxedStep_domination thr w q hq st a T)) (le_trans (le_of_eq ?_) ihf)
    refine tsum_congr fun st => ?_
    split_ifs
    · rw [PMF.bind_apply]
    · rfl

end Esa22Copy.Analysis
