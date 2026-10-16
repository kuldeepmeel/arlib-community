import Cellcounting.Analysis.RefChainLaw
import Cellcounting.Analysis.TransMassEqCpart
import Cellcounting.Analysis.PmfClose

/-!
# The exact `μ₀` sampler draws `μ_0` (`lem:initialization`)

`algorithm.tex:44-47`: independently for each small cell `s`, a uniform
`k_s ∈ {0, …, b_s}` and a uniform `k_s`-subset of its `b_s` pairs (which use their row
elements) give the law `μ_0`.  At parameter zero `h_0 = M_f` is constant, so
`μ_0(S) ∝ ∏_s x_s! y_s! / b_s! = ∏_s C(b_s, x_s)⁻¹` on transversals, which is the
probability `∏_s 1/((b_s + 1) C(b_s, k_s))` of the sampler.

The proof: lexicographic unranking is a bijection from ranks below `C(b, k)` onto the
`k`-subsets of `[0, b)` (`Mu0Law.unrank_exists`, `Mu0Law.unrankAux_inj`), so one cell's
draw gives `U ⊆ [0, b)` probability `1/((b + 1) C(b, |U|))` (`Mu0Law.cellDraw_apply`); by
induction on the cells the sampler gives each transversal the product of these
(`Mu0Law.loop_apply`); and the normalizer is `transMass 0 = C(0) = M_f ∏_s (b_s + 1)`
(`transMass_eq_Cpart`, `Cpart_zero`).
-/

namespace Cellcounting.Analysis.Mu0Law

open Cellcounting Pseudocode Finset

/-- INTERNAL: the greedy loop of `unrank` on positions `[t0, t0 + n)`, written as a
recursion so that its combinatorics can be proved by induction.
TEXLINE: sections/algorithm.tex:44-47 -/
def unrankAux : ℕ → ℕ → ℕ → ℕ → Finset ℕ
  | _, 0, _, _ => ∅
  | t0, n + 1, k, r =>
    if 0 < k then
      if r < Nat.choose n (k - 1) then insert t0 (unrankAux (t0 + 1) n (k - 1) r)
      else unrankAux (t0 + 1) n k (r - Nat.choose n (k - 1))
    else unrankAux (t0 + 1) n k r

/-- INTERNAL: `unrank` is `unrankAux` from position `0`. -/
theorem unrank_eq_aux (b k r : ℕ) : unrank b k r = unrankAux 0 b k r := by
  have key : ∀ n t0 (st : Finset ℕ × ℕ × ℕ), t0 + n = b →
      ((List.range' t0 n).foldl (fun st t =>
        if 0 < st.2.1 then
          if st.2.2 < Nat.choose (b - (t + 1)) (st.2.1 - 1) then (insert t st.1, st.2.1 - 1, st.2.2)
          else (st.1, st.2.1, st.2.2 - Nat.choose (b - (t + 1)) (st.2.1 - 1))
        else st) st).1 = st.1 ∪ unrankAux t0 n st.2.1 st.2.2 := by
    intro n
    induction n with
    | zero => intro t0 st _; simp [unrankAux]
    | succ n ih =>
      intro t0 ⟨A, k, r⟩ h
      rw [List.range'_succ, List.foldl_cons]
      have hb : b - (t0 + 1) = n := by omega
      simp only [hb]
      by_cases hk : 0 < k
      · by_cases hr : r < Nat.choose n (k - 1)
        · simp only [hk, hr, ↓reduceIte]
          rw [ih (t0 + 1) _ (by omega)]
          simp only [unrankAux, hk, hr, ↓reduceIte]
          ext x; simp
        · simp only [hk, hr, ↓reduceIte]
          rw [ih (t0 + 1) _ (by omega)]
          simp [unrankAux, hk, hr]
      · simp only [hk, ↓reduceIte]
        rw [ih (t0 + 1) _ (by omega)]
        simp [unrankAux, hk]
  unfold unrank
  rw [List.range_eq_range', key b 0 (∅, k, r) (by simp)]
  simp

/-- INTERNAL: `unrankAux t0 n` chooses positions in `[t0, t0 + n)`. -/
theorem unrankAux_sub (n : ℕ) : ∀ t0 k r, unrankAux t0 n k r ⊆ Ico t0 (t0 + n) := by
  induction n with
  | zero => intro t0 k r; simp [unrankAux]
  | succ n ih =>
    intro t0 k r
    have h1 : Ico (t0 + 1) (t0 + 1 + n) ⊆ Ico t0 (t0 + (n + 1)) := by
      intro x hx; simp only [mem_Ico] at hx ⊢; omega
    simp only [unrankAux]
    split_ifs
    · intro x hx
      rcases mem_insert.1 hx with rfl | hx
      · simp
      · exact h1 (ih _ _ _ hx)
    · exact (ih _ _ _).trans h1
    · exact (ih _ _ _).trans h1

/-- INTERNAL: a rank below `C(n, k)` unranks to a `k`-set. -/
theorem unrankAux_card (n : ℕ) : ∀ t0 k r, r < Nat.choose n k → (unrankAux t0 n k r).card = k := by
  induction n with
  | zero =>
    intro t0 k r hr
    rcases k with _ | k
    · simp [unrankAux]
    · simp at hr
  | succ n ih =>
    intro t0 k r hr
    simp only [unrankAux]
    rcases k with _ | k
    · simpa using ih (t0 + 1) 0 r (by simpa using hr)
    · rw [Nat.choose_succ_succ'] at hr
      simp only [Nat.succ_pos, ↓reduceIte, Nat.add_sub_cancel]
      split_ifs with h
      · have hn : t0 ∉ unrankAux (t0 + 1) n k r := fun h' => by
          have := mem_Ico.1 (unrankAux_sub n _ _ _ h'); omega
        rw [card_insert_of_notMem hn, ih _ _ _ h]
      · exact ih _ _ _ (by omega)

/-- INTERNAL: unranking is injective on ranks below `C(n, k)`. -/
theorem unrankAux_inj (n : ℕ) : ∀ t0 k r1 r2, r1 < Nat.choose n k → r2 < Nat.choose n k →
    unrankAux t0 n k r1 = unrankAux t0 n k r2 → r1 = r2 := by
  induction n with
  | zero =>
    intro t0 k r1 r2 h1 h2 _
    rcases k with _ | k <;> simp at h1 h2; omega
  | succ n ih =>
    intro t0 k r1 r2 h1 h2 he
    simp only [unrankAux] at he
    rcases k with _ | k
    · simp at h1 h2; omega
    · rw [Nat.choose_succ_succ'] at h1 h2
      simp only [Nat.succ_pos, ↓reduceIte, Nat.add_sub_cancel] at he
      have hn : ∀ r, t0 ∉ unrankAux (t0 + 1) n k r := fun r h' => by
        have := mem_Ico.1 (unrankAux_sub n _ _ _ h'); omega
      have hn' : ∀ r, t0 ∉ unrankAux (t0 + 1) n (k + 1) r := fun r h' => by
        have := mem_Ico.1 (unrankAux_sub n _ _ _ h'); omega
      split_ifs at he with a b b
      · have := congrArg (fun s => s.erase t0) he
        simp only [erase_insert (hn _)] at this
        exact ih _ _ _ _ a b this
      · exact absurd (he ▸ mem_insert_self t0 _) (hn' _)
      · exact absurd (he.symm ▸ mem_insert_self t0 _) (hn' _)
      · have := ih _ _ _ _ (by omega) (by omega) he; omega


/-- INTERNAL: every subset of `[0, b)` is the unranking of some rank below
`C(b, |U|)` (by injectivity and counting). -/
theorem unrank_exists (b : ℕ) (U : Finset ℕ) (hU : U ⊆ range b) :
    ∃ r < Nat.choose b U.card, unrank b U.card r = U := by
  set k := U.card
  have hsub : (range (Nat.choose b k)).image (unrankAux 0 b k) ⊆ powersetCard k (range b) := by
    intro V hV
    obtain ⟨r, hr, rfl⟩ := mem_image.1 hV
    rw [mem_powersetCard]
    refine ⟨fun x hx => ?_, unrankAux_card b 0 k r (mem_range.1 hr)⟩
    have := mem_Ico.1 (unrankAux_sub b 0 k r hx); simp; omega
  have hcard : (range (Nat.choose b k)).image (unrankAux 0 b k) = powersetCard k (range b) := by
    refine eq_of_subset_of_card_le hsub ?_
    rw [card_powersetCard, card_range, card_image_of_injOn, card_range]
    intro r1 hr1 r2 hr2 he
    exact unrankAux_inj b 0 k r1 r2 (mem_range.1 hr1) (mem_range.1 hr2) he
  have hUm : U ∈ powersetCard k (range b) := mem_powersetCard.2 ⟨hU, rfl⟩
  rw [← hcard] at hUm
  obtain ⟨r, hr, he⟩ := mem_image.1 hUm
  exact ⟨r, mem_range.1 hr, by rw [unrank_eq_aux]; exact he⟩

/-- INTERNAL: the mass function of `uniformBelow k`, `k > 0`. -/
theorem uniformBelow_apply (k a : ℕ) (hk : 0 < k) :
    uniformBelow k a = if a < k then ((k : ENNReal))⁻¹ else 0 := by
  unfold uniformBelow; rw [dif_pos hk]
  exact (PMF.uniformOfFinset_apply ⟨0, mem_range.2 hk⟩ a).trans (by simp)

/-- INTERNAL: one cell's draw of the `μ₀` sampler: a uniform size `k ≤ b`, then the
unranking of a uniform rank below `C(b, k)`.
TEXLINE: sections/algorithm.tex:44-47 -/
noncomputable def cellDraw (b : ℕ) : PMF (Finset ℕ) :=
  (uniformBelow (b + 1)).bind fun k =>
    (uniformBelow (Nat.choose b k)).bind fun r => PMF.pure (unrank b k r)

/-- INTERNAL: `x! (b - x)! / b! / (b + 1) = 1 / ((b + 1) C(b, x))`. -/
noncomputable def cellW (b x : ℕ) : ℝ :=
  (x.factorial : ℝ) * ((b - x).factorial : ℝ) / (b.factorial : ℝ) / ((b : ℝ) + 1)

/-- INTERNAL: `cellW` is nonnegative. -/
theorem cellW_nonneg (b x : ℕ) : 0 ≤ cellW b x := by unfold cellW; positivity

/-- INTERNAL: one cell's draw gives `U ⊆ [0, b)` probability `1/((b + 1) C(b, |U|))`.
TEXLINE: sections/algorithm.tex:44-47 -/
theorem cellDraw_apply (b : ℕ) (U : Finset ℕ) :
    cellDraw b U = if U ⊆ range b then ENNReal.ofReal (cellW b U.card) else 0 := by
  rw [cellDraw, PMF.bind_apply]
  split_ifs with hU
  · set k := U.card with hkdef
    have hk : k ≤ b := by simpa using card_le_card hU
    have hC : 0 < Nat.choose b k := Nat.choose_pos hk
    obtain ⟨r0, hr0, he0⟩ := unrank_exists b U hU
    rw [tsum_eq_single k]
    · rw [PMF.bind_apply, tsum_eq_single r0]
      · rw [uniformBelow_apply _ _ (by omega), uniformBelow_apply _ _ hC, if_pos (by omega),
          if_pos hr0, PMF.pure_apply, if_pos he0.symm, mul_one]
        have hreal : cellW b k = (((b + 1) * Nat.choose b k : ℕ) : ℝ)⁻¹ := by
          have h := Nat.choose_mul_factorial_mul_factorial hk
          unfold cellW
          have hf : (b.factorial : ℝ) ≠ 0 := by positivity
          have hc : (Nat.choose b k : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
          rw [← h]; push_cast
          field_simp
        rw [hreal, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast, Nat.cast_mul,
          ENNReal.mul_inv (by simp) (by simp)]
      · intro r hr
        rw [uniformBelow_apply _ _ hC]
        split_ifs with h
        · rw [PMF.pure_apply, if_neg, mul_zero]
          intro hUr
          apply hr
          refine unrankAux_inj b 0 k r r0 h hr0 ?_
          rw [← unrank_eq_aux, ← unrank_eq_aux, he0, ← hUr]
        · simp
    · intro k' hk'
      rw [uniformBelow_apply _ _ (by omega)]
      split_ifs with h
      · rw [PMF.bind_apply]
        refine mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.2 fun r => ?_)
        by_cases hr : r < Nat.choose b k'
        · rw [PMF.pure_apply, if_neg, mul_zero]
          intro hUr
          have := unrankAux_card b 0 k' r hr
          rw [← unrank_eq_aux, ← hUr] at this
          exact hk' this.symm
        · rw [uniformBelow_apply _ _ (Nat.choose_pos (by omega)), if_neg hr, zero_mul]
      · simp
  · refine ENNReal.tsum_eq_zero.2 fun k => mul_eq_zero_of_right _ ?_
    rw [PMF.bind_apply]
    refine ENNReal.tsum_eq_zero.2 fun r => mul_eq_zero_of_right _ ?_
    rw [PMF.pure_apply, if_neg]
    rintro rfl
    apply hU
    intro x hx
    rw [unrank_eq_aux] at hx
    have := mem_Ico.1 (unrankAux_sub b 0 k r hx); simp; omega


/-- INTERNAL: the elements written for one small cell starting at pair label `c`:
the row element of pair `c + t` for `t ∈ U`, its column element otherwise. -/
def blk (c b : ℕ) (U : Finset ℕ) : Finset ℕ :=
  (range b).image fun t => if t ∈ U then 2 * (c + t) else 2 * (c + t) + 1

/-- INTERNAL: the offsets `t < b` whose row element `2 (c + t)` is in `S`. -/
def rowSet (c b : ℕ) (S : Finset ℕ) : Finset ℕ := (range b).filter fun t => 2 * (c + t) ∈ S

/-- INTERNAL: `S` lives on the pairs below `c` and meets each of them once. -/
def Valid (c : ℕ) (S : Finset ℕ) : Prop :=
  (∀ e ∈ S, e < 2 * c) ∧ ∀ i < c, (2 * i ∈ S ↔ 2 * i + 1 ∉ S)

/-- INTERNAL: membership in `blk`. -/
theorem mem_blk (c b : ℕ) (U : Finset ℕ) (e : ℕ) : e ∈ blk c b U ↔
    ∃ t < b, (t ∈ U ∧ e = 2 * (c + t)) ∨ (t ∉ U ∧ e = 2 * (c + t) + 1) := by
  simp only [blk, mem_image, mem_range]
  constructor
  · rintro ⟨t, ht, rfl⟩
    by_cases hU : t ∈ U
    · exact ⟨t, ht, Or.inl ⟨hU, by simp [hU]⟩⟩
    · exact ⟨t, ht, Or.inr ⟨hU, by simp [hU]⟩⟩
  · rintro ⟨t, ht, (⟨hU, rfl⟩ | ⟨hU, rfl⟩)⟩
    · exact ⟨t, ht, by simp [hU]⟩
    · exact ⟨t, ht, by simp [hU]⟩

/-- INTERNAL: `blk c b U` lies in `[2c, 2(c + b))`. -/
theorem blk_bounds {c b : ℕ} {U : Finset ℕ} {e : ℕ} (he : e ∈ blk c b U) :
    2 * c ≤ e ∧ e < 2 * (c + b) := by
  obtain ⟨t, ht, (⟨-, rfl⟩ | ⟨-, rfl⟩)⟩ := (mem_blk c b U e).1 he <;> omega

/-- INTERNAL: appending one block keeps every pair singly occupied. -/
theorem valid_union {c b : ℕ} {S : Finset ℕ} (U : Finset ℕ) (hS : Valid c S) :
    Valid (c + b) (S ∪ blk c b U) := by
  obtain ⟨h2, h1⟩ := hS
  refine ⟨fun e he => ?_, fun i hi => ?_⟩
  · rcases mem_union.1 he with he | he
    · have := h2 e he; omega
    · have := blk_bounds he; omega
  · simp only [mem_union, mem_blk]
    by_cases hic : i < c
    · have a1 : ¬ ∃ t < b, (t ∈ U ∧ 2 * i = 2 * (c + t)) ∨ (t ∉ U ∧ 2 * i = 2 * (c + t) + 1) := by
        rintro ⟨t, -, (⟨-, h⟩ | ⟨-, h⟩)⟩ <;> omega
      have a2 : ¬ ∃ t < b, (t ∈ U ∧ 2 * i + 1 = 2 * (c + t)) ∨
          (t ∉ U ∧ 2 * i + 1 = 2 * (c + t) + 1) := by
        rintro ⟨t, -, (⟨-, h⟩ | ⟨-, h⟩)⟩ <;> omega
      simp only [a1, a2, or_false]
      exact h1 i hic
    · have s1 : 2 * i ∉ S := fun h => by have := h2 _ h; omega
      have s2 : 2 * i + 1 ∉ S := fun h => by have := h2 _ h; omega
      simp only [s1, s2, false_or]
      constructor
      · rintro ⟨t, ht, (⟨hU, h⟩ | ⟨hU, h⟩)⟩
        · rintro ⟨t', ht', (⟨hU', h'⟩ | ⟨hU', h'⟩)⟩
          · omega
          · obtain rfl : t' = t := by omega
            exact hU' hU
        · omega
      · intro h
        refine ⟨i - c, by omega, ?_⟩
        by_cases hU : i - c ∈ U
        · exact Or.inl ⟨hU, by omega⟩
        · exact absurd ⟨i - c, by omega, Or.inr ⟨hU, by omega⟩⟩ h

/-- INTERNAL: the part below `2c` of `S ∪ blk c b U` is `S`. -/
theorem filter_union_blk {c b : ℕ} {S : Finset ℕ} (U : Finset ℕ) (hS : ∀ e ∈ S, e < 2 * c) :
    (S ∪ blk c b U).filter (· < 2 * c) = S := by
  ext e
  simp only [mem_filter, mem_union]
  constructor
  · rintro ⟨he | he, hlt⟩
    · exact he
    · have := blk_bounds he; omega
  · intro he; exact ⟨Or.inl he, hS e he⟩

/-- INTERNAL: the block offsets of `S ∪ blk c b U` decode to `U`. -/
theorem rowSet_union_blk {c b : ℕ} {S U : Finset ℕ} (hS : ∀ e ∈ S, e < 2 * c)
    (hU : U ⊆ range b) : rowSet c b (S ∪ blk c b U) = U := by
  ext t
  simp only [rowSet, mem_filter, mem_range, mem_union, mem_blk]
  constructor
  · rintro ⟨ht, h | ⟨t', ht', (⟨hU', h⟩ | ⟨-, h⟩)⟩⟩
    · have := hS _ h; omega
    · obtain rfl : t' = t := by omega
      exact hU'
    · omega
  · intro h
    exact ⟨mem_range.1 (hU h), Or.inr ⟨t, mem_range.1 (hU h), Or.inl ⟨h, rfl⟩⟩⟩

/-- INTERNAL: `rowSet c b S ⊆ [0, b)`. -/
theorem rowSet_sub (c b : ℕ) (S : Finset ℕ) : rowSet c b S ⊆ range b := filter_subset _ _

/-- INTERNAL: a valid state on `c + b` pairs is its part below `2c` plus one block. -/
theorem valid_split {c b : ℕ} {S : Finset ℕ} (hS : Valid (c + b) S) :
    S = S.filter (· < 2 * c) ∪ blk c b (rowSet c b S) ∧ Valid c (S.filter (· < 2 * c)) := by
  obtain ⟨h2, h1⟩ := hS
  refine ⟨?_, fun e he => (mem_filter.1 he).2, fun i hi => ?_⟩
  · ext e
    simp only [mem_union, mem_filter, mem_blk, rowSet, mem_range]
    constructor
    · intro he
      by_cases hlt : e < 2 * c
      · exact Or.inl ⟨he, hlt⟩
      · right
        have := h2 e he
        obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' e
        · refine ⟨q - c, by omega, Or.inl ⟨⟨by omega, ?_⟩, by omega⟩⟩
          rwa [show c + (q - c) = q by omega]
        · refine ⟨q - c, by omega, Or.inr ⟨?_, by omega⟩⟩
          rintro ⟨-, h⟩
          rw [show c + (q - c) = q by omega] at h
          exact (h1 q (by omega)).1 h he
    · rintro (⟨he, -⟩ | ⟨t, ht, (⟨⟨-, h⟩, rfl⟩ | ⟨h, rfl⟩)⟩)
      · exact he
      · exact h
      · by_contra h'
        exact h ⟨ht, (h1 (c + t) (by omega)).2 h'⟩
  · simp only [mem_filter]
    have := h1 i (by omega)
    constructor
    · rintro ⟨h, -⟩ ⟨h', -⟩; exact this.1 h h'
    · intro h; exact ⟨this.2 fun h' => h ⟨h', by omega⟩, by omega⟩

/-- INTERNAL: earlier blocks are unaffected by cutting at `2c`. -/
theorem rowSet_filter {c' b' c : ℕ} (h : c' + b' ≤ c) (S : Finset ℕ) :
    rowSet c' b' (S.filter (· < 2 * c)) = rowSet c' b' S := by
  ext t
  simp only [rowSet, mem_filter, mem_range]
  constructor
  · rintro ⟨ht, h', -⟩; exact ⟨ht, h'⟩
  · rintro ⟨ht, h'⟩; exact ⟨ht, h', by omega⟩


/-- INTERNAL: the block of small cell `s + 1` starts `b_s` after that of `s`. -/
theorem cellFirst_succ (I : Instance) (ε δ : ℚ) (s : ℕ) :
    cellFirst I ε δ (s + 1) = cellFirst I ε δ s + smallB I ε δ s :=
  Finset.sum_range_succ _ _

/-- INTERNAL: block starts are monotone. -/
theorem cellFirst_mono (I : Instance) (ε δ : ℚ) {s t : ℕ} (h : s ≤ t) :
    cellFirst I ε δ s ≤ cellFirst I ε δ t :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

/-- INTERNAL: one step of the `μ₀` sampler is `cellDraw` pushed through `blk`. -/
theorem step_eq (I : Instance) (ε δ : ℚ) (s : ℕ) (S : Finset ℕ) :
    (do
      let k ← uniformBelow (smallB I ε δ s + 1)
      let rank ← uniformBelow (Nat.choose (smallB I ε δ s) k)
      pure (S ∪ (Finset.range (smallB I ε δ s)).image fun t =>
        if t ∈ unrank (smallB I ε δ s) k rank then 2 * (cellFirst I ε δ s + t)
        else 2 * (cellFirst I ε δ s + t) + 1) : PMF (Finset ℕ)) =
      (cellDraw (smallB I ε δ s)).map fun U => S ∪ blk (cellFirst I ε δ s) (smallB I ε δ s) U := by
  simp only [cellDraw, PMF.map_bind, PMF.pure_map]
  rfl

open Classical in
/-- INTERNAL: closed form of the first `m` cells of the `μ₀` sampler: a valid state
on the first `cellFirst m` pairs gets `∏_{s<m} 1/((b_s + 1) C(b_s, x_s))`.
TEXLINE: sections/algorithm.tex:44-47 -/
theorem loop_apply (I : Instance) (ε δ : ℚ) (m : ℕ) (S : Finset ℕ) :
    loop (fun s S => do
      let k ← uniformBelow (smallB I ε δ s + 1)
      let rank ← uniformBelow (Nat.choose (smallB I ε δ s) k)
      pure (S ∪ (Finset.range (smallB I ε δ s)).image fun t =>
        if t ∈ unrank (smallB I ε δ s) k rank then 2 * (cellFirst I ε δ s + t)
        else 2 * (cellFirst I ε δ s + t) + 1)) m ∅ S =
      if Valid (cellFirst I ε δ m) S then
        ENNReal.ofReal (∏ s ∈ range m,
          cellW (smallB I ε δ s) (rowSet (cellFirst I ε δ s) (smallB I ε δ s) S).card)
      else 0 := by
  induction m generalizing S with
  | zero =>
    rw [loop_zero, PMF.pure_apply]
    have : Valid (cellFirst I ε δ 0) S ↔ S = ∅ := by
      simp only [Valid, cellFirst, range_zero, sum_empty, mul_zero, Nat.not_lt_zero]
      constructor
      · rintro ⟨h, -⟩; exact eq_empty_of_forall_notMem fun e he => h e he
      · rintro rfl; simp
    simp [this]
  | succ m ih =>
    rw [loop_succ, PMF.bind_apply]
    set c := cellFirst I ε δ m
    set b := smallB I ε δ m
    rw [cellFirst_succ]
    by_cases hV : Valid (c + b) S
    · obtain ⟨hSeq, hV0⟩ := valid_split hV
      rw [if_pos hV, tsum_eq_single (S.filter (· < 2 * c))]
      · rw [ih, if_pos hV0, step_eq, PMF.map_apply, tsum_eq_single (rowSet c b S)]
        · rw [if_pos hSeq, cellDraw_apply, if_pos (rowSet_sub _ _ _),
            ← ENNReal.ofReal_mul (prod_nonneg fun _ _ => cellW_nonneg _ _), prod_range_succ]
          congr 2
          refine prod_congr rfl fun s hs => ?_
          rw [rowSet_filter]
          rw [← cellFirst_succ]
          exact cellFirst_mono I ε δ (by simpa using hs)
        · intro U hU
          split_ifs with h
          · rw [cellDraw_apply]
            split_ifs with hUb
            · exfalso; apply hU
              rw [h, rowSet_union_blk (fun e he => (mem_filter.1 he).2) hUb]
            · rfl
          · rfl
      · intro S0 hS0
        rw [ih]
        split_ifs with hv
        · refine mul_eq_zero_of_right _ ?_
          rw [step_eq, PMF.map_apply]
          refine ENNReal.tsum_eq_zero.2 fun U => ?_
          rw [if_neg]
          intro h
          apply hS0
          rw [h, filter_union_blk U hv.1]
        · exact zero_mul _
    · rw [if_neg hV]
      refine ENNReal.tsum_eq_zero.2 fun S0 => ?_
      rw [ih]
      split_ifs with hv
      · refine mul_eq_zero_of_right _ ?_
        rw [step_eq, PMF.map_apply]
        refine ENNReal.tsum_eq_zero.2 fun U => ?_
        rw [if_neg]
        rintro rfl
        exact hV (valid_union U hv)
      · exact zero_mul _


/-- INTERNAL: the pair labels of all small cells fill `[0, p)`. -/
theorem cellFirst_nSmall (I : Instance) (ε δ : ℚ) :
    cellFirst I ε δ (nSmall I ε δ) = pSmall I ε δ := by
  unfold cellFirst smallB smallAt pSmall nSmall
  exact sum_range_getD_eq _ (fun e : Entry => e.2.2) _

/-- INTERNAL: reading a concatenation of constant blocks. -/
theorem flatMap_replicate_getD (b : ℕ → ℕ) (n s t : ℕ) (hs : s < n) (ht : t < b s) :
    ((List.range n).flatMap fun u => List.replicate (b u) u).getD
      (∑ u ∈ Finset.range s, b u + t) 0 = s := by
  have hlen : ∀ n, ((List.range n).flatMap fun u => List.replicate (b u) u).length =
      ∑ u ∈ Finset.range n, b u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih,
        Finset.sum_range_succ]; simp
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_ge s n with h | h
    · have hlt : ∑ u ∈ Finset.range s, b u + t <
          ((List.range n).flatMap fun u => List.replicate (b u) u).length := by
        rw [hlen]
        calc ∑ u ∈ Finset.range s, b u + t < ∑ u ∈ Finset.range (s + 1), b u := by
              rw [Finset.sum_range_succ]; omega
          _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
      rw [List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
      exact ih h
    · obtain rfl : s = n := by omega
      rw [List.getElem?_append_right (by rw [hlen]; omega), hlen]
      simp [ht]

/-- INTERNAL: the labels of small cell `s` are `[cellFirst s, cellFirst s + b_s)`. -/
theorem pairCell_block (I : Instance) (ε δ : ℚ) (s : ℕ) (hs : s < nSmall I ε δ) :
    (range (pSmall I ε δ)).filter (fun i => pairCell I ε δ i = s) =
      (range (smallB I ε δ s)).image (cellFirst I ε δ s + ·) := by
  symm
  refine eq_of_subset_of_card_le ?_ ?_
  · intro i hi
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hi
    have ht := mem_range.1 ht
    have hle : cellFirst I ε δ (s + 1) ≤ pSmall I ε δ := by
      rw [← cellFirst_nSmall]; exact cellFirst_mono I ε δ hs
    rw [cellFirst_succ] at hle
    refine mem_filter.2 ⟨mem_range.2 (by omega), ?_⟩
    exact flatMap_replicate_getD (smallB I ε δ) _ s t hs ht
  · rw [← smallB_eq_card, card_image_of_injective _ (add_right_injective _), card_range]

/-- INTERNAL: counting labels of small cell `s` with a property, by offset. -/
theorem card_block (I : Instance) (ε δ : ℚ) (s : ℕ) (hs : s < nSmall I ε δ)
    (P : ℕ → Prop) [DecidablePred P] :
    ((range (pSmall I ε δ)).filter (fun i => pairCell I ε δ i = s ∧ P i)).card =
      ((range (smallB I ε δ s)).filter (fun t => P (cellFirst I ε δ s + t))).card := by
  rw [← filter_filter, pairCell_block I ε δ s hs, filter_image,
    card_image_of_injective _ (add_right_injective _)]


end Cellcounting.Analysis.Mu0Law

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal

open Finset Mu0Law in
/-- **The `μ₀` sampler has law `μ_0`** (`lem:initialization`, last claim).
PAPER: sections/algorithm.tex:44-47 -/
theorem refMu0_apply (I : Instance) (ε δ : ℚ) (S : Finset ℕ) :
    refMu0 I ε δ S = ENNReal.ofReal (refMu I ε δ 0 S) := by
  classical
  have hval : Mu0Law.Valid (pSmall I ε δ) S ↔ S ∈ transStates I ε δ := by
    simp only [Mu0Law.Valid, transStates, refStates, mem_filter, mem_powerset, kind_eq_transversal_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun e he => mem_range.2 (h1 e he), h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun e he => mem_range.1 (h1 he), h2⟩
  unfold refMu0
  rw [loop_apply, cellFirst_nSmall, refMu]
  by_cases hS : S ∈ transStates I ε δ
  · rw [if_pos (hval.2 hS), if_pos hS]
    congr 1
    have hV := hval.2 hS
    -- the profile in terms of the blocks
    have hx : ∀ s ∈ range (nSmall I ε δ), (profile I ε δ S).1 s =
        (rowSet (cellFirst I ε δ s) (smallB I ε δ s) S).card := by
      intro s hs
      exact card_block I ε δ s (mem_range.1 hs) (fun i => 2 * i ∈ S)
    have hy : ∀ s ∈ range (nSmall I ε δ), (profile I ε δ S).2 s =
        smallB I ε δ s - (rowSet (cellFirst I ε δ s) (smallB I ε δ s) S).card := by
      intro s hs
      have hs' := mem_range.1 hs
      have hle : cellFirst I ε δ (s + 1) ≤ pSmall I ε δ := by
        rw [← cellFirst_nSmall]; exact cellFirst_mono I ε δ hs'
      rw [cellFirst_succ] at hle
      show ((range (pSmall I ε δ)).filter fun i => pairCell I ε δ i = s ∧ 2 * i + 1 ∈ S).card = _
      rw [card_block I ε δ s hs' (fun i => 2 * i + 1 ∈ S)]
      have hsplit := card_filter_add_card_filter_not
        (s := range (smallB I ε δ s)) (fun t => 2 * (cellFirst I ε δ s + t) ∈ S)
      rw [card_range] at hsplit
      have : (range (smallB I ε δ s)).filter (fun t => 2 * (cellFirst I ε δ s + t) + 1 ∈ S) =
          (range (smallB I ε δ s)).filter (fun t => ¬ 2 * (cellFirst I ε δ s + t) ∈ S) := by
        refine filter_congr fun t ht => ?_
        have := hV.2 (cellFirst I ε δ s + t) (by have := mem_range.1 ht; omega)
        tauto
      rw [this, rowSet]
      omega
    have hh : ∀ x y, hWeight I ε δ 0 x y = (Mf I ε δ : ℝ) := by
      intro x y
      simp [hWeight, card_freeBox]
    have hMf : (Mf I ε δ : ℝ) ≠ 0 := by
      have : 0 < Mf I ε δ := by
        unfold Mf
        refine List.prod_pos fun a ha => ?_
        obtain ⟨e, -, rfl⟩ := List.mem_map.1 ha
        omega
      exact_mod_cast this.ne'
    rw [transMass_eq_Cpart, Cpart_zero, fWeight, hh, C0]
    push_cast
    rw [mul_div_mul_left _ _ hMf, ← prod_div_distrib]
    refine prod_congr rfl fun s hs => ?_
    rw [hx s hs, hy s hs, cellW]
  · rw [if_neg (fun h => hS (hval.1 h)), if_neg hS, ENNReal.ofReal_zero]

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `refMu0_apply` via the unranking bijection, per-cell law and loop induction
-/
