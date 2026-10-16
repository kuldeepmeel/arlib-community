import Cellcounting.Analysis.PmfClose
import Cellcounting.Analysis.RefExperiment
import Cellcounting.Analysis.WeightOracle
import Cellcounting.Analysis.DyadicDraw
import Cellcounting.Analysis.ApproxCoupling

/-!
# Coupling the implemented run to the reference experiment

`lem:bounded-implementation` (`algorithm.tex:466-603`), coupling clause, in the
form `annealRun_good` uses.  There is a joint law `ν` of the implemented output
`Ẑ` (`Pseudocode.annealRun`) and the reference output `Z_ref` (`refRun`) such
that, except on an event of probability at most `10 J_* ξ`, whenever the
reference run does not abort, neither does the implemented one, and
`|log(Ẑ / Z_ref)| ≤ 4 H ξ`.

The proof follows the paper's coupling argument (`algorithm.tex:472-524`), built
with the `ACouple` calculus of `ApproxCoupling.lean` (`bind`, `bind_left`, `loop`,
`map`, `of_pclose`):

* `draw_couple`, `mu0_couple`: each dyadic draw is within `ξ` of the exact uniform
  draw (`dyadicDraw_close`), so the two `μ₀` draws agree except with probability
  `2 n_small ξ`, and the common value is a transversal (`refMu0_kind`);
* `oracle_bad_le`, `lam_bad_le`: each evaluation, at the profile of a state of `X`
  (`profile_valid_of_kind`), meets its relative tolerance `ξ` except with
  probability `ξ` (`weight_oracle_accurate`, `ξ_in = θ = ξ`); the factorial and
  multiplier factors of `λ` are exact on both sides;
* `accept_couple`: from accurate evaluations, `|min{1, r'}⁺ - min{1, r}⁺| ≤ 4ξ`
  whatever the multipliers are, and the dyadic threshold adds at most `ξ`;
* `step_couple` (`9ξ` per transition), `restartStep_couple`, `restart_couple`
  (cap decisions agree because states agree), `observeState_couple`,
  `observe_couple` (`Σ G_j` within `exp(±4ξ)`, counts equal), `phase_couple`
  (`R̂_j` within `exp(±4ξ)`, multiplier updates equal);
* `ACouple.loop` over the `H` phases and `ACouple.map` through the output map.

The total charge is `H (2 n_small + 9 (B_ret + 1) + 11 N_av + 2) ξ ≤ 10 J_* ξ`.
The paper charges `7 T_max + 2 H N_av + 2 H s_sm` actions at `ξ` each plus `4ξ` per
acceptance; the count here differs only in bookkeeping and stays far inside
`10 J_* ξ`.  Only `h_j ≥ 0` is used; no positivity of the multipliers is needed.

Facts about the paired encoding (`signatures.tex:13-41`) that the coupling needs
before it may call the weight oracle:

* `profile_valid_of_kind`: a state of `X` (a transversal or a defect state) has
  a small-count profile `(x, y)` inside the box `x_s, y_s ≤ b_s` and of total
  `Σ_s (x_s + y_s) = p`, which are the hypotheses of `weight_oracle_accurate`;
* `refMu0_kind`: every state the exact `μ₀` sampler can return is a
  transversal (each pair `i < p` carries exactly one of its elements `2i`,
  `2i + 1`);
* `nSmall_le_pSmall`: every small cell has a positive bound, so there are at
  most `p` small cells.
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal

/-- INTERNAL: every retained, hence every small, cell has a positive bound, so
the number of small cells is at most `p = Σ_s b_s`.
TEXLINE: sections/algorithm.tex:466-490 -/
theorem nSmall_le_pSmall (I : Instance) (ε δ : ℚ) : nSmall I ε δ ≤ pSmall I ε δ := by
  have h := List.length_le_sum_of_one_le ((smallCells I ε δ).map fun e => e.2.2) (by
    intro i hi
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hi
    have he' : e ∈ retained I := (List.mem_filter.1 he).1
    simp only [retained, List.mem_flatMap, List.mem_filterMap] at he'
    obtain ⟨a, _, b, _, hb⟩ := he'
    split_ifs at hb with h0
    · cases hb; exact h0)
  simpa [nSmall, pSmall] using h


/-- INTERNAL: the block of small cell `s + 1` starts `b_s` after that of `s`. -/
theorem cellFirst_succ' (I : Instance) (ε δ : ℚ) (s : ℕ) :
    cellFirst I ε δ (s + 1) = cellFirst I ε δ s + smallB I ε δ s :=
  Finset.sum_range_succ _ _

/-- INTERNAL: the pair labels of all small cells fill `[0, p)`. -/
theorem cellFirst_nSmall (I : Instance) (ε δ : ℚ) : cellFirst I ε δ (nSmall I ε δ) = pSmall I ε δ := by
  unfold cellFirst smallB smallAt pSmall nSmall
  exact sum_range_getD_eq _ (fun e : Entry => e.2.2) _

/-- INTERNAL: block starts are monotone. -/
theorem cellFirst_mono' (I : Instance) (ε δ : ℚ) {s t : ℕ} (h : s ≤ t) :
    cellFirst I ε δ s ≤ cellFirst I ε δ t :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

/-- INTERNAL: every label below `cellFirst n` lies in the block of some cell `s < n`. -/
theorem exists_cell_of_lt (I : Instance) (ε δ : ℚ) (n i : ℕ) (hi : i < cellFirst I ε δ n) :
    ∃ s < n, cellFirst I ε δ s ≤ i ∧ i < cellFirst I ε δ s + smallB I ε δ s := by
  induction n with
  | zero => simp [cellFirst] at hi
  | succ n ih =>
    by_cases h : i < cellFirst I ε δ n
    · obtain ⟨s, hs, h1, h2⟩ := ih h; exact ⟨s, by omega, h1, h2⟩
    · rw [cellFirst_succ'] at hi; exact ⟨n, by omega, by omega, hi⟩

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

/-- INTERNAL: label `cellFirst s + t`, `t < b_s`, belongs to small cell `s`. -/
theorem pairCell_eq (I : Instance) (ε δ : ℚ) (s t : ℕ) (hs : s < nSmall I ε δ)
    (ht : t < smallB I ε δ s) : pairCell I ε δ (cellFirst I ε δ s + t) = s :=
  flatMap_replicate_getD (smallB I ε δ) _ s t hs ht

/-- INTERNAL: every pair label below `p` lies in the block of its own small cell.
TEXLINE: sections/signatures.tex:13-41 -/
theorem pairCell_spec (I : Instance) (ε δ : ℚ) (i : ℕ) (hi : i < pSmall I ε δ) :
    pairCell I ε δ i < nSmall I ε δ ∧ cellFirst I ε δ (pairCell I ε δ i) ≤ i ∧
      i < cellFirst I ε δ (pairCell I ε δ i) + smallB I ε δ (pairCell I ε δ i) := by
  rw [← cellFirst_nSmall] at hi
  obtain ⟨s, hs, h1, h2⟩ := exists_cell_of_lt I ε δ _ i hi
  have := pairCell_eq I ε δ s (i - cellFirst I ε δ s) hs (by omega)
  rw [Nat.add_sub_cancel' h1] at this
  rw [this]; exact ⟨hs, h1, h2⟩

/-- INTERNAL: a state of `X` has a box-valid small-count profile of total `p`.
TEXLINE: sections/signatures.tex:13-41 -/
theorem profile_valid_of_kind (I : Instance) (ε δ : ℚ) (S : Finset ℕ)
    (hS : kind I ε δ S ≠ .outside) :
    (∀ s < nSmall I ε δ, (profile I ε δ S).1 s ≤ smallB I ε δ s ∧
        (profile I ε δ S).2 s ≤ smallB I ε δ s) ∧
      ∑ s ∈ Finset.range (nSmall I ε δ), ((profile I ε δ S).1 s + (profile I ε δ S).2 s) =
        pSmall I ε δ := by
  have hblock : ∀ s < nSmall I ε δ, ∀ (P : ℕ → Prop) [DecidablePred P],
      ((Finset.range (pSmall I ε δ)).filter fun i => pairCell I ε δ i = s ∧ P i).card ≤
        smallB I ε δ s := by
    intro s hs P _
    calc _ ≤ (Finset.Ico (cellFirst I ε δ s) (cellFirst I ε δ s + smallB I ε δ s)).card :=
          Finset.card_le_card (by
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_range] at hi
            obtain ⟨_, h1, h2⟩ := pairCell_spec I ε δ i hi.1
            rw [hi.2.1] at h1 h2
            exact Finset.mem_Ico.2 ⟨h1, h2⟩)
      _ = _ := by simp
  have hfib : ∀ (P : ℕ → Prop) [DecidablePred P],
      ∑ s ∈ Finset.range (nSmall I ε δ),
        ((Finset.range (pSmall I ε δ)).filter fun i => pairCell I ε δ i = s ∧ P i).card =
        ((Finset.range (pSmall I ε δ)).filter P).card := by
    intro P _
    rw [Finset.card_eq_sum_card_fiberwise (f := pairCell I ε δ) (t := Finset.range (nSmall I ε δ))
      (fun i hi => Finset.mem_range.2
        (pairCell_spec I ε δ i (Finset.mem_range.1 (Finset.mem_filter.1 hi).1)).1)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.filter_filter]
    congr 1; ext i; simp only [Finset.mem_filter]; tauto
  refine ⟨fun s hs => ⟨hblock s hs _, hblock s hs _⟩, ?_⟩
  rw [Finset.sum_add_distrib]
  simp only [profile]
  rw [hfib, hfib]
  set E := (Finset.range (pSmall I ε δ)).filter fun i => 2 * i ∉ S ∧ 2 * i + 1 ∉ S with hE
  set F := (Finset.range (pSmall I ε δ)).filter fun i => 2 * i ∈ S ∧ 2 * i + 1 ∈ S with hF
  have hEF : E.card = F.card := by
    have : kind I ε δ S = if E.card = 0 then (if F.card = 0 then .transversal else .outside)
        else if E.card = 1 ∧ F.card = 1 then .defect (E.sup id) (F.sup id) else .outside := rfl
    rw [this] at hS
    split_ifs at hS with h1 h2 h3 <;> first | exact absurd rfl hS | omega
  have hcount : ((Finset.range (pSmall I ε δ)).filter fun i => 2 * i ∈ S).card +
      ((Finset.range (pSmall I ε δ)).filter fun i => 2 * i + 1 ∈ S).card + E.card =
      pSmall I ε δ + F.card := by
    simp only [hE, hF, Finset.card_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    rw [show ∀ g : ℕ → ℕ, pSmall I ε δ + ∑ i ∈ Finset.range (pSmall I ε δ), g i =
        ∑ i ∈ Finset.range (pSmall I ε δ), (1 + g i) from fun g => by
      rw [Finset.sum_add_distrib]; simp]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : 2 * i ∈ S <;> by_cases h2 : 2 * i + 1 ∈ S <;> simp [h1, h2]
  omega

/-- INTERNAL: one block of the `μ₀` construction keeps every pair singly occupied. -/
theorem mu0_block_inv (c b : ℕ) (U : Finset ℕ) (S : Finset ℕ)
    (h1 : ∀ i < c, (2 * i ∈ S ↔ 2 * i + 1 ∉ S)) (h2 : ∀ e ∈ S, e < 2 * c) :
    (∀ i < c + b, (2 * i ∈ S ∪ (Finset.range b).image (fun t =>
        if t ∈ U then 2 * (c + t) else 2 * (c + t) + 1) ↔
      2 * i + 1 ∉ S ∪ (Finset.range b).image (fun t =>
        if t ∈ U then 2 * (c + t) else 2 * (c + t) + 1))) ∧
    ∀ e ∈ S ∪ (Finset.range b).image (fun t =>
        if t ∈ U then 2 * (c + t) else 2 * (c + t) + 1), e < 2 * (c + b) := by
  have himg : ∀ e, e ∈ (Finset.range b).image (fun t =>
        if t ∈ U then 2 * (c + t) else 2 * (c + t) + 1) ↔
      ∃ t < b, (t ∈ U ∧ e = 2 * (c + t)) ∨ (t ∉ U ∧ e = 2 * (c + t) + 1) := by
    intro e
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨t, ht, rfl⟩
      by_cases hU : t ∈ U
      · exact ⟨t, ht, Or.inl ⟨hU, by simp [hU]⟩⟩
      · exact ⟨t, ht, Or.inr ⟨hU, by simp [hU]⟩⟩
    · rintro ⟨t, ht, (⟨hU, rfl⟩ | ⟨hU, rfl⟩)⟩
      · exact ⟨t, ht, by simp [hU]⟩
      · exact ⟨t, ht, by simp [hU]⟩
  refine ⟨fun i hi => ?_, fun e he => ?_⟩
  · simp only [Finset.mem_union, himg]
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
  · rcases Finset.mem_union.1 he with he | he
    · have := h2 e he; omega
    · obtain ⟨t, ht, (⟨-, rfl⟩ | ⟨-, rfl⟩)⟩ := (himg e).1 he <;> omega

/-- INTERNAL: after `m` blocks of the exact `μ₀` sampler, the pairs below
`cellFirst m` are singly occupied and nothing else is.
TEXLINE: sections/algorithm.tex:44-47 -/
theorem refMu0_inv (I : Instance) (ε δ : ℚ) (m : ℕ) (S : Finset ℕ)
    (hS : S ∈ (loop (fun s S => do
      let k ← uniformBelow (smallB I ε δ s + 1)
      let rank ← uniformBelow (Nat.choose (smallB I ε δ s) k)
      pure (S ∪ (Finset.range (smallB I ε δ s)).image fun t =>
        if t ∈ unrank (smallB I ε δ s) k rank then 2 * (cellFirst I ε δ s + t)
        else 2 * (cellFirst I ε δ s + t) + 1)) m ∅).support) :
    (∀ i < cellFirst I ε δ m, (2 * i ∈ S ↔ 2 * i + 1 ∉ S)) ∧
      ∀ e ∈ S, e < 2 * cellFirst I ε δ m := by
  induction m generalizing S with
  | zero =>
    rw [loop_zero, PMF.support_pure, Set.mem_singleton_iff] at hS
    subst hS; simp [cellFirst]
  | succ m ih =>
    rw [loop_succ] at hS
    obtain ⟨S0, hS0, hS⟩ := (PMF.mem_support_bind_iff _ _ _).1 hS
    obtain ⟨k, -, hS⟩ := (PMF.mem_support_bind_iff _ _ _).1 hS
    obtain ⟨rank, -, hS⟩ := (PMF.mem_support_bind_iff _ _ _).1 hS
    have hS : S = _ := (PMF.mem_support_pure_iff _ _).1 hS
    subst hS
    obtain ⟨a1, a2⟩ := ih S0 hS0
    rw [cellFirst_succ']
    exact mu0_block_inv _ _ _ _ a1 a2

/-- INTERNAL: the exact `μ₀` sampler returns transversals only.
TEXLINE: sections/algorithm.tex:44-47 -/
theorem refMu0_kind (I : Instance) (ε δ : ℚ) (S : Finset ℕ) (hS : S ∈ (refMu0 I ε δ).support) :
    kind I ε δ S = .transversal := by
  obtain ⟨h1, -⟩ := refMu0_inv I ε δ (nSmall I ε δ) S hS
  rw [cellFirst_nSmall] at h1
  have hE : ((Finset.range (pSmall I ε δ)).filter fun i => 2 * i ∉ S ∧ 2 * i + 1 ∉ S) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro i hi; have := h1 i (Finset.mem_range.1 hi); tauto
  have hF : ((Finset.range (pSmall I ε δ)).filter fun i => 2 * i ∈ S ∧ 2 * i + 1 ∈ S) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro i hi; have := h1 i (Finset.mem_range.1 hi); tauto
  show (if _ then _ else _) = _
  simp [hE, hF]


/-- INTERNAL: `0 < ξ < 1/4`.
TEXLINE: sections/algorithm.tex:385-391 -/
theorem xi_bounds (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (hε1 : ε < 1) :
    0 < ξParam I ε δ ∧ ξParam I ε δ < 1 / 4 := by
  have hJ : 0 < JstarParam I ε δ := by unfold JstarParam; positivity
  have hη : 0 < ηParam I ε δ := by unfold ηParam; positivity
  have hη1 : ηParam I ε δ < 1 := by
    unfold ηParam
    have : (1 : ℚ) ≤ ((200 * (HParam I ε δ + 1) : ℕ) : ℚ) := by
      exact_mod_cast (by omega : 1 ≤ 200 * (HParam I ε δ + 1))
    rw [div_lt_one (by linarith)]; linarith
  unfold ξParam
  have : (1000 : ℚ) ≤ ((1000 * JstarParam I ε δ : ℕ) : ℚ) := by
    exact_mod_cast (by omega : 1000 ≤ 1000 * JstarParam I ε δ)
  refine ⟨div_pos hη (by linarith), ?_⟩
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-- INTERNAL: a computed value `l` is `t r` for a factor `t ∈ [1 - ξ, 1 + ξ]`.
TEXLINE: sections/algorithm.tex:483-498 -/
def OracleOK (ξ : ℚ) (r : ℝ) (l : ℚ) : Prop :=
  ∃ t : ℝ, 1 - (ξ : ℝ) ≤ t ∧ t ≤ 1 + (ξ : ℝ) ∧ (l : ℝ) = t * r

/-- INTERNAL: a two-sided relative bound gives the multiplicative form. -/
theorem oracleOK_of_bounds {ξ : ℚ} {r : ℝ} {l : ℚ} (hξ : 0 ≤ (ξ : ℝ)) (hr : 0 ≤ r) (h1 : (1 - (ξ : ℝ)) * r ≤ l)
    (h2 : (l : ℝ) ≤ (1 + (ξ : ℝ)) * r) : OracleOK ξ r l := by
  rcases hr.eq_or_lt with h | h
  · subst h
    simp only [mul_zero] at h1 h2
    exact ⟨1, by linarith, by linarith, by simp; exact_mod_cast le_antisymm h2 h1⟩
  · refine ⟨(l : ℝ) / r, ?_, ?_, by field_simp⟩
    · rw [le_div_iff₀ h]; linarith
    · rw [div_le_iff₀ h]; linarith

/-- INTERNAL: a ratio of two `(1 ± ξ)` factors lies within `1 ± 4ξ` and `exp(±4ξ)`.
TEXLINE: sections/algorithm.tex:487-498 -/
theorem ratio_bounds {ξ t1 t2 : ℝ} (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 4) (a1 : 1 - ξ ≤ t1)
    (b1 : t1 ≤ 1 + ξ) (a2 : 1 - ξ ≤ t2) (b2 : t2 ≤ 1 + ξ) :
    0 < t1 / t2 ∧ 1 - 4 * ξ ≤ t1 / t2 ∧ t1 / t2 ≤ 1 + 4 * ξ ∧
      Real.exp (-(4 * ξ)) ≤ t1 / t2 ∧ t1 / t2 ≤ Real.exp (4 * ξ) := by
  have ht2 : 0 < t2 := by linarith
  have ht1 : 0 < t1 := by linarith
  have hup : t1 / t2 ≤ 1 + 4 * ξ := by rw [div_le_iff₀ ht2]; nlinarith
  have hlow' : 1 / (1 + 4 * ξ) ≤ t1 / t2 := by
    rw [div_le_div_iff₀ (by linarith) ht2]; nlinarith
  refine ⟨div_pos ht1 ht2, ?_, hup, ?_, ?_⟩
  · rw [le_div_iff₀ ht2]; nlinarith
  · refine le_trans ?_ hlow'
    rw [le_div_iff₀ (by linarith), Real.exp_neg]
    rw [inv_mul_le_iff₀ (Real.exp_pos _), mul_one]
    linarith [Real.add_one_le_exp (4 * ξ)]
  · linarith [Real.add_one_le_exp (4 * ξ)]

/-- INTERNAL: `r ↦ min{1, r}⁺` moves by at most `|s - 1|` under `r ↦ s r`.
TEXLINE: sections/algorithm.tex:491-498 -/
theorem clamp_close (r s ξ : ℝ) (hs0 : 0 < s) (hs1 : 1 - 4 * ξ ≤ s) (hs2 : s ≤ 1 + 4 * ξ) :
    |max (min 1 (s * r)) 0 - max (min 1 r) 0| ≤ 4 * ξ := by
  rcases le_or_gt r 0 with hr | hr
  · have : s * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs0.le hr
    rw [max_eq_right (min_le_of_right_le this), max_eq_right (min_le_of_right_le hr)]
    simp; linarith
  · have hsr : 0 < s * r := mul_pos hs0 hr
    rw [max_eq_left (le_min zero_le_one hsr.le), max_eq_left (le_min zero_le_one hr.le),
      abs_sub_le_iff]
    constructor
    · rcases le_total r 1 with h | h
      · rw [min_eq_right h]
        calc min 1 (s * r) - r ≤ s * r - r := by linarith [min_le_right 1 (s * r)]
          _ = (s - 1) * r := by ring
          _ ≤ 4 * ξ * 1 := by
            rcases le_total s 1 with h' | h'
            · nlinarith
            · exact mul_le_mul (by linarith) h hr.le (by linarith)
          _ = 4 * ξ := mul_one _
      · rw [min_eq_left h]; linarith [min_le_left 1 (s * r)]
    · rcases le_total (s * r) 1 with h | h
      · rw [min_eq_right h]
        rcases le_total r 1 with h' | h'
        · rw [min_eq_right h']
          calc r - s * r = (1 - s) * r := by ring
            _ ≤ 4 * ξ := by
              rcases le_total s 1 with h'' | h''
              · calc (1 - s) * r ≤ 4 * ξ * 1 := mul_le_mul (by linarith) h' hr.le (by linarith)
                  _ = _ := mul_one _
              · nlinarith
        · rw [min_eq_left h']
          have : s ≤ 1 := by nlinarith
          nlinarith
      · rw [min_eq_left h]; linarith [min_le_left 1 r]

/-- INTERNAL: a `Bool` law is close to another when their `true` masses are. -/
theorem bool_pclose (μ ν : PMF Bool) (ζ : ℝ)
    (h : |(μ true).toReal - (ν true).toReal| ≤ ζ) : PClose μ ν (ENNReal.ofReal ζ) := by
  have hsum : ∀ ρ : PMF Bool, (ρ false).toReal = 1 - (ρ true).toReal := by
    intro ρ
    have h1 := ρ.tsum_coe
    rw [tsum_fintype, Fintype.sum_bool] at h1
    have := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_add (ρ.apply_ne_top _) (ρ.apply_ne_top _)] at this
    simp at this; linarith
  refine PClose.of_pointwise (fun b => ENNReal.ofReal ((μ b).toReal - (ν b).toReal)) ?_ ?_
  · intro b
    rw [← ENNReal.ofReal_toReal (μ.apply_ne_top b), ← ENNReal.ofReal_toReal (ν.apply_ne_top b)]
    refine le_trans ?_ ENNReal.ofReal_add_le
    simp only [ENNReal.toReal_nonneg, ENNReal.toReal_ofReal]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · rw [tsum_fintype, Fintype.sum_bool, hsum μ, hsum ν]
    set d := (μ true).toReal - (ν true).toReal
    rw [show 1 - (μ true).toReal - (1 - (ν true).toReal) = -d by ring]
    rcases le_total 0 d with hd | hd
    · rw [ENNReal.ofReal_of_nonpos (p := -d) (by linarith), add_zero]
      exact ENNReal.ofReal_le_ofReal (le_trans (le_abs_self d) h)
    · rw [ENNReal.ofReal_of_nonpos (p := d) hd, zero_add]
      exact ENNReal.ofReal_le_ofReal (le_trans (neg_le_abs d) h)

/-- INTERNAL: the acceptance probability of the dyadic threshold test. -/
theorem acceptTest_true (I : Instance) (ε δ : ℚ) (c : ℚ) :
    ((acceptTest I ε δ c) true).toReal =
      (min ⌊c * ((2 ^ kAccParam I ε δ : ℕ) : ℚ)⌋₊ (2 ^ kAccParam I ε δ) : ℕ) /
        ((2 ^ kAccParam I ε δ : ℕ) : ℝ) := by
  rw [← PMF.toOuterMeasure_apply_singleton, acceptTest, PMF.toOuterMeasure_map_apply,
    uniformBits_eq, PMF.toOuterMeasure_uniformOfFinset_apply, Finset.card_range]
  simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq]
  rw [show ((Finset.range (2 ^ kAccParam I ε δ)).filter fun x =>
      x < ⌊c * ((2 ^ kAccParam I ε δ : ℕ) : ℚ)⌋₊) =
      Finset.range (min ⌊c * ((2 ^ kAccParam I ε δ : ℕ) : ℚ)⌋₊ (2 ^ kAccParam I ε δ)) by
    ext Y; simp only [Finset.mem_filter, Finset.mem_range]; omega]
  rw [Finset.card_range, ENNReal.toReal_div]
  simp

/-- INTERNAL: the exact acceptance probability. -/
theorem refAccept_true (r : ℝ) : ((refAccept r) true).toReal = max (min 1 r) 0 := by
  rw [refAccept, PMF.bernoulli_apply]
  simp [Real.coe_toNNReal']

/-- INTERNAL: rounding a threshold in `[0, 1]` down to the grid `1/K`. -/
theorem floor_close (c : ℚ) (K : ℕ) (hK : 0 < K) (hc : c ≤ 1) :
    |((min ⌊c * (K : ℚ)⌋₊ K : ℕ) : ℝ) / (K : ℝ) - max (c : ℝ) 0| ≤ 1 / (K : ℝ) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  rcases le_or_gt c 0 with h | h
  · rw [Nat.floor_of_nonpos (mul_nonpos_of_nonpos_of_nonneg h (by positivity)),
      max_eq_right (by exact_mod_cast h)]
    simp
  · have h1 : ((⌊c * (K : ℚ)⌋₊ : ℕ) : ℚ) ≤ c * K := Nat.floor_le (by positivity)
    have h2 : c * K < ((⌊c * (K : ℚ)⌋₊ : ℕ) : ℚ) + 1 := Nat.lt_floor_add_one _
    have h3 : ⌊c * (K : ℚ)⌋₊ ≤ K := by
      have : ((⌊c * (K : ℚ)⌋₊ : ℕ) : ℚ) ≤ K := h1.trans (by nlinarith)
      exact_mod_cast this
    rw [min_eq_left h3, max_eq_left (by exact_mod_cast h.le)]
    have h1' : ((⌊c * (K : ℚ)⌋₊ : ℕ) : ℝ) ≤ (c : ℝ) * K := by exact_mod_cast h1
    have h2' : (c : ℝ) * K < ((⌊c * (K : ℚ)⌋₊ : ℕ) : ℝ) + 1 := by exact_mod_cast h2
    rw [abs_sub_le_iff, div_sub' hKr.ne', sub_div' hKr.ne', div_le_div_iff_of_pos_right hKr,
      div_le_div_iff_of_pos_right hKr]
    constructor <;> linarith

/-- INTERNAL: the acceptance grid is finer than `ξ`. -/
theorem two_pow_kAcc_inv_le (I : Instance) (ε δ : ℚ) (hξ : 0 < ξParam I ε δ) :
    1 / ((2 ^ kAccParam I ε δ : ℕ) : ℝ) ≤ (ξParam I ε δ : ℝ) := by
  have h1 : ⌈(ξParam I ε δ)⁻¹⌉₊ ≤ 2 ^ kAccParam I ε δ := Nat.le_pow_clog one_lt_two _
  have h2 : (ξParam I ε δ)⁻¹ ≤ ((2 ^ kAccParam I ε δ : ℕ) : ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have h2' : ((ξParam I ε δ)⁻¹ : ℝ) ≤ ((2 ^ kAccParam I ε δ : ℕ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 h2; push_cast at this ⊢; exact this
  have hξr : (0 : ℝ) < ξParam I ε δ := by exact_mod_cast hξ
  rw [div_le_iff₀ (by positivity)]
  calc (1 : ℝ) = (ξParam I ε δ : ℝ) * (ξParam I ε δ : ℝ)⁻¹ := (mul_inv_cancel₀ hξr.ne').symm
    _ ≤ _ := mul_le_mul_of_nonneg_left h2' hξr.le

/-- INTERNAL: the acceptance decisions of the implemented and exact transitions
coincide except with probability `5ξ`: `|min{1, r'} - min{1, r}| ≤ 4ξ` and the
dyadic threshold adds `≤ ξ`.
TEXLINE: sections/algorithm.tex:487-509 -/
theorem accept_couple (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (hε1 : ε < 1) (lN lO : ℚ) (rN rO : ℝ)
    (hN : OracleOK (ξParam I ε δ) rN lN) (hO : OracleOK (ξParam I ε δ) rO lO) :
    ACouple (acceptTest I ε δ (min 1 (lN / lO))) (refAccept (rN / rO)) (· = ·)
      (ENNReal.ofReal (5 * (ξParam I ε δ : ℝ))) := by
  obtain ⟨hξ, hξ1⟩ := xi_bounds I ε δ hε hε1
  have hξr : (0 : ℝ) ≤ ξParam I ε δ := by exact_mod_cast hξ.le
  have hξr1 : (ξParam I ε δ : ℝ) ≤ 1 / 4 := by
    rw [show (1 / 4 : ℝ) = ((1 / 4 : ℚ) : ℝ) by norm_num]; exact_mod_cast hξ1.le
  obtain ⟨t1, a1, b1, e1⟩ := hN
  obtain ⟨t2, a2, b2, e2⟩ := hO
  obtain ⟨hs0, hs1, hs2, -, -⟩ := ratio_bounds hξr hξr1 a1 b1 a2 b2
  refine ACouple.of_pclose (bool_pclose _ _ _ ?_)
  rw [acceptTest_true, refAccept_true]
  have hfl := floor_close (min 1 (lN / lO)) (2 ^ kAccParam I ε δ) (Nat.two_pow_pos _)
    (min_le_left _ _)
  have hk := two_pow_kAcc_inv_le I ε δ hξ
  have hcl := clamp_close (rN / rO) (t1 / t2) (ξParam I ε δ) hs0 hs1 hs2
  have hc : ((min 1 (lN / lO) : ℚ) : ℝ) = min 1 (t1 / t2 * (rN / rO)) := by
    push_cast; rw [e1, e2, mul_div_mul_comm]
  rw [hc] at hfl
  calc _ ≤ |((min ⌊min 1 (lN / lO) * ((2 ^ kAccParam I ε δ : ℕ) : ℚ)⌋₊ (2 ^ kAccParam I ε δ) : ℕ) : ℝ) /
          ((2 ^ kAccParam I ε δ : ℕ) : ℝ) - max (min 1 (t1 / t2 * (rN / rO))) 0| +
        |max (min 1 (t1 / t2 * (rN / rO))) 0 - max (min 1 (rN / rO)) 0| := abs_sub_le _ _ _
    _ ≤ (ξParam I ε δ : ℝ) + 4 * (ξParam I ε δ : ℝ) := add_le_add (hfl.trans hk) hcl
    _ = _ := by ring

/-- INTERNAL: `h_j ≥ 0`. -/
theorem hWeight_nonneg (I : Instance) (ε δ : ℚ) (j : ℕ) (x y : ℕ → ℕ) :
    0 ≤ hWeight I ε δ j x y :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- INTERNAL: a lower bound `1 - a` on an event bounds its complement by `a`. -/
theorem outer_compl_le {α : Type*} (μ : PMF α) (G : Set α) (a : ℝ)
    (h : ENNReal.ofReal (1 - a) ≤ μ.toOuterMeasure G) :
    μ.toOuterMeasure Gᶜ ≤ ENNReal.ofReal a := by
  have hsum : μ.toOuterMeasure G + μ.toOuterMeasure Gᶜ = 1 := by
    simp only [PMF.toOuterMeasure_apply]
    rw [← ENNReal.tsum_add]
    simp [Set.indicator_self_add_compl_apply]
  have hG : μ.toOuterMeasure G ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hsum ▸ le_self_add)
  have hc : μ.toOuterMeasure Gᶜ = 1 - μ.toOuterMeasure G := by
    rw [← hsum, ENNReal.add_sub_cancel_left hG]
  rw [hc]
  refine (tsub_le_tsub_left h _).trans ?_
  rcases le_or_gt a 1 with h1 | h1
  · rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · rw [ENNReal.ofReal_of_nonpos (by linarith), tsub_zero, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal h1.le

/-- INTERNAL: one evaluation `ĥ_j(x, y)` at the profile of a state of `X` fails its
relative tolerance `ξ` with probability at most `ξ` (`prop:weight-oracle` with
`ξ_in = θ = ξ`).
TEXLINE: sections/algorithm.tex:472-481 -/
theorem oracle_bad_le (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (S : Finset ℕ) (hS : kind I ε δ S ≠ .outside) (j : ℕ)
    (hj : j ≤ HParam I ε δ) :
    (oracle I ε δ (profile I ε δ S).1 (profile I ε δ S).2 j (ξParam I ε δ)
        (ξParam I ε δ)).toOuterMeasure
      {h | ¬ OracleOK (ξParam I ε δ) (hWeight I ε δ j (profile I ε δ S).1 (profile I ε δ S).2) h} ≤
      ENNReal.ofReal (ξParam I ε δ : ℝ) := by
  obtain ⟨hξ, hξ1⟩ := xi_bounds I ε δ hε hε1
  obtain ⟨hbox, htot⟩ := profile_valid_of_kind I ε δ S hS
  have hacc := weight_oracle_accurate hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas _ _ hbox htot j hj
    _ _ hξ hξ1 hξ hξ1
  refine le_trans (MeasureTheory.measure_mono fun h hh => ?_) (outer_compl_le _ _ _ hacc)
  exact fun hg => hh (oracleOK_of_bounds (by exact_mod_cast hξ.le) (hWeight_nonneg _ _ _ _ _ _)
    hg.1 hg.2)

/-- INTERNAL: an implemented `λ(S)` is within its relative tolerance of the exact
`λ(S)`, except with probability `ξ`; the factorial and multiplier factors are exact.
TEXLINE: sections/algorithm.tex:483-491 -/
theorem lam_bad_le (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (S : Finset ℕ) (k : Program.Kind) (hk : kind I ε δ S = k)
    (hS : k ≠ .outside) (a : ℕ) (ha : a ≤ HParam I ε δ) (w : ℕ → ℕ → ℚ) :
    (lam I ε δ S k a w).toOuterMeasure
      {l | ¬ OracleOK (ξParam I ε δ) (refLam I ε δ S a w) l} ≤
      ENNReal.ofReal (ξParam I ε δ : ℝ) := by
  unfold lam
  rw [PMF.toOuterMeasure_map_apply]
  refine le_trans (MeasureTheory.measure_mono fun h hh => ?_)
    (oracle_bad_le hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas S (hk ▸ hS) a ha)
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hh ⊢
  intro hok; apply hh
  obtain ⟨t, h1, h2, he⟩ := hok
  refine ⟨t, h1, h2, ?_⟩
  unfold refLam fWeight; rw [hk]
  cases k <;> (push_cast; rw [he]; ring)

/-- INTERNAL: the exact uniform draw of the reference experiment is `idealDraw`. -/
theorem uniformBelow_eq_idealDraw (k : ℕ) : uniformBelow k = idealDraw k := by
  unfold uniformBelow idealDraw; rfl

/-- INTERNAL: a dyadic draw couples to the exact uniform draw at cost `ξ`.
TEXLINE: sections/algorithm.tex:483-485 -/
theorem draw_couple (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (hε1 : ε < 1) (M : ℕ) :
    ACouple (dyadicDraw M (ξParam I ε δ)) (uniformBelow M) (· = ·)
      (ENNReal.ofReal (ξParam I ε δ : ℝ)) := by
  rw [uniformBelow_eq_idealDraw]
  exact ACouple.of_pclose (dyadicDraw_close M _ (xi_bounds I ε δ hε hε1).1).symm

/-- INTERNAL: one implemented transition couples to one exact transition from the
same state of `X`, at cost `9ξ`: two element draws (`ξ` each), two evaluations
(`ξ` each), and the acceptance decision (`5ξ`).  The common outcome is again in `X`.
TEXLINE: sections/algorithm.tex:472-509 -/
theorem step_couple (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (a : ℕ) (ha : a ≤ HParam I ε δ) (w : ℕ → ℕ → ℚ) (S : Finset ℕ)
    (hS : kind I ε δ S ≠ .outside) :
    ACouple (step I ε δ a w S) (refStep I ε δ a w S)
      (fun A B => A = B ∧ kind I ε δ A ≠ .outside) (9 * ENNReal.ofReal (ξParam I ε δ : ℝ)) := by
  set x := ENNReal.ofReal (ξParam I ε δ : ℝ) with hx
  have hξ0 : (0 : ℝ) ≤ ξParam I ε δ := by exact_mod_cast (xi_bounds I ε δ hε hε1).1.le
  refine ACouple.mono (ε := 0 + (x + (x + (x + (x + (ENNReal.ofReal (5 * (ξParam I ε δ : ℝ))
    + 0)))))) ?_ (fun _ _ h => h) ?_
  · unfold step refStep
    refine (ACouple.refl Arlib.Computation.ProbRAM.fair).bind fun h1 h2 hh => ?_
    subst hh
    cases h1
    · dsimp only [Bool.false_eq_true, ite_false]
      refine (draw_couple I ε δ hε hε1 _).bind fun u1 u1' hu => ?_
      subst hu
      refine (draw_couple I ε δ hε hε1 _).bind fun u2 u2' hu => ?_
      subst hu
      generalize insert (nthWith I ε δ S false u2) (S.erase (nthWith I ε δ S true u1)) = S'
      have key : ∀ k : Program.Kind, kind I ε δ S' = k → k ≠ .outside →
          ACouple (do
            let lNew ← lam I ε δ S' k a w
            let lOld ← lam I ε δ S (kind I ε δ S) a w
            let ok ← acceptTest I ε δ (min 1 (lNew / lOld))
            pure (if ok = true then S' else S))
          (do
            let ok ← refAccept (refLam I ε δ S' a w / refLam I ε δ S a w)
            pure (if ok = true then S' else S))
          (fun A B => A = B ∧ kind I ε δ A ≠ .outside)
          (x + (x + (ENNReal.ofReal (5 * (ξParam I ε δ : ℝ)) + 0))) := by
        intro k hk hk'
        refine ACouple.bind_left
          (lam_bad_le hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas S' k hk hk' a ha w) fun lN hN => ?_
        refine ACouple.bind_left
          (lam_bad_le hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas S _ rfl hS a ha w) fun lO hO => ?_
        refine (accept_couple I ε δ hε hε1 lN lO _ _ hN hO).bind fun o o' ho => ?_
        subst ho
        refine ACouple.pure ⟨rfl, ?_⟩
        cases o
        · simpa using hS
        · simpa [hk] using hk'
      cases hk : kind I ε δ S' with
      | outside => exact ACouple.mono (ACouple.pure ⟨rfl, hS⟩) (fun _ _ h => h) zero_le
      | transversal => exact key _ hk (by simp)
      | defect i l => exact key _ hk (by simp)
    · exact ACouple.mono (ACouple.pure ⟨rfl, hS⟩) (fun _ _ h => h) zero_le
  · rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    apply le_of_eq; ring

/-- INTERNAL: the restart invariant: the state is in `X`, and an unfinished
restart is at a stage `≤ j`.
TEXLINE: sections/algorithm.tex:214-225 -/
def RestInv (I : Instance) (ε δ : ℚ) (j : ℕ) (st : Restart) : Prop :=
  kind I ε δ st.S ≠ .outside ∧ (st.finished = false → st.stage ≤ j)

/-- INTERNAL: one iteration of the implemented capped restart couples to the
reference one at cost `9ξ`; the cap decisions agree because the states agree.
TEXLINE: sections/algorithm.tex:514-519 -/
theorem restartStep_couple (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (j : ℕ) (hj : j ≤ HParam I ε δ) (ws : ℕ → ℕ → ℕ → ℚ) (st : Restart)
    (hinv : RestInv I ε δ j st) :
    ACouple (restartStep I ε δ ws j st) (refRestartStep I ε δ ws j st)
      (fun a b => a = b ∧ RestInv I ε δ j a) (9 * ENNReal.ofReal (ξParam I ε δ : ℝ)) := by
  unfold restartStep refRestartStep
  split_ifs with hf hab hcap hτ
  · exact ACouple.mono (ACouple.pure ⟨rfl, hinv⟩) (fun _ _ h => h) zero_le
  · exact ACouple.mono (ACouple.pure ⟨rfl, hinv⟩) (fun _ _ h => h) zero_le
  · exact ACouple.mono (ACouple.pure ⟨rfl, hinv⟩) (fun _ _ h => h) zero_le
  all_goals
    have hst : st.stage ≤ j := hinv.2 (by simpa using hf)
    refine ACouple.mono (ε := 9 * ENNReal.ofReal (ξParam I ε δ : ℝ) + 0) ?_ (fun _ _ h => h)
      (by simp)
    refine (step_couple hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas st.stage (by omega)
      (ws st.stage) st.S hinv.1).bind fun S' S'' hS' => ?_
    obtain ⟨rfl, hk⟩ := hS'
  · cases hk' : kind I ε δ S' with
    | transversal =>
      refine ACouple.pure ⟨rfl, hk, fun h => ?_⟩
      simp only [decide_eq_false_iff_not] at h
      show st.stage + 1 ≤ j
      omega
    | defect i l => exact ACouple.pure ⟨rfl, hk, fun _ => hst⟩
    | outside => exact ACouple.pure ⟨rfl, hk, fun _ => hst⟩
  · cases hk' : kind I ε δ S' with
    | transversal => exact ACouple.pure ⟨rfl, hk, fun _ => hst⟩
    | defect i l => exact ACouple.pure ⟨rfl, hk, fun _ => hst⟩
    | outside => exact ACouple.pure ⟨rfl, hk, fun _ => hst⟩

/-- INTERNAL: the implemented capped restart couples to the reference one at
cost `9ξ` per allowed transition.
TEXLINE: sections/algorithm.tex:514-522 -/
theorem restart_couple (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (j : ℕ) (hj : j ≤ HParam I ε δ) (ws : ℕ → ℕ → ℕ → ℚ)
    (S0 : Finset ℕ) (hS0 : kind I ε δ S0 ≠ .outside) :
    ACouple (restart I ε δ ws j S0) (refRestart I ε δ ws j S0)
      (fun a b => a = b ∧ RestInv I ε δ j a)
      (((9 * (BretParam I ε δ + 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (ξParam I ε δ : ℝ)) := by
  unfold restart refRestart
  refine ACouple.mono (ACouple.loop (R := fun _ a b => a = b ∧ RestInv I ε δ j a)
    (ζ := fun _ => 9 * ENNReal.ofReal (ξParam I ε δ : ℝ)) _
    (fun i _ x y hxy => ?_) ⟨rfl, hS0, fun h => ?_⟩) (fun _ _ h => h) (le_of_eq ?_)
  · obtain ⟨rfl, hinv⟩ := hxy
    exact restartStep_couple hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas j hj ws x hinv
  · simp only [decide_eq_false_iff_not] at h
    show 1 ≤ j
    omega
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; ring

/-- INTERNAL: matched observation tallies: same state (in `X`), same type counts,
and `Σ G_j` within a factor `exp(±4ξ)` of the reference sum, which is nonnegative.
TEXLINE: sections/algorithm.tex:514-524 -/
def ObsRel (I : Instance) (ε δ : ℚ) (o : Obs) (r : RefObs) : Prop :=
  o.S = r.S ∧ o.n0 = r.n0 ∧ o.nT = r.nT ∧ kind I ε δ o.S ≠ .outside ∧ 0 ≤ r.sumG ∧
    Real.exp (-(4 * (ξParam I ε δ : ℝ))) * r.sumG ≤ (o.sumG : ℝ) ∧
    (o.sumG : ℝ) ≤ Real.exp (4 * (ξParam I ε δ : ℝ)) * r.sumG

/-- INTERNAL: one observed term `ĥ_{j+1}/ĥ_j` is within `exp(±4ξ)` of `h_{j+1}/h_j`.
TEXLINE: sections/algorithm.tex:519-524 -/
theorem gterm_close {ξ : ℚ} (hξ : 0 ≤ (ξ : ℝ)) (hξ1 : (ξ : ℝ) ≤ 1 / 4) {hN hC : ℚ} {rN rC : ℝ}
    (hrN : 0 ≤ rN) (hrC : 0 ≤ rC) (h1 : OracleOK ξ rN hN) (h2 : OracleOK ξ rC hC) :
    0 ≤ rN / rC ∧ Real.exp (-(4 * (ξ : ℝ))) * (rN / rC) ≤ ((hN / hC : ℚ) : ℝ) ∧
      ((hN / hC : ℚ) : ℝ) ≤ Real.exp (4 * (ξ : ℝ)) * (rN / rC) := by
  obtain ⟨t1, a1, b1, e1⟩ := h1
  obtain ⟨t2, a2, b2, e2⟩ := h2
  obtain ⟨-, -, -, hlo, hhi⟩ := ratio_bounds hξ hξ1 a1 b1 a2 b2
  have hq : 0 ≤ rN / rC := div_nonneg hrN hrC
  have he : ((hN / hC : ℚ) : ℝ) = t1 / t2 * (rN / rC) := by
    push_cast; rw [e1, e2, mul_div_mul_comm]
  rw [he]
  exact ⟨hq, mul_le_mul_of_nonneg_right hlo hq, mul_le_mul_of_nonneg_right hhi hq⟩

/-- INTERNAL: one implemented observation couples to the exact one at cost `2ξ`
(two evaluations at a transversal).
TEXLINE: sections/algorithm.tex:514-524 -/
theorem observeState_couple (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (j : ℕ) (hj : j < HParam I ε δ) (o : Obs) (r : RefObs)
    (h : ObsRel I ε δ o r) :
    ACouple (observeState I ε δ j o) (PMF.pure (refObserveState I ε δ j r)) (ObsRel I ε δ)
      (2 * ENNReal.ofReal (ξParam I ε δ : ℝ)) := by
  obtain ⟨hξ, hξ1⟩ := xi_bounds I ε δ hε hε1
  have hξr : (0 : ℝ) ≤ ξParam I ε δ := by exact_mod_cast hξ.le
  have hξr1 : (ξParam I ε δ : ℝ) ≤ 1 / 4 := by
    rw [show (1 / 4 : ℝ) = ((1 / 4 : ℚ) : ℝ) by norm_num]; exact_mod_cast hξ1.le
  obtain ⟨S, n0, nT, sG⟩ := o
  obtain ⟨S', n0', nT', sG'⟩ := r
  obtain ⟨hS, hn0, hnT, hk, hpos, hlo, hhi⟩ := h
  dsimp only at hS hn0 hnT hk hpos hlo hhi
  subst hS hn0 hnT
  unfold observeState refObserveState
  dsimp only
  cases hkS : kind I ε δ S with
  | transversal =>
    refine ACouple.mono (ε := ENNReal.ofReal (ξParam I ε δ : ℝ) +
      (ENNReal.ofReal (ξParam I ε δ : ℝ) + 0)) ?_ (fun _ _ h => h) (by rw [add_zero, two_mul])
    refine ACouple.bind_left (oracle_bad_le hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas S hk (j + 1)
      (by omega)) fun hN hN' => ?_
    refine ACouple.bind_left (oracle_bad_le hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas S hk j
      (by omega)) fun hC hC' => ?_
    obtain ⟨g0, glo, ghi⟩ := gterm_close hξr hξr1 (hWeight_nonneg _ _ _ _ _ _)
      (hWeight_nonneg _ _ _ _ _ _) hN' hC'
    refine ACouple.pure ⟨rfl, rfl, rfl, hk, add_nonneg hpos g0, ?_, ?_⟩
    · push_cast
      rw [mul_add]
      push_cast at glo
      linarith
    · push_cast
      rw [mul_add]
      push_cast at ghi
      linarith
  | defect i l =>
    exact ACouple.mono (ACouple.pure ⟨rfl, rfl, rfl, hk, hpos, hlo, hhi⟩) (fun _ _ h => h) zero_le
  | outside => exact absurd hkS hk

/-- INTERNAL: the implemented observation run couples to the exact one: `N_av - 1`
coupled transitions (`9ξ` each) and `N_av` coupled observations (`2ξ` each).
TEXLINE: sections/algorithm.tex:514-524 -/
theorem observe_couple (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (j : ℕ) (hj : j < HParam I ε δ) (w : ℕ → ℕ → ℚ) (S0 : Finset ℕ)
    (hS0 : kind I ε δ S0 ≠ .outside) :
    ACouple (observe I ε δ j w S0) (refObserve I ε δ j w S0) (ObsRel I ε δ)
      (((11 * NavParam I ε δ + 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (ξParam I ε δ : ℝ)) := by
  set x := ENNReal.ofReal (ξParam I ε δ : ℝ) with hx
  have hinit : ObsRel I ε δ ⟨S0, 0, fun _ _ => 0, 0⟩ ⟨S0, 0, fun _ _ => 0, 0⟩ :=
    ⟨rfl, rfl, rfl, hS0, le_rfl, by simp, by simp⟩
  have hR : refObserve I ε δ j w S0 = (PMF.pure (refObserveState I ε δ j
      ⟨S0, 0, fun _ _ => 0, 0⟩)).bind fun r => loop (fun _ o =>
        (refStep I ε δ j w o.S).map fun S' => refObserveState I ε δ j { o with S := S' })
        (NavParam I ε δ - 1) r := by rw [PMF.pure_bind]; rfl
  rw [hR]
  unfold observe
  refine ACouple.mono ((observeState_couple hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas j hj _ _
    hinit).bind fun o r hor => ACouple.loop (R := fun _ => ObsRel I ε δ)
      (ζ := fun _ => 9 * x + 2 * x) _ (fun i _ o r hor => ?_) hor) (fun _ _ h => h) ?_
  · obtain ⟨hS, hn0, hnT, hk, hpos, hlo, hhi⟩ := hor
    rw [← PMF.bind_pure_comp, ← hS]
    refine (step_couple hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas j hj.le w o.S hk).bind
      fun S' S'' hS' => ?_
    obtain ⟨rfl, hk'⟩ := hS'
    exact observeState_couple hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas j hj _ _
      ⟨rfl, hn0, hnT, hk', hpos, hlo, hhi⟩
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : ((NavParam I ε δ - 1 : ℕ) : ℝ≥0∞) ≤ (NavParam I ε δ : ℝ≥0∞) := by
      exact_mod_cast Nat.sub_le _ _
    calc 2 * x + ((NavParam I ε δ - 1 : ℕ) : ℝ≥0∞) * (9 * x + 2 * x)
        ≤ 2 * x + (NavParam I ε δ : ℝ≥0∞) * (9 * x + 2 * x) := by gcongr
      _ = _ := by push_cast; ring

/-- INTERNAL: the implemented `μ₀` draw couples to the exact one at cost `2ξ`
per small cell (two dyadic draws each); the common value is in the support of the
exact sampler.
TEXLINE: sections/algorithm.tex:483-485 -/
theorem mu0_couple (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (hε1 : ε < 1) :
    ACouple (mu0 I ε δ) (refMu0 I ε δ) (fun a b => a = b ∧ b ∈ (refMu0 I ε δ).support)
      (((2 * nSmall I ε δ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (ξParam I ε δ : ℝ)) := by
  have hξ := (xi_bounds I ε δ hε hε1).1
  have hd : ∀ M : ℕ, PClose (dyadicDraw M (ξParam I ε δ)) (uniformBelow M)
      (ENNReal.ofReal (ξParam I ε δ : ℝ)) := fun M => by
    rw [uniformBelow_eq_idealDraw]; exact (dyadicDraw_close M _ hξ).symm
  have hc : PClose (mu0 I ε δ) (refMu0 I ε δ) (∑ _i ∈ Finset.range (nSmall I ε δ),
      (ENNReal.ofReal (ξParam I ε δ : ℝ) + (ENNReal.ofReal (ξParam I ε δ : ℝ) + 0))) := by
    unfold mu0 refMu0
    exact PClose.loop (fun s S => (hd _).bind fun k _ => (hd _).bind fun rank _ =>
      PClose.refl _ 0) _ _
  refine ACouple.mono (ACouple.of_pclose hc).support_right (fun _ _ h => h) (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast; ring

/-- INTERNAL: matched run states after `k` phases: the same stored multipliers and
abort flag, and `∏ R̂` within a factor `exp(±4kξ)` of the reference product, which is
nonnegative.
TEXLINE: sections/algorithm.tex:466-479 -/
def RunRel (I : Instance) (ε δ : ℚ) (k : ℕ) (o : RunState) (r : RefRunState) : Prop :=
  o.ws = r.ws ∧ o.aborted = r.aborted ∧ 0 ≤ r.prod ∧
    Real.exp (-(4 * (k : ℝ) * (ξParam I ε δ : ℝ))) * r.prod ≤ (o.prod : ℝ) ∧
    (o.prod : ℝ) ≤ Real.exp (4 * (k : ℝ) * (ξParam I ε δ : ℝ)) * r.prod

/-- INTERNAL: products of sandwiched nonnegative factors are sandwiched. -/
theorem prod_sandwich {P P' R R' a b : ℝ} (hP' : 0 ≤ P') (h1 : Real.exp (-a) * P' ≤ P)
    (h2 : P ≤ Real.exp a * P') (hR : 0 ≤ R) (h3 : Real.exp (-b) * R ≤ R')
    (h4 : R' ≤ Real.exp b * R) :
    0 ≤ P' * R ∧ Real.exp (-(a + b)) * (P' * R) ≤ P * R' ∧
      P * R' ≤ Real.exp (a + b) * (P' * R) := by
  have hP : 0 ≤ P := le_trans (by positivity) h1
  have hR' : 0 ≤ R' := le_trans (by positivity) h3
  refine ⟨mul_nonneg hP' hR, ?_, ?_⟩
  · calc Real.exp (-(a + b)) * (P' * R) = (Real.exp (-a) * P') * (Real.exp (-b) * R) := by
          rw [neg_add, Real.exp_add]; ring
      _ ≤ P * R' := mul_le_mul h1 h3 (by positivity) hP
  · calc P * R' ≤ (Real.exp a * P') * (Real.exp b * R) := mul_le_mul h2 h4 hR' (by positivity)
      _ = _ := by rw [Real.exp_add]; ring

/-- INTERNAL: matched states that did not run phase `k` stay matched at `k + 1`. -/
theorem runRel_succ_of_eq (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (hε1 : ε < 1) {k : ℕ}
    {o o' : RunState} {r r' : RefRunState} (h : RunRel I ε δ k o r) (hws : o'.ws = r'.ws)
    (hab : o'.aborted = r'.aborted) (ho : o'.prod = o.prod) (hr : r'.prod = r.prod) :
    RunRel I ε δ (k + 1) o' r' := by
  obtain ⟨-, -, h0, h1, h2⟩ := h
  have hξ : (0 : ℝ) ≤ ξParam I ε δ := by exact_mod_cast (xi_bounds I ε δ hε hε1).1.le
  unfold RunRel
  rw [ho, hr]
  refine ⟨hws, hab, h0, le_trans ?_ h1, h2.trans ?_⟩
  · gcongr; nlinarith
  · gcongr; nlinarith

/-- INTERNAL: the ratio estimates `R̂_j = (Σ G / N)/(n_0 / N)` of matched tallies are
within `exp(±4ξ)` of each other.
TEXLINE: sections/algorithm.tex:514-524 -/
theorem ratio_close (I : Instance) (ε δ : ℚ) (o : Obs) (r : RefObs) (h : ObsRel I ε δ o r) :
    0 ≤ (r.sumG / (NavParam I ε δ : ℝ)) / ((r.n0 : ℝ) / (NavParam I ε δ : ℝ)) ∧
    Real.exp (-(4 * (ξParam I ε δ : ℝ))) *
        ((r.sumG / (NavParam I ε δ : ℝ)) / ((r.n0 : ℝ) / (NavParam I ε δ : ℝ))) ≤
      (((o.sumG / (NavParam I ε δ : ℚ)) / ((o.n0 : ℚ) / (NavParam I ε δ : ℚ)) : ℚ) : ℝ) ∧
    (((o.sumG / (NavParam I ε δ : ℚ)) / ((o.n0 : ℚ) / (NavParam I ε δ : ℚ)) : ℚ) : ℝ) ≤
      Real.exp (4 * (ξParam I ε δ : ℝ)) *
        ((r.sumG / (NavParam I ε δ : ℝ)) / ((r.n0 : ℝ) / (NavParam I ε δ : ℝ))) := by
  obtain ⟨-, hn0, -, -, hpos, hlo, hhi⟩ := h
  have hN : (0 : ℝ) ≤ NavParam I ε δ := by positivity
  have hD : (0 : ℝ) ≤ (r.n0 : ℝ) / NavParam I ε δ := by positivity
  push_cast
  rw [hn0]
  refine ⟨by positivity, ?_, ?_⟩
  · rw [← mul_div_assoc, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hlo hN) hD
  · rw [← mul_div_assoc, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hhi hN) hD

/-- INTERNAL: one implemented phase couples to the reference phase from matched
states, at cost `(2 n_small + 9 (B_ret + 1) + 11 N_av + 2) ξ`; matched states stay
matched, with the product error growing by `4ξ`.
TEXLINE: sections/algorithm.tex:472-524 -/
theorem phase_couple (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (j : ℕ) (hj : j < HParam I ε δ) (o : RunState) (r : RefRunState)
    (h : RunRel I ε δ j o r) :
    ACouple (phase I ε δ j o) (refPhase I ε δ j r) (RunRel I ε δ (j + 1))
      (((2 * nSmall I ε δ + (9 * (BretParam I ε δ + 1) + (11 * NavParam I ε δ + 2)) : ℕ) :
        ℝ≥0∞) * ENNReal.ofReal (ξParam I ε δ : ℝ)) := by
  set x := ENNReal.ofReal (ξParam I ε δ : ℝ) with hx
  have hcost : ((2 * nSmall I ε δ + (9 * (BretParam I ε δ + 1) + (11 * NavParam I ε δ + 2)) :
      ℕ) : ℝ≥0∞) * x = ((2 * nSmall I ε δ : ℕ) : ℝ≥0∞) * x +
        (((9 * (BretParam I ε δ + 1) : ℕ) : ℝ≥0∞) * x +
          (((11 * NavParam I ε δ + 2 : ℕ) : ℝ≥0∞) * x + 0)) := by
    push_cast; ring
  have hrel := h
  obtain ⟨ws, prod, ab⟩ := o
  obtain ⟨ws', prod', ab'⟩ := r
  obtain ⟨hws, hab, h0, hlo, hhi⟩ := h
  dsimp only at hws hab h0 hlo hhi
  subst hws hab
  unfold phase refPhase
  cases ab
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hcost]
    refine (mu0_couple I ε δ hε hε1).bind fun S0 S0' hS0 => ?_
    obtain ⟨rfl, hsupp⟩ := hS0
    have hk0 : kind I ε δ S0 ≠ .outside := by rw [refMu0_kind I ε δ S0 hsupp]; simp
    refine (restart_couple hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas j hj.le ws S0 hk0).bind
      fun rs rs' hrs => ?_
    obtain ⟨rfl, hinv⟩ := hrs
    cases hra : rs.aborted
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine (observe_couple hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas j hj (ws j) rs.S
        hinv.1).bind fun ob rob hob => ?_
      have hcnt : ob.n0 = rob.n0 ∧ ob.nT = rob.nT := ⟨hob.2.1, hob.2.2.1⟩
      by_cases hpos : allPositive (pSmall I ε δ) ob
      · have hpos' : 0 < rob.n0 ∧ ∀ i < pSmall I ε δ, ∀ l < pSmall I ε δ, i ≠ l →
            0 < rob.nT i l := by rw [← hcnt.1, ← hcnt.2]; exact hpos
        rw [if_pos hpos, if_pos hpos']
        obtain ⟨R0, Rlo, Rhi⟩ := ratio_close I ε δ ob rob hob
        obtain ⟨P0, Plo, Phi⟩ := prod_sandwich h0 hlo hhi R0 Rlo Rhi
        have hupd : updateW (pSmall I ε δ) (ws j) ob = refUpdateW (pSmall I ε δ) (ws j) rob := by
          funext i l; simp [updateW, refUpdateW, hcnt.1, hcnt.2]
        have hexp : 4 * ((j + 1 : ℕ) : ℝ) * (ξParam I ε δ : ℝ) =
            4 * (j : ℝ) * (ξParam I ε δ : ℝ) + 4 * (ξParam I ε δ : ℝ) := by push_cast; ring
        split_ifs
        · refine ACouple.pure ⟨by rw [hupd], rfl, P0, ?_, ?_⟩
          · dsimp only; rw [hexp, Rat.cast_mul]; exact Plo
          · dsimp only; rw [hexp, Rat.cast_mul]; exact Phi
        · refine ACouple.pure ⟨rfl, rfl, P0, ?_, ?_⟩
          · dsimp only; rw [hexp, Rat.cast_mul]; exact Plo
          · dsimp only; rw [hexp, Rat.cast_mul]; exact Phi
      · have hpos' : ¬ (0 < rob.n0 ∧ ∀ i < pSmall I ε δ, ∀ l < pSmall I ε δ, i ≠ l →
            0 < rob.nT i l) := by rw [← hcnt.1, ← hcnt.2]; exact hpos
        rw [if_neg hpos, if_neg hpos']
        exact ACouple.pure (runRel_succ_of_eq I ε δ hε hε1 hrel rfl rfl rfl rfl)
    · simp only [↓reduceIte]
      exact ACouple.mono (ACouple.pure (runRel_succ_of_eq I ε δ hε hε1 hrel rfl rfl rfl rfl))
        (fun _ _ h => h) zero_le
  · simp only [↓reduceIte]
    exact ACouple.mono (ACouple.pure (runRel_succ_of_eq I ε δ hε hε1 hrel rfl rfl rfl rfl))
      (fun _ _ h => h) zero_le

/-- **Coupling** (`lem:bounded-implementation`, coupling clause, read through the
output): a joint law of `(Ẑ, Z_ref)` with the right marginals, under which
`Z_ref > 0` implies `Ẑ > 0` and `|log(Ẑ / Z_ref)| ≤ 4 H ξ`, except with
probability at most `10 J_* ξ`.
PAPER: sections/algorithm.tex:466-479 -/
theorem implementation_coupling (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) :
    ∃ ν : PMF (ℚ × ℝ), ν.map Prod.fst = annealRun I ε δ ∧ ν.map Prod.snd = refRun I ε δ ∧
      ν.toOuterMeasure {q | ¬ (0 < q.2 → 0 < (q.1 : ℝ) ∧
          |Real.log ((q.1 : ℝ) / q.2)| ≤ 4 * (HParam I ε δ : ℝ) * (ξParam I ε δ : ℝ))} ≤
        ENNReal.ofReal (10 * (JstarParam I ε δ : ℝ) * (ξParam I ε δ : ℝ)) := by
  set H := HParam I ε δ with hH
  set ξr : ℝ := (ξParam I ε δ : ℝ) with hξr
  set c := 2 * nSmall I ε δ + (9 * (BretParam I ε δ + 1) + (11 * NavParam I ε δ + 2)) with hc
  have hξ0 : 0 ≤ ξr := by
    show (0 : ℝ) ≤ (ξParam I ε δ : ℝ); exact_mod_cast (xi_bounds I ε δ hε hε1).1.le
  have hC0 : (0 : ℝ) < (C0 I ε δ : ℝ) := by rw [← Cpart_zero]; exact Cpart_pos I ε δ 0
  have hloop := ACouple.loop (f := phase I ε δ) (g := refPhase I ε δ) (R := RunRel I ε δ)
    (ζ := fun _ => ((c : ℕ) : ℝ≥0∞) * ENNReal.ofReal ξr) H
    (fun i hi o r h => phase_couple hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas i hi o r h)
    (x := ⟨fun a => if a = 0 then w0 I ε δ else fun _ _ => 0, 1, false⟩)
    (y := ⟨fun a => if a = 0 then w0 I ε δ else fun _ _ => 0, 1, false⟩)
    ⟨rfl, rfl, zero_le_one, by simp, by simp⟩
  have hmap := hloop.map (fun st : RunState => if st.aborted then (0 : ℚ) else C0 I ε δ * st.prod)
    (fun st : RefRunState => if st.aborted then (0 : ℝ) else (C0 I ε δ : ℝ) * st.prod)
    (S := fun (q1 : ℚ) (q2 : ℝ) => 0 < q2 → 0 < (q1 : ℝ) ∧
      |Real.log ((q1 : ℝ) / q2)| ≤ 4 * (H : ℝ) * ξr) (fun a b hab => ?_)
  · obtain ⟨π, h1, h2, h3⟩ := hmap
    refine ⟨π, by unfold annealRun; exact h1, by unfold refRun; exact h2, h3.trans ?_⟩
    have hsum : ∑ _i ∈ Finset.range H, ((c : ℕ) : ℝ≥0∞) * ENNReal.ofReal ξr =
        ENNReal.ofReal (((H * c : ℕ) : ℝ) * ξr) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ← mul_assoc]
      push_cast; rfl
    rw [hsum]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hξ0)
    have hns := nSmall_le_pSmall I ε δ
    have hcX : c ≤ 11 * (BretParam I ε δ + NavParam I ε δ + pSmall I ε δ + dParam I + 1) := by
      omega
    have : H * c ≤ 10 * JstarParam I ε δ := by
      calc H * c ≤ (H + 1) * (11 * (BretParam I ε δ + NavParam I ε δ + pSmall I ε δ +
            dParam I + 1)) := Nat.mul_le_mul (Nat.le_succ H) hcX
        _ ≤ 10 * JstarParam I ε δ := by
            have hJ : JstarParam I ε δ = 100 * (H + 1) * (BretParam I ε δ + NavParam I ε δ +
                pSmall I ε δ + dParam I + 1) := rfl
            rw [hJ]
            generalize BretParam I ε δ + NavParam I ε δ + pSmall I ε δ + dParam I + 1 = X
            calc (H + 1) * (11 * X) = 11 * ((H + 1) * X) := by ring
              _ ≤ 1000 * ((H + 1) * X) := by omega
              _ = 10 * (100 * (H + 1) * X) := by ring
    exact_mod_cast this
  · obtain ⟨-, hab', h0, hlo, hhi⟩ := hab
    intro hpos
    cases hb : b.aborted
    · have ha : a.aborted = false := by rw [hab', hb]
      simp only [hb, ha, Bool.false_eq_true, ↓reduceIte] at hpos ⊢
      have hbp : 0 < b.prod := pos_of_mul_pos_right hpos hC0.le
      have hap : (0 : ℝ) < a.prod := lt_of_lt_of_le (by positivity) hlo
      have hq : ((C0 I ε δ * a.prod : ℚ) : ℝ) / ((C0 I ε δ : ℝ) * b.prod) =
          (a.prod : ℝ) / b.prod := by
        push_cast; rw [mul_div_mul_left _ _ hC0.ne']
      refine ⟨by push_cast; positivity, ?_⟩
      rw [hq, abs_le]
      have hdiv : 0 < (a.prod : ℝ) / b.prod := div_pos hap hbp
      constructor
      · rw [Real.le_log_iff_exp_le hdiv, le_div_iff₀ hbp]; exact hlo
      · rw [Real.log_le_iff_le_exp hdiv, div_le_iff₀ hbp]; exact hhi
    · simp [hb] at hpos

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · `implementation_coupling`, `profile_valid_of_kind`, `refMu0_kind` closed; rests only on `weight_oracle_accurate` (open, `WeightOracle.lean`)
-/
