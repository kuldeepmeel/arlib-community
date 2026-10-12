import Esa22Copy.Meta.ModelClosure
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Esa22Copy.Model.Prior
import Esa22Copy.Model.Run
import Esa22Copy.Interface.Encoding
import Esa22Copy.Interface.Pseudocode
import Esa22Copy.Interface.ProgramModel

/-!
# Expected time of the F0-Estimator: `O(m)`

Proves `Esa22Copy.Analysis.time_proof`: the expected number of unit-cost steps of
`run ε δ s` is at most `9 · (m + 1)`, with `C = 9` independent of `n, s, ε, δ`.

The paper (esa22-final.tex:509-511) argues: every iteration costs `O(1)` except
those that run the throw, which cost `O(thresh)`; with `T` throws discarding
`R_j` elements, Wald's identity gives `𝔼[Σ R_j] = 𝔼[T]·thresh/2`, and `Σ R_j ≤ m`
pathwise, so `𝔼[T] ≤ 2m/thresh`.

The Lean proof replaces Wald's identity by an equivalent amortized (potential)
argument with `Φ = 3·|𝒳|`:

* an iteration that does not throw costs `≤ 4` and raises `Φ` by `≤ 3`;
* an iteration that throws costs `≤ 6 + thresh + R` (one coin per element of
  `𝒳`, one erase per discarded element), and the new potential is `3·(thresh − R)`;
  since the coins are a fresh uniform subset, `𝔼[thresh − R] = thresh/2`
  (`expect_kept`), and `Φ_before ≥ 3·(thresh − 1)`.

So `𝔼[cost + Φ_after] ≤ 9 + Φ_before` per iteration (`cell_expect`); induction
over the independently drawn tape (`fold_expect`) and the `≤ 2` cost of the
output line give the bound (`time_bound`).  The theorem uses nothing from
`Prior`.
-/

section
open scoped ENNReal
open Arlib.Computation (Rate Charged Roster Block Coins Sampler CostVec randOpcode)

namespace Esa22Copy.Analysis.TimeAmortized
open Esa22Copy Esa22Copy.Program Esa22Copy.Model.Operations


/-- INTERNAL: expectation of a `PMF.bind` is the iterated expectation. -/
theorem expect_bind {α β : Type*} (μ : PMF α) (g : α → PMF β) (f : β → ℝ≥0∞) :
    ∑' y, (μ.bind g) y * f y = ∑' x, μ x * ∑' y, g x y * f y := by
  simp_rw [PMF.bind_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  congr 1; ext x
  rw [← ENNReal.tsum_mul_left]
  congr 1; ext y; ring

/-- INTERNAL: expectation under a point mass. -/
theorem expect_pure {α : Type*} (a : α) (f : α → ℝ≥0∞) :
    ∑' y, (PMF.pure a) y * f y = f a := by
  classical
  simp_rw [PMF.pure_apply, ite_mul, one_mul, zero_mul]
  exact tsum_ite_eq a f

/-- INTERNAL: expectation of a pushforward. -/
theorem expect_map {α β : Type*} (μ : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    ∑' y, (μ.map g) y * f y = ∑' x, μ x * f (g x) := by
  rw [← PMF.bind_pure_comp, expect_bind]
  simp only [Function.comp, expect_pure]

/-- INTERNAL: a pointwise bound bounds the expectation. -/
theorem expect_le_const {α : Type*} (μ : PMF α) (f : α → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ x, f x ≤ c) : ∑' x, μ x * f x ≤ c := by
  calc ∑' x, μ x * f x ≤ ∑' x, μ x * c := ENNReal.tsum_le_tsum fun x => by gcongr; exact h x
    _ = c := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- INTERNAL: a constant comes out of an expectation. -/
theorem expect_const_add {α : Type*} (μ : PMF α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    ∑' x, μ x * (c + f x) = c + ∑' x, μ x * f x := by
  simp_rw [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- INTERNAL: a uniform subset `S` of `Fin n` keeps half of `X` in expectation,
`𝔼[2·|X ∩ S|] = |X|` (pairing `S` with `Sᶜ`).  This is the paper's `𝔼[R_j] = thresh/2`.
TEXLINE: esa22-final.tex:511 -/
theorem expect_kept {n : ℕ} (X : Finset (Fin n)) :
    ∑' S, PMF.uniformOfFintype (Finset (Fin n)) S * (2 * ((X.filter (· ∈ S)).card : ℝ≥0∞))
      = X.card := by
  have hnat : ∑ S : Finset (Fin n), 2 * (X.filter (· ∈ S)).card
      = Fintype.card (Finset (Fin n)) * X.card := by
    have h1 : ∑ S : Finset (Fin n), (X.filter (· ∈ Sᶜ)).card
        = ∑ S : Finset (Fin n), (X.filter (· ∈ S)).card :=
      Equiv.sum_comp (compl_involutive.toPerm _) (fun S => (X.filter (· ∈ S)).card)
    have h2 : ∀ S : Finset (Fin n), (X.filter (· ∈ S)).card + (X.filter (· ∈ Sᶜ)).card
        = X.card := by
      intro S
      simpa [Finset.mem_compl] using Finset.card_filter_add_card_filter_not (s := X) (p := (· ∈ S))
    calc ∑ S : Finset (Fin n), 2 * (X.filter (· ∈ S)).card
        = ∑ S : Finset (Fin n), ((X.filter (· ∈ S)).card + (X.filter (· ∈ Sᶜ)).card) := by
          rw [Finset.sum_add_distrib, h1, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun S _ => by ring
      _ = Fintype.card (Finset (Fin n)) * X.card := by
          rw [Finset.sum_congr rfl (fun S _ => h2 S)]
          simp
  rw [tsum_fintype]
  simp_rw [PMF.uniformOfFintype_apply]
  rw [← Finset.mul_sum]
  have hcast : ∑ S : Finset (Fin n), 2 * ((X.filter (· ∈ S)).card : ℝ≥0∞)
      = ((Fintype.card (Finset (Fin n)) * X.card : ℕ) : ℝ≥0∞) := by
    rw [← hnat]; push_cast; rfl
  rw [hcast, Nat.cast_mul, ← mul_assoc, ENNReal.inv_mul_cancel, one_mul]
  · exact_mod_cast Fintype.card_ne_zero
  · exact ENNReal.natCast_ne_top _
variable {n w : ℕ}

/-- INTERNAL: lines afinal-drop/afinal-pick cost at most three operations. -/
theorem steps_arrival (a : Fin n) (b : Block w) (st : State (Fin n)) :
    Charged.steps rate (arrival a b st) ≤ 3 := by
  unfold arrival
  simp only [Charged.steps_bind]
  split <;> simp [Charged.steps]

/-- INTERNAL: `|𝒳|` grows by at most one at lines afinal-drop/afinal-pick.
TEXLINE: esa22-final.tex:511 -/
theorem card_arrival (a : Fin n) (b : Block w) (st : State (Fin n)) :
    (arrival a b st).val.card ≤ st.samples.card + 1 := by
  unfold arrival
  simp only [Charged.val_bind]
  rw [← Roster.card_toFinset, ← Roster.card_toFinset]
  split
  · rw [Roster.toFinset_insert, Roster.toFinset_erase]
    exact (Finset.card_insert_le _ _).trans (by have := Finset.card_erase_le (s := st.samples.toFinset) (a := a); omega)
  · simp only [Charged.val_pure, Roster.toFinset_erase]
    have := Finset.card_erase_le (s := st.samples.toFinset) (a := a); omega


/-- INTERNAL: the throw keeps exactly the elements whose coin is in `S`. -/
theorem thin_filter (S : Finset (Fin n)) (X : Roster (Fin n)) :
    X.toFinset.filter (fun x => (Coins.flip x (Coins.ofFinset S) : Charged Op Cell Bool).val)
      = X.toFinset.filter (· ∈ S) := by
  ext x
  simp only [Finset.mem_filter, Coins.val_flip, decide_eq_true_eq]
  rfl

/-- INTERNAL: the throw costs `|𝒳|` coin flips plus one erase per discarded element.
TEXLINE: esa22-final.tex:509 -/
theorem thin_steps (S : Finset (Fin n)) (X : Roster (Fin n)) :
    Charged.steps rate (thin (Coins.ofFinset S) X)
      = X.card + (X.card - (X.toFinset.filter (· ∈ S)).card) := by
  unfold thin
  rw [Charged.steps, Roster.cost_filterErase_card (randOpcode Op .flip) _ X (fun x => by simp),
    thin_filter]
  simp

/-- INTERNAL: size of `𝒳` after the throw. -/
theorem thin_card (S : Finset (Fin n)) (X : Roster (Fin n)) :
    (thin (Coins.ofFinset S) X : Charged Op Cell _).val.card = (X.toFinset.filter (· ∈ S)).card := by
  unfold thin
  rw [← Roster.card_toFinset, Roster.toFinset_filterErase, thin_filter]

/-- INTERNAL: the amortization potential `3·|𝒳|` (`0` after `⊥`).  It replaces the
paper's Wald's-identity step (esa22-final.tex:511) by a potential argument, as the
settled issue on Wald's identity asks. -/
noncomputable def pot : Option (State (Fin n)) → ℕ
  | none => 0
  | some st => 3 * st.samples.card

/-- INTERNAL: one iteration's cost plus the new potential, pointwise in the throw's
coins.  When the throw runs (`|𝒳| = thr`) it is `6 + 2·thr + 2·|kept|`, otherwise
`4 + 3·|𝒳|`.  TEXLINE: esa22-final.tex:509 -/
theorem step_some_le (thr : ℕ) (st : State (Fin n)) (a : Fin n) (b : Block w) (S : Finset (Fin n)) :
    Charged.steps rate (step thr (some st) (a, ⟨b, Coins.ofFinset S⟩))
        + pot (step thr (some st) (a, ⟨b, Coins.ofFinset S⟩)).val
      ≤ if (arrival a b st : Charged Op Cell _).val.card = thr then
          6 + 2 * thr + 2 * ((arrival a b st : Charged Op Cell _).val.toFinset.filter (· ∈ S)).card
        else 4 + 3 * (arrival a b st : Charged Op Cell _).val.card := by
  simp only [step, Charged.steps_bind, Charged.val_bind]
  have hA : Charged.steps rate (arrival a b st : Charged Op Cell _) ≤ 3 := steps_arrival a b st
  generalize (arrival a b st : Charged Op Cell _) = A at hA ⊢
  generalize hX : A.val = X
  have hK : (X.toFinset.filter (· ∈ S)).card ≤ X.card := by
    rw [← Roster.card_toFinset]; exact Finset.card_filter_le _ _
  have hS := thin_steps S X
  have hC := thin_card S X
  have hE : ∀ Y : Roster (Fin n), Charged.steps rate (Roster.cardEq thr Y : Charged Op Cell Bool) = 1 := by
    intro Y; simp [Charged.steps]
  have hH : Charged.steps rate (st.sampler.halve : Charged Op Cell _) = 1 := by
    simp [Charged.steps]
  simp only [Roster.val_cardEq, decide_eq_true_eq]
  by_cases hfull : X.card = thr
  · simp only [hfull, if_true, Charged.steps_bind, Charged.val_bind]
    generalize (thin (Coins.ofFinset S) X : Charged Op Cell _) = T at hS hC
    by_cases h2 : T.val.card = thr
    · simp only [Roster.val_cardEq, decide_eq_true_eq, h2, pot, hS, hE, hH, if_true,
        Charged.steps_pure, Charged.val_pure]
      omega
    · rw [hC] at h2
      simp only [Roster.val_cardEq, h2, pot, hS, hE, hH, if_false, Bool.false_eq_true,
        Charged.steps_pure, Charged.val_pure, hC, decide_false]
      omega
  · simp only [hfull, pot, hE, if_false, Charged.steps_pure, Charged.val_pure]
    omega

/-- INTERNAL: amortized cost of one iteration: `𝔼[cost + Φ_after] ≤ 9 + Φ_before`.
TEXLINE: esa22-final.tex:509-511 -/
theorem cell_expect (thr : ℕ) (acc : Option (State (Fin n))) (a : Fin n) :
    ∑' c, cellLaw n w c * ((Charged.steps rate (step thr acc (a, c))
        + pot (step thr acc (a, c)).val : ℕ) : ℝ≥0∞) ≤ 9 + (pot acc : ℝ≥0∞) := by
  cases acc with
  | none =>
      apply expect_le_const
      intro c
      simp [step, pot]
  | some st =>
  unfold cellLaw
  rw [expect_bind]
  apply expect_le_const
  intro f
  rw [expect_map]
  have hX := card_arrival a (Block.ofFun f) st
  generalize hA : (arrival a (Block.ofFun f) st : Charged Op Cell _).val = X at hX
  have hb := fun S => step_some_le thr st a (Block.ofFun f) S
  rw [hA] at hb
  by_cases hfull : X.card = thr
  · simp only [hfull, if_true] at hb
    calc ∑' S, PMF.uniformOfFintype (Finset (Fin n)) S *
          ((Charged.steps rate (step thr (some st) (a, ⟨Block.ofFun f, Coins.ofFinset S⟩))
            + pot (step thr (some st) (a, ⟨Block.ofFun f, Coins.ofFinset S⟩)).val : ℕ) : ℝ≥0∞)
        ≤ ∑' S, PMF.uniformOfFintype (Finset (Fin n)) S *
          (((6 + 2 * thr : ℕ) : ℝ≥0∞) + 2 * ((X.toFinset.filter (· ∈ S)).card : ℝ≥0∞)) := by
          refine ENNReal.tsum_le_tsum fun S => ?_
          gcongr
          exact_mod_cast hb S
      _ = ((6 + 2 * thr : ℕ) : ℝ≥0∞) + X.toFinset.card := by
          rw [expect_const_add, expect_kept]
      _ ≤ 9 + (pot (some st) : ℝ≥0∞) := by
          rw [Roster.card_toFinset]
          simp only [pot]
          exact_mod_cast (by omega : 6 + 2 * thr + X.card ≤ 9 + 3 * st.samples.card)
  · simp only [hfull, if_false] at hb
    apply expect_le_const
    intro S
    exact_mod_cast (hb S).trans (by simp only [pot]; omega)

/-- INTERNAL: amortized cost of the whole loop, by induction over the stream using
that the tape's cells are drawn independently (`tape` is a `bind`-recursion).
TEXLINE: esa22-final.tex:511 -/
theorem fold_expect (thr : ℕ) : ∀ (s : List (Fin n)) (acc : Option (State (Fin n))),
    ∑' t, tape n w s.length t * ((Charged.steps rate (Charged.foldl (step thr) (s.zip t) acc)
        + pot (Charged.foldl (step thr) (s.zip t) acc).val : ℕ) : ℝ≥0∞)
      ≤ 9 * (s.length : ℝ≥0∞) + pot acc := by
  intro s
  induction s with
  | nil =>
      intro acc
      simp only [List.length_nil, tape]
      rw [expect_pure]
      simp [Charged.steps]
  | cons a s ih =>
      intro acc
      simp only [List.length_cons, tape]
      rw [expect_bind]
      calc ∑' c, cellLaw n w c * ∑' y, ((tape n w s.length).map (fun t => c :: t)) y *
            ((Charged.steps rate (Charged.foldl (step thr) ((a :: s).zip y) acc)
              + pot (Charged.foldl (step thr) ((a :: s).zip y) acc).val : ℕ) : ℝ≥0∞)
          ≤ ∑' c, cellLaw n w c * (9 * (s.length : ℝ≥0∞) + ((Charged.steps rate (step thr acc (a, c))
              + pot (step thr acc (a, c)).val : ℕ) : ℝ≥0∞)) := by
            refine ENNReal.tsum_le_tsum fun c => ?_
            gcongr
            rw [expect_map]
            have hc : ∀ t : List (Program.Randomness (Fin n) w),
                ((Charged.steps rate (Charged.foldl (step thr) ((a :: s).zip (c :: t)) acc)
                  + pot (Charged.foldl (step thr) ((a :: s).zip (c :: t)) acc).val : ℕ) : ℝ≥0∞)
                = (Charged.steps rate (step thr acc (a, c)) : ℝ≥0∞)
                  + ((Charged.steps rate (Charged.foldl (step thr) (s.zip t) (step thr acc (a, c)).val)
                    + pot (Charged.foldl (step thr) (s.zip t) (step thr acc (a, c)).val).val : ℕ)
                      : ℝ≥0∞) := by
              intro t
              simp only [List.zip_cons_cons, Charged.steps, Charged.cost_foldl_cons,
                Charged.val_foldl_cons, CostVec.steps_add]
              push_cast; ring
            simp_rw [hc]
            rw [expect_const_add]
            calc _ ≤ (Charged.steps rate (step thr acc (a, c)) : ℝ≥0∞)
                  + (9 * (s.length : ℝ≥0∞) + pot (step thr acc (a, c)).val) := by
                  gcongr; exact ih _
              _ = _ := by push_cast; ring
        _ = 9 * (s.length : ℝ≥0∞) + ∑' c, cellLaw n w c * ((Charged.steps rate (step thr acc (a, c))
              + pot (step thr acc (a, c)).val : ℕ) : ℝ≥0∞) := expect_const_add _ _ _
        _ ≤ 9 * (s.length : ℝ≥0∞) + (9 + pot acc) := by gcongr; exact cell_expect thr acc a
        _ = 9 * ((s.length + 1 : ℕ) : ℝ≥0∞) + pot acc := by push_cast; ring

/-- INTERNAL: the explicit constant: expected steps `≤ 9·(m + 1)`.
TEXLINE: esa22-final.tex:509-511 -/
theorem time_bound {n : ℕ} (ε δ : ℝ) (s : List (Fin n)) :
    Esa22Copy.expectedSteps rate (Esa22Copy.run ε δ s) ≤ (9 : ℕ) * ((s.length : ℝ≥0∞) + 1) := by
  unfold Esa22Copy.expectedSteps Esa22Copy.run
  rw [expect_map]
  have hrep : ∀ acc : Option (State (Fin n)),
      Charged.steps rate (report acc : Charged Op Cell _) ≤ 2 := by
    intro acc; cases acc <;> simp [report, Charged.steps]
  calc ∑' t, tape n (s.length + 1) s.length t *
        (Charged.steps rate (estimate (thresh ε δ s.length) s t) : ℝ≥0∞)
      ≤ ∑' t, tape n (s.length + 1) s.length t * (2 +
        ((Charged.steps rate (Charged.foldl (step (thresh ε δ s.length)) (s.zip t) (some initial))
          + pot (Charged.foldl (step (thresh ε δ s.length)) (s.zip t) (some initial)).val : ℕ)
            : ℝ≥0∞)) := by
        refine ENNReal.tsum_le_tsum fun t => ?_
        gcongr
        have h := hrep (Charged.foldl (step (thresh ε δ s.length)) (s.zip t) (some initial)).val
        have he : Charged.steps rate (estimate (thresh ε δ s.length) s t)
            = Charged.steps rate (Charged.foldl (step (thresh ε δ s.length)) (s.zip t) (some initial))
              + Charged.steps rate (report (Charged.foldl (step (thresh ε δ s.length)) (s.zip t)
                  (some initial)).val : Charged Op Cell _) := by
          simp only [estimate, Charged.steps_bind]
        rw [he]
        exact_mod_cast (by omega)
    _ = 2 + _ := expect_const_add _ _ _
    _ ≤ 2 + (9 * (s.length : ℝ≥0∞) + pot (some (initial : State (Fin n)))) := by
        gcongr; exact fold_expect _ s _
    _ ≤ (9 : ℕ) * ((s.length : ℝ≥0∞) + 1) := by
        have : pot (some (initial : State (Fin n))) = 0 := by
          simp [pot, initial, ← Roster.card_toFinset]
        rw [this, Nat.cast_zero, add_zero, Nat.cast_ofNat]
        calc 2 + 9 * (s.length : ℝ≥0∞)
            = 9 * (s.length : ℝ≥0∞) + 2 := by ring
          _ ≤ 9 * (s.length : ℝ≥0∞) + 9 := by gcongr; norm_num
          _ = 9 * ((s.length : ℝ≥0∞) + 1) := by ring

end Esa22Copy.Analysis.TimeAmortized

/-- Proof-side owner for `Esa22Copy.esa22copy_time`; its statement is fixed by the proof charter.
PAPER: esa22-final.tex:502 (time claim of `thm:main`), proof esa22-final.tex:509-511.
Proved with `C = 9` by `TimeAmortized.time_bound`. -/
theorem Esa22Copy.Analysis.time_proof (hprior : Prior) : ∃ C : ℕ, ∀ (n : ℕ) (s : List (Fin n)) (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 → Esa22Copy.expectedSteps Esa22Copy.Model.Operations.rate (Esa22Copy.run ε δ s) ≤ (C : ENNReal) * ((s.length : ENNReal) + 1) := by
  exact ⟨9, fun _ s ε δ _ _ _ _ => Esa22Copy.Analysis.TimeAmortized.time_bound ε δ s⟩

end

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `time_proof` with `C = 9` via the potential `3·|𝒳|` in place of Wald's identity
-/
