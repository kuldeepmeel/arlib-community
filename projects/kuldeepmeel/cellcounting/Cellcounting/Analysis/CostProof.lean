import Cellcounting.Model.Run
import Cellcounting.Model.Prior
import Arlib.Computation.ChargedPMF
import Mathlib.Data.Nat.Log
import Cellcounting.Meta.ModelClosure
import Cellcounting.Interface.Encoding
import Cellcounting.Interface.Pseudocode
import Cellcounting.Interface.ProgramModel
import Cellcounting.Analysis.CostScale
import Cellcounting.Analysis.PrepCost
import Cellcounting.Analysis.PrepPenaltyBound
import Cellcounting.Analysis.OracleCost
import Cellcounting.Analysis.AnnealCost

/-!
# The running time: one polynomial bounds every execution

`Cellcounting.Analysis.fpras_time_owner` (`sections/introduction.tex:30-33`,
`sections/algorithm.tex:692-706`): there are `C, k` such that every execution of the
algorithm on `(I, ε, δ)` performs at most `C (L + ⌈ε⁻¹⌉ + ⌈log₂ ⌈δ⁻¹⌉⌉ + 1)^k` steps,
where a step is one bit operation or one fair-bit read (`Model/Operations.lean`).

The proof is deterministic.  `worstSteps` is a supremum over the support of `run`, which
is the image of the tape law under `Program.fpras`, so it suffices to bound
`Charged.steps rate (Program.fpras I ε δ tape)` for **every** coin family `tape`
(`fpras_steps_le`).  That bound follows the program, with the base
`costScale I ε δ = L + ⌈ε⁻¹⌉ + ⌈log₂ ⌈δ⁻¹⌉⌉ + 1`:

* S0–S4 (input, feasibility, tightening, parameters, forest, `p`): `prep_cost`
  (`Analysis/PrepCost.lean`), which also bounds every size of the resulting context.
* On an infeasible input: the literal `0` and its output.
* On a feasible input: the arithmetic on `δ` (`s = ⌈log₂ ⌈δ⁻¹⌉⌉ ≤ costScale`,
  `R = 10 s + 1`), then `R` runs and their median.  A `p = 0` run is one oracle call
  (`oracle_cost`, `Analysis/OracleCost.lean`); a `p ≥ 1` run is an annealing run after
  one setup (`anneal_cost`, `Analysis/AnnealCost.lean`).  Both need the penalty to be
  polynomially bounded on the extended free box, which is `lem:forest`'s `0 ≤ D ≤ H`
  for the program's own context (`prep_penalty_bound`,
  `Analysis/PrepPenaltyBound.lean`).  The median is an insertion sort of `R` rationals of
  polynomial length (`orderStat_cost`).

Every bound is a power of `costScale`; the exponents of the four pieces combine into one.
The shared vocabulary (primitive prices, loops with invariants, size predicates) is in
`Analysis/CostScale.lean`.

The theorem takes `C = 1`.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Program
open Cellcounting.Model.Operations
open Cellcounting.Interface

/-- INTERNAL: the value of `Program.clog2`: `Nat.size (x - 1)`. -/
theorem clog2_get (x : SNat) : (clog2 x).val.get = Nat.size (x.get - 1) := by
  unfold clog2; simp only [costVb, SNat.get_size, SNat.get_sub, SNat.get_lit]

/-- INTERNAL: the price of `Program.clog2`. -/
theorem clog2_steps (x : SNat) :
    Charged.steps rate (clog2 x) = bitLen 1 + (bitLen x.get + bitLen 1) + bitLen (x.get - 1) := by
  unfold clog2
  simp only [Charged.steps_bind, steps_SNat_lit, steps_SNat_sub, steps_SNat_size,
    SNat.get_sub, SNat.get_lit]
  omega

/-- INTERNAL: the loop of S12 that runs `R` single runs on consecutive stretches of the tape and pushes their outputs: the list has `R` entries, each of length at most `M`, and the loop costs at most `R (M + R + 1)`. -/
theorem runLoop_cost (g : ℕ → Prog (SRat × ℕ)) (M n : ℕ)
    (hg : ∀ cur, Charged.steps rate (g cur) ≤ M ∧ ratLen (g cur).val.1.get ≤ M) :
    (Charged.repeatFor (fun _ (st : List SRat × ℕ) => do
        let __x ← g st.2
        let outs ← Model.Operations.push st.1 __x.1
        pure (outs, __x.2)) n ([], 0)).val.1.length = n ∧
    (∀ z ∈ (Charged.repeatFor (fun _ (st : List SRat × ℕ) => do
        let __x ← g st.2
        let outs ← Model.Operations.push st.1 __x.1
        pure (outs, __x.2)) n ([], 0)).val.1, ratLen z.get ≤ M) ∧
    Charged.steps rate (Charged.repeatFor (fun _ (st : List SRat × ℕ) => do
        let __x ← g st.2
        let outs ← Model.Operations.push st.1 __x.1
        pure (outs, __x.2)) n ([], 0)) ≤ n * (M + n + 1) := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := repeatFor_inv (fun _ (st : List SRat × ℕ) => (do
        let __x ← g st.2
        let outs ← Model.Operations.push st.1 __x.1
        pure (outs, __x.2) : Prog (List SRat × ℕ)))
    (fun r (st : List SRat × ℕ) => st.1.length = r ∧ ∀ z ∈ st.1, ratLen z.get ≤ M)
    (M + n + 1) n ([], 0) (by simp)
    (by
      rintro r ⟨l, cur⟩ hr ⟨hlen, hall⟩
      obtain ⟨g1, g2⟩ := hg cur
      simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_push, val_push]
        at hlen hall ⊢
      refine ⟨⟨by simp [hlen], ?_⟩, by omega⟩
      intro z hz; simp at hz; aesop)
  exact ⟨h1, h2, h3⟩

/-- INTERNAL: one insertion of the median selection: the list grows by one, keeps entries of length at most `M`, and the pass costs at most `(|l| + 1)(2|l| + 5 + (M + 1)²)`. -/
theorem insertAsc_cost (M : ℕ) (l : List SRat) (x : SRat) (hx : ratLen x.get ≤ M)
    (hl : ∀ y ∈ l, ratLen y.get ≤ M) :
    (insertAsc l x).val.length = l.length + 1 ∧ (∀ z ∈ (insertAsc l x).val, ratLen z.get ≤ M) ∧
    Charged.steps rate (insertAsc l x) ≤ (l.length + 1) * (2 * l.length + 5 + (M + 1) * (M + 1)) := by
  unfold insertAsc
  obtain ⟨⟨h1, h2⟩, h3⟩ := foldl_inv
    (fun (st : List SRat × Bool) (y : SRat) => (if st.2 then do
        let o ← Model.Operations.push st.1 y
        pure (o, true)
      else do
        let before ← SRat.lt x y
        if before then do
          let o ← Model.Operations.push st.1 x
          let o' ← Model.Operations.push o y
          pure (o', true)
        else do
          let o ← Model.Operations.push st.1 y
          pure (o, false) : Prog (List SRat × Bool)))
    (fun i (st : List SRat × Bool) => st.1.length = i + (if st.2 then 1 else 0) ∧
      ∀ z ∈ st.1, ratLen z.get ≤ M)
    (2 * l.length + 4 + (M + 1) * (M + 1)) l 0 ([], false) (by simp)
    (by
      rintro i ⟨o, fl⟩ a - hi ha ⟨hlen, hall⟩
      have haM := hl a ha
      cases fl with
      | true =>
        simp only [ite_true, costVb, costVp, Charged.steps_bind, Charged.steps_pure,
          steps_push, val_push] at hlen ⊢
        refine ⟨⟨by simp [hlen], ?_⟩, by omega⟩
        intro z hz; simp at hz; aesop
      | false =>
        simp only [Bool.false_eq_true, ite_false, add_zero, costVb, Charged.steps_bind,
          steps_SRat_lt] at hlen ⊢
        have hc : (ratLen x.get + 1) * (ratLen a.get + 1) ≤ (M + 1) * (M + 1) :=
          Nat.mul_le_mul (by omega) (by omega)
        split
        · simp only [costVb, costVp, Charged.steps_bind, Charged.steps_pure, steps_push,
            val_push, ite_true, List.length_append, List.length_cons, List.length_nil]
          refine ⟨⟨by omega, ?_⟩, by omega⟩
          intro z hz; simp at hz; aesop
        · simp only [costVb, costVp, Charged.steps_bind, Charged.steps_pure, steps_push,
            val_push, Bool.false_eq_true, ite_false, List.length_append, List.length_cons,
            List.length_nil]
          refine ⟨⟨by omega, ?_⟩, by omega⟩
          intro z hz; simp at hz; aesop)
  simp only [Charged.steps_bind, costVb]
  split
  · rename_i hfl
    simp only [hfl, ite_true, zero_add, costVp, Charged.steps_pure] at h1 h2 ⊢
    refine ⟨h1, h2, ?_⟩
    nlinarith
  · rename_i hfl
    rw [Bool.not_eq_true] at hfl
    simp only [hfl, Bool.false_eq_true, ite_false, zero_add, add_zero, val_push,
      steps_push] at h1 h2 ⊢
    refine ⟨by simp only [List.length_append, List.length_singleton, h1], ?_, ?_⟩
    · intro z hz; simp at hz; aesop
    · nlinarith

/-- INTERNAL: a read with the default `0` from a list of rationals of length at most `M ≥ 3`. -/
theorem ratLen_getD_le (M : ℕ) (hM : 3 ≤ M) (L : List SRat) (idx : ℕ)
    (hL : ∀ z ∈ L, ratLen z.get ≤ M) : ratLen (L.getD idx default).get ≤ M := by
  rw [List.getD_eq_getElem?_getD]
  cases hc : L[idx]? with
  | none => simp [ratLen_zero, hM]
  | some z => simpa using hL z (List.mem_of_getElem? hc)

/-- INTERNAL: the median selection `Program.orderStat` (insertion sort, then one read): its result has length at most `M` and its price is quadratic in the number of runs. -/
theorem orderStat_cost (M : ℕ) (hM : 3 ≤ M) (outs : List SRat) (idx : ℕ)
    (h : ∀ y ∈ outs, ratLen y.get ≤ M) :
    ratLen (orderStat outs idx).val.get ≤ M ∧
    Charged.steps rate (orderStat outs idx) ≤
      outs.length * ((outs.length + 1) * (2 * outs.length + 5 + (M + 1) * (M + 1))) + idx + 1 := by
  unfold orderStat
  obtain ⟨⟨h1, h2⟩, h3⟩ := foldl_inv (fun acc x => insertAsc acc x)
    (fun i (acc : List SRat) => acc.length = i ∧ ∀ z ∈ acc, ratLen z.get ≤ M)
    ((outs.length + 1) * (2 * outs.length + 5 + (M + 1) * (M + 1))) outs 0 [] (by simp)
    (by
      rintro i acc a - hi ha ⟨hlen, hall⟩
      obtain ⟨g1, g2, g3⟩ := insertAsc_cost M acc a (h a ha) hall
      refine ⟨⟨by omega, g2⟩, g3.trans ?_⟩
      apply Nat.mul_le_mul <;> nlinarith)
  simp only [Charged.steps_bind, costVb, steps_get, val_get]
  exact ⟨ratLen_getD_le M hM _ idx h2, by omega⟩

/-- INTERNAL: arithmetic for the price of one `p = 0` run. -/
theorem costArith_zeroRun (S Q kO : ℕ) (hS : 128 ≤ S) (hSQ : S ≤ Q) (h1 : S ^ kO ≤ Q) :
    54 + (S + 1) * 36 + S ^ kO ≤ Q * Q := by nlinarith

/-- INTERNAL: arithmetic facts about `Q ≥ 128`. -/
theorem costArith_sq (Q : ℕ) (hQ : 128 ≤ Q) : 3 ≤ Q * Q ∧ Q ≤ Q * Q ∧ 2 * Q ≤ Q * Q ∧
    Q * Q ≤ Q ^ 9 ∧ Q ≤ Q ^ 9 := by
  refine ⟨by nlinarith, by nlinarith, by nlinarith, ?_, ?_⟩
  · calc Q * Q = Q ^ 2 := (sq Q).symm
      _ ≤ Q ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  · calc Q = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)

/-- INTERNAL: arithmetic for the price of the `R`-run loop. -/
theorem costArith_loop (Q R M : ℕ) (hQ : 128 ≤ Q) (hR : R ≤ Q) (hM : M ≤ Q * Q) :
    R * (M + R + 1) ≤ Q ^ 9 := by
  have h1 : M + R + 1 ≤ 3 * (Q * Q) := by nlinarith
  calc R * (M + R + 1) ≤ Q * (3 * (Q * Q)) := Nat.mul_le_mul hR h1
    _ = 3 * (Q * (Q * Q)) := by ring
    _ ≤ Q * (Q * (Q * Q)) := Nat.mul_le_mul_right _ (by omega)
    _ = Q * (Q * Q) * Q := by ring
    _ = Q ^ 4 := by ring
    _ ≤ Q ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)

/-- INTERNAL: arithmetic for the price of the median selection. -/
theorem costArith_order (Q R mid M : ℕ) (hQ : 128 ≤ Q) (hR : R ≤ Q) (hmid : mid ≤ Q)
    (hM : M ≤ Q * Q) :
    R * ((R + 1) * (2 * R + 5 + (M + 1) * (M + 1))) + mid + 1 ≤ Q ^ 9 := by
  have e0 : M + 1 ≤ 2 * (Q * Q) := by nlinarith
  have e1 : (M + 1) * (M + 1) ≤ 4 * Q ^ 4 := by
    calc (M + 1) * (M + 1) ≤ (2 * (Q * Q)) * (2 * (Q * Q)) := Nat.mul_le_mul e0 e0
      _ = 4 * Q ^ 4 := by ring
  have hQ4 : 3 * Q ≤ Q ^ 4 := by
    calc 3 * Q ≤ Q * Q := Nat.mul_le_mul_right _ (by omega)
      _ = Q ^ 2 := (sq Q).symm
      _ ≤ Q ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have e2 : 2 * R + 5 + (M + 1) * (M + 1) ≤ 5 * Q ^ 4 := by omega
  have e3 : (R + 1) * (2 * R + 5 + (M + 1) * (M + 1)) ≤ (2 * Q) * (5 * Q ^ 4) :=
    Nat.mul_le_mul (by omega) e2
  have e4 : R * ((R + 1) * (2 * R + 5 + (M + 1) * (M + 1))) ≤ Q * ((2 * Q) * (5 * Q ^ 4)) :=
    Nat.mul_le_mul hR e3
  have e5 : Q * ((2 * Q) * (5 * Q ^ 4)) = 10 * Q ^ 6 := by ring
  have e6 : Q ^ 7 = Q * Q ^ 6 := by ring
  have e7 : Q ≤ Q ^ 6 := by
    calc Q = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have e8 : 10 * Q ^ 6 + Q + 1 ≤ Q ^ 7 := by rw [e6]; nlinarith
  have e9 : Q ^ 7 ≤ Q ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- INTERNAL: what the theorem's base `costScale` dominates: `2`, `ratLen ε`, `ratLen δ`, `ε⁻¹` and `⌈log₂ ⌈δ⁻¹⌉⌉`. -/
theorem costScale_facts (I : Instance) (ε δ : ℚ) :
    2 ≤ costScale I ε δ ∧ ratLen ε ≤ costScale I ε δ ∧ ratLen δ ≤ costScale I ε δ ∧
    ε⁻¹ ≤ (costScale I ε δ : ℚ) ∧ Nat.clog 2 ⌈δ⁻¹⌉₊ ≤ costScale I ε δ := by
  have h1 : ratLen ε ≤ inputLength I ε δ := by unfold inputLength; omega
  have h2 : ratLen δ ≤ inputLength I ε δ := by unfold inputLength; omega
  have h3 : 2 ≤ inputLength I ε δ := by
    have := one_le_bitLen I.m; have := one_le_bitLen I.n; unfold inputLength; omega
  have h4 : ε⁻¹ ≤ (⌈ε⁻¹⌉₊ : ℚ) := Nat.le_ceil _
  unfold costScale
  refine ⟨by omega, by omega, by omega, ?_, by omega⟩
  push_cast
  have : (0 : ℚ) ≤ inputLength I ε δ := by positivity
  have : (0 : ℚ) ≤ Nat.clog 2 ⌈δ⁻¹⌉₊ := by positivity
  linarith

/-- INTERNAL: the length of the literal `32`. -/
theorem ratLen_lit32 : ratLen (32 : ℚ) ≤ 35 := by
  have h := ratLen_natCast 32
  have h' := bitLen_le_succ 32
  push_cast at h; omega

/-- INTERNAL: the length of the literal `1/16`. -/
theorem ratLen_lit16inv : ratLen (1 / 16 : ℚ) ≤ 19 := by
  rw [one_div, ratLen_inv]
  have h := ratLen_natCast 16
  have h' := bitLen_le_succ 16
  push_cast at h; omega

/-- INTERNAL: one `p = 0` run (S7) is one oracle call with `ξ_in = ε/32`, `θ = 1/16`, plus three rational operations. -/
theorem zeroRun_cost (kO : ℕ) (hO : ∀ (S : ℕ) (C : Ctx), 2 ≤ S → CtxSize S C → PenaltyOK S C →
    ∀ (x y : List SNat), ProfileValid C x y → ∀ (j : ℕ), j ≤ S →
    ∀ (ξin θ : SRat), 0 < ξin.get → 0 < θ.get → ξin.get⁻¹ ≤ S → θ.get⁻¹ ≤ S →
    ratLen ξin.get ≤ S → ratLen θ.get ≤ S →
    ∀ (tape : Coins ℕ) (cur : ℕ),
      Charged.steps rate (oracle C tape x y j ξin θ cur) ≤ S ^ kO ∧
      ratLen (oracle C tape x y j ξin θ cur).val.1.get ≤ S ^ kO)
    (S : ℕ) (C : Ctx) (hS : 19 ≤ S) (hC : CtxSize S C) (hP : PenaltyOK S C) (Hn : ℕ)
    (hHn : Hn ≤ S) (εS : SRat) (hε : 0 < εS.get) (hεinv : 32 * εS.get⁻¹ ≤ S)
    (hεlen : ratLen εS.get + 35 ≤ S) (tape : Coins ℕ) (cur : ℕ) :
    Charged.steps rate (zeroRun C Hn εS tape cur) ≤ 54 + (S + 1) * 36 + S ^ kO ∧
    ratLen (zeroRun C Hn εS tape cur).val.1.get ≤ S ^ kO := by
  have hpv : ProfileValid C [] [] := by
    intro k _; simp [SNat.get_default]
  have h32 := ratLen_lit32
  have h16 := ratLen_lit16inv
  obtain ⟨o1, o2⟩ := hO S C (by omega) hC hP [] [] hpv Hn hHn
    (SRat.div εS (SRat.lit 32).val).val (SRat.lit (1 / 16)).val
    (by simp only [SRat.get_div, SRat.get_lit]; positivity)
    (by simp only [SRat.get_lit]; norm_num)
    (by
      simp only [SRat.get_div, SRat.get_lit]
      rw [inv_div, div_eq_mul_inv]; linarith)
    (by simp only [SRat.get_lit]; norm_num; exact_mod_cast (by omega : 16 ≤ S))
    (by
      simp only [SRat.get_div, SRat.get_lit]
      have := ratLen_div_le εS.get 32
      omega)
    (by simp only [SRat.get_lit]; omega)
    tape cur
  unfold zeroRun
  simp only [Charged.steps_bind, costVb, steps_SRat_lit, steps_SRat_div, SRat.get_lit]
  refine ⟨?_, o2⟩
  have : (ratLen εS.get + 1) * (ratLen (32 : ℚ) + 1) ≤ (S + 1) * 36 :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

/-- **Every execution of `Program.fpras` costs at most `costScale ^ k` bit operations**, on
every coin family.  The prefix S0–S4 is `prep_cost`; on an infeasible input only the
feasibility test and the output `0` follow.  On a feasible input the arithmetic on `δ`
gives `R = 10 ⌈log₂ ⌈δ⁻¹⌉⌉ + 1` runs; each `p = 0` run is one oracle call
(`oracle_cost`), each `p ≥ 1` run an annealing run (`anneal_cost`), both on a context
whose penalty is bounded by `prep_penalty_bound`; the median of `R` outputs is an
insertion sort (`orderStat_cost`).
PAPER: sections/algorithm.tex:692-698 ("The number of repetitions is `O(log(δ⁻¹))`;
exact comparisons and median selection on their polynomial-length rational outputs also
have polynomial bit cost.") -/
theorem fpras_steps_le (hprior : Prior) : ∃ k : ℕ, ∀ (I : Instance) (ε δ : ℚ), 0 < I.m → 0 < I.n →
    0 < ε → ε < 1 → 0 < δ → δ < 1 →
    ∀ tape : Coins ℕ, Charged.steps rate (fpras I ε δ tape) ≤ costScale I ε δ ^ k := by
  obtain ⟨kP, hP⟩ := prep_cost
  obtain ⟨kO, hO⟩ := oracle_cost
  obtain ⟨kA, hA⟩ := anneal_cost
  refine ⟨(kP + 7) * (kO + kA + 1) * 10, ?_⟩
  intro I ε δ hm hn hε hε1 hδ hδ1 tape
  obtain ⟨hcost, hctx, hpm, hps⟩ := hP I ε δ hm hn hε hε1 hδ hδ1
  obtain ⟨hN2, hεN, hδN, hεinvN, hclogN⟩ := costScale_facts I ε δ
  generalize hNdef : costScale I ε δ = N at *
  have hNpos : 1 ≤ N := by omega
  have hN6 : 64 ≤ N ^ 6 := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ N ^ 6 := Nat.pow_le_pow_left hN2 6
  have hN7 : 64 * N ≤ N ^ 7 := by rw [pow_succ]; exact Nat.mul_le_mul_right N hN6
  obtain ⟨S, hSdef⟩ : ∃ S, S = N ^ (kP + 7) := ⟨_, rfl⟩
  have hNkPS : N ^ kP ≤ S := hSdef ▸ Nat.pow_le_pow_right hNpos (by omega)
  have hNS' : 64 * N ≤ S := le_trans hN7 (hSdef ▸ Nat.pow_le_pow_right hNpos (by omega))
  have hS128 : 128 ≤ S := by omega
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = S ^ (kO + kA + 1) := ⟨_, rfl⟩
  have hSQ1 : S ^ kO ≤ Q := hQdef ▸ Nat.pow_le_pow_right (by omega) (by omega)
  have hSQ2 : S ^ kA ≤ Q := hQdef ▸ Nat.pow_le_pow_right (by omega) (by omega)
  have hSQ : S ≤ Q := by
    have : S ^ 1 ≤ Q := hQdef ▸ Nat.pow_le_pow_right (by omega) (by omega)
    simpa using this
  have hfin : N ^ ((kP + 7) * (kO + kA + 1) * 10) = Q ^ 10 := by
    rw [hQdef, hSdef, ← pow_mul, ← pow_mul, Nat.mul_assoc]
  rw [hfin]
  have hQ128 : 128 ≤ Q := le_trans hS128 hSQ
  have hQ9 : 40 * Q ^ 9 ≤ Q ^ 10 := by
    rw [pow_succ, Nat.mul_comm 40]; exact Nat.mul_le_mul_left _ (by omega)
  have hQ1 : Q ≤ Q ^ 9 := by
    calc Q = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold prepCost at hcost
  unfold fpras
  simp only [Charged.steps_bind]
  rw [show (readList (List.ofFn I.r)).val = prepR I from rfl,
    show (readList (List.ofFn I.c)).val = prepC I from rfl,
    show (readMatrix (List.ofFn fun i => List.ofFn fun j => I.b i j)).val = prepB I from rfl]
  split
  · rename_i hfeas
    have hpen := prep_penalty_bound hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas
    have hCS : CtxSize S (prepCtx I ε δ) := hctx.mono hNkPS
    have hPmS : PmSize S (prepPm I ε δ) := hpm.mono hNkPS
    have hpS : (prepPS I ε δ).get ≤ S := hps.trans hNkPS
    have hPenS : PenaltyOK S (prepCtx I ε δ) := fun x y zf hxy hz => by
      obtain ⟨h0, h1⟩ := hpen x y zf hxy hz
      rw [abs_of_nonneg h0]
      exact h1.trans (by exact_mod_cast hCS.H_le)
    simp only [Charged.steps_bind]
    rw [show (tighten I.m I.n (prepR I) (prepC I) (prepB I)).val = prepT I from rfl,
      show (params I.m I.n (inputLen I ε δ).val (SRat.lit ε).val).val = prepPm I ε δ from rfl,
      show (buildCtx I.m I.n (prepT I) (prepPm I ε δ)).val = prepCtx I ε δ from rfl,
      show (Charged.foldl (fun acc (e : Entry) => SNat.add acc e.2.2) (prepCtx I ε δ).small
        (SNat.lit 0).val).val = prepPS I ε δ from rfl]
    -- the arithmetic on `δ`: `s = ⌈log₂ ⌈δ⁻¹⌉⌉`, `R = 10 s + 1`, `5 s`
    generalize hδS : (SRat.lit δ).val = δS
    generalize h1Q : (SRat.lit 1).val = oneQ
    generalize hiv : (SRat.div oneQ δS).val = iv
    generalize hcd : (SRat.natCeil iv).val = cd
    generalize hsv : (clog2 cd).val = sv
    generalize hc10 : (SNat.lit 10).val = c10
    generalize hs10 : (SNat.mul c10 sv).val = s10
    generalize hone : (SNat.lit 1).val = one
    generalize hR : (SNat.add s10 one).val = R
    generalize hc5 : (SNat.lit 5).val = c5
    generalize hmid : (SNat.mul c5 sv).val = mid
    have gδ : δS.get = δ := by rw [← hδS]; simp
    have g1 : oneQ.get = 1 := by rw [← h1Q]; simp
    have giv : iv.get = 1 / δ := by rw [← hiv]; simp [gδ, g1]
    have gcd : cd.get = ⌈δ⁻¹⌉₊ := by rw [← hcd]; simp [giv]
    have gsv : sv.get = Nat.size (⌈δ⁻¹⌉₊ - 1) := by rw [← hsv, clog2_get, gcd]
    have gc10 : c10.get = 10 := by rw [← hc10]; simp
    have gs10 : s10.get = 10 * sv.get := by rw [← hs10]; simp [gc10]
    have gone : one.get = 1 := by rw [← hone]; simp
    have gR : R.get = 10 * sv.get + 1 := by rw [← hR]; simp [gs10, gone]
    have gc5 : c5.get = 5 := by rw [← hc5]; simp
    have gmid : mid.get = 5 * sv.get := by rw [← hmid]; simp [gc5]
    have hsN : sv.get ≤ N := by
      rw [gsv]; exact (size_sub_one_le_clog _).trans hclogN
    have hRQ : R.get ≤ Q := by omega
    have hmidQ : mid.get ≤ Q := by omega
    -- the price of each step of the `δ` arithmetic
    have hr1 : ratLen (1 : ℚ) ≤ 4 := by
      have h := ratLen_natCast 1; have h' := bitLen_le_succ 1; push_cast at h; omega
    have hivlen : ratLen iv.get ≤ N + 4 := by
      rw [giv]; have := ratLen_div_le 1 δ; omega
    have a1 : Charged.steps rate (SRat.lit δ) ≤ Q := by rw [steps_SRat_lit]; omega
    have a2 : Charged.steps rate (SRat.lit 1) ≤ Q := by rw [steps_SRat_lit]; omega
    have a3 : Charged.steps rate (SRat.div oneQ δS) ≤ Q * Q := by
      rw [steps_SRat_div, g1, gδ]; exact Nat.mul_le_mul (by omega) (by omega)
    have a4 : Charged.steps rate (SRat.natCeil iv) ≤ Q * Q := by
      rw [steps_SRat_natCeil]; exact Nat.mul_le_mul (by omega) (by omega)
    have a5 : Charged.steps rate (clog2 cd) ≤ Q := by
      rw [clog2_steps, gcd]
      have h1 := bitLen_natCeil_le δ⁻¹
      have h2 := bitLen_mono (Nat.sub_le ⌈δ⁻¹⌉₊ 1)
      have h3 : ratLen δ⁻¹ ≤ N := by rw [ratLen_inv]; exact hδN
      have h4 : bitLen 1 ≤ 2 := bitLen_le_succ 1
      omega
    have a6 : Charged.steps rate (SNat.lit 10) ≤ Q := by
      rw [steps_SNat_lit]; have := bitLen_le_succ 10; omega
    have a7 : Charged.steps rate (SNat.mul c10 sv) ≤ Q * Q := by
      rw [steps_SNat_mul, gc10]
      have := bitLen_le_succ 10; have := bitLen_le_succ sv.get
      exact Nat.mul_le_mul (by omega) (by omega)
    have a8 : Charged.steps rate (SNat.lit 1) ≤ Q := by
      rw [steps_SNat_lit]; have := bitLen_le_succ 1; omega
    have a9 : Charged.steps rate (SNat.add s10 one) ≤ Q := by
      rw [steps_SNat_add, gs10, gone]
      have := bitLen_le_succ (10 * sv.get); have := bitLen_le_succ 1; omega
    have a10 : Charged.steps rate (SNat.index R) ≤ Q := by
      rw [steps_SNat_index]; have := bitLen_le_succ R.get; omega
    have a11 : Charged.steps rate (SNat.lit 5) ≤ Q := by
      rw [steps_SNat_lit]; have := bitLen_le_succ 5; omega
    have a12 : Charged.steps rate (SNat.mul c5 sv) ≤ Q * Q := by
      rw [steps_SNat_mul, gc5]
      have := bitLen_le_succ 5; have := bitLen_le_succ sv.get
      exact Nat.mul_le_mul (by omega) (by omega)
    have a13 : Charged.steps rate (SNat.index mid) ≤ Q := by
      rw [steps_SNat_index]; have := bitLen_le_succ mid.get; omega
    have hQ2 : 2 * Q ≤ Q * Q := Nat.mul_le_mul_right Q (by omega)
    have a14 : Charged.steps rate (SNat.eq (prepPS I ε δ) (SNat.lit 0).val) ≤ Q * Q := by
      rw [steps_SNat_eq, SNat.get_lit]
      have := bitLen_le_succ (prepPS I ε δ).get; have := bitLen_le_succ 0; omega
    have hQQ : Q * Q ≤ Q ^ 9 := by
      calc Q * Q = Q ^ 2 := (sq Q).symm
        _ ≤ Q ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [SNat.val_index]
    split
    · -- `p = 0`: `R` single oracle calls, then the median
      simp only [Charged.steps_bind, SNat.val_index]
      have hεS : (SRat.lit ε).val.get = ε := SRat.get_lit ε
      have hzr : ∀ cur, Charged.steps rate (zeroRun (prepCtx I ε δ) (prepPm I ε δ).H.get
            (SRat.lit ε).val tape cur) ≤ Q * Q ∧
          ratLen (zeroRun (prepCtx I ε δ) (prepPm I ε δ).H.get (SRat.lit ε).val tape cur).val.1.get
            ≤ Q * Q := by
        intro cur
        obtain ⟨z1, z2⟩ := zeroRun_cost kO hO S (prepCtx I ε δ) (by omega) hCS hPenS _
          hPmS.H_le (SRat.lit ε).val (by rw [hεS]; exact hε)
          (by
            rw [hεS]
            have h64 : ((64 * N : ℕ) : ℚ) ≤ (S : ℚ) := by exact_mod_cast hNS'
            calc 32 * ε⁻¹ ≤ 32 * (N : ℚ) := by gcongr
              _ ≤ ((64 * N : ℕ) : ℚ) := by push_cast; linarith [(Nat.cast_nonneg N : (0:ℚ) ≤ N)]
              _ ≤ S := h64)
          (by rw [hεS]; omega) tape cur
        exact ⟨z1.trans (costArith_zeroRun S Q kO hS128 hSQ hSQ1),
          z2.trans (hSQ1.trans (costArith_sq Q hQ128).2.1)⟩
      obtain ⟨l1, l2, l3⟩ := runLoop_cost (zeroRun (prepCtx I ε δ)
        (prepPm I ε δ).H.get (SRat.lit ε).val tape) (Q * Q) R.get hzr
      obtain ⟨q1, q2, q3, q4, q5⟩ := costArith_sq Q hQ128
      obtain ⟨o1, o2⟩ := orderStat_cost (Q * Q) q1 _ mid.get l2
      rw [l1] at o2
      have b1 : Charged.steps rate (prepPm I ε δ).H.index ≤ Q * Q := by
        rw [steps_SNat_index]; have := bitLen_le_succ (prepPm I ε δ).H.get
        have := hPmS.H_le; omega
      have b2 := costArith_loop Q R.get (Q * Q) hQ128 hRQ le_rfl
      have b3 := costArith_order Q R.get mid.get (Q * Q) hQ128 hRQ hmidQ le_rfl
      rw [steps_SRat_output]
      linarith
    · -- `p ≥ 1`: the chain setup, `R` annealing runs, then the median
      simp only [Charged.steps_bind]
      have hεS : (SRat.lit ε).val.get = ε := SRat.get_lit ε
      obtain ⟨c1, c2⟩ := hA S (prepCtx I ε δ) (prepPm I ε δ) (prepPS I ε δ) (SRat.lit ε).val
        (by omega) hCS hPenS hPmS hpS (by rw [hεS]; exact hε)
        (by
          rw [hεS]
          have hNS0 : ((N : ℕ) : ℚ) ≤ (S : ℚ) := by exact_mod_cast (show N ≤ S by omega)
          exact hεinvN.trans hNS0)
        (by rw [hεS]; omega)
      obtain ⟨q1, q2, q3, q4, q5⟩ := costArith_sq Q hQ128
      obtain ⟨l1, l2, l3⟩ := runLoop_cost
        (annealRun (prepCtx I ε δ)
          (chainSetup (prepCtx I ε δ) (prepPm I ε δ) (prepPS I ε δ) (SRat.lit ε).val).val.1 tape
          (chainSetup (prepCtx I ε δ) (prepPm I ε δ) (prepPS I ε δ) (SRat.lit ε).val).val.2.1
          (chainSetup (prepCtx I ε δ) (prepPm I ε δ) (prepPS I ε δ) (SRat.lit ε).val).val.2.2.1
          (chainSetup (prepCtx I ε δ) (prepPm I ε δ) (prepPS I ε δ) (SRat.lit ε).val).val.2.2.2)
        (Q * Q) R.get (fun cur => ⟨(c2 tape cur).1.trans (hSQ2.trans q2),
          (c2 tape cur).2.trans (hSQ2.trans q2)⟩)
      obtain ⟨o1, o2⟩ := orderStat_cost (Q * Q) q1 _ mid.get l2
      rw [l1] at o2
      have b1 : Charged.steps rate (chainSetup (prepCtx I ε δ) (prepPm I ε δ) (prepPS I ε δ)
          (SRat.lit ε).val) ≤ Q := c1.trans hSQ2
      have b2 := costArith_loop Q R.get (Q * Q) hQ128 hRQ le_rfl
      have b3 := costArith_order Q R.get mid.get (Q * Q) hQ128 hRQ hmidQ le_rfl
      rw [steps_SRat_output]
      linarith
  · -- infeasible input: the answer `0` is written at once
    simp only [Charged.steps_bind, steps_SRat_lit, steps_SRat_output, SRat.get_lit,
      ratLen_zero]
    omega

end Cellcounting.Analysis

/-- Proof-side owner for `Cellcounting.fpras_time`; its statement is fixed by the proof charter.
PAPER: sections/introduction.tex:30-33 ("one fixed polynomial in `L`, `ε⁻¹`, and
`log(δ⁻¹)` bounds its total bit operations on every execution"); proof assembled at
sections/algorithm.tex:692-706. -/
theorem Cellcounting.Analysis.fpras_time_owner (hprior : Prior) : ∃ C k : ℕ, ∀ (I : Instance) (ε δ : ℚ), 0 < I.m → 0 < I.n → 0 < ε → ε < 1 → 0 < δ → δ < 1 → Arlib.Computation.worstSteps Model.Operations.rate (run I ε δ) ≤ ((C * (inputLength I ε δ + ⌈ε⁻¹⌉₊ + Nat.clog 2 ⌈δ⁻¹⌉₊ + 1) ^ k : ℕ) : ℕ∞) := by
  obtain ⟨k, hk⟩ := Cellcounting.Analysis.fpras_steps_le hprior
  refine ⟨1, k, fun I ε δ hm hn hε hε1 hδ hδ1 => ?_⟩
  rw [Arlib.Computation.worstSteps_le_iff]
  intro p hp
  rw [run, PMF.mem_support_map_iff] at hp
  obtain ⟨c, -, rfl⟩ := hp
  rw [one_mul]
  exact hk I ε δ hm hn hε hε1 hδ hδ1 c

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · assembled · `fpras_time_owner` proved from `fpras_steps_le`; open children `prep_cost`, `prep_penalty_bound`, `oracle_cost`, `anneal_cost`
-/
