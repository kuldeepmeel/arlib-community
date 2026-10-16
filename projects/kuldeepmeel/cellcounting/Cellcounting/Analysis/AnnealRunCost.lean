import Cellcounting.Analysis.StepCost
import Cellcounting.Analysis.Mu0Cost

/-!
# One annealing run costs a polynomial number of bit operations

`Cellcounting.Analysis.annealRun_cost_of`: under `CtxSize T C`, `PenaltyOK T C`,
`ChainSize T C K Ph`, with initial multipliers `WSize T w0` and `ratLen C(0) ≤ T`, the
run `Program.annealRun C K tape Ph w0 C0 cur` costs at most `T ^ k` on every tape and
returns a rational of length at most `T ^ k`, for one fixed `k`.

Route (`H = Ph.Hn ≤ T` phases): carry `RunInv` — "`ws` has at most `j + 1` tables,
each with `WSize (T + 1 + j·T²(2T + 8))`; `ratLen prod ≤ 4 + j·rBound`" — through
`phase` (`phase_le`), where `rBound` bounds one ratio estimate.  In a phase: `mu0_cost`; `restart` is `B_ret + 1 ≤ T + 1`
rounds with `hits, used ≤ T + 1` and stage `≤ T + 1`, each one `step_cost` (applied at a
polynomial bound `T'` via `ChainSize.mono`, `CtxSize.mono`, `PenaltyOK.mono`) and one
`kind_cost`; `observe` is `N_av ≤ T` rounds, each `step_cost` and `observeState` (one
`kind_cost`, one `profile_cost`, two `oracle_cost` calls at `j, j + 1 ≤ T`; counts
`≤ N_av`; `Σ G_j` has a common-denominator bound `∏ den`, not a doubling one);
`allPositive` and `updateW` are `p²` rounds (each update multiplies by `n_0/n_il`,
adding `≤ 2T + 8` to the length); the estimate `R̂ = (ΣG/N)/(n_0/N)`.  The final
exponent comes from one master scale `V = T^E` dominating `T`, the oracle bound, the
step bound, the `μ₀` bound and the multiplier bound (`phaseBound_mono`, `run_poly`).
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Model
open Cellcounting.Program
open Cellcounting.Model.Operations
open Cellcounting.Interface

/-- INTERNAL: the size invariant of a running sum of rationals of length `≤ G`: after `r`
terms the denominator has length `≤ 2 + rG` (it divides the product of the denominators)
and the value is at most `r 2^G` in absolute value. -/
theorem sum_inv_step (s g : ℚ) (G r : ℕ) (hd : bitLen s.den ≤ 2 + r * G)
    (hs : |s| ≤ r * 2 ^ G) (hg : ratLen g ≤ G) :
    bitLen (s + g).den ≤ 2 + (r + 1) * G ∧ |s + g| ≤ (r + 1) * 2 ^ G := by
  constructor
  · have h1 : (s + g).den ≤ s.den * g.den := Nat.le_of_dvd (Nat.mul_pos s.den_pos g.den_pos)
      (Rat.add_den_dvd s g)
    have h2 := bitLen_mul_le s.den g.den
    have h3 : bitLen g.den ≤ G := by unfold ratLen at hg; omega
    have := bitLen_mono h1
    rw [Nat.add_mul]; omega
  · have h1 := abs_lt_two_pow_ratLen g
    have h2 : (2 : ℚ) ^ ratLen g ≤ 2 ^ G := pow_le_pow_right₀ (by norm_num) hg
    calc |s + g| ≤ |s| + |g| := abs_add_le s g
      _ ≤ r * 2 ^ G + 2 ^ G := by linarith
      _ = (r + 1) * 2 ^ G := by push_cast; ring

/-- INTERNAL: the length of a rational from its denominator length and a bound on its
absolute value. -/
theorem ratLen_le_of_inv (s : ℚ) (D M : ℕ) (hd : bitLen s.den ≤ D) (hs : |s| ≤ M) :
    ratLen s ≤ bitLen M + 2 * D := by
  have h := Rat.mul_den_eq_num s
  have hnum : s.num.natAbs ≤ M * s.den := by
    have : (s.num.natAbs : ℚ) = |s| * s.den := by
      rw [Nat.cast_natAbs, Int.cast_abs, ← h, abs_mul,
        abs_of_pos (by exact_mod_cast s.den_pos : (0 : ℚ) < s.den)]
    have h' : (s.num.natAbs : ℚ) ≤ M * s.den := by
      rw [this]; exact mul_le_mul_of_nonneg_right hs (by positivity)
    exact_mod_cast h'
  have := bitLen_mono hnum
  have := bitLen_mul_le M s.den
  unfold ratLen; omega

/-- INTERNAL: the size invariant of the observation tallies after `r` observed states:
counts at most `r`, and `Σ G_j` a sum of `r` terms of length `≤ G`. -/
def ObsInv (G r : ℕ) (o : Obs) : Prop :=
  o.n0.get ≤ r ∧ (∀ row ∈ o.nT, ∀ c ∈ row, c.get ≤ r) ∧ bitLen o.sumG.get.den ≤ 2 + r * G ∧
    |o.sumG.get| ≤ ((r * 2 ^ G : ℕ) : ℚ)

/-- INTERNAL: the length of `Σ G_j` under `ObsInv`. -/
theorem ObsInv.ratLen_le {G r : ℕ} {o : Obs} (h : ObsInv G r o) :
    ratLen o.sumG.get ≤ bitLen r + G + 2 + 2 * (2 + r * G) := by
  have := ratLen_le_of_inv o.sumG.get _ _ h.2.2.1 h.2.2.2
  have h1 := bitLen_mul_le r (2 ^ G)
  rw [bitLen_two_pow] at h1
  omega

/-- INTERNAL: one observation keeps `ObsInv` (one more state) and costs `O(((T + 2)(Q + 2))²)`. -/
theorem observeState_le (T Q j : ℕ) (C : Ctx) (K : Chain) (Ph : Phase) (hT : 2 ≤ T)
    (hK : ChainSize T C K Ph)
    (hO : ∀ (x y : List SNat), ProfileValid C x y → ∀ (j' : ℕ), j' ≤ T → ∀ (tape : Coins ℕ) (cur : ℕ),
      Charged.steps rate (oracle C tape x y j' K.ξ K.ξ cur) ≤ Q ∧
      ratLen (oracle C tape x y j' K.ξ K.ξ cur).val.1.get ≤ Q)
    (hj : j + 1 ≤ T) (tape : Coins ℕ) (r : ℕ) (hr : r ≤ T + 1) (o : Obs)
    (hinv : ObsInv (2 * Q) r o) :
    ObsInv (2 * Q) (r + 1) (observeState C K tape j o).val ∧
    Charged.steps rate (observeState C K tape j o) ≤ 200 * ((T + 2) * (Q + 2)) ^ 2 := by
  obtain ⟨hn0, hnT, hd, hs⟩ := hinv
  have hsl := ObsInv.ratLen_le ⟨hn0, hnT, hd, hs⟩
  unfold observeState
  simp only [Charged.steps_bind, costVb, steps_SNat_lit]
  obtain ⟨kd, kc⟩ := kind_cost K o.S
  generalize hkv : Charged.val (kind K o.S) = k at kd
  have hb1 : bitLen 1 = 2 := by decide
  have hp := hK.p_le
  have hkc : Charged.steps rate (kind K o.S) ≤ 6 * (T + 2) ^ 2 :=
    kc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have hsc : (T + 2) ^ 2 ≤ ((T + 2) * (Q + 2)) ^ 2 :=
    Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by omega)) 2
  rcases k with _ | ⟨i, l⟩ | _ <;> dsimp only
  · -- a transversal: two fresh oracle calls
    simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SNat_add,
      SNat.get_add, SNat.get_lit, steps_SRat_div, steps_SRat_add, SRat.get_div, SRat.get_add, hb1]
    obtain ⟨hpv, -, hpc⟩ := profile_cost hK o.S
    generalize profile K o.S = P at *
    obtain ⟨o1c, o1v⟩ := hO _ _ hpv (j + 1) hj tape o.cur
    generalize oracle C tape (Charged.val P).1 (Charged.val P).2 (j + 1) K.ξ K.ξ o.cur = O1 at *
    obtain ⟨o2c, o2v⟩ := hO _ _ hpv j (by omega) tape (Charged.val O1).2
    generalize oracle C tape (Charged.val P).1 (Charged.val P).2 j K.ξ K.ξ (Charged.val O1).2 = O2 at *
    have hg := ratLen_div_le (Charged.val O1).1.get (Charged.val O2).1.get
    obtain ⟨s1, s2⟩ := sum_inv_step o.sumG.get ((Charged.val O1).1.get / (Charged.val O2).1.get)
      (2 * Q) r hd (by push_cast at hs; exact hs) (by omega)
    refine ⟨⟨by simp only [SNat.get_add, SNat.get_lit]; omega,
      fun row h c hc => (hnT row h c hc).trans (Nat.le_succ r),
      by simpa only [SRat.get_add, SRat.get_div] using s1,
      by simp only [SRat.get_add, SRat.get_div]; push_cast; exact s2⟩, ?_⟩
    have hX : (T + 2) * (Q + 2) = T * Q + 2 * T + 2 * Q + 4 := by ring
    generalize hXd : (T + 2) * (Q + 2) = X at *
    have hn0b : bitLen o.n0.get ≤ T + 2 := (bitLen_le_succ _).trans (by omega)
    have hrb : bitLen r ≤ T + 2 := (bitLen_le_succ _).trans (by omega)
    have hrQ : r * (2 * Q) ≤ (T + 1) * (2 * Q) := Nat.mul_le_mul_right _ hr
    have hTQ : (T + 1) * (2 * Q) ≤ 2 * X := by rw [← hXd]; nlinarith
    have hsl' : ratLen o.sumG.get + 1 ≤ 7 * X := by omega
    have hm1 : (ratLen (Charged.val O1).1.get + 1) * (ratLen (Charged.val O2).1.get + 1) ≤ X * X :=
      Nat.mul_le_mul (by omega) (by omega)
    have hm2 : (ratLen o.sumG.get + 1) * (ratLen ((Charged.val O1).1.get / (Charged.val O2).1.get) + 1)
        ≤ (7 * X) * (2 * X) := Nat.mul_le_mul hsl' (by omega)
    have hX2 : X ^ 2 = X * X := sq X
    have h1 : (T + 1) ^ 2 ≤ (T + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hXX : X ≤ X * X := Nat.le_mul_self X
    have hQX : Q ≤ X := by omega
    have hTX : T + 2 ≤ X := by omega
    clear hO s1 s2 hs hd hsl hpv
    linarith
  · -- a defect state: one counter update
    obtain ⟨hi, hl⟩ := kd i l rfl
    have hc := get2_pred (fun c : SNat => c.get ≤ r) o.nT i l hnT (by simp)
    simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_get2, steps_set2,
      steps_SNat_add, SNat.get_add, SNat.get_lit, hb1]
    have hcb : bitLen (get2 o.nT i l).val.get ≤ T + 2 := (bitLen_le_succ _).trans (by omega)
    have hs' : ((r * 2 ^ (2 * Q) : ℕ) : ℚ) ≤ (((r + 1) * 2 ^ (2 * Q) : ℕ) : ℚ) := by
      exact_mod_cast Nat.mul_le_mul_right _ (Nat.le_succ r)
    refine ⟨⟨Nat.le_succ_of_le hn0, set2_pred (fun c : SNat => c.get ≤ r + 1) _ _ _ _
        (fun row h c hc => (hnT row h c hc).trans (Nat.le_succ r))
        (by simp only [SNat.get_add, SNat.get_lit]; omega),
      hd.trans (by rw [Nat.add_mul]; omega), hs.trans hs'⟩, ?_⟩
    have hX : T + 2 ≤ (T + 2) * (Q + 2) := Nat.le_mul_of_pos_right _ (by omega)
    have hXX : (T + 2) * (Q + 2) ≤ ((T + 2) * (Q + 2)) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  · -- outside `X`: nothing observed
    simp only [Charged.steps_pure]
    have hs' : ((r * 2 ^ (2 * Q) : ℕ) : ℚ) ≤ (((r + 1) * 2 ^ (2 * Q) : ℕ) : ℚ) := by
      exact_mod_cast Nat.mul_le_mul_right _ (Nat.le_succ r)
    refine ⟨⟨Nat.le_succ_of_le hn0, fun row h c hc => (hnT row h c hc).trans (Nat.le_succ r),
      hd.trans (by rw [Nat.add_mul]; omega), hs.trans hs'⟩, ?_⟩
    have : (T + 2) ^ 2 ≥ 1 := Nat.one_le_pow _ _ (by omega)
    omega

/-- INTERNAL: the `N_av` observations of one phase. -/
theorem observe_le (T Q Sb j : ℕ) (C : Ctx) (K : Chain) (Ph : Phase) (hT : 2 ≤ T)
    (hK : ChainSize T C K Ph)
    (hO : ∀ (x y : List SNat), ProfileValid C x y → ∀ (j' : ℕ), j' ≤ T → ∀ (tape : Coins ℕ) (cur : ℕ),
      Charged.steps rate (oracle C tape x y j' K.ξ K.ξ cur) ≤ Q ∧
      ratLen (oracle C tape x y j' K.ξ K.ξ cur).val.1.get ≤ Q)
    (hj : j + 1 ≤ T) (tape : Coins ℕ) (w : List (List SRat))
    (hstep : ∀ (S : List Bool) (cur : ℕ), Charged.steps rate (step C K tape j w S cur) ≤ Sb)
    (S0 : List Bool) (cur : ℕ) :
    ObsInv (2 * Q) (T + 1) (observe C K tape Ph j w S0 cur).val ∧
    Charged.steps rate (observe C K tape Ph j w S0 cur) ≤
      (T + 1) * (Sb + 200 * ((T + 2) * (Q + 2)) ^ 2) + 2 * T + 6 := by
  unfold observe
  simp only [Charged.steps_bind, costVb, steps_SNat_lit, steps_SRat_lit, steps_replicate,
    val_replicate]
  have hb0 : bitLen 0 = 1 := by decide
  have hz : ratLen (0 : ℚ) = 3 := ratLen_zero
  have hinit : ObsInv (2 * Q) 0 ⟨S0, (SNat.lit 0).val,
      List.replicate K.p (List.replicate K.p (SNat.lit 0).val), (SRat.lit 0).val, cur⟩ := by
    refine ⟨by simp, ?_, by simp [bitLen], by simp⟩
    intro row hrow c hc
    rw [List.mem_replicate] at hrow
    rw [hrow.2, List.mem_replicate] at hc
    rw [hc.2]; simp
  obtain ⟨i0, c0⟩ := observeState_le T Q j C K Ph hT hK hO hj tape 0 (by omega) _ hinit
  generalize observeState C K tape j ⟨S0, (SNat.lit 0).val,
      List.replicate K.p (List.replicate K.p (SNat.lit 0).val), (SRat.lit 0).val, cur⟩ = O0 at *
  generalize hR : Charged.repeatFor _ (Ph.NavN - 1) (Charged.val O0) = R
  have hN := hK.NavN_le
  have key : ObsInv (2 * Q) (Ph.NavN - 1 + 1) R.val ∧
      Charged.steps rate R ≤ (Ph.NavN - 1) * (Sb + 200 * ((T + 2) * (Q + 2)) ^ 2) := by
    subst hR
    refine repeatFor_inv _ (fun r (st : Obs) => ObsInv (2 * Q) (r + 1) st)
      (Sb + 200 * ((T + 2) * (Q + 2)) ^ 2) (Ph.NavN - 1) _ i0 ?_
    intro r st hr hst
    simp only [Charged.steps_bind, costVb]
    have hs := hstep st.S st.cur
    generalize step C K tape j w st.S st.cur = St at *
    obtain ⟨i1, c1⟩ := observeState_le T Q j C K Ph hT hK hO hj tape (r + 1) (by omega)
      ⟨(Charged.val St).1, st.n0, st.nT, st.sumG, (Charged.val St).2⟩ hst
    exact ⟨i1, by omega⟩
  clear hR
  obtain ⟨k1, k2⟩ := key
  have hmono : ∀ {a b : ℕ} {o : Obs}, a ≤ b → ObsInv (2 * Q) a o → ObsInv (2 * Q) b o := by
    intro a b o hab ⟨h1, h2, h3, h4⟩
    refine ⟨h1.trans hab, fun row h c hc => (h2 row h c hc).trans hab,
      h3.trans (by have := Nat.mul_le_mul_right (2 * Q) hab; omega), h4.trans ?_⟩
    exact_mod_cast Nat.mul_le_mul_right _ hab
  refine ⟨hmono (by omega) k1, ?_⟩
  have : (Ph.NavN - 1) * (Sb + 200 * ((T + 2) * (Q + 2)) ^ 2) ≤
      T * (Sb + 200 * ((T + 2) * (Q + 2)) ^ 2) := Nat.mul_le_mul_right _ (by omega)
  have hp := hK.p_le
  rw [hb0, hz]
  nlinarith

/-- INTERNAL: the capped restart: `B_ret + 1 ≤ T + 1` rounds, stage, hits and used counts at most
the round number. -/
theorem restart_le (T B Sb j : ℕ) (C : Ctx) (K : Chain) (Ph : Phase) (hT : 2 ≤ T)
    (hK : ChainSize T C K Ph) (hTB : T + 2 ≤ B) (hj : j ≤ T) (tape : Coins ℕ)
    (ws : List (List (List SRat))) (hws : ∀ w ∈ ws, WSize B w)
    (hstep : ∀ (a : ℕ), a ≤ B → ∀ (w : List (List SRat)), WSize B w →
      ∀ (S : List Bool) (cur : ℕ), Charged.steps rate (step C K tape a w S cur) ≤ Sb)
    (S0 : List Bool) (cur : ℕ) :
    Charged.steps rate (restart C K tape Ph ws j S0 cur) ≤
      (T + 1) * (Sb + 10 * (T + 3) ^ 2) + T + 5 := by
  unfold restart
  simp only [Charged.steps_bind, costVb, steps_SNat_lit, steps_idxEq]
  have hb0 : bitLen 0 = 1 := by decide
  have hb1 : bitLen 1 = 2 := by decide
  have hp := hK.p_le
  have hBr := hK.BretN_le
  generalize hR : Charged.repeatFor _ (Ph.BretN + 1) _ = R
  have key : Charged.steps rate R ≤ (Ph.BretN + 1) * (Sb + 10 * (T + 3) ^ 2) := by
    subst hR
    refine (repeatFor_inv _ (fun r (st : Restart) => st.stage ≤ r + 1 ∧ st.hits.get ≤ r ∧
      st.used.get ≤ r) (Sb + 10 * (T + 3) ^ 2) (Ph.BretN + 1) _ (by simp) ?_).2
    rintro r ⟨S, stage, hits, used, fin, ab, c⟩ hr ⟨hst, hhi, hus⟩
    dsimp only at hst hhi hus ⊢
    have hbu : bitLen used.get ≤ T + 2 := (bitLen_le_succ _).trans (by omega)
    have hbh : bitLen (hits.get + 1) ≤ T + 2 := (bitLen_le_succ _).trans (by omega)
    have hbB : bitLen Ph.Bret.get ≤ T + 1 := (bitLen_le_succ _).trans (by have := hK.Bret_le; omega)
    have hbτ : bitLen Ph.τ.get ≤ T + 1 := (bitLen_le_succ _).trans (by have := hK.τ_le; omega)
    have hbs : bitLen stage ≤ T + 2 := (bitLen_le_succ _).trans (by omega)
    have hbj : bitLen j ≤ T + 1 := (bitLen_le_succ _).trans (by omega)
    have hsq : 6 * (K.p + 2) ^ 2 ≤ 6 * (T + 3) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    have hsq' : 3 * (T + 3) ≤ (T + 3) ^ 2 := by nlinarith
    have hbhi : bitLen hits.get ≤ T + 1 := (bitLen_le_succ _).trans (by omega)
    cases fin
    swap
    · simp only [↓reduceIte, Charged.steps_pure, costVp]; omega
    cases ab
    swap
    · simp only [↓reduceIte, Charged.steps_pure, costVp, Bool.false_eq_true]; omega
    simp only [Bool.false_eq_true, ↓reduceIte, Charged.steps_bind, costVb, steps_SNat_le,
      SNat.val_le]
    by_cases hf : Ph.Bret.get ≤ used.get
    · simp only [hf, decide_true, ↓reduceIte, Charged.steps_pure, costVp]; omega
    simp only [hf, decide_false, Bool.false_eq_true, ↓reduceIte, Charged.steps_bind, costVb,
      val_get, steps_get, steps_SNat_add, SNat.get_add, SNat.get_lit, hb1]
    have hw : WSize B (ws.getD stage default) :=
      getD_pred_of_forall (fun w => WSize B w) ws stage hws (by simp [WSize, default])
    have hs := hstep stage (by omega) _ hw S c
    generalize step C K tape stage (ws.getD stage default) S c = St at *
    obtain ⟨-, kc⟩ := kind_cost K (Charged.val St).1
    generalize hkv : Charged.val (kind K (Charged.val St).1) = k
    rcases k with _ | ⟨i, l⟩ | _ <;> dsimp only
    · simp only [Charged.steps_bind, costVb, steps_SNat_add, SNat.get_add, SNat.get_lit,
        steps_SNat_eq, SNat.val_eq, hb1]
      by_cases hd : hits.get + 1 = Ph.τ.get
      · simp only [hd, decide_true, ↓reduceIte, Charged.steps_bind, costVb, costVp,
          Charged.steps_pure, steps_idxEq, SNat.get_lit]
        refine ⟨⟨by omega, by simp, by simp only [SNat.get_add, SNat.get_lit]; omega⟩, by omega⟩
      · simp only [hd, decide_false, Bool.false_eq_true, ↓reduceIte, Charged.steps_pure, costVp]
        refine ⟨⟨by omega, by simp only [SNat.get_add, SNat.get_lit]; omega,
          by simp only [SNat.get_add, SNat.get_lit]; omega⟩, by omega⟩
    · simp only [Charged.steps_pure, costVp, SNat.get_add, SNat.get_lit]
      refine ⟨⟨by omega, by omega, by omega⟩, by omega⟩
    · simp only [Charged.steps_pure, costVp, SNat.get_add, SNat.get_lit]
      refine ⟨⟨by omega, by omega, by omega⟩, by omega⟩
  clear hR
  rw [hb0, hb1]
  have hbj : bitLen j ≤ T + 1 := (bitLen_le_succ _).trans (by omega)
  have : (Ph.BretN + 1) * (Sb + 10 * (T + 3) ^ 2) ≤ (T + 1) * (Sb + 10 * (T + 3) ^ 2) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- INTERNAL: the zero-count test, `p²` rounds. -/
theorem allPositive_le (T : ℕ) (K : Chain) (o : Obs) (hp : K.p ≤ T) (hn0 : o.n0.get ≤ T + 1)
    (hnT : ∀ row ∈ o.nT, ∀ c ∈ row, c.get ≤ T + 1) :
    Charged.steps rate (allPositive K o) ≤ T * (T * (6 * T + 8)) + T + 4 := by
  unfold allPositive
  simp only [Charged.steps_bind, costVb, steps_SNat_lit, steps_SNat_lt, SNat.val_lt,
    SNat.get_lit]
  have hb0 : bitLen 0 = 1 := by decide
  have hbn : bitLen o.n0.get ≤ T + 2 := (bitLen_le_succ _).trans (by omega)
  by_cases h0 : 0 < o.n0.get
  swap
  · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte, Charged.steps_pure]; omega
  simp only [h0, decide_true, ↓reduceIte]
  generalize hR : Charged.repeatFor _ K.p true = R
  have outer : Charged.steps rate R ≤ K.p * (T * (6 * T + 8)) := by
    subst hR
    refine (repeatFor_inv _ (fun _ (_ : Bool) => True) (T * (6 * T + 8)) K.p true trivial
      (fun i acc hi _ => ⟨trivial, ?_⟩)).2
    cases acc
    · simp
    simp only [↓reduceIte]
    refine le_trans (repeatFor_inv _ (fun _ (_ : Bool) => True) (6 * T + 8) K.p true trivial
      (fun l acc' hl _ => ⟨trivial, ?_⟩)).2 (Nat.mul_le_mul_right _ hp)
    cases acc'
    · simp
    simp only [↓reduceIte, Charged.steps_bind, costVb, steps_idxEq, val_idxEq]
    have hbi : bitLen i ≤ T + 1 := (bitLen_le_succ _).trans (by omega)
    have hbl : bitLen l ≤ T + 1 := (bitLen_le_succ _).trans (by omega)
    by_cases hd : i = l
    · simp only [hd, decide_true, ↓reduceIte, Charged.steps_pure]; omega
    simp only [hd, decide_false, Bool.false_eq_true, ↓reduceIte, Charged.steps_bind, costVb,
      steps_get2, steps_SNat_lt, SNat.get_lit, hb0]
    have hc := get2_pred (fun c : SNat => c.get ≤ T + 1) o.nT i l hnT (by simp)
    have : bitLen (get2 o.nT i l).val.get ≤ T + 2 := (bitLen_le_succ _).trans (by omega)
    omega
  have : K.p * (T * (6 * T + 8)) ≤ T * (T * (6 * T + 8)) := Nat.mul_le_mul_right _ hp
  rw [hb0]; omega

/-- INTERNAL: the multiplier update `w_il ← w_il n_0/n_il`: `p²` writes, each adding at most
`2T + 8` to the length of the entry it writes. -/
theorem updateW_le (T W : ℕ) (K : Chain) (w : List (List SRat)) (o : Obs) (hp : K.p ≤ T)
    (hW3 : 3 ≤ W) (hw : WSize W w) (hn0 : o.n0.get ≤ T + 1) (hnT : ∀ row ∈ o.nT, ∀ c ∈ row, c.get ≤ T + 1) :
    WSize (W + T * (T * (2 * T + 8))) (updateW K w o).val ∧
    Charged.steps rate (updateW K w o) ≤
      T * (T * (2 * (W + T * (T * (2 * T + 8)) + T + 8) * (T + 5) + 10 * T + 10)) + T + 2 := by
  unfold updateW
  simp only [Charged.steps_bind, costVb, steps_SNat_toRat, SNat.get_toRat]
  have hn0q : ratLen (o.n0.get : ℚ) ≤ T + 4 := by
    rw [ratLen_natCast]; have := bitLen_le_succ o.n0.get; omega
  have hbn : bitLen o.n0.get ≤ T + 2 := (bitLen_le_succ _).trans (by omega)
  have hWMd : W + T * (T * (2 * T + 8)) ≥ W := Nat.le_add_right _ _
  generalize hWM : W + T * (T * (2 * T + 8)) = WM at hWMd ⊢
  generalize hR : Charged.repeatFor _ K.p w = R
  have key : WSize (W + K.p * (T * (2 * T + 8))) R.val ∧
      Charged.steps rate R ≤ K.p * (T * (2 * (WM + T + 8) * (T + 5) + 10 * T + 10)) := by
    subst hR
    refine repeatFor_inv _ (fun i (acc : List (List SRat)) => WSize (W + i * (T * (2 * T + 8))) acc)
      (T * (2 * (WM + T + 8) * (T + 5) + 10 * T + 10)) K.p w (by simpa using hw) ?_
    intro i acc hi hacc
    have hiT : i < T := lt_of_lt_of_le hi hp
    generalize hR2 : Charged.repeatFor _ K.p acc = R2
    have key2 : WSize (W + i * (T * (2 * T + 8)) + K.p * (2 * T + 8)) R2.val ∧
        Charged.steps rate R2 ≤ K.p * (2 * (WM + T + 8) * (T + 5) + 10 * T + 10) := by
      subst hR2
      refine repeatFor_inv _ (fun l (acc' : List (List SRat)) =>
          WSize (W + i * (T * (2 * T + 8)) + l * (2 * T + 8)) acc')
        (2 * (WM + T + 8) * (T + 5) + 10 * T + 10) K.p acc (by simpa using hacc) ?_
      intro l acc' hl hacc'
      have hlT : l < T := lt_of_lt_of_le hl hp
      have hbi : bitLen i ≤ T + 1 := (bitLen_le_succ _).trans (by omega)
      have hbl : bitLen l ≤ T + 1 := (bitLen_le_succ _).trans (by omega)
      have hB : W + i * (T * (2 * T + 8)) + l * (2 * T + 8) + (2 * T + 8) ≤ WM := by
        rw [← hWM]
        have : i * (T * (2 * T + 8)) + T * (2 * T + 8) ≤ T * (T * (2 * T + 8)) := by
          have := Nat.mul_le_mul_right (T * (2 * T + 8)) (Nat.succ_le_of_lt hiT)
          rw [Nat.succ_mul] at this; exact this
        have : l * (2 * T + 8) + (2 * T + 8) ≤ T * (2 * T + 8) := by
          have := Nat.mul_le_mul_right (2 * T + 8) (Nat.succ_le_of_lt hlT)
          rw [Nat.succ_mul] at this; exact this
        omega
      simp only [Charged.steps_bind, costVb, steps_idxEq, val_idxEq]
      by_cases hd : i = l
      · simp only [hd, decide_true, ↓reduceIte, Charged.steps_pure, costVp]
        subst hd
        refine ⟨fun row h x hx => (hacc' row h x hx).trans (by rw [Nat.add_mul]; omega), by omega⟩
      simp only [hd, decide_false, Bool.false_eq_true, ↓reduceIte, Charged.steps_bind, costVb,
        steps_get2, steps_SNat_toRat, SNat.get_toRat, steps_SRat_mul, steps_SRat_div,
        SRat.get_mul, SRat.get_div, steps_set2]
      have hwl := get2_pred (fun x : SRat => ratLen x.get ≤ W + i * (T * (2 * T + 8)) +
        l * (2 * T + 8)) acc' i l hacc'
        (by simp only [SRat.get_default, ratLen_zero]; omega)
      have hc := get2_pred (fun c : SNat => c.get ≤ T + 1) o.nT i l hnT (by simp)
      have hcq : ratLen ((get2 o.nT i l).val.get : ℚ) ≤ T + 4 := by
        rw [ratLen_natCast]; have := bitLen_le_succ (get2 o.nT i l).val.get; omega
      have hcb : bitLen (get2 o.nT i l).val.get ≤ T + 2 := (bitLen_le_succ _).trans (by omega)
      have m1 := ratLen_mul_le (get2 acc' i l).val.get (o.n0.get : ℚ)
      have m2 := ratLen_div_le ((get2 acc' i l).val.get * (o.n0.get : ℚ))
        ((get2 o.nT i l).val.get : ℚ)
      refine ⟨set2_pred (fun x : SRat => ratLen x.get ≤ W + i * (T * (2 * T + 8)) +
          (l + 1) * (2 * T + 8)) _ _ _ _
          (fun row h x hx => (hacc' row h x hx).trans (by rw [Nat.add_mul]; omega))
          (by simp only [SRat.get_div, SRat.get_mul, SNat.get_toRat]; rw [Nat.add_mul]; omega), ?_⟩
      have e1 : (ratLen (Charged.val (get2 acc' i l)).get + 1) * (ratLen (o.n0.get : ℚ) + 1) ≤
          (WM + T + 8) * (T + 5) := Nat.mul_le_mul (by omega) (by omega)
      have e2 : (ratLen ((Charged.val (get2 acc' i l)).get * (o.n0.get : ℚ)) + 1) *
          (ratLen ((Charged.val (get2 o.nT i l)).get : ℚ) + 1) ≤ (WM + T + 8) * (T + 5) :=
        Nat.mul_le_mul (by omega) (by omega)
      have e3 : (WM + T + 8) * (T + 5) + (WM + T + 8) * (T + 5) = 2 * (WM + T + 8) * (T + 5) := by
        ring
      omega
    clear hR2
    obtain ⟨k1, k2⟩ := key2
    refine ⟨fun row h x hx => (k1 row h x hx).trans ?_, ?_⟩
    · have : K.p * (2 * T + 8) ≤ T * (2 * T + 8) := Nat.mul_le_mul_right _ hp
      rw [Nat.add_mul]; omega
    · have : K.p * (2 * (WM + T + 8) * (T + 5) + 10 * T + 10) ≤
          T * (2 * (WM + T + 8) * (T + 5) + 10 * T + 10) := Nat.mul_le_mul_right _ hp
      omega
  clear hR
  obtain ⟨k1, k2⟩ := key
  refine ⟨fun row h x hx => (k1 row h x hx).trans ?_, ?_⟩
  · rw [← hWM]; have := Nat.mul_le_mul_right (T * (2 * T + 8)) hp; omega
  · have : K.p * (T * (2 * (WM + T + 8) * (T + 5) + 10 * T + 10)) ≤
        T * (T * (2 * (WM + T + 8) * (T + 5) + 10 * T + 10)) := Nat.mul_le_mul_right _ hp
    omega

/-- INTERNAL: the length bound for `Σ G_j` after at most `T + 1` observations with
oracle outputs of length `≤ Q`. -/
def sgBound (T Q : ℕ) : ℕ := T + 2 * Q + 8 + 4 * (T + 1) * Q

/-- INTERNAL: the length bound for one ratio estimate `R̂_j`. -/
def rBound (T Q : ℕ) : ℕ := sgBound T Q + 3 * T + 10

/-- INTERNAL: the run invariant before phase `j`. -/
def RunInv (W0 Δ Rb j : ℕ) (st : Run) : Prop :=
  st.ws.length ≤ j + 1 ∧ (∀ w ∈ st.ws, WSize (W0 + j * Δ) w) ∧ ratLen st.prod.get ≤ 4 + j * Rb

/-- INTERNAL: `RunInv` is monotone in the phase index. -/
theorem RunInv.mono {W0 Δ Rb j : ℕ} {st : Run} (h : RunInv W0 Δ Rb j st) :
    RunInv W0 Δ Rb (j + 1) st :=
  ⟨by have := h.1; omega, fun w hw => (h.2.1 w hw).mono (by rw [Nat.add_mul]; omega),
    h.2.2.trans (by rw [Nat.add_mul]; omega)⟩

/-- INTERNAL: one phase keeps `RunInv` and costs at most `phaseBound`. -/
theorem phase_le (T Q Sb Mb B W0 : ℕ) (C : Ctx) (K : Chain) (Ph : Phase) (hT : 2 ≤ T)
    (hK : ChainSize T C K Ph)
    (hO : ∀ (x y : List SNat), ProfileValid C x y → ∀ (j' : ℕ), j' ≤ T → ∀ (tape : Coins ℕ) (cur : ℕ),
      Charged.steps rate (oracle C tape x y j' K.ξ K.ξ cur) ≤ Q ∧
      ratLen (oracle C tape x y j' K.ξ K.ξ cur).val.1.get ≤ Q)
    (tape : Coins ℕ)
    (hstep : ∀ (a : ℕ), a ≤ B → ∀ (w : List (List SRat)), WSize B w →
      ∀ (S : List Bool) (cur : ℕ), Charged.steps rate (step C K tape a w S cur) ≤ Sb)
    (hmu : ∀ cur, Charged.steps rate (mu0 K tape cur) ≤ Mb)
    (hW3 : 3 ≤ W0) (hWB : W0 + T * (T * (T * (2 * T + 8))) ≤ B) (hTB : T + 2 ≤ B)
    (j : ℕ) (hj : j < Ph.Hn) (st : Run)
    (hinv : RunInv W0 (T * (T * (2 * T + 8))) (rBound T Q) j st) :
    RunInv W0 (T * (T * (2 * T + 8))) (rBound T Q) (j + 1) (phase C K tape Ph j st).val ∧
    Charged.steps rate (phase C K tape Ph j st) ≤
      Mb + ((T + 1) * (Sb + 10 * (T + 3) ^ 2) + T + 5) + (T + 1) +
      ((T + 1) * (Sb + 200 * ((T + 2) * (Q + 2)) ^ 2) + 2 * T + 6) +
      (T * (T * (6 * T + 8)) + T + 4) + (T + 1) + (sgBound T Q + 1) * (T + 4) + (T + 2) +
      (T + 5) * (T + 4) + (sgBound T Q + T + 4) * (2 * T + 8) +
      (4 + T * rBound T Q + 1) * (rBound T Q + 1) + (2 * T + 2) +
      (T * (T * (2 * (B + T * (T * (2 * T + 8)) + T + 8) * (T + 5) + 10 * T + 10)) + T + 2) +
      (T + 2) := by
  have hHn := hK.Hn_le
  have hjT : j + 1 ≤ T := by omega
  obtain ⟨hlen, hws, hprod⟩ := hinv
  have hjΔ : W0 + j * (T * (T * (2 * T + 8))) ≤ B := by
    have := Nat.mul_le_mul_right (T * (T * (2 * T + 8))) (show j ≤ T by omega)
    omega
  have hwsB : ∀ w ∈ st.ws, WSize B w := fun w hw => (hws w hw).mono hjΔ
  unfold phase
  cases hab : st.aborted
  swap
  · simp only [↓reduceIte, Charged.steps_pure, costVp]
    exact ⟨RunInv.mono ⟨hlen, hws, hprod⟩, Nat.zero_le _⟩
  simp only [Bool.false_eq_true, ↓reduceIte, Charged.steps_bind, costVb]
  have hm := hmu st.cur
  generalize mu0 K tape st.cur = M0 at *
  have hr := restart_le T B Sb j C K Ph hT hK hTB (by omega) tape st.ws hwsB hstep
    (Charged.val M0).1 (Charged.val M0).2
  generalize restart C K tape Ph st.ws j (Charged.val M0).1 (Charged.val M0).2 = RS at *
  cases hra : (Charged.val RS).aborted
  swap
  · simp only [↓reduceIte, Charged.steps_pure, costVp]
    refine ⟨RunInv.mono ⟨hlen, hws, hprod⟩, ?_⟩
    omega
  simp only [Bool.false_eq_true, ↓reduceIte, Charged.steps_bind, costVb, val_get, steps_get]
  have hwj : WSize (W0 + j * (T * (T * (2 * T + 8)))) (st.ws.getD j default) :=
    getD_pred_of_forall _ st.ws j hws (by simp [WSize, default])
  obtain ⟨oi, oc⟩ := observe_le T Q Sb j C K Ph hT hK hO hjT tape (st.ws.getD j default)
    (fun S cur => hstep j (by omega) _ (hwj.mono hjΔ) S cur) (Charged.val RS).S (Charged.val RS).cur
  generalize observe C K tape Ph j (st.ws.getD j default) (Charged.val RS).S (Charged.val RS).cur
    = Ob at *
  have hsg : ratLen (Charged.val Ob).sumG.get ≤ sgBound T Q := by
    have h1 := ObsInv.ratLen_le oi
    have : bitLen (T + 1) ≤ T + 2 := bitLen_le_succ _
    have : (T + 1) * (2 * Q) = 2 * ((T + 1) * Q) := by ring
    unfold sgBound
    have : 4 * (T + 1) * Q = 4 * ((T + 1) * Q) := by ring
    omega
  obtain ⟨on0, onT, -, -⟩ := oi
  have hap := allPositive_le T K (Charged.val Ob) hK.p_le on0 onT
  generalize allPositive K (Charged.val Ob) = AP at *
  cases hpos : (Charged.val AP)
  · simp only [Bool.false_eq_true, ↓reduceIte, Charged.steps_pure, costVp]
    refine ⟨RunInv.mono ⟨hlen, hws, hprod⟩, ?_⟩
    omega
  simp only [↓reduceIte, Charged.steps_bind, costVb, steps_SNat_toRat, SNat.get_toRat,
    steps_SRat_div, SRat.get_div, steps_SRat_mul, SRat.get_mul, steps_idxLt, val_idxLt]
  -- sizes of the estimate
  have hNav : ratLen (Ph.Nav.get : ℚ) ≤ T + 3 := by
    rw [ratLen_natCast]; have := bitLen_le_succ Ph.Nav.get; have := hK.Nav_le; omega
  have hn0q : ratLen ((Charged.val Ob).n0.get : ℚ) ≤ T + 4 := by
    rw [ratLen_natCast]; have := bitLen_le_succ (Charged.val Ob).n0.get; omega
  have hbNav : bitLen Ph.Nav.get ≤ T + 1 := (bitLen_le_succ _).trans (by have := hK.Nav_le; omega)
  have hbn0 : bitLen (Charged.val Ob).n0.get ≤ T + 2 := (bitLen_le_succ _).trans (by omega)
  have hu := ratLen_div_le (Charged.val Ob).sumG.get (Ph.Nav.get : ℚ)
  have hp0 := ratLen_div_le ((Charged.val Ob).n0.get : ℚ) (Ph.Nav.get : ℚ)
  have hR := ratLen_div_le ((Charged.val Ob).sumG.get / Ph.Nav.get)
    (((Charged.val Ob).n0.get : ℚ) / Ph.Nav.get)
  have hRb : ratLen ((Charged.val Ob).sumG.get / Ph.Nav.get /
      (((Charged.val Ob).n0.get : ℚ) / Ph.Nav.get)) ≤ rBound T Q := by
    unfold rBound; omega
  have hpr := ratLen_mul_le st.prod.get ((Charged.val Ob).sumG.get / Ph.Nav.get /
      (((Charged.val Ob).n0.get : ℚ) / Ph.Nav.get))
  have hbj : bitLen (j + 1) ≤ T + 1 := (bitLen_le_succ _).trans (by omega)
  have hbH : bitLen Ph.Hn ≤ T + 1 := (bitLen_le_succ _).trans (by omega)
  have c1 : (ratLen (Charged.val Ob).sumG.get + 1) * (ratLen (Ph.Nav.get : ℚ) + 1) ≤
      (sgBound T Q + 1) * (T + 4) := Nat.mul_le_mul (by omega) (by omega)
  have c2 : (ratLen ((Charged.val Ob).n0.get : ℚ) + 1) * (ratLen (Ph.Nav.get : ℚ) + 1) ≤
      (T + 5) * (T + 4) := Nat.mul_le_mul (by omega) (by omega)
  have c3 : (ratLen ((Charged.val Ob).sumG.get / Ph.Nav.get) + 1) *
      (ratLen (((Charged.val Ob).n0.get : ℚ) / Ph.Nav.get) + 1) ≤
      (sgBound T Q + T + 4) * (2 * T + 8) := Nat.mul_le_mul (by omega) (by omega)
  have hjR : j * rBound T Q ≤ T * rBound T Q := Nat.mul_le_mul_right _ (by omega)
  have c4 : (ratLen st.prod.get + 1) * (ratLen ((Charged.val Ob).sumG.get / Ph.Nav.get /
      (((Charged.val Ob).n0.get : ℚ) / Ph.Nav.get)) + 1) ≤
      (4 + T * rBound T Q + 1) * (rBound T Q + 1) := Nat.mul_le_mul (by omega) (by omega)
  have hprod' : ratLen (st.prod.get * ((Charged.val Ob).sumG.get / Ph.Nav.get /
      (((Charged.val Ob).n0.get : ℚ) / Ph.Nav.get))) ≤ 4 + (j + 1) * rBound T Q := by
    rw [Nat.add_mul]; omega
  by_cases hmore : j + 1 < Ph.Hn
  · simp only [hmore, decide_true, ↓reduceIte, Charged.steps_bind, costVb, costVp,
      Charged.steps_pure, val_push, steps_push]
    obtain ⟨uw, uc⟩ := updateW_le T (W0 + j * (T * (T * (2 * T + 8)))) K (st.ws.getD j default)
      (Charged.val Ob) hK.p_le (by omega) hwj on0 onT
    have uc' : Charged.steps rate (updateW K (st.ws.getD j default) (Charged.val Ob)) ≤
        T * (T * (2 * (B + T * (T * (2 * T + 8)) + T + 8) * (T + 5) + 10 * T + 10)) + T + 2 := by
      refine uc.trans ?_
      gcongr
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simp only [List.length_append, List.length_singleton]; omega
    rotate_left
    · simpa only [SRat.get_mul, SRat.get_div, SNat.get_toRat] using hprod'
    · clear hO hstep hmu hpr hR hu hp0
      generalize (T + 1) * (Sb + 10 * (T + 3) ^ 2) = A1 at hr ⊢
      generalize (T + 1) * (Sb + 200 * ((T + 2) * (Q + 2)) ^ 2) = A2 at oc ⊢
      generalize T * (T * (6 * T + 8)) = A3 at hap ⊢
      generalize (sgBound T Q + 1) * (T + 4) = A4 at c1 ⊢
      generalize (T + 5) * (T + 4) = A5 at c2 ⊢
      generalize (sgBound T Q + T + 4) * (2 * T + 8) = A6 at c3 ⊢
      generalize (4 + T * rBound T Q + 1) * (rBound T Q + 1) = A7 at c4 ⊢
      generalize T * (T * (2 * (B + T * (T * (2 * T + 8)) + T + 8) * (T + 5) + 10 * T + 10)) = A8 at uc' ⊢
      linarith
    intro w hw
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact (hws w hw).mono (by rw [Nat.add_mul]; omega)
    · exact uw.mono (by rw [Nat.add_mul]; omega)
  · simp only [hmore, decide_false, Bool.false_eq_true, ↓reduceIte, Charged.steps_pure, costVp]
    refine ⟨⟨Nat.le_succ_of_le hlen, fun w hw => (hws w hw).mono (by rw [Nat.add_mul]; omega),
      by simpa only [SRat.get_mul, SRat.get_div, SNat.get_toRat] using hprod'⟩, ?_⟩
    clear hO hstep hmu hpr hR hu hp0
    generalize (T + 1) * (Sb + 10 * (T + 3) ^ 2) = A1 at hr ⊢
    generalize (T + 1) * (Sb + 200 * ((T + 2) * (Q + 2)) ^ 2) = A2 at oc ⊢
    generalize T * (T * (6 * T + 8)) = A3 at hap ⊢
    generalize (sgBound T Q + 1) * (T + 4) = A4 at c1 ⊢
    generalize (T + 5) * (T + 4) = A5 at c2 ⊢
    generalize (sgBound T Q + T + 4) * (2 * T + 8) = A6 at c3 ⊢
    generalize (4 + T * rBound T Q + 1) * (rBound T Q + 1) = A7 at c4 ⊢
    generalize T * (T * (2 * (B + T * (T * (2 * T + 8)) + T + 8) * (T + 5) + 10 * T + 10)) = A8 at ⊢
    linarith

/-- INTERNAL: the per-phase price bound of `phase_le`. -/
def phaseBound (T Q Sb Mb B : ℕ) : ℕ :=
  Mb + ((T + 1) * (Sb + 10 * (T + 3) ^ 2) + T + 5) + (T + 1) +
      ((T + 1) * (Sb + 200 * ((T + 2) * (Q + 2)) ^ 2) + 2 * T + 6) +
      (T * (T * (6 * T + 8)) + T + 4) + (T + 1) + (sgBound T Q + 1) * (T + 4) + (T + 2) +
      (T + 5) * (T + 4) + (sgBound T Q + T + 4) * (2 * T + 8) +
      (4 + T * rBound T Q + 1) * (rBound T Q + 1) + (2 * T + 2) +
      (T * (T * (2 * (B + T * (T * (2 * T + 8)) + T + 8) * (T + 5) + 10 * T + 10)) + T + 2) +
      (T + 2)

/-- INTERNAL: the run over `H ≤ T` phases, given step, `μ₀` and oracle bounds. -/
theorem annealRun_le (T Q Sb Mb : ℕ) (C : Ctx) (K : Chain) (Ph : Phase) (hT : 2 ≤ T)
    (hK : ChainSize T C K Ph)
    (hO : ∀ (x y : List SNat), ProfileValid C x y → ∀ (j' : ℕ), j' ≤ T → ∀ (tape : Coins ℕ) (cur : ℕ),
      Charged.steps rate (oracle C tape x y j' K.ξ K.ξ cur) ≤ Q ∧
      ratLen (oracle C tape x y j' K.ξ K.ξ cur).val.1.get ≤ Q)
    (tape : Coins ℕ)
    (hstep : ∀ (a : ℕ), a ≤ T + 1 + T * (T * (T * (2 * T + 8))) → ∀ (w : List (List SRat)),
      WSize (T + 1 + T * (T * (T * (2 * T + 8)))) w →
      ∀ (S : List Bool) (cur : ℕ), Charged.steps rate (step C K tape a w S cur) ≤ Sb)
    (hmu : ∀ cur, Charged.steps rate (mu0 K tape cur) ≤ Mb)
    (w0 : List (List SRat)) (hw0 : WSize T w0) (C0 : SRat) (hC0 : ratLen C0.get ≤ T) (cur : ℕ) :
    Charged.steps rate (annealRun C K tape Ph w0 C0 cur) ≤
      T * phaseBound T Q Sb Mb (T + 1 + T * (T * (T * (2 * T + 8)))) + 7 +
        (T + 1) * (T + 5 + T * rBound T Q) ∧
    ratLen (annealRun C K tape Ph w0 C0 cur).val.1.get ≤ T + 4 + T * rBound T Q := by
  unfold annealRun
  simp only [Charged.steps_bind, costVb, steps_SRat_lit, SRat.get_lit]
  have hr1 : ratLen (1 : ℚ) = 4 := by
    have h := ratLen_natCast 1; push_cast at h; rw [h]; decide
  have hHn := hK.Hn_le
  generalize hBd : T + 1 + T * (T * (T * (2 * T + 8))) = B at hstep ⊢
  have hWB : T + 1 + T * (T * (T * (2 * T + 8))) ≤ B := hBd.le
  have hTB : T + 2 ≤ B := by
    rw [← hBd]; have : 1 ≤ T * (T * (T * (2 * T + 8))) :=
      Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  generalize hR : Charged.repeatFor _ Ph.Hn _ = R
  have key : RunInv (T + 1) (T * (T * (2 * T + 8))) (rBound T Q) Ph.Hn R.val ∧
      Charged.steps rate R ≤ Ph.Hn * phaseBound T Q Sb Mb B := by
    subst hR
    refine repeatFor_inv _ (fun j st => RunInv (T + 1) (T * (T * (2 * T + 8))) (rBound T Q) j st)
      (phaseBound T Q Sb Mb B) Ph.Hn _ ?_ ?_
    · refine ⟨by simp, ?_, by simp [hr1]⟩
      intro w hw
      simp only [List.mem_singleton] at hw
      subst hw
      exact hw0.mono (by omega)
    · intro j st hj hst
      exact phase_le T Q Sb Mb B (T + 1) C K Ph hT hK hO tape hstep hmu (by omega) hWB hTB j hj st hst
  clear hR
  obtain ⟨⟨-, -, hprod⟩, hc⟩ := key
  have hHR : Ph.Hn * rBound T Q ≤ T * rBound T Q := Nat.mul_le_mul_right _ hHn
  have hHP : Ph.Hn * phaseBound T Q Sb Mb B ≤ T * phaseBound T Q Sb Mb B :=
    Nat.mul_le_mul_right _ hHn
  cases hab : R.val.aborted
  · simp only [Bool.false_eq_true, ↓reduceIte, Charged.steps_bind, costVb, costVp,
      Charged.steps_pure, steps_SRat_mul, SRat.get_mul, hr1]
    have hm := ratLen_mul_le C0.get R.val.prod.get
    have : (ratLen C0.get + 1) * (ratLen R.val.prod.get + 1) ≤ (T + 1) * (T + 5 + T * rBound T Q) :=
      Nat.mul_le_mul (by omega) (by omega)
    refine ⟨by omega, by omega⟩
  · simp only [↓reduceIte, Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SRat_lit,
      SRat.get_lit, hr1, ratLen_zero]
    refine ⟨by omega, by omega⟩

set_option maxHeartbeats 1000000 in
/-- INTERNAL: the run bound at one master scale `V ≥ 64`. -/
theorem run_poly (V : ℕ) (hV : 64 ≤ V) :
    V * phaseBound V V V V V + 7 + (V + 1) * (V + 5 + V * rBound V V) ≤ V ^ 10 := by
  obtain ⟨t, rfl⟩ : ∃ t, V = t + 64 := ⟨V - 64, by omega⟩
  unfold phaseBound rBound sgBound
  ring_nf
  omega

/-- INTERNAL: `phaseBound` and `rBound` are monotone. -/
theorem phaseBound_mono {T Q Sb Mb B V : ℕ} (hT : T ≤ V) (hQ : Q ≤ V) (hS : Sb ≤ V) (hM : Mb ≤ V)
    (hB : B ≤ V) : phaseBound T Q Sb Mb B ≤ phaseBound V V V V V ∧ rBound T Q ≤ rBound V V := by
  unfold phaseBound rBound sgBound
  constructor <;> gcongr

/-- **One annealing run is polynomial.**
INTERNAL: the run half of the resource bound of `lem:bounded-implementation`, for an
arbitrary chain satisfying `ChainSize`.
TEXLINE: sections/algorithm.tex:526-603 -/
theorem annealRun_cost_of : ∃ k : ℕ, ∀ (T : ℕ) (C : Ctx) (K : Chain) (Ph : Phase)
    (w0 : List (List SRat)) (C0 : SRat),
    2 ≤ T → CtxSize T C → PenaltyOK T C → ChainSize T C K Ph → WSize T w0 →
    ratLen C0.get ≤ T →
    ∀ (tape : Coins ℕ) (cur : ℕ),
      Charged.steps rate (annealRun C K tape Ph w0 C0 cur) ≤ T ^ k ∧
      ratLen (annealRun C K tape Ph w0 C0 cur).val.1.get ≤ T ^ k := by
  obtain ⟨k0, hO⟩ := oracle_cost
  obtain ⟨ks, hS⟩ := step_cost
  obtain ⟨km, hM⟩ := mu0_cost
  refine ⟨10 * (k0 + 8 * ks + km + 16), ?_⟩
  intro T C K Ph w0 C0 hT hC hpen hK hw0 hC0 tape cur
  have hT1 : 1 ≤ T := by omega
  have hB8 : T + 1 + T * (T * (T * (2 * T + 8))) ≤ T ^ 8 := by
    have h4 : 16 ≤ T ^ 4 := by
      have := Nat.pow_le_pow_left hT 4; norm_num at this; omega
    have : T ^ 8 = T ^ 4 * T ^ 4 := by ring
    have : T * (T * (T * (2 * T + 8))) + T + 1 ≤ 11 * T ^ 4 := by
      have : 2 * T ≤ T ^ 4 := by
        have e1 : T ^ 4 = T * T ^ 3 := by ring
        have e2 : 2 ^ 3 ≤ T ^ 3 := Nat.pow_le_pow_left hT 3
        rw [e1]; nlinarith
      have : T * (T * (T * (2 * T + 8))) = 2 * T ^ 4 + 8 * (T * T ^ 2) := by ring
      have : T * T ^ 2 ≤ T ^ 4 := by
        have : T * T ^ 2 = T ^ 3 := by ring
        rw [this]; exact Nat.pow_le_pow_right hT1 (by norm_num)
      omega
    nlinarith
  generalize hBd : T + 1 + T * (T * (T * (2 * T + 8))) = B at hB8
  have hTB : T ≤ B := by omega
  have hstep : ∀ (a : ℕ), a ≤ T + 1 + T * (T * (T * (2 * T + 8))) → ∀ (w : List (List SRat)),
      WSize (T + 1 + T * (T * (T * (2 * T + 8)))) w →
      ∀ (S : List Bool) (cur : ℕ), Charged.steps rate (step C K tape a w S cur) ≤ B ^ ks := by
    rw [hBd]
    intro a ha w hw S cur
    exact hS B C K Ph (by omega) (hC.mono hTB) (hpen.mono hTB) (hK.mono hTB) a ha w hw tape S cur
  have hO' : ∀ (x y : List SNat), ProfileValid C x y → ∀ (j : ℕ), j ≤ T →
      ∀ (tape : Coins ℕ) (cur : ℕ),
      Charged.steps rate (oracle C tape x y j K.ξ K.ξ cur) ≤ T ^ k0 ∧
      ratLen (oracle C tape x y j K.ξ K.ξ cur).val.1.get ≤ T ^ k0 :=
    fun x y hv j hj tape cur => hO T C hT hC hpen x y hv j hj K.ξ K.ξ hK.ξ_pos hK.ξ_pos
      hK.ξ_inv_le hK.ξ_inv_le hK.ξ_len hK.ξ_len tape cur
  obtain ⟨r1, r2⟩ := annealRun_le T (T ^ k0) (B ^ ks) (T ^ km) C K Ph hT hK hO' tape hstep
    (fun cur => hM T C K Ph hT hK tape cur) w0 hw0 C0 hC0 cur
  rw [hBd] at r1
  -- one master scale
  generalize hE : k0 + 8 * ks + km + 16 = E
  have hle : ∀ a, a ≤ E → T ^ a ≤ T ^ E := fun a ha => Nat.pow_le_pow_right hT1 ha
  have hV64 : 64 ≤ T ^ E := by
    have := Nat.pow_le_pow_left hT E
    have : 2 ^ 6 ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hTV : T ≤ T ^ E := by simpa using hle 1 (by omega)
  have hQV : T ^ k0 ≤ T ^ E := hle k0 (by omega)
  have hSV : B ^ ks ≤ T ^ E :=
    (Nat.pow_le_pow_left hB8 ks).trans (by rw [← pow_mul]; exact hle _ (by omega))
  have hMV : T ^ km ≤ T ^ E := hle km (by omega)
  have hBV : B ≤ T ^ E := hB8.trans (hle 8 (by omega))
  obtain ⟨m1, m2⟩ := phaseBound_mono hTV hQV hSV hMV hBV
  have hP := run_poly (T ^ E) hV64
  have hfin : T ^ (10 * E) = (T ^ E) ^ 10 := by rw [← pow_mul, Nat.mul_comm]
  rw [hfin]
  generalize T ^ E = V at *
  constructor
  · calc _ ≤ T * phaseBound T (T ^ k0) (B ^ ks) (T ^ km) B + 7 +
          (T + 1) * (T + 5 + T * rBound T (T ^ k0)) := r1
      _ ≤ V * phaseBound V V V V V + 7 + (V + 1) * (V + 5 + V * rBound V V) := by gcongr
      _ ≤ V ^ 10 := hP
  · calc _ ≤ T + 4 + T * rBound T (T ^ k0) := r2
      _ ≤ V + 4 + V * rBound V V := by gcongr
      _ ≤ V * phaseBound V V V V V + 7 + (V + 1) * (V + 5 + V * rBound V V) := by
          have : V + 4 + V * rBound V V ≤ (V + 1) * (V + 5 + V * rBound V V) :=
            (by omega : V + 4 + V * rBound V V ≤ V + 5 + V * rBound V V).trans
              (Nat.le_mul_of_pos_left _ (by omega))
          omega
      _ ≤ V ^ 10 := hP

end Cellcounting.Analysis
