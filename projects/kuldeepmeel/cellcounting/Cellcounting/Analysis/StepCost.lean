import Cellcounting.Analysis.ChainSize

/-!
# One implemented Metropolis transition costs a polynomial number of bit operations

`Cellcounting.Analysis.step_cost`: under `CtxSize T C`, `PenaltyOK T C` and
`ChainSize T C K Ph`, for a stage `a ≤ T` and a multiplier table with `WSize T w`,
one transition `Program.step C K tape a w S cur` costs at most `T ^ k` on every tape,
from every state `S`, for one fixed `k`.

Route: the hold coin; two `dyadicDraw_cost` draws with `M = p_S ≤ T`, `ζ = ξ` (outputs
`≤ p_S`, so `nthWith` compares positions `≤ 2p` with targets `≤ T`); two `kind_cost`
calls; two `lam` evaluations, each one `profile_cost` (box-valid, so `oracle_cost`
applies at `T`: price and output length `≤ T ^ k₀`), `nsm` rounds of three `factQ_cost`
factors (lengths `≤ T² + 4`), and one `WSize.get2` multiplier;
the quotient `r = λ(S')/λ(S)` (length `≤ 2·poly(T)`); and `acceptTest` (one `pow2` of
`k_acc ≤ T`, one `natFloor`, `uniformBits_cost` with `k_acc` bits).
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Model
open Cellcounting.Program
open Cellcounting.Model.Operations
open Cellcounting.Interface

/-- INTERNAL: `nthWith` returns a position `≤ 2p` and costs `O(p (p + bitLen target))`. -/
theorem nthWith_cost (K : Chain) (S : List Bool) (val : Bool) (target : ℕ) :
    (nthWith K S val target).val ≤ 2 * K.p ∧
    Charged.steps rate (nthWith K S val target) ≤ 2 * K.p * (4 * K.p + 2 + bitLen target) := by
  unfold nthWith
  simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, add_zero]
  generalize hR : Charged.repeatFor _ (2 * K.p) (0, 0) = R
  subst hR
  refine (fun h => ⟨h.1.2, h.2⟩) (repeatFor_inv _ (fun r (st : ℕ × ℕ) => st.1 ≤ r ∧ st.2 ≤ r)
    (4 * K.p + 2 + bitLen target) (2 * K.p) _ (by simp) ?_)
  rintro e ⟨n, x⟩ he ⟨hn, hx⟩
  dsimp only at hn hx ⊢
  have hbn : bitLen n ≤ 2 * K.p + 1 := (bitLen_le_succ n).trans (by omega)
  rcases Bool.eq_false_or_eq_true (S.getD e default) with h1 | h1 <;>
  cases val <;>
  by_cases h2 : n = target <;>
    simp only [h1, h2, Charged.steps_bind, costVb, costVp, Charged.steps_pure, val_get, steps_get,
      val_idxEq, steps_idxEq, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte,
      Bool.true_eq_false] <;> (try subst h2) <;> omega

/-- INTERNAL: the dyadic acceptance test costs `O((ratLen c + k_acc)²)`. -/
theorem acceptTest_cost (K : Chain) (tape : Coins ℕ) (c : SRat) (cur : ℕ) :
    Charged.steps rate (acceptTest K tape c cur) ≤
      10 * (ratLen c.get + K.kAccS.get + K.kAcc + 8) ^ 2 := by
  unfold acceptTest
  simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SNat_pow2,
    steps_SNat_toRat, steps_SRat_mul, steps_SRat_natFloor, steps_SNat_lt, SNat.get_pow2,
    SNat.get_toRat, SRat.get_mul, SRat.get_natFloor, add_zero]
  obtain ⟨hY, -, hU⟩ := uniformBits_cost tape K.kAcc cur
  generalize uniformBits tape K.kAcc cur = U at *
  generalize hYd : (Charged.val U).1.get = Y at hY ⊢
  have hYb : bitLen Y ≤ K.kAcc + 1 := bitLen_le_of_lt_two_pow hY
  have h2k : bitLen (2 ^ K.kAccS.get) = K.kAccS.get + 2 := bitLen_two_pow _
  have hr2 : ratLen ((2 ^ K.kAccS.get : ℕ) : ℚ) = K.kAccS.get + 4 := by
    rw [ratLen_natCast, h2k]
  have hrt : ratLen (c.get * ((2 ^ K.kAccS.get : ℕ) : ℚ)) ≤ ratLen c.get + K.kAccS.get + 4 := by
    have := ratLen_mul_le c.get ((2 ^ K.kAccS.get : ℕ) : ℚ); omega
  have hm := bitLen_natFloor_le (c.get * ((2 ^ K.kAccS.get : ℕ) : ℚ))
  generalize ratLen (c.get * ((2 ^ K.kAccS.get : ℕ) : ℚ)) = rt at *
  generalize bitLen ⌊c.get * ((2 ^ K.kAccS.get : ℕ) : ℚ)⌋₊ = bm at *
  rw [hr2, h2k]
  generalize ratLen c.get = rc at *
  generalize K.kAccS.get = kS at *
  generalize K.kAcc = kA at *
  generalize Charged.steps rate U = sU at *
  have e1 : (rc + 1) * (kS + 4 + 1) ≤ (rc + kS + kA + 8) * (rc + kS + kA + 8) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e2 : (rt + 1) * (rt + 1) ≤ (rc + kS + kA + 8) * (rc + kS + kA + 8) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e3 : kA * (4 * kA + 8) ≤ (rc + kS + kA + 8) * (4 * (rc + kS + kA + 8)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e4 : (rc + kS + kA + 8) ^ 2 = (rc + kS + kA + 8) * (rc + kS + kA + 8) := sq _
  rw [e4]
  nlinarith

/-- INTERNAL: arithmetic for `lam_cost_le`. -/
theorem lam_arith (Q F : ℕ) (hF : 1 ≤ F) : Q + 4 * F + 1 ≤ (Q + 1) * (5 * F) := by
  nlinarith

/-- INTERNAL: one evaluation of the implemented `λ(S)`, given an oracle bound `Q`: price
`≤ 80 (Q + 1)(T + 4)⁶`, length `≤ Q + 5 (T + 4)³`. -/
theorem lam_cost_le (T Q : ℕ) (C : Ctx) (K : Chain) (Ph : Phase) (hT : 2 ≤ T)
    (hK : ChainSize T C K Ph)
    (hO : ∀ (x y : List SNat), ProfileValid C x y → ∀ (j : ℕ), j ≤ T → ∀ (tape : Coins ℕ) (cur : ℕ),
      Charged.steps rate (oracle C tape x y j K.ξ K.ξ cur) ≤ Q ∧
      ratLen (oracle C tape x y j K.ξ K.ξ cur).val.1.get ≤ Q)
    (a : ℕ) (ha : a ≤ T) (w : List (List SRat)) (hw : WSize T w) (S : List Bool) (k : Kind)
    (hk : ∀ i l, k = .defect i l → i < K.p ∧ l < K.p) (tape : Coins ℕ) (cur : ℕ) :
    Charged.steps rate (lam C K tape S k a w cur) ≤ 80 * ((Q + 1) * (T + 4) ^ 6) ∧
    ratLen (lam C K tape S k a w cur).val.1.get ≤ Q + 5 * (T + 4) ^ 3 := by
  unfold lam
  simp only [Charged.steps_bind, costVb, costVp, steps_SRat_lit, SRat.get_lit]
  obtain ⟨hpv, hpb, hpc⟩ := profile_cost hK S
  obtain ⟨hoc, hol⟩ := hO _ _ hpv a ha tape cur
  generalize profile K S = P at *
  generalize oracle C tape (Charged.val P).1 (Charged.val P).2 a K.ξ K.ξ cur = O at *
  have hE : T * T + 5 ≤ (T + 4) ^ 2 := by nlinarith
  have hF : T * T + 4 ≤ (T + 4) ^ 3 := by nlinarith
  have hEF : (T + 4) ^ 2 * (T + 4) ^ 3 = (T + 4) ^ 5 := by ring
  have h45 : (T + 4) ^ 4 ≤ (T + 4) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h15 : T + 4 ≤ (T + 4) ^ 5 := Nat.le_self_pow (by norm_num) _
  have hr1 : ratLen (1 : ℚ) = 4 := by
    have h := ratLen_natCast 1; push_cast at h; rw [h]; decide
  generalize hR : Charged.repeatFor _ K.nsm (SRat.lit 1).val = R
  have key : (ratLen R.val.get ≤ 4 + K.nsm * (3 * (T * T + 4))) ∧
      Charged.steps rate R ≤ K.nsm * (25 * (T + 4) ^ 5) := by
    subst hR
    refine repeatFor_inv _ (fun r (acc : SRat) => ratLen acc.get ≤ 4 + r * (3 * (T * T + 4)))
      (25 * (T + 4) ^ 5) K.nsm _ (by simp [hr1]) ?_
    intro r acc hr hacc
    simp only [Charged.steps_bind, costVb, val_get, steps_get, steps_SRat_mul, steps_SRat_div,
      SRat.get_mul, SRat.get_div] at hacc ⊢
    have hrT : r < T := lt_of_lt_of_le hr hK.nsm_le
    have hA : ratLen acc.get ≤ 4 * (T + 4) ^ 3 := by
      have : r * (3 * (T * T + 4)) ≤ T * (3 * (T * T + 4)) := Nat.mul_le_mul_right _ hrT.le
      nlinarith
    have fq : ∀ v : SNat, v.get ≤ T → ratLen (factQ v).val.get ≤ T * T + 4 ∧
        Charged.steps rate (factQ v) ≤ (T + 4) ^ 4 := by
      intro v hv
      obtain ⟨-, h2, h3⟩ := factQ_cost v
      exact ⟨h2.trans (by nlinarith), h3.trans (Nat.pow_le_pow_left (by omega) 4)⟩
    obtain ⟨x1, x2⟩ := fq _ (hpb r).1
    obtain ⟨y1, y2⟩ := fq _ (hpb r).2
    obtain ⟨b1, b2⟩ := fq (K.smallB.getD r default)
      (getD_pred_of_forall (fun b : SNat => b.get ≤ T) _ _ hK.smallB_le (by simp))
    generalize factQ ((Charged.val P).1.getD r default) = FX at *
    generalize factQ ((Charged.val P).2.getD r default) = FY at *
    generalize factQ (K.smallB.getD r default) = FB at *
    have m1 := ratLen_mul_le acc.get (Charged.val FX).get
    have m2 := ratLen_mul_le (acc.get * (Charged.val FX).get) (Charged.val FY).get
    have m3 := ratLen_div_le (acc.get * (Charged.val FX).get * (Charged.val FY).get) (Charged.val FB).get
    refine ⟨by rw [Nat.add_mul]; omega, ?_⟩
    have c1 : (ratLen acc.get + 1) * (ratLen (Charged.val FX).get + 1) ≤
        (5 * (T + 4) ^ 3) * (T + 4) ^ 2 := Nat.mul_le_mul (by omega) (by omega)
    have c2 : (ratLen (acc.get * (Charged.val FX).get) + 1) * (ratLen (Charged.val FY).get + 1) ≤
        (6 * (T + 4) ^ 3) * (T + 4) ^ 2 := Nat.mul_le_mul (by omega) (by omega)
    have c3 : (ratLen (acc.get * (Charged.val FX).get * (Charged.val FY).get) + 1) *
        (ratLen (Charged.val FB).get + 1) ≤ (7 * (T + 4) ^ 3) * (T + 4) ^ 2 :=
      Nat.mul_le_mul (by omega) (by omega)
    clear m1 m2 m3 hacc hA
    nlinarith
  clear hR
  obtain ⟨k1, k2⟩ := key
  have hn := hK.nsm_le
  have hfac : ratLen R.val.get ≤ 4 * (T + 4) ^ 3 := by
    have : K.nsm * (3 * (T * T + 4)) ≤ T * (3 * (T * T + 4)) := Nat.mul_le_mul_right _ hn
    nlinarith
  have hfacc : Charged.steps rate R ≤ 25 * (T + 4) ^ 6 := by
    have : K.nsm * (25 * (T + 4) ^ 5) ≤ (T + 4) * (25 * (T + 4) ^ 5) :=
      Nat.mul_le_mul_right _ (by omega)
    have : (T + 4) * (25 * (T + 4) ^ 5) = 25 * (T + 4) ^ 6 := by ring
    omega
  have hf := ratLen_mul_le (Charged.val O).1.get R.val.get
  have hpc' : 40 * (T + 1) ^ 2 ≤ 40 * (T + 4) ^ 6 :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) 2).trans
      (Nat.pow_le_pow_right (by omega) (by omega)))
  have hm1 : (ratLen (Charged.val O).1.get + 1) * (ratLen R.val.get + 1) ≤
      (Q + 1) * (5 * (T + 4) ^ 3) := Nat.mul_le_mul (by omega) (by omega)
  have h36 : (T + 4) ^ 3 ≤ (T + 4) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h16 : T + 4 ≤ (T + 4) ^ 6 := Nat.le_self_pow (by norm_num) _
  have hQ6 : (T + 4) ^ 6 ≤ (Q + 1) * (T + 4) ^ 6 := Nat.le_mul_of_pos_left _ (by omega)
  have hQ3 : (Q + 1) * (5 * (T + 4) ^ 3) ≤ 5 * ((Q + 1) * (T + 4) ^ 6) := by
    rw [Nat.mul_left_comm]; exact Nat.mul_le_mul_left 5 (Nat.mul_le_mul_left _ h36)
  have hQ : Q ≤ (Q + 1) * (T + 4) ^ 6 :=
    (Nat.le_succ Q).trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega)))
  rcases k with _ | ⟨i, l⟩ | _
  · dsimp only
    simp only [Charged.steps_pure, costVp, hr1, steps_SRat_mul, SRat.get_mul]
    clear hO hpv hpb hw hk
    refine ⟨by omega, by omega⟩
  · obtain ⟨hi, hl⟩ := hk i l rfl
    have hip : i < T := lt_of_lt_of_le hi hK.p_le
    have hlp : l < T := lt_of_lt_of_le hl hK.p_le
    have hwl := (hw.mono (Nat.le_succ T)).get2 (by omega) i l
    dsimp only
    simp only [get2, Charged.steps_bind, costVb, costVp, Charged.steps_pure, val_get, steps_get,
      steps_SRat_mul, SRat.get_mul, hr1]
    have hg := ratLen_mul_le ((Charged.val O).1.get * R.val.get)
      ((w.getD i default).getD l default).get
    have hm2 : (ratLen ((Charged.val O).1.get * R.val.get) + 1) *
        (ratLen ((w.getD i default).getD l default).get + 1) ≤
        ((Q + 1) * (5 * (T + 4) ^ 3)) * (T + 4) :=
      Nat.mul_le_mul ((by omega : _ ≤ Q + 4 * (T + 4) ^ 3 + 1).trans
        (lam_arith Q _ (Nat.one_le_pow _ _ (by omega)))) (by omega)
    have hm3 : ((Q + 1) * (5 * (T + 4) ^ 3)) * (T + 4) ≤ 5 * ((Q + 1) * (T + 4) ^ 6) := by
      have : (T + 4) ^ 3 * (T + 4) ≤ (T + 4) ^ 6 := by
        rw [← pow_succ]; exact Nat.pow_le_pow_right (by omega) (by omega)
      calc ((Q + 1) * (5 * (T + 4) ^ 3)) * (T + 4) = 5 * ((Q + 1) * ((T + 4) ^ 3 * (T + 4))) := by
            ring
        _ ≤ 5 * ((Q + 1) * (T + 4) ^ 6) := Nat.mul_le_mul_left 5 (Nat.mul_le_mul_left _ this)
    clear hO hpv hpb hw hk
    refine ⟨by omega, ?_⟩
    have : T + 1 ≤ (T + 4) ^ 3 := (by omega : T + 1 ≤ T + 4).trans (Nat.le_self_pow (by norm_num) _)
    omega
  · dsimp only
    simp only [Charged.steps_pure, costVp, hr1, steps_SRat_mul, SRat.get_mul]
    clear hO hpv hpb hw hk
    refine ⟨by omega, by omega⟩

/-- INTERNAL: one implemented transition, given an oracle bound `Q`. -/
theorem step_cost_le (T Q : ℕ) (C : Ctx) (K : Chain) (Ph : Phase) (hT : 2 ≤ T)
    (hK : ChainSize T C K Ph)
    (hO : ∀ (x y : List SNat), ProfileValid C x y → ∀ (j : ℕ), j ≤ T → ∀ (tape : Coins ℕ) (cur : ℕ),
      Charged.steps rate (oracle C tape x y j K.ξ K.ξ cur) ≤ Q ∧
      ratLen (oracle C tape x y j K.ξ K.ξ cur).val.1.get ≤ Q)
    (a : ℕ) (ha : a ≤ T) (w : List (List SRat)) (hw : WSize T w) (tape : Coins ℕ)
    (S : List Bool) (cur : ℕ) :
    Charged.steps rate (step C K tape a w S cur) ≤ 4096 * ((Q + 1) * (T + 4) ^ 6) ^ 2 := by
  unfold step coin
  simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_flip]
  have hZ1 : 1 ≤ ((Q + 1) * (T + 4) ^ 6) ^ 2 :=
    Nat.one_le_pow _ _ (Nat.mul_pos (by omega) (Nat.pow_pos (by omega)))
  by_cases h : (Coins.flip cur tape : Prog Bool).val = true
  · simp only [h, ↓reduceIte, Charged.steps_pure]; omega
  simp only [h, Bool.false_eq_true, ↓reduceIte]
  simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, SNat.val_index,
    steps_SNat_index, val_set, steps_set]
  obtain ⟨u1v, u1c⟩ := dyadicDraw_cost tape K.pS K.ξ (cur + 1)
  generalize dyadicDraw tape K.pS K.ξ (cur + 1) = D1 at *
  obtain ⟨u2v, u2c⟩ := dyadicDraw_cost tape K.pS K.ξ (Charged.val D1).2
  generalize dyadicDraw tape K.pS K.ξ (Charged.val D1).2 = D2 at *
  obtain ⟨n1v, n1c⟩ := nthWith_cost K S true (Charged.val D1).1.get
  obtain ⟨n2v, n2c⟩ := nthWith_cost K S false (Charged.val D2).1.get
  generalize nthWith K S true (Charged.val D1).1.get = N1 at *
  generalize nthWith K S false (Charged.val D2).1.get = N2 at *
  obtain ⟨kd', kc'⟩ := kind_cost K (((S.set (Charged.val N1) false).set (Charged.val N2) true))
  generalize ((S.set (Charged.val N1) false).set (Charged.val N2) true) = S' at *
  -- the scale `Z = (Q + 1)(T + 4)^6`
  have hp := hK.p_le
  have hpS := hK.pS_le
  have hξ := hK.ξ_len
  have hkA := hK.kAcc_le
  have hkS := hK.kAccS_le
  have hT6 : (T + 4) ^ 6 ≤ (Q + 1) * (T + 4) ^ 6 := Nat.le_mul_of_pos_left _ (by omega)
  have hQZ : Q ≤ (Q + 1) * (T + 4) ^ 6 :=
    (Nat.le_succ Q).trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega)))
  have h26 : (T + 4) ^ 2 ≤ (T + 4) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h36 : (T + 4) ^ 3 ≤ (T + 4) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h16 : T + 4 ≤ (T + 4) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hsq : (T + 2) ^ 2 ≤ (T + 4) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hZZ : (Q + 1) * (T + 4) ^ 6 ≤ ((Q + 1) * (T + 4) ^ 6) ^ 2 := Nat.le_self_pow (by norm_num) _
  generalize hZd : (Q + 1) * (T + 4) ^ 6 = Z at *
  have hZsq : Z ^ 2 = Z * Z := sq Z
  -- outer draws and searches
  have hb1 : bitLen K.pS.get ≤ T + 1 := (bitLen_le_succ _).trans (by omega)
  have hd : (bitLen K.pS.get + ratLen K.ξ.get + 6) ^ 2 ≤ (T + 4) ^ 2 * 4 := by
    rw [show (T + 4) ^ 2 * 4 = (2 * (T + 4)) ^ 2 by ring]
    exact Nat.pow_le_pow_left (by omega) 2
  have hu1 : bitLen (Charged.val D1).1.get ≤ T + 1 := (bitLen_mono u1v).trans hb1
  have hu2 : bitLen (Charged.val D2).1.get ≤ T + 1 := (bitLen_mono u2v).trans hb1
  have hn1 : 2 * K.p * (4 * K.p + 2 + bitLen (Charged.val D1).1.get) ≤ 2 * T * (5 * T + 3) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hn2 : 2 * K.p * (4 * K.p + 2 + bitLen (Charged.val D2).1.get) ≤ 2 * T * (5 * T + 3) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hn3 : 2 * T * (5 * T + 3) ≤ 10 * (T + 4) ^ 2 := by nlinarith
  have hk' : 6 * (K.p + 2) ^ 2 ≤ 6 * (T + 4) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have hZ6 : (T + 4) ^ 6 ≤ Z := hT6
  clear u1v u2v
  generalize Charged.steps rate D1 = sD1 at *
  generalize Charged.steps rate D2 = sD2 at *
  generalize Charged.steps rate N1 = sN1 at *
  generalize Charged.steps rate N2 = sN2 at *
  generalize Charged.steps rate (kind K S') = sK' at *
  generalize hk'v : Charged.val (kind K S') = k' at kd' ⊢
  rcases k' with _ | ⟨i, l⟩ | _ <;> dsimp only
  rotate_left 2
  · simp only [Charged.steps_pure]; clear hO; omega
  all_goals
    obtain ⟨kd, kc⟩ := kind_cost K S
    simp only [Charged.steps_bind, costVb, costVp]
    generalize hk1 : Charged.val (kind K S) = k1 at kd
    obtain ⟨l1c, l1v⟩ := lam_cost_le T Q C K Ph hT hK hO a ha w hw S' _ kd' tape (Charged.val D2).2
    generalize lam C K tape S' _ a w (Charged.val D2).2 = L1 at *
    obtain ⟨l2c, l2v⟩ := lam_cost_le T Q C K Ph hT hK hO a ha w hw S _ kd tape (Charged.val L1).2
    generalize lam C K tape S k1 a w (Charged.val L1).2 = L2 at *
    clear hO
    rw [hZd] at l1c l2c
    have hr1 : ratLen (1 : ℚ) = 4 := by
      have h := ratLen_natCast 1; push_cast at h; rw [h]; decide
    have hpp : ∀ (c : Bool) (x y : List Bool × ℕ),
        Charged.steps rate (if c = true then pure x else pure y : Prog (List Bool × ℕ)) = 0 := by
      intro c x y; cases c <;> simp
    simp only [steps_SRat_div, steps_SRat_lit, steps_SRat_le, SRat.get_div, SRat.get_lit,
      SRat.val_le, hr1]
    have hrr := ratLen_div_le (Charged.val L1).1.get (Charged.val L2).1.get
    have hL1 : ratLen (Charged.val L1).1.get ≤ 6 * Z := by omega
    have hL2 : ratLen (Charged.val L2).1.get ≤ 6 * Z := by omega
    have hdiv : (ratLen (Charged.val L1).1.get + 1) * (ratLen (Charged.val L2).1.get + 1) ≤
        (7 * Z) * (7 * Z) := Nat.mul_le_mul (by omega) (by omega)
    have hacc1 := acceptTest_cost K tape (SRat.lit 1).val (Charged.val L2).2
    have hacc2 := acceptTest_cost K tape ((Charged.val L1).1.div (Charged.val L2).1).val
      (Charged.val L2).2
    simp only [SRat.get_lit, SRat.get_div, hr1] at hacc1 hacc2
    have ha1 : (4 + K.kAccS.get + K.kAcc + 8) ^ 2 ≤ (14 * Z) * (14 * Z) := by
      rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
    have ha2 : (ratLen ((Charged.val L1).1.get / (Charged.val L2).1.get) + K.kAccS.get + K.kAcc + 8) ^ 2
        ≤ (14 * Z) * (14 * Z) := by
      rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
    generalize acceptTest K tape (SRat.lit 1).val (Charged.val L2).2 = A1 at *
    generalize acceptTest K tape ((Charged.val L1).1.div (Charged.val L2).1).val
      (Charged.val L2).2 = A2 at *
    by_cases hc : (1 : ℚ) ≤ (Charged.val L1).1.get / (Charged.val L2).1.get <;>
      simp only [hc, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true,
        Charged.steps_bind, hpp, add_zero]
    all_goals
      have hy : (T + 4) ^ 2 ≤ Z := h26.trans hZ6
      have hle : (4 + 1) * (ratLen ((Charged.val L1).1.get / (Charged.val L2).1.get) + 1) ≤
          60 * Z + 5 := by omega
      linarith

/-- INTERNAL: exponent arithmetic for `step_cost`. -/
theorem step_arith (T k0 : ℕ) (hT : 2 ≤ T) :
    4096 * ((T ^ k0 + 1) * (T + 4) ^ 6) ^ 2 ≤ T ^ (2 * k0 + 50) := by
  have h1 : 1 ≤ T ^ k0 := Nat.one_le_pow _ _ (by omega)
  have a1 : T ^ k0 + 1 ≤ T ^ (k0 + 1) := by rw [pow_succ]; nlinarith
  have a2 : (T + 4) ^ 6 ≤ T ^ 18 := by
    rw [show 18 = 3 * 6 from rfl, pow_mul]
    apply Nat.pow_le_pow_left
    have : 2 ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hT 2
    have : T ^ 3 = T * T ^ 2 := by ring
    nlinarith
  have a3 : 4096 ≤ T ^ 12 := by
    have := Nat.pow_le_pow_left hT 12; norm_num at this ⊢; omega
  calc 4096 * ((T ^ k0 + 1) * (T + 4) ^ 6) ^ 2 ≤ T ^ 12 * (T ^ (k0 + 1) * T ^ 18) ^ 2 :=
        Nat.mul_le_mul a3 (Nat.pow_le_pow_left (Nat.mul_le_mul a1 a2) 2)
    _ = T ^ (2 * k0 + 50) := by rw [← pow_add, ← pow_mul, ← pow_add]; ring_nf

/-- **One transition is polynomial.**
INTERNAL: the per-transition part of the resource bound of `lem:bounded-implementation`.
TEXLINE: sections/algorithm.tex:565-580 (oracle outputs, factorial factor and
multipliers give every Metropolis ratio and threshold comparison polynomial operands) -/
theorem step_cost : ∃ k : ℕ, ∀ (T : ℕ) (C : Ctx) (K : Chain) (Ph : Phase),
    2 ≤ T → CtxSize T C → PenaltyOK T C → ChainSize T C K Ph →
    ∀ (a : ℕ), a ≤ T → ∀ (w : List (List SRat)), WSize T w →
    ∀ (tape : Coins ℕ) (S : List Bool) (cur : ℕ),
      Charged.steps rate (step C K tape a w S cur) ≤ T ^ k := by
  obtain ⟨k0, hO⟩ := oracle_cost
  refine ⟨2 * k0 + 50, ?_⟩
  intro T C K Ph hT hC hpen hK a ha w hw tape S cur
  have hO' : ∀ (x y : List SNat), ProfileValid C x y → ∀ (j : ℕ), j ≤ T →
      ∀ (tape : Coins ℕ) (cur : ℕ),
      Charged.steps rate (oracle C tape x y j K.ξ K.ξ cur) ≤ T ^ k0 ∧
      ratLen (oracle C tape x y j K.ξ K.ξ cur).val.1.get ≤ T ^ k0 :=
    fun x y hv j hj tape cur => hO T C hT hC hpen x y hv j hj K.ξ K.ξ hK.ξ_pos hK.ξ_pos
      hK.ξ_inv_le hK.ξ_inv_le hK.ξ_len hK.ξ_len tape cur
  exact (step_cost_le T (T ^ k0) C K Ph hT hK hO' a ha w hw tape S cur).trans (step_arith T k0 hT)

end Cellcounting.Analysis
