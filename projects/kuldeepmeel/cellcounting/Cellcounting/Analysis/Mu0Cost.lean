import Cellcounting.Analysis.ChainSize

/-!
# A fresh `μ₀` draw costs a polynomial number of bit operations

`Cellcounting.Analysis.mu0_cost`: under `ChainSize T C K Ph`, the initial draw
`Program.mu0 K tape cur` costs at most `T ^ k` on every tape, for one fixed `k`.

Route: `nsm ≤ T` rounds; in each, `b ≤ T`, a `dyadicDraw_cost` draw on `[0, b + 1)`
(output `k ≤ b + 1`), `binom b k` (crude: the accumulator after `i` rounds is at most
`(b + k + 2)^i`, `binom_cost`), a draw on
`[0, C(b, k))` (output `≤ C(b, k)`), and an inner loop of `b` rounds, each one `binom`
and a write at position `2 (first + t) + 1 ≤ 4T + 1`; the rank and remaining count only
decrease.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Model
open Cellcounting.Program
open Cellcounting.Model.Operations
open Cellcounting.Interface

/-- INTERNAL: the binomial coefficient routine: value at most `(n + k + 2)^k` (the
accumulator gains at most a factor `n + k + 2` per round), price `≤ 12 (n + k + 2)⁴`. -/
theorem binom_cost (n k : SNat) :
    (binom n k).val.get ≤ (n.get + k.get + 2) ^ k.get ∧
    Charged.steps rate (binom n k) ≤ 12 * (n.get + k.get + 2) ^ 4 := by
  unfold binom
  simp only [Charged.steps_bind, costVb, steps_SNat_index, steps_SNat_lit, steps_SNat_sub,
    SNat.val_index, SNat.get_sub, SNat.get_lit]
  generalize hm : n.get + k.get + 2 = m
  generalize hR : Charged.repeatFor _ k.get (SNat.lit 1).val = R
  have key : (R.val.get ≤ m ^ k.get) ∧ Charged.steps rate R ≤ k.get * (10 * m ^ 3) := by
    subst hR
    refine repeatFor_inv _ (fun r (acc : SNat) => acc.get ≤ m ^ r) (10 * m ^ 3) k.get _
      (by simp) ?_
    intro r acc hr hacc
    simp only [Charged.steps_bind, costVb, steps_SNat_lit, steps_SNat_add, steps_SNat_mul,
      steps_SNat_div, SNat.get_lit, SNat.get_add, SNat.get_sub, SNat.get_mul, SNat.get_div] at hacc ⊢
    have hnum : n.get - k.get + (r + 1) ≤ m := by omega
    have hm2 : 2 ≤ m := by omega
    refine ⟨?_, ?_⟩
    · calc acc.get * (n.get - k.get + (r + 1)) / (r + 1) ≤ acc.get * (n.get - k.get + (r + 1)) :=
            Nat.div_le_self _ _
        _ ≤ m ^ r * m := Nat.mul_le_mul hacc hnum
        _ = m ^ (r + 1) := (pow_succ _ _).symm
    · have hL : bitLen m ≤ m + 1 := bitLen_le_succ m
      have e1 : bitLen (n.get - k.get + (r + 1)) ≤ m + 1 := (bitLen_mono hnum).trans hL
      have e2 : bitLen (r + 1) ≤ m + 1 := (bitLen_mono (by omega)).trans hL
      have e3 : bitLen (n.get - k.get) ≤ m + 1 := (bitLen_mono (by omega)).trans hL
      have e4 : bitLen acc.get ≤ m * (m + 1) + 2 :=
        (bitLen_mono hacc).trans ((bitLen_pow_le m r).trans
          (by have := Nat.mul_le_mul (show r ≤ m by omega) hL; omega))
      have e5 := bitLen_mul_le acc.get (n.get - k.get + (r + 1))
      generalize bitLen acc.get = a at *
      generalize bitLen (n.get - k.get + (r + 1)) = b at *
      generalize bitLen (acc.get * (n.get - k.get + (r + 1))) = c at *
      generalize bitLen (r + 1) = d at *
      have f1 : a * b ≤ (m * (m + 1) + 2) * (m + 1) := Nat.mul_le_mul e4 e1
      have f2 : c * d ≤ (m * (m + 1) + 2 + (m + 1)) * (m + 1) := Nat.mul_le_mul (by omega) e2
      have f3 : (m * (m + 1) + 2) * (m + 1) + (m * (m + 1) + 2 + (m + 1)) * (m + 1) + 3 * (m + 1)
          ≤ 10 * m ^ 3 := by nlinarith
      omega
  subst hR
  obtain ⟨k1, k2⟩ := key
  refine ⟨k1, ?_⟩
  have hm2 : 2 ≤ m := by omega
  have hL : bitLen m ≤ m + 1 := bitLen_le_succ m
  have e1 : bitLen k.get ≤ m + 1 := (bitLen_mono (by omega)).trans hL
  have e2 : bitLen n.get ≤ m + 1 := (bitLen_mono (by omega)).trans hL
  have hb1 : bitLen 1 = 2 := by decide
  have e3 : k.get * (10 * m ^ 3) ≤ m * (10 * m ^ 3) := Nat.mul_le_mul_right _ (by omega)
  have e4 : m * (10 * m ^ 3) + 3 * (m + 1) + 2 ≤ 12 * m ^ 4 := by
    have h4 : m ^ 4 = m * m ^ 3 := by ring
    have h8 : 2 ^ 3 ≤ m ^ 3 := Nat.pow_le_pow_left hm2 3
    rw [h4]; nlinarith
  omega

/-- INTERNAL: the length of a `binom` value. -/
theorem bitLen_binom_le (n k : SNat) :
    bitLen (binom n k).val.get ≤ k.get * (n.get + k.get + 2 + 1) + 2 :=
  (bitLen_mono (binom_cost n k).1).trans ((bitLen_pow_le _ _).trans
    (by have := Nat.mul_le_mul_left k.get (bitLen_le_succ (n.get + k.get + 2)); omega))

/-- INTERNAL: arithmetic for `mu0_cost`. -/
theorem mu0_arith (V T : ℕ) (hV : 16 ≤ V) (hVd : 8 * T = V) :
    V * (30 * V ^ 5) + 2 * T + 4 ≤ V ^ 8 := by
  have : V ^ 8 = V ^ 2 * V ^ 6 := by ring
  have : V * (30 * V ^ 5) = 30 * V ^ 6 := by ring
  have h256 : 16 ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left hV 2
  have : V ≤ V ^ 6 := Nat.le_self_pow (by norm_num) V
  nlinarith

/-- INTERNAL: the explicit bound behind `mu0_cost`. -/
theorem mu0_cost_le (T : ℕ) (C : Ctx) (K : Chain) (Ph : Phase) (hT : 2 ≤ T)
    (hK : ChainSize T C K Ph) (tape : Coins ℕ) (cur : ℕ) :
    Charged.steps rate (mu0 K tape cur) ≤ T ^ 32 := by
  unfold mu0
  simp only [Charged.steps_bind, costVb, steps_SNat_lit, steps_replicate, val_replicate]
  have hV : 16 ≤ 8 * T := by omega
  generalize hVd : 8 * T = V at hV
  have hξ : ratLen K.ξ.get ≤ T := hK.ξ_len
  generalize hR : Charged.repeatFor _ K.nsm _ = R
  have key : Charged.steps rate R ≤ K.nsm * (30 * V ^ 5) := by
    subst hR
    refine (repeatFor_inv _ (fun _ _ => True) (30 * V ^ 5) K.nsm _ trivial ?_).2
    rintro r ⟨S, c⟩ hr -
    simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, val_get, steps_get,
      steps_SNat_add, SNat.get_add, SNat.get_lit, steps_SNat_index, SNat.val_index]
    have hbT : (K.smallB.getD r default).get ≤ T :=
      getD_pred_of_forall (fun b : SNat => b.get ≤ T) _ _ hK.smallB_le (by simp)
    have hfT : K.cellFirst.getD r default ≤ T :=
      getD_pred_of_forall (fun f : ℕ => f ≤ T) _ _ hK.cellFirst_le (by simp [default])
    generalize K.smallB.getD r default = b at *
    generalize K.cellFirst.getD r default = f at *
    obtain ⟨d1v, d1c⟩ := dyadicDraw_cost tape (b.add (SNat.lit 1).val).val K.ξ c
    generalize dyadicDraw tape (b.add (SNat.lit 1).val).val K.ξ c = D1 at *
    simp only [SNat.get_add, SNat.get_lit] at d1v d1c
    generalize hk : (Charged.val D1).1 = k at *
    obtain ⟨bv, bc⟩ := binom_cost b k
    have bl := bitLen_binom_le b k
    obtain ⟨d2v, d2c⟩ := dyadicDraw_cost tape (binom b k).val K.ξ (Charged.val D1).2
    generalize dyadicDraw tape (binom b k).val K.ξ (Charged.val D1).2 = D2 at *
    generalize hcnt : (binom b k).val = cnt at *
    -- size bounds, all in terms of `V = 8T`
    have hk1 : k.get ≤ T + 1 := by omega
    have hbl : bitLen cnt.get ≤ V ^ 2 := by
      have : k.get * (b.get + k.get + 2 + 1) ≤ (T + 1) * (2 * T + 4) :=
        Nat.mul_le_mul hk1 (by omega)
      nlinarith
    clear bv bl hk
    generalize hR2 : Charged.repeatFor _ b.get (S, k, (Charged.val D2).1) = R2
    have key2 : Charged.steps rate R2 ≤ b.get * (20 * V ^ 4) := by
      subst hR2
      refine (repeatFor_inv _ (fun _ (st' : List Bool × SNat × SNat) =>
        st'.2.1.get ≤ T + 1 ∧ st'.2.2.get ≤ cnt.get) (20 * V ^ 4) b.get _ ⟨hk1, d2v⟩ ?_).2
      rintro t ⟨S', k1, rk⟩ ht ⟨hk1', hrk⟩
      dsimp only at hk1' hrk ⊢
      have hb0 : bitLen 0 = 1 := by decide
      have hb1 : bitLen 1 = 2 := by decide
      have hkl : bitLen k1.get ≤ T + 2 := (bitLen_le_succ _).trans (by omega)
      have htl : bitLen (t + 1) ≤ T + 1 := (bitLen_le_succ _).trans (by omega)
      have hbb : bitLen b.get ≤ T + 1 := (bitLen_le_succ _).trans (by omega)
      have hrl : bitLen rk.get ≤ V ^ 2 := (bitLen_mono hrk).trans hbl
      obtain ⟨-, bc'⟩ := binom_cost (b.sub (SNat.lit (t + 1)).val).val (k1.sub (SNat.lit 1).val).val
      have bl' := bitLen_binom_le (b.sub (SNat.lit (t + 1)).val).val (k1.sub (SNat.lit 1).val).val
      simp only [SNat.get_sub, SNat.get_lit] at bc' bl'
      have hcl : bitLen (binom (b.sub (SNat.lit (t + 1)).val).val
          (k1.sub (SNat.lit 1).val).val).val.get ≤ V ^ 2 := by
        have : (k1.get - 1) * (b.get - (t + 1) + (k1.get - 1) + 2 + 1) ≤ (T + 1) * (2 * T + 4) :=
          Nat.mul_le_mul (by omega) (by omega)
        nlinarith
      have hbc : Charged.steps rate (binom (b.sub (SNat.lit (t + 1)).val).val
          (k1.sub (SNat.lit 1).val).val) ≤ 12 * V ^ 4 :=
        bc'.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4))
      clear bc' bl'
      have hV2 : V ≤ V ^ 2 := Nat.le_self_pow (by norm_num) V
      have hV4 : V ^ 2 ≤ V ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
      by_cases h1 : 0 < k1.get
      · simp only [SNat.val_lt, SNat.get_lit, h1, decide_true, ↓reduceIte,
          Charged.steps_bind, costVb, costVp, steps_SNat_lt, steps_SNat_lit,
          steps_SNat_sub, SNat.get_sub, hb0, hb1]
        generalize binom (b.sub (SNat.lit (t + 1)).val).val (k1.sub (SNat.lit 1).val).val = Bn at *
        by_cases h2 : rk.get < (Charged.val Bn).get <;>
          simp only [SNat.val_lt, h2, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte,
            Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SNat_lt,
            steps_SNat_sub, SNat.get_sub, SNat.get_lit, steps_set] <;>
          clear d1c bc d2c <;>
          refine ⟨⟨by omega, by omega⟩, ?_⟩ <;> omega
      · simp only [SNat.val_lt, SNat.get_lit, h1, decide_false, Bool.false_eq_true, ↓reduceIte,
          Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SNat_lt, steps_set, hb0]
        clear d1c bc d2c
        refine ⟨⟨by omega, by omega⟩, ?_⟩; omega
    have hb1 : bitLen 1 = 2 := by decide
    have hbb : bitLen b.get ≤ T + 1 := (bitLen_le_succ _).trans (by omega)
    have e1 : (bitLen (b.get + 1) + ratLen K.ξ.get + 6) ^ 2 ≤ V ^ 2 :=
      Nat.pow_le_pow_left (by have := bitLen_le_succ (b.get + 1); omega) 2
    have e2 : (b.get + k.get + 2) ^ 4 ≤ V ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have hV2 : V ≤ V ^ 2 := Nat.le_self_pow (by norm_num) V
    have e3 : (bitLen cnt.get + ratLen K.ξ.get + 6) ^ 2 ≤ (2 * V ^ 2) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have e3' : (2 * V ^ 2) ^ 2 = 4 * V ^ 4 := by ring
    have e4 : b.get * (20 * V ^ 4) ≤ T * (20 * V ^ 4) := Nat.mul_le_mul_right _ hbT
    have e5 : V ^ 5 = 8 * (T * V ^ 4) := by rw [← hVd]; ring
    have e6 : 2 * V ^ 4 ≤ T * V ^ 4 := Nat.mul_le_mul_right _ hT
    have hV4 : V ^ 2 ≤ V ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have hrT : r < T := lt_of_lt_of_le hr hK.nsm_le
    clear hR2
    refine ⟨trivial, ?_⟩
    have hV1 : V ≤ V ^ 4 := hV2.trans hV4
    linarith
  clear hR
  have hb0 : bitLen 0 = 1 := by decide
  have hb1 : bitLen 1 = 2 := by decide
  rw [hb0, hb1]
  have hp := hK.p_le
  have e1 : K.nsm * (30 * V ^ 5) ≤ T * (30 * V ^ 5) := Nat.mul_le_mul_right _ hK.nsm_le
  have e2 : T * (30 * V ^ 5) ≤ V * (30 * V ^ 5) := Nat.mul_le_mul_right _ (by omega)
  have e3 := mu0_arith V T hV hVd
  have e4 : V ^ 8 ≤ T ^ 32 := hVd ▸ eight_mul_pow_le T hT 8
  linarith

/-- **A `μ₀` draw is polynomial.**
INTERNAL: the initial-sampling part of the resource bound of `lem:bounded-implementation`.
TEXLINE: sections/algorithm.tex:526-603 -/
theorem mu0_cost : ∃ k : ℕ, ∀ (T : ℕ) (C : Ctx) (K : Chain) (Ph : Phase),
    2 ≤ T → ChainSize T C K Ph → ∀ (tape : Coins ℕ) (cur : ℕ),
      Charged.steps rate (mu0 K tape cur) ≤ T ^ k :=
  ⟨32, fun T C K Ph hT hK tape cur => mu0_cost_le T C K Ph hT hK tape cur⟩

end Cellcounting.Analysis
