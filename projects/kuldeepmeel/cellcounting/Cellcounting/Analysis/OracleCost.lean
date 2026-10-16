import Cellcounting.Analysis.CostScale
import Cellcounting.Analysis.PenaltyCost

/-!
# One weight-oracle call costs a polynomial number of bit operations

`Cellcounting.Analysis.oracle_cost`: for any context whose sizes are bounded by
`S` (`CtxSize`) and whose penalty is bounded by `S` on the extended box
(`PenaltyOK`), one call `Program.oracle C tape x y j ξin θ cur` on a box-valid
profile, with `j ≤ S` and `ξin⁻¹, θ⁻¹, ratLen ξin, ratLen θ ≤ S`, costs at most
`S ^ k` bit operations on every tape, and returns a rational of length at most
`S ^ k`.  The exponent is `k = 1000`.

The proof works at the size `U = S^20 ≥ 2^20`, where every constant of the program is
absorbed by one power of `U`, and bounds each sub-procedure on every tape
(namespace `OCost`):

* `oracleParams_spec`: `N_in ≤ U^10`, `ℓ_in ≤ U^24`, `⌈log₂ 4d⌉ ≤ U`, `s' = 2^ks ≤ U^4`,
  `ks, depth ≤ U^2`, `0 < ζ`, `ζ⁻¹, ratLen ζ ≤ U^15`, `B^e` exact; price `≤ U^6`.
* `binPoint_spec`, `penalty_spec` (from `penalty_cost` of `PenaltyCost.lean`),
  `levelExp_spec`, `binExp_spec`: a bin vector of the box `{0..B-1}^e` (`BoxV`) gives a
  bin point of the extended free box in `(1/B)ℤ` (`PtOK`), a penalty with `|D| ≤ U`
  (from `PenaltyOK`) and an integer level exponent of size `≤ U^2 + 1`.
* `binAccept_spec`, `walkStep_spec`, `sampleBin_spec`: the bin walk stays in the box;
  the dyadic Metropolis trial reads `≤ 2U^2 + 2` fair bits.
* `ratioAvg_spec`: the sum of `N_in` dyadic ratios `2^{k_a - k_{a+1}}` stays in
  `(1/2^M)ℤ`, `M = 2U^2 + 2`, so its length is `O(N_in + U^2)`.
* `pow2Approx_spec`: the bisection endpoints stay in `(1/2^r)ℤ ∩ [0, 8]`; the
  `ks` squarings multiply lengths by `s' ≤ U^4`.
* `dyadicDraw_spec`, `binOffsets_spec`: the integer offset point lies in the extended
  free box, the product of interval lengths has length `≤ 2U^2`.
* `corrAvg_spec`: the sum of `N_in` correction samples stays in
  `(1/(max(M_f,1) 2^depth))ℤ` with magnitude `≤ N_in 2^{4U^2+3}`.
* `oracle_spec`: the product of `j` ratio estimates has length `≤ U^13 + 4`; total
  price `≤ U^50`, output length `≤ U^14`.

The loop lengths are polynomial because `ξin⁻¹, θ⁻¹ ≤ S` (so `σ⁻¹ ≤ 100 U^2`,
`N_in ≤ U^9`, `Q_in ≤ U^12`); the binary lengths of sums of polynomially many rationals
stay polynomial because every summand lies in one fixed lattice `(1/D)ℤ`.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Program
open Cellcounting.Model.Operations
open Cellcounting.Interface

/-- INTERNAL: `k` fair bits read as a binary integer: the value is `< 2^k`, the cursor
advances by `k`, and the price is quadratic in `k` (the accumulator has at most `k` bits).
Used by the bin walk's dyadic trials, the dyadic draws, and the acceptance test.
TEXLINE: sections/evaluation.tex:356-371 -/
theorem uniformBits_cost (tape : Coins ℕ) (k cur : ℕ) :
    (uniformBits tape k cur).val.1.get < 2 ^ k ∧ (uniformBits tape k cur).val.2 = cur + k ∧
    Charged.steps rate (uniformBits tape k cur) ≤ 7 + k * (4 * k + 8) := by
  unfold uniformBits
  simp only [Charged.steps_bind, costVb, steps_SNat_lit]
  obtain ⟨⟨h1, h2⟩, h3⟩ := repeatFor_inv (fun _ (st : SNat × ℕ) => (do
      let __x ← coin tape st.2
      let y2 ← SNat.mul st.1 (SNat.lit 2).val
      if __x.1 then do
        let y ← SNat.add y2 (SNat.lit 1).val
        pure (y, __x.2)
      else pure (y2, __x.2) : Prog (SNat × ℕ)))
    (fun r (st : SNat × ℕ) => st.1.get < 2 ^ r ∧ st.2 = cur + r) (4 * k + 8) k
    ((SNat.lit 0).val, cur) (by simp)
    (by
      rintro r ⟨y, c⟩ hr ⟨hy, hc⟩
      simp only [coin, Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_flip,
        steps_SNat_mul, SNat.get_mul, SNat.get_lit] at hy hc ⊢
      have hb2 : bitLen 2 = 3 := by decide
      have hb1 : bitLen 1 = 2 := by decide
      have hyl : bitLen y.get ≤ r + 1 := bitLen_le_of_lt_two_pow hy
      have hmul : bitLen y.get * bitLen 2 ≤ 3 * k := by rw [hb2]; omega
      split
      · simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SNat_add,
          SNat.get_add, SNat.get_mul, SNat.get_lit]
        have h2y : bitLen (y.get * 2) ≤ r + 2 := by
          apply bitLen_le_of_lt_two_pow; rw [pow_succ]; omega
        refine ⟨⟨by rw [pow_succ]; omega, by omega⟩, by rw [hb1]; omega⟩
      · simp only [costVp, Charged.steps_pure, SNat.get_mul, SNat.get_lit]
        refine ⟨⟨by rw [pow_succ]; omega, by omega⟩, by omega⟩)
  refine ⟨h1, h2, ?_⟩
  have hb0 : bitLen 0 = 1 := by decide
  have hb1 : bitLen 1 = 2 := by decide
  have hb2 : bitLen 2 = 3 := by decide
  omega
namespace OCost

open Arlib.Computation
open Cellcounting.Program
open Cellcounting.Model.Operations
open Cellcounting.Interface
open OC

/-- INTERNAL: a bin vector in `{0..B-1}^e`, read the way the program reads it. -/
def BoxV (C : Ctx) (v : List SNat) : Prop :=
  ∀ k < C.nFree, (v.getD k default).get + 1 ≤ C.B.get

/-- INTERNAL: a free vector of the extended free box in `(1/B)ℤ`: the hypothesis of
`penalty_cost`. -/
def PtOK (C : Ctx) (z : List SRat) : Prop :=
  ∀ k < C.nFree, 0 ≤ (z.getD k default).get ∧
    (z.getD k default).get ≤ (C.free.getD k default).2.2.get + 1 ∧
    BInt C.B.get (z.getD k default).get

/-- INTERNAL: a valid penalty argument lies in the extended free box. -/
theorem PtOK.freeValid {C : Ctx} {z : List SRat} (h : PtOK C z) : FreeValid C z :=
  fun k hk => ⟨(h k hk).1, (h k hk).2.1⟩

/-- INTERNAL: every free bound read by the program has length `≤ U`. -/
theorem free_bits {U : ℕ} {C : Ctx} (hC : CtxSize U C) (hU : 1 ≤ U) (k : ℕ) :
    bitLen (C.free.getD k default).2.2.get ≤ U :=
  getD_pred (fun e : Entry => bitLen e.2.2.get ≤ U) C.free k (fun e he => (hC.free_le e he).2.2)
    (by have h0 : bitLen 0 = 1 := (by decide); show bitLen (0 : ℕ) ≤ U; omega)

/-- INTERNAL: a read from a list after one push. -/
theorem getD_push {α : Type} [Inhabited α] (l : List α) (a : α) (i : ℕ) :
    (l ++ [a]).getD i default = if i < l.length then l.getD i default
      else if i = l.length then a else default := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · obtain ⟨t, ht⟩ : ∃ t, i - l.length = t + 1 := ⟨i - l.length - 1, by omega⟩
    rw [ht]; rfl


/-- INTERNAL: `bitLen 1 = 2`. -/
theorem bitLen_one : bitLen 1 = 2 := by decide

/-- INTERNAL: `c U^k ≤ U^(k+1)` for `c ≤ 2^20 ≤ U`. -/
theorem pw_absorb {U : ℕ} (hU : 2 ^ 20 ≤ U) {c k m : ℕ} (hc : c ≤ 2 ^ 20) (hm : m = k + 1) :
    c * U ^ k ≤ U ^ m := by
  subst hm; rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_left _ (hc.trans hU)

/-- INTERNAL: `U^a ≤ U^b` for `a ≤ b`. -/
theorem pw_mono {U : ℕ} (hU : 1 ≤ U) {a b : ℕ} (h : a ≤ b) : U ^ a ≤ U ^ b :=
  Nat.pow_le_pow_right hU h
/-- INTERNAL: `bitLen 0 = 1`. -/
theorem bitLen_zero' : bitLen 0 = 1 := by decide

/-- INTERNAL: the bin point of a box bin vector is a valid penalty argument; price `≤ U^4`. -/
theorem binPoint_spec {U : ℕ} (C : Ctx) (hU : 2 ^ 20 ≤ U) (hC : CtxSize U C) (v : List SNat)
    (hv : BoxV C v) : PtOK C (binPoint C v).val ∧ Charged.steps rate (binPoint C v) ≤ U ^ 4 := by
  have hB1 : 1 ≤ C.B.get := hC.B_pos
  have hBU : C.B.get ≤ U := hC.B_le
  have hBq := hC.Bq_eq
  have hnF := hC.nFree_le
  unfold binPoint
  simp only [Charged.steps_bind, costVb, steps_SNat_lit, bitLen_one]
  generalize hR : Charged.repeatFor _ C.nFree [] = R
  obtain ⟨⟨_, hP⟩, hs⟩ : ((R.val.length = C.nFree ∧ ∀ i < C.nFree,
      0 ≤ (R.val.getD i default).get ∧
      (R.val.getD i default).get ≤ (C.free.getD i default).2.2.get + 1 ∧
      BInt C.B.get (R.val.getD i default).get)) ∧ Charged.steps rate R ≤ C.nFree * (4 * U ^ 2) := by
    subst hR
    refine repeatFor_inv _ (fun r (acc : List SRat) => acc.length = r ∧ ∀ i < r,
      0 ≤ (acc.getD i default).get ∧
      (acc.getD i default).get ≤ (C.free.getD i default).2.2.get + 1 ∧
      BInt C.B.get (acc.getD i default).get) (4 * U ^ 2) C.nFree [] ⟨rfl, by simp⟩ ?_
    rintro r acc hr ⟨hlen, hacc⟩
    simp only [Charged.steps_bind, costVb, steps_get, val_get, steps_SNat_add, SNat.get_add,
      SNat.get_lit, steps_SNat_mul, SNat.get_mul, steps_SNat_toRat, SNat.get_toRat,
      steps_SRat_div, steps_push, val_push, bitLen_one]
    have hb := free_bits hC (by omega) r
    have hvr := hv r hr
    set b := (C.free.getD r default).2.2.get with hbdef
    set w := (v.getD r default).get with hwdef
    refine ⟨⟨by simp [hlen], fun i hi => ?_⟩, ?_⟩
    · rw [getD_push]
      rcases Nat.lt_or_ge i r with h | h
      · simp only [show i < acc.length by omega, ↓reduceIte]; exact hacc i h
      · obtain rfl : i = r := by omega
        simp only [hlen, lt_irrefl, ↓reduceIte, SRat.get_div, SNat.get_toRat, SNat.get_mul,
          SNat.get_add, SNat.get_lit, hBq]
        rw [← hbdef, ← hwdef]
        have hB0 : (0 : ℚ) < C.B.get := by exact_mod_cast hB1
        refine ⟨by positivity, ?_, ⟨((b + 1) * w : ℕ), ?_⟩⟩
        · rw [div_le_iff₀ hB0]
          have : (w : ℚ) + 1 ≤ C.B.get := by exact_mod_cast hvr
          push_cast
          have hb0 : (0 : ℚ) ≤ b := by positivity
          nlinarith
        · rw [div_mul_cancel₀ _ hB0.ne']; push_cast; ring
    · have h1 : bitLen (b + 1) ≤ U + 2 := (bitLen_add_le' b 1).trans (by rw [bitLen_one]; omega)
      have h2 : bitLen w ≤ U := (bitLen_le_succ w).trans (by omega)
      have h3 : bitLen ((b + 1) * w) ≤ 2 * U + 2 := (bitLen_mul_le _ _).trans (by omega)
      have h4 : ratLen (((b + 1) * w : ℕ) : ℚ) ≤ 2 * U + 4 := by rw [ratLen_natCast]; omega
      have h5 : ratLen C.Bq.get ≤ U + 3 := by
        rw [hBq, ratLen_natCast]; have := bitLen_le_succ C.B.get; omega
      have m1 : bitLen (b + 1) * bitLen w ≤ (U + 2) * U := Nat.mul_le_mul h1 h2
      have m2 : (ratLen (((b + 1) * w : ℕ) : ℚ) + 1) * (ratLen C.Bq.get + 1) ≤
          (2 * U + 5) * (U + 4) := Nat.mul_le_mul (by omega) (by omega)
      have e1 : (U + 2) * U = U ^ 2 + 2 * U := by ring
      have e2 : (2 * U + 5) * (U + 4) = 2 * U ^ 2 + 13 * U + 20 := by ring
      have e3 : 100 * U ^ 1 ≤ U ^ 2 := pw_absorb hU (by norm_num) rfl
      rw [pow_one] at e3
      push_cast at m2 h4 ⊢
      omega
  refine ⟨hP, ?_⟩
  have : C.nFree * (4 * U ^ 2) ≤ 4 * U ^ 3 :=
    (Nat.mul_le_mul_right _ hnF).trans_eq (by ring)
  have e3 : 100 * U ^ 3 ≤ U ^ 4 := pw_absorb hU (by norm_num) rfl
  have : 1 ≤ U ^ 3 := Nat.one_le_pow _ _ (by omega)
  omega


/-- INTERNAL: `ratLen` of a natural at most `U`. -/
theorem ratLen_nat_le {U n : ℕ} (h : n ≤ U) : ratLen (n : ℚ) ≤ U + 3 := by
  rw [ratLen_natCast]; have := bitLen_le_succ n; omega

/-- INTERNAL: value and price of `levelExp` at a level `a ≤ U` and a penalty `|D| ≤ U` of
length `≤ U^3`: an integer of absolute value `≤ U^2 + 1`, for `≤ U^7`. -/
theorem levelExp_spec {U : ℕ} (C : Ctx) (hU : 2 ^ 20 ≤ U) (hC : CtxSize U C) (aq D : SRat)
    (a : ℕ) (ha : aq.get = a) (haU : a ≤ U) (hD : |D.get| ≤ U) (hDl : ratLen D.get ≤ U ^ 3) :
    (∃ z : ℤ, (levelExp C aq D).val.get = z ∧ z.natAbs ≤ U ^ 2 + 1) ∧
      Charged.steps rate (levelExp C aq D) ≤ U ^ 7 := by
  have hH1 : 1 ≤ C.H.get := hC.H_pos
  have hHU : C.H.get ≤ U := hC.H_le
  have hHq := hC.Hq_eq
  unfold levelExp
  simp only [Charged.steps_bind, costVb, steps_SRat_mul, SRat.get_mul, steps_SRat_div,
    SRat.get_div, steps_SRat_floor, SRat.get_floor, hHq, ha]
  have l1 : ratLen (a : ℚ) ≤ U + 3 := ratLen_nat_le haU
  have l2 : ratLen (C.H.get : ℚ) ≤ U + 3 := ratLen_nat_le hHU
  have l3 := ratLen_mul_le (a : ℚ) D.get
  have l4 := ratLen_div_le ((a : ℚ) * D.get) (C.H.get : ℚ)
  have hU3 : 100 * U ^ 1 ≤ U ^ 2 := pw_absorb hU (by norm_num) rfl
  have hU4 : 100 * U ^ 2 ≤ U ^ 3 := pw_absorb hU (by norm_num) rfl
  rw [pow_one] at hU3
  refine ⟨⟨_, rfl, ?_⟩, ?_⟩
  · have hH0 : (1 : ℚ) ≤ C.H.get := by exact_mod_cast hH1
    have hu : |(a : ℚ) * D.get / C.H.get| ≤ (U : ℚ) ^ 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ a),
        abs_of_nonneg (by positivity : (0 : ℚ) ≤ C.H.get), div_le_iff₀ (by linarith)]
      have : (a : ℚ) ≤ U := by exact_mod_cast haU
      have h0 : (0 : ℚ) ≤ U := by positivity
      have : (a : ℚ) * |D.get| ≤ U * U := mul_le_mul this hD (abs_nonneg _) h0
      nlinarith [abs_nonneg D.get, sq_nonneg (U : ℚ)]
    have h1 := Int.floor_le ((a : ℚ) * D.get / C.H.get)
    have h2 := Int.lt_floor_add_one ((a : ℚ) * D.get / C.H.get)
    have h3 := abs_le.1 hu
    have : ((⌊(a : ℚ) * D.get / C.H.get⌋.natAbs : ℤ) : ℚ) ≤ ((U ^ 2 + 1 : ℕ) : ℚ) := by
      rw [Int.natCast_natAbs, Int.cast_abs]; push_cast
      rw [abs_le]; constructor <;> linarith
    exact_mod_cast this
  · have m1 : (ratLen (a : ℚ) + 1) * (ratLen D.get + 1) ≤ (U + 4) * (U ^ 3 + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have m2 : (ratLen ((a : ℚ) * D.get) + 1) * (ratLen (C.H.get : ℚ) + 1) ≤
        (2 * U ^ 3) * (U + 4) := Nat.mul_le_mul (by omega) (by omega)
    have m3 : (ratLen ((a : ℚ) * D.get / C.H.get) + 1) * (ratLen ((a : ℚ) * D.get / C.H.get) + 1)
        ≤ (2 * U ^ 3) * (2 * U ^ 3) := Nat.mul_le_mul (by omega) (by omega)
    have e1 : (U + 4) * (U ^ 3 + 1) = U ^ 4 + 4 * U ^ 3 + U + 4 := by ring
    have e2 : (2 * U ^ 3) * (U + 4) = 2 * U ^ 4 + 8 * U ^ 3 := by ring
    have e3 : (2 * U ^ 3) * (2 * U ^ 3) = 4 * U ^ 6 := by ring
    have p5 : 100 * U ^ 3 ≤ U ^ 4 := pw_absorb hU (by norm_num) rfl
    have p6 : 100 * U ^ 4 ≤ U ^ 5 := pw_absorb hU (by norm_num) rfl
    have p7 : 100 * U ^ 5 ≤ U ^ 6 := pw_absorb hU (by norm_num) rfl
    have p8 : 100 * U ^ 6 ≤ U ^ 7 := pw_absorb hU (by norm_num) rfl
    omega


/-- INTERNAL: the standing hypotheses on the context of one oracle call, at size `U`. -/
structure Env (U : ℕ) (C : Ctx) (x y : List SNat) : Prop where
  big : 2 ^ 20 ≤ U
  size : CtxSize U C
  pen : PenaltyOK U C
  prof : ProfileValid C x y

/-- INTERNAL: the penalty on a valid point: `|D| ≤ U`, length `≤ U^3`, price `≤ U^6`. -/
theorem penalty_spec {U : ℕ} {C : Ctx} {x y : List SNat} (E : Env U C x y) (z : List SRat)
    (hz : PtOK C z) : |(penalty C x y z).val.get| ≤ U ∧ ratLen (penalty C x y z).val.get ≤ U ^ 3 ∧
      Charged.steps rate (penalty C x y z) ≤ U ^ 6 := by
  obtain ⟨h1, h2⟩ := penalty_cost U C E.big E.size x y E.prof z hz
  exact ⟨E.pen x y z E.prof hz.freeValid, h2, h1⟩

/-- INTERNAL: value and price of `binExp` on a box bin vector. -/
theorem binExp_spec {U : ℕ} {C : Ctx} {x y : List SNat} (E : Env U C x y) (aq : SRat) (a : ℕ)
    (ha : aq.get = a) (haU : a ≤ U) (v : List SNat) (hv : BoxV C v) :
    (∃ z : ℤ, (binExp C aq x y v).val.get = z ∧ z.natAbs ≤ U ^ 2 + 1) ∧
      Charged.steps rate (binExp C aq x y v) ≤ U ^ 8 := by
  unfold binExp
  simp only [Charged.steps_bind, costVb]
  obtain ⟨hz, s1⟩ := binPoint_spec C E.big E.size v hv
  obtain ⟨d1, d2, s2⟩ := penalty_spec E _ hz
  obtain ⟨hv', s3⟩ := levelExp_spec C E.big E.size aq _ a ha haU d1 d2
  refine ⟨hv', ?_⟩
  have hU := E.big
  have p5 : 100 * U ^ 4 ≤ U ^ 5 := pw_absorb hU (by norm_num) rfl
  have p6 : 100 * U ^ 5 ≤ U ^ 6 := pw_absorb hU (by norm_num) rfl
  have p7 : 100 * U ^ 6 ≤ U ^ 7 := pw_absorb hU (by norm_num) rfl
  have p8 : 100 * U ^ 7 ≤ U ^ 8 := pw_absorb hU (by norm_num) rfl
  omega


/-- INTERNAL: `⌊q⌋₊ ≤ |q|`. -/
theorem natFloor_le_abs (q : ℚ) : (⌊q⌋₊ : ℚ) ≤ |q| := by
  rcases le_or_gt q 0 with h | h
  · rw [Nat.floor_eq_zero.2 (by linarith)]; simp
  · exact (Nat.floor_le h.le).trans (le_abs_self q)

/-- INTERNAL: the length of an integer of absolute value `≤ M`. -/
theorem ratLen_int_le {z : ℤ} {M : ℕ} (h : z.natAbs ≤ M) : ratLen (z : ℚ) ≤ M + 3 := by
  rw [ratLen_intCast]; have := bitLen_le_succ z.natAbs; omega

/-- INTERNAL: price of `binAccept` between box bin vectors; it returns one of them. -/
theorem binAccept_spec {U : ℕ} {C : Ctx} {x y : List SNat} (E : Env U C x y) (tape : Coins ℕ)
    (aq : SRat) (a : ℕ) (ha : aq.get = a) (haU : a ≤ U) (v w : List SNat) (hv : BoxV C v)
    (hw : BoxV C w) (cur : ℕ) :
    ((binAccept C tape aq x y v w cur).val.1 = v ∨ (binAccept C tape aq x y v w cur).val.1 = w) ∧
      Charged.steps rate (binAccept C tape aq x y v w cur) ≤ U ^ 9 := by
  have hU := E.big
  obtain ⟨⟨zv, hzv, hzvb⟩, s1⟩ := binExp_spec E aq a ha haU v hv
  obtain ⟨⟨zw, hzw, hzwb⟩, s2⟩ := binExp_spec E aq a ha haU w hw
  unfold binAccept
  simp only [Charged.steps_bind, costVb, steps_SRat_le, SRat.val_le]
  generalize binExp C aq x y v = Pv at hzv s1 ⊢
  generalize binExp C aq x y w = Pw at hzw s2 ⊢
  have lv : ratLen Pv.val.get ≤ U ^ 2 + 4 := by rw [hzv]; have := ratLen_int_le hzvb; omega
  have lw : ratLen Pw.val.get ≤ U ^ 2 + 4 := by rw [hzw]; have := ratLen_int_le hzwb; omega
  have m1 : (ratLen Pw.val.get + 1) * (ratLen Pv.val.get + 1) ≤ (U ^ 2 + 5) * (U ^ 2 + 5) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e1 : (U ^ 2 + 5) * (U ^ 2 + 5) = U ^ 4 + 10 * U ^ 2 + 25 := by ring
  have p3 : 100 * U ^ 2 ≤ U ^ 3 := pw_absorb hU (by norm_num) rfl
  have p4 : 100 * U ^ 3 ≤ U ^ 4 := pw_absorb hU (by norm_num) rfl
  have p5 : 100 * U ^ 4 ≤ U ^ 5 := pw_absorb hU (by norm_num) rfl
  have p6 : 100 * U ^ 5 ≤ U ^ 6 := pw_absorb hU (by norm_num) rfl
  have p7 : 100 * U ^ 6 ≤ U ^ 7 := pw_absorb hU (by norm_num) rfl
  have p8 : 100 * U ^ 7 ≤ U ^ 8 := pw_absorb hU (by norm_num) rfl
  have p9 : 100 * U ^ 8 ≤ U ^ 9 := pw_absorb hU (by norm_num) rfl
  have q1 : 1 ≤ U ^ 2 := Nat.one_le_pow _ _ (by omega)
  by_cases hdown : Pw.val.get ≤ Pv.val.get
  · simp only [hdown, decide_true, ↓reduceIte, costVp, Charged.steps_pure]
    exact ⟨by simp, by omega⟩
  · simp only [hdown, decide_false, Bool.false_eq_true, ↓reduceIte]
    simp only [Charged.steps_bind, costVb, steps_SRat_sub, SRat.get_sub, steps_SRat_natFloor,
      SRat.get_natFloor, steps_SNat_index, SNat.val_index, steps_SNat_lit, steps_SNat_eq,
      SNat.val_eq, SNat.get_lit, bitLen_zero']
    rw [hzw, hzv]
    rw [hzw, hzv] at m1
    have hd : ((zw : ℚ) - zv) = ((zw - zv : ℤ) : ℚ) := by push_cast; ring
    rw [hd]
    have hdb : (zw - zv).natAbs ≤ 2 * U ^ 2 + 2 := by omega
    have ld := ratLen_int_le hdb
    have hf : ⌊((zw - zv : ℤ) : ℚ)⌋₊ ≤ 2 * U ^ 2 + 2 := by
      have := natFloor_le_abs ((zw - zv : ℤ) : ℚ)
      have h2 : |((zw - zv : ℤ) : ℚ)| ≤ ((2 * U ^ 2 + 2 : ℕ) : ℚ) := by
        rw [← Int.cast_abs, ← Int.natCast_natAbs]; exact_mod_cast hdb
      exact_mod_cast this.trans h2
    set dI := ⌊((zw - zv : ℤ) : ℚ)⌋₊ with hdI
    obtain ⟨u1, u2, u3⟩ := uniformBits_cost tape dI cur
    have hY := bitLen_le_of_lt_two_pow u1
    generalize uniformBits tape dI cur = PY at u1 u2 u3 hY ⊢
    have m2 : (ratLen ((zw - zv : ℤ) : ℚ) + 1) * (ratLen ((zw - zv : ℤ) : ℚ) + 1) ≤
        (2 * U ^ 2 + 6) * (2 * U ^ 2 + 6) := Nat.mul_le_mul (by omega) (by omega)
    have m3 : dI * (4 * dI + 8) ≤ (2 * U ^ 2 + 2) * (8 * U ^ 2 + 16) :=
      Nat.mul_le_mul hf (by omega)
    have e2 : (2 * U ^ 2 + 6) * (2 * U ^ 2 + 6) = 4 * U ^ 4 + 24 * U ^ 2 + 36 := by ring
    have e3 : (2 * U ^ 2 + 2) * (8 * U ^ 2 + 16) = 16 * U ^ 4 + 48 * U ^ 2 + 32 := by ring
    have hbd := bitLen_le_succ dI
    by_cases hok : PY.val.1.get = 0
    · simp only [hok, decide_true, ↓reduceIte, costVp, Charged.steps_pure, bitLen_zero']
      exact ⟨by simp, by omega⟩
    · simp only [hok, decide_false, Bool.false_eq_true, ↓reduceIte, costVp, Charged.steps_pure]
      exact ⟨by simp, by omega⟩


/-- INTERNAL: a read after a write is the written value or the old read. -/
theorem getD_set_cases {α : Type} (l : List α) (i k : ℕ) (a d : α) :
    (l.set i a).getD k d = a ∨ (l.set i a).getD k d = l.getD k d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs <;> simp_all

/-- INTERNAL: writing a box value keeps a box bin vector. -/
theorem BoxV.set {C : Ctx} {l : List SNat} (h : BoxV C l) (i : ℕ) (a : SNat)
    (ha : a.get + 1 ≤ C.B.get) : BoxV C (l.set i a) := by
  intro k hk
  rcases getD_set_cases l i k a default with e | e <;> rw [e]
  · exact ha
  · exact h k hk

/-- INTERNAL: the walk-relevant oracle parameters. -/
structure WalkOK (U : ℕ) (C : Ctx) (P : OParams) : Prop where
  kd_le : P.kd ≤ U
  twoE : P.twoE.get = 2 * C.nFree
  Bm1 : P.Bm1.get = C.B.get - 1

/-- INTERNAL: `bitLen 2 = 3`. -/
theorem bitLen_two : bitLen 2 = 3 := by decide

/-- INTERNAL: one bin-walk step keeps the bin vector in the box, for `≤ U^10`. -/
theorem walkStep_spec {U : ℕ} {C : Ctx} {x y : List SNat} (E : Env U C x y) (P : OParams)
    (hP : WalkOK U C P) (tape : Coins ℕ) (aq : SRat) (a : ℕ) (ha : aq.get = a) (haU : a ≤ U)
    (st : List SNat × ℕ) (hst : BoxV C st.1) :
    BoxV C (walkStep C P tape aq x y st).val.1 ∧
      Charged.steps rate (walkStep C P tape aq x y st) ≤ U ^ 10 := by
  have hU := E.big
  have hC := E.size
  have hnF := hC.nFree_le
  have hBU := hC.B_le
  have hkd := hP.kd_le
  obtain ⟨u1, u2, u3⟩ := uniformBits_cost tape P.kd st.2
  have hub := bitLen_le_of_lt_two_pow u1
  unfold walkStep
  simp only [Charged.steps_bind, costVb, steps_SNat_lt, SNat.val_lt]
  generalize uniformBits tape P.kd st.2 = PU at u1 u2 u3 hub ⊢
  have m0 : P.kd * (4 * P.kd + 8) ≤ U * (4 * U + 8) := Nat.mul_le_mul hkd (by omega)
  have e0 : U * (4 * U + 8) = 4 * U ^ 2 + 8 * U := by ring
  have htw : bitLen P.twoE.get ≤ 2 * U + 1 := by
    rw [hP.twoE]; exact (bitLen_le_succ _).trans (by omega)
  have p2 : 100 * U ^ 1 ≤ U ^ 2 := pw_absorb hU (by norm_num) rfl
  have p3 : 100 * U ^ 2 ≤ U ^ 3 := pw_absorb hU (by norm_num) rfl
  have p4 : 100 * U ^ 3 ≤ U ^ 4 := pw_absorb hU (by norm_num) rfl
  have p5 : 100 * U ^ 4 ≤ U ^ 5 := pw_absorb hU (by norm_num) rfl
  have p6 : 100 * U ^ 5 ≤ U ^ 6 := pw_absorb hU (by norm_num) rfl
  have p7 : 100 * U ^ 6 ≤ U ^ 7 := pw_absorb hU (by norm_num) rfl
  have p8 : 100 * U ^ 7 ≤ U ^ 8 := pw_absorb hU (by norm_num) rfl
  have p9 : 100 * U ^ 8 ≤ U ^ 9 := pw_absorb hU (by norm_num) rfl
  have p10 : 100 * U ^ 9 ≤ U ^ 10 := pw_absorb hU (by norm_num) rfl
  rw [pow_one] at p2
  by_cases hmv : PU.val.1.get < P.twoE.get
  swap
  · simp only [hmv, decide_false, Bool.false_eq_true, ↓reduceIte, costVp, Charged.steps_pure]
    exact ⟨hst, by omega⟩
  simp only [hmv, decide_true, ↓reduceIte, Charged.steps_bind, costVb, steps_SNat_lit,
    SNat.get_lit, steps_SNat_div, SNat.get_div, steps_SNat_mod, SNat.get_mod,
    steps_SNat_index, SNat.val_index, steps_get, val_get, steps_SNat_eq, SNat.val_eq,
    bitLen_two, bitLen_one, bitLen_zero']
  have hci : PU.val.1.get / 2 < C.nFree := by rw [hP.twoE] at hmv; omega
  have hvc := hst (PU.val.1.get / 2) hci
  set vc := (st.1.getD (PU.val.1.get / 2) default) with hvcdef
  have hdiv : bitLen (PU.val.1.get / 2) ≤ P.kd + 1 := (bitLen_mono (Nat.div_le_self PU.val.1.get 2)).trans hub
  have hmod : bitLen (PU.val.1.get % 2) ≤ 2 := by
    have : PU.val.1.get % 2 ≤ 1 := by omega
    exact (bitLen_mono this).trans (by rw [bitLen_one])
  have hvcb : bitLen vc.get ≤ U := (bitLen_le_succ _).trans (by omega)
  have hBm : bitLen P.Bm1.get ≤ U := by
    rw [hP.Bm1]; exact (bitLen_le_succ _).trans (by omega)
  have md : bitLen PU.val.1.get * 3 ≤ (U + 1) * 3 := Nat.mul_le_mul_right _ (by omega)
  have hBox := hst
  by_cases hup : PU.val.1.get % 2 = 1
  · simp only [hup, decide_true, ↓reduceIte, Charged.steps_bind, costVb, steps_SNat_eq,
      SNat.val_eq, bitLen_one]
    by_cases hedge : vc.get = P.Bm1.get
    · simp only [hedge, decide_true, ↓reduceIte, costVp, Charged.steps_pure]
      exact ⟨hst, by omega⟩
    simp only [hedge, decide_false, Bool.false_eq_true, ↓reduceIte, Charged.steps_bind, costVb,
      steps_SNat_add, SNat.get_lit, steps_set, val_set, bitLen_one]
    have hw : BoxV C (st.1.set (PU.val.1.get / 2) ((SNat.add vc (SNat.lit 1).val).val)) :=
      hst.set _ _ (by rw [SNat.get_add, SNat.get_lit]; rw [hP.Bm1] at hedge; omega)
    obtain ⟨b1, b2⟩ := binAccept_spec E tape aq a ha haU st.1 _ hst hw PU.val.2
    refine ⟨?_, by omega⟩
    rcases b1 with e | e <;> rw [e]
    · exact hst
    · exact hw
  · simp only [hup, decide_false, Bool.false_eq_true, ↓reduceIte, Charged.steps_bind, costVb,
      steps_SNat_eq, SNat.val_eq, SNat.get_lit, bitLen_zero']
    by_cases hedge : vc.get = 0
    · simp only [hedge, decide_true, ↓reduceIte, costVp, Charged.steps_pure, bitLen_zero']
      exact ⟨hst, by omega⟩
    simp only [hedge, decide_false, Bool.false_eq_true, ↓reduceIte, Charged.steps_bind, costVb,
      steps_SNat_sub, SNat.get_lit, steps_set, val_set, bitLen_one]
    have hw : BoxV C (st.1.set (PU.val.1.get / 2) ((SNat.sub vc (SNat.lit 1).val).val)) :=
      hst.set _ _ (by rw [SNat.get_sub, SNat.get_lit]; omega)
    obtain ⟨b1, b2⟩ := binAccept_spec E tape aq a ha haU st.1 _ hst hw PU.val.2
    refine ⟨?_, by omega⟩
    rcases b1 with e | e <;> rw [e]
    · exact hst
    · exact hw


/-- INTERNAL: the bounds on the oracle parameters that the price of an oracle call uses. -/
structure POK (U : ℕ) (C : Ctx) (P : OParams) : Prop extends WalkOK U C P where
  N_le : P.N ≤ U ^ 10
  Nq : P.Nq.get = P.N
  ell_le : P.ell ≤ U ^ 24
  ζ_pos : 0 < P.ζ.get
  ζ_inv : P.ζ.get⁻¹ ≤ U ^ 15
  ζ_len : ratLen P.ζ.get ≤ U ^ 15
  ks_le : P.ks ≤ U ^ 2
  sPrime : P.sPrime.get = 2 ^ P.ks
  sPrime_le : 2 ^ P.ks ≤ U ^ 4
  depth_le : P.depth ≤ U ^ 2
  Be : P.Be.get = C.B.get ^ C.nFree

/-- INTERNAL: one bin sample is a box bin vector, for `≤ U^35`. -/
theorem sampleBin_spec {U : ℕ} {C : Ctx} {x y : List SNat} (E : Env U C x y) (P : OParams)
    (hP : POK U C P) (tape : Coins ℕ) (aq : SRat) (a : ℕ) (ha : aq.get = a) (haU : a ≤ U)
    (cur : ℕ) :
    BoxV C (sampleBin C P tape aq x y cur).val.1 ∧
      Charged.steps rate (sampleBin C P tape aq x y cur) ≤ U ^ 35 := by
  have hU := E.big
  have hC := E.size
  have hnF := hC.nFree_le
  have hB1 := hC.B_pos
  have hell := hP.ell_le
  unfold sampleBin
  simp only [Charged.steps_bind, costVb, steps_idxEq, val_idxEq, bitLen_zero']
  have hnb : bitLen C.nFree ≤ U + 1 := (bitLen_le_succ _).trans (by omega)
  have p35 : 100 * U ^ 34 ≤ U ^ 35 := pw_absorb hU (by norm_num) rfl
  have q1 : U ^ 1 ≤ U ^ 34 := pw_mono (by omega) (by norm_num)
  rw [pow_one] at q1
  by_cases h0 : C.nFree = 0
  · simp only [h0, decide_true, ↓reduceIte, costVp, Charged.steps_pure, bitLen_zero']
    refine ⟨fun k hk => by simp; omega, by omega⟩
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte, Charged.steps_bind, costVb,
    steps_SNat_lit, steps_replicate, val_replicate, bitLen_zero']
  generalize hR : Charged.repeatFor _ P.ell _ = R
  obtain ⟨hv, hs⟩ : BoxV C R.val.1 ∧ Charged.steps rate R ≤ P.ell * U ^ 10 := by
    subst hR
    refine repeatFor_inv _ (fun _ (st : List SNat × ℕ) => BoxV C st.1) (U ^ 10) P.ell _ ?_ ?_
    · intro k hk
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split_ifs
      simp only [Option.getD_some]; show 0 + 1 ≤ C.B.get; omega
    · intro r st _ hst
      exact walkStep_spec E P hP.toWalkOK tape aq a ha haU st hst
  refine ⟨hv, ?_⟩
  have : P.ell * U ^ 10 ≤ U ^ 24 * U ^ 10 := Nat.mul_le_mul_right _ hell
  have e : U ^ 24 * U ^ 10 = U ^ 34 := by ring
  omega


/-- INTERNAL: `2^d` for `|d| ≤ M` lies in `(1/2^M)ℤ` and in `(0, 2^M]`. -/
theorem zpow_BInt (d : ℤ) (M : ℕ) (hd : d.natAbs ≤ M) :
    BInt (2 ^ M) ((2 : ℚ) ^ d) ∧ 0 < (2 : ℚ) ^ d ∧ (2 : ℚ) ^ d ≤ 2 ^ M := by
  refine ⟨⟨2 ^ (d + M).toNat, ?_⟩, by positivity, ?_⟩
  · have h1 : (0 : ℤ) ≤ d + M := by omega
    push_cast
    rw [← zpow_natCast (2 : ℚ) M, ← zpow_add₀ (by norm_num), ← zpow_natCast,
      Int.toNat_of_nonneg h1]
  · rw [← zpow_natCast (2 : ℚ) M]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)

/-- INTERNAL: the length of a `(1/2^M)ℤ` value of magnitude `≤ r 2^M`. -/
theorem ratLen_dyadic_le {q : ℚ} {M r : ℕ} (hq : BInt (2 ^ M) q) (hr : |q| ≤ r * 2 ^ M) :
    ratLen q ≤ r + 3 * M + 6 := by
  have h1 : |q| ≤ 2 ^ (r + M) := by
    have : (r : ℚ) ≤ 2 ^ r := by exact_mod_cast (Nat.lt_two_pow_self).le
    rw [pow_add]; exact hr.trans (mul_le_mul_of_nonneg_right this (by positivity))
  have := ratLen_le_of_BInt (Nat.one_le_two_pow) hq h1
  rw [bitLen_two_pow] at this; omega

/-- INTERNAL: value and price of `ratioAvg` at a level `a + 1 ≤ U`. -/
theorem ratioAvg_spec {U : ℕ} {C : Ctx} {x y : List SNat} (E : Env U C x y) (P : OParams)
    (hP : POK U C P) (tape : Coins ℕ) (a : ℕ) (haU : a + 1 ≤ U) (cur : ℕ) :
    ratLen (ratioAvg C P tape x y a cur).val.1.get ≤ U ^ 12 ∧
      Charged.steps rate (ratioAvg C P tape x y a cur) ≤ U ^ 47 := by
  have hU := E.big
  have hC := E.size
  have hN := hP.N_le
  have p3 : 100 * U ^ 2 ≤ U ^ 3 := pw_absorb hU (by norm_num) rfl
  have p4 : 100 * U ^ 3 ≤ U ^ 4 := pw_absorb hU (by norm_num) rfl
  have p5 : 100 * U ^ 4 ≤ U ^ 5 := pw_absorb hU (by norm_num) rfl
  have p6 : 100 * U ^ 5 ≤ U ^ 6 := pw_absorb hU (by norm_num) rfl
  have p7 : 100 * U ^ 6 ≤ U ^ 7 := pw_absorb hU (by norm_num) rfl
  have p8 : 100 * U ^ 7 ≤ U ^ 8 := pw_absorb hU (by norm_num) rfl
  have p9 : 100 * U ^ 8 ≤ U ^ 9 := pw_absorb hU (by norm_num) rfl
  have p10 : 100 * U ^ 9 ≤ U ^ 10 := pw_absorb hU (by norm_num) rfl
  have p11 : 100 * U ^ 10 ≤ U ^ 11 := pw_absorb hU (by norm_num) rfl
  have p12 : 100 * U ^ 11 ≤ U ^ 12 := pw_absorb hU (by norm_num) rfl
  have q2 : U ^ 2 ≤ U ^ 3 := pw_mono (by omega) (by norm_num)
  have q1 : 100 * U ^ 1 ≤ U ^ 2 := pw_absorb hU (by norm_num) rfl
  rw [pow_one] at q1
  set M := 2 * U ^ 2 + 2 with hM
  unfold ratioAvg
  simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SNat_lit,
    steps_SNat_toRat, steps_SNat_add, steps_SRat_lit, steps_SRat_div, SRat.get_div,
    SNat.get_lit, SNat.get_add, bitLen_one, ratLen_zero]
  generalize hR : Charged.repeatFor _ P.N _ = R
  obtain ⟨⟨hb, hm⟩, hs⟩ : (BInt (2 ^ M) R.val.1.get ∧ |R.val.1.get| ≤ (P.N : ℚ) * 2 ^ M) ∧
      Charged.steps rate R ≤ P.N * U ^ 36 := by
    subst hR
    refine repeatFor_inv _ (fun r (st : SRat × ℕ) => BInt (2 ^ M) st.1.get ∧
      |st.1.get| ≤ (r : ℚ) * 2 ^ M) (U ^ 36) P.N _ ⟨by simp [BInt.zero], by simp⟩ ?_
    rintro r st hr ⟨hb, hm⟩
    simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SRat_sub,
      SRat.get_sub, steps_SRat_zpow2, SRat.get_zpow2, steps_SRat_add, SRat.get_add]
    have ha : (SNat.toRat (SNat.lit a).val).val.get = (a : ℚ) := by simp
    have ha1 : (SNat.toRat (SNat.add (SNat.lit a).val (SNat.lit 1).val).val).val.get =
        ((a + 1 : ℕ) : ℚ) := by simp
    generalize SNat.toRat (SNat.lit a).val = Pa at ha ⊢
    generalize SNat.toRat (SNat.add (SNat.lit a).val (SNat.lit 1).val).val = Pa1 at ha1 ⊢
    obtain ⟨hv, s1⟩ := sampleBin_spec E P hP tape Pa.val a ha (by omega) st.2
    generalize sampleBin C P tape Pa.val x y st.2 = PS at hv s1 ⊢
    obtain ⟨hz, s2⟩ := binPoint_spec C hU hC _ hv
    generalize binPoint C PS.val.1 = PZ at hz s2 ⊢
    obtain ⟨d1, d2, s3⟩ := penalty_spec E _ hz
    generalize penalty C x y PZ.val = PD at d1 d2 s3 ⊢
    obtain ⟨⟨z0, hz0, hz0b⟩, s4⟩ := levelExp_spec C hU hC Pa.val PD.val a ha (by omega) d1 d2
    obtain ⟨⟨z1, hz1, hz1b⟩, s5⟩ := levelExp_spec C hU hC Pa1.val PD.val (a + 1) ha1 haU d1 d2
    generalize levelExp C Pa.val PD.val = P0 at hz0 s4 ⊢
    generalize levelExp C Pa1.val PD.val = P1 at hz1 s5 ⊢
    rw [hz0, hz1]
    have hd : ((z0 : ℚ) - z1) = ((z0 - z1 : ℤ) : ℚ) := by push_cast; ring
    rw [hd, Int.floor_intCast]
    have hdb : (z0 - z1).natAbs ≤ M := by omega
    obtain ⟨r1, r2, r3⟩ := zpow_BInt (z0 - z1) M hdb
    have l0 := ratLen_int_le hz0b
    have l1 := ratLen_int_le hz1b
    have ld := ratLen_int_le hdb
    have ls : ratLen st.1.get ≤ r + 3 * M + 6 := ratLen_dyadic_le hb hm
    have lr : ratLen ((2 : ℚ) ^ (z0 - z1)) ≤ 1 + 3 * M + 6 :=
      ratLen_dyadic_le r1 (by rw [abs_of_pos r2]; simpa using r3)
    refine ⟨⟨hb.add r1, ?_⟩, ?_⟩
    · calc |st.1.get + (2 : ℚ) ^ (z0 - z1)| ≤ |st.1.get| + |(2 : ℚ) ^ (z0 - z1)| :=
            abs_add_le _ _
        _ ≤ r * 2 ^ M + 2 ^ M := by rw [abs_of_pos r2]; linarith
        _ = ((r + 1 : ℕ) : ℚ) * 2 ^ M := by push_cast; ring
    · have hrN : r ≤ U ^ 10 := by omega
      have m1 : (ratLen (z0 : ℚ) + 1) * (ratLen (z1 : ℚ) + 1) ≤ (U ^ 2 + 5) * (U ^ 2 + 5) :=
        Nat.mul_le_mul (by omega) (by omega)
      have m2 : (ratLen st.1.get + 1) * (ratLen ((2 : ℚ) ^ (z0 - z1)) + 1) ≤
          (U ^ 10 + 6 * U ^ 2 + 13) * (6 * U ^ 2 + 14) := Nat.mul_le_mul (by omega) (by omega)
      have e1 : (U ^ 2 + 5) * (U ^ 2 + 5) = U ^ 4 + 10 * U ^ 2 + 25 := by ring
      have e2 : (U ^ 10 + 6 * U ^ 2 + 13) * (6 * U ^ 2 + 14) =
          6 * U ^ 12 + 14 * U ^ 10 + 36 * U ^ 4 + 162 * U ^ 2 + 182 := by ring
      have p13 : 100 * U ^ 12 ≤ U ^ 13 := pw_absorb hU (by norm_num) rfl
      have p14 : 100 * U ^ 13 ≤ U ^ 14 := pw_absorb hU (by norm_num) rfl
      have q35 : 100 * U ^ 14 ≤ U ^ 35 := (pw_absorb hU (by norm_num) rfl).trans
        (pw_mono (by omega) (by norm_num))
      have p36 : 100 * U ^ 35 ≤ U ^ 36 := pw_absorb hU (by norm_num) rfl
      omega
  have ls : ratLen R.val.1.get ≤ P.N + 3 * M + 6 := ratLen_dyadic_le hb hm
  have lN : ratLen P.Nq.get ≤ U ^ 10 + 3 := by
    rw [hP.Nq, ratLen_natCast]; have := bitLen_le_succ P.N; omega
  have ha1 : bitLen (a + 1) ≤ U + 1 := (bitLen_le_succ _).trans (by omega)
  have ha0 : bitLen a ≤ U := (bitLen_le_succ _).trans (by omega)
  have l1 := ratLen_div_le R.val.1.get P.Nq.get
  have m1 : (ratLen R.val.1.get + 1) * (ratLen P.Nq.get + 1) ≤
      (U ^ 10 + 6 * U ^ 2 + 13) * (U ^ 10 + 4) := Nat.mul_le_mul (by omega) (by omega)
  have e1 : (U ^ 10 + 6 * U ^ 2 + 13) * (U ^ 10 + 4) =
      U ^ 20 + 6 * U ^ 12 + 17 * U ^ 10 + 24 * U ^ 2 + 52 := by ring
  have m2 : P.N * U ^ 36 ≤ U ^ 10 * U ^ 36 := Nat.mul_le_mul_right _ hN
  have e2 : U ^ 10 * U ^ 36 = U ^ 46 := by ring
  have q20 : U ^ 12 ≤ U ^ 20 := pw_mono (by omega) (by norm_num)
  have p21 : 100 * U ^ 20 ≤ U ^ 46 := (pw_absorb hU (by norm_num) rfl).trans
    (pw_mono (by omega) (by norm_num))
  have p47 : 100 * U ^ 46 ≤ U ^ 47 := pw_absorb hU (by norm_num) rfl
  exact ⟨by omega, by omega⟩


/-- INTERNAL: `n` repeated squarings at most multiply the length by `2^n`. -/
theorem sq_loop (n L : ℕ) (m : SRat) (hm : ratLen m.get ≤ L) :
    ratLen (Charged.repeatFor (fun _ acc => SRat.mul acc acc) n m : Prog SRat).val.get ≤
      2 ^ n * L ∧
    Charged.steps rate (Charged.repeatFor (fun _ acc => SRat.mul acc acc) n m : Prog SRat) ≤
      n * ((2 ^ n * L + 1) * (2 ^ n * L + 1)) := by
  refine repeatFor_inv _ (fun i (acc : SRat) => ratLen acc.get ≤ 2 ^ i * L) _ n m
    (by simpa using hm) ?_
  intro r acc hr hacc
  simp only [steps_SRat_mul, SRat.get_mul]
  have h1 := ratLen_mul_le acc.get acc.get
  have h2 : 2 ^ r * L ≤ 2 ^ n * L :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hr.le)
  refine ⟨by rw [pow_succ]; nlinarith, Nat.mul_le_mul (by omega) (by omega)⟩

/-- INTERNAL: the length of `2^h`. -/
theorem ratLen_zpow_le (h : ℤ) : ratLen ((2 : ℚ) ^ h) ≤ 3 * h.natAbs + 7 := by
  obtain ⟨r1, r2, r3⟩ := zpow_BInt h h.natAbs le_rfl
  have := ratLen_dyadic_le r1 (r := 1) (by rw [abs_of_pos r2]; simpa using r3)
  omega

/-- INTERNAL: `ratLen (1/2) = 5`. -/
theorem ratLen_half : ratLen (1 / 2 : ℚ) = 5 := by
  have h2 : bitLen 2 = 3 := by decide
  have h1 : bitLen 1 = 2 := by decide
  have : (1 / 2 : ℚ).num = 1 := by norm_num
  have h' : (1 / 2 : ℚ).den = 2 := by norm_num
  simp only [ratLen, this, h']; simp [h1, h2]

/-- INTERNAL: `ratLen 8 = 7`. -/
theorem ratLen_eight : ratLen (8 : ℚ) = 7 := by
  rw [show (8 : ℚ) = ((8 : ℕ) : ℚ) by norm_num, ratLen_natCast]; decide

/-- INTERNAL: `(1/2^r)ℤ ⊆ (1/2^(r+1))ℤ`. -/
theorem bint_up {r : ℕ} {q : ℚ} (h : BInt (2 ^ r) q) : BInt (2 ^ (r + 1)) q := by
  have := h.mul_nat 2; rwa [← pow_succ] at this

/-- INTERNAL: halving maps `(1/2^r)ℤ` into `(1/2^(r+1))ℤ`. -/
theorem bint_half {r : ℕ} {q : ℚ} (h : BInt (2 ^ r) q) : BInt (2 ^ (r + 1)) (q * (1 / 2)) := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, by push_cast at ha ⊢; rw [← ha]; ring⟩

/-- INTERNAL: value and price of `pow2Approx` on an exponent of length `≤ U^4` and
magnitude `≤ U^3`: a dyadic of `[0, 8]` with denominator `2^depth`, for `≤ U^19`. -/
theorem pow2Approx_spec {U : ℕ} {C : Ctx} (hU : 2 ^ 20 ≤ U) (P : OParams) (hP : POK U C P)
    (β : SRat) (hβl : ratLen β.get ≤ U ^ 4) (hβ : |β.get| ≤ U ^ 3) :
    (BInt (2 ^ P.depth) (pow2Approx P β).val.get ∧ 0 ≤ (pow2Approx P β).val.get ∧
      (pow2Approx P β).val.get ≤ 8) ∧ Charged.steps rate (pow2Approx P β) ≤ U ^ 19 := by
  have hks := hP.ks_le
  have hsp := hP.sPrime_le
  have hdep := hP.depth_le
  have p3 : 100 * U ^ 2 ≤ U ^ 3 := pw_absorb hU (by norm_num) rfl
  have p4 : 100 * U ^ 3 ≤ U ^ 4 := pw_absorb hU (by norm_num) rfl
  have p5 : 100 * U ^ 4 ≤ U ^ 5 := pw_absorb hU (by norm_num) rfl
  have p6 : 100 * U ^ 5 ≤ U ^ 6 := pw_absorb hU (by norm_num) rfl
  have p7 : 100 * U ^ 6 ≤ U ^ 7 := pw_absorb hU (by norm_num) rfl
  have p8 : 100 * U ^ 7 ≤ U ^ 8 := pw_absorb hU (by norm_num) rfl
  have p9 : 100 * U ^ 8 ≤ U ^ 9 := pw_absorb hU (by norm_num) rfl
  have p10 : 100 * U ^ 9 ≤ U ^ 10 := pw_absorb hU (by norm_num) rfl
  have p11 : 100 * U ^ 10 ≤ U ^ 11 := pw_absorb hU (by norm_num) rfl
  have p12 : 100 * U ^ 11 ≤ U ^ 12 := pw_absorb hU (by norm_num) rfl
  have p13 : 100 * U ^ 12 ≤ U ^ 13 := pw_absorb hU (by norm_num) rfl
  have p14 : 100 * U ^ 13 ≤ U ^ 14 := pw_absorb hU (by norm_num) rfl
  have p15 : 100 * U ^ 14 ≤ U ^ 15 := pw_absorb hU (by norm_num) rfl
  have p16 : 100 * U ^ 15 ≤ U ^ 16 := pw_absorb hU (by norm_num) rfl
  have p17 : 100 * U ^ 16 ≤ U ^ 17 := pw_absorb hU (by norm_num) rfl
  have p18 : 100 * U ^ 17 ≤ U ^ 18 := pw_absorb hU (by norm_num) rfl
  have p19 : 100 * U ^ 18 ≤ U ^ 19 := pw_absorb hU (by norm_num) rfl
  have q1 : 100 * U ^ 1 ≤ U ^ 2 := pw_absorb hU (by norm_num) rfl
  rw [pow_one] at q1
  unfold pow2Approx
  simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SNat_toRat,
    SNat.get_toRat, steps_SRat_mul, SRat.get_mul, steps_SRat_lit, SRat.get_lit,
    steps_SRat_add, SRat.get_add, steps_SRat_floor, SRat.get_floor, steps_SRat_zpow2,
    Int.floor_intCast, hP.sPrime, ratLen_half, ratLen_zero, ratLen_eight]
  -- the prefix values
  have hsq : ratLen ((2 ^ P.ks : ℕ) : ℚ) ≤ U ^ 2 + 4 := by
    rw [ratLen_natCast, bitLen_two_pow]; omega
  have hspq : ((2 ^ P.ks : ℕ) : ℚ) ≤ (U : ℚ) ^ 4 := by exact_mod_cast hsp
  have ht := ratLen_mul_le β.get ((2 ^ P.ks : ℕ) : ℚ)
  have ht' := ratLen_add_le (β.get * ((2 ^ P.ks : ℕ) : ℚ)) (1 / 2)
  rw [ratLen_half] at ht'
  set h := ⌊β.get * ((2 ^ P.ks : ℕ) : ℚ) + 1 / 2⌋ with hh
  have hhb : h.natAbs ≤ U ^ 7 + 2 := by
    have a1 : |β.get * ((2 ^ P.ks : ℕ) : ℚ)| ≤ (U : ℚ) ^ 3 * U ^ 4 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ ((2 ^ P.ks : ℕ) : ℚ))]
      exact mul_le_mul hβ hspq (by positivity) (by positivity)
    have a2 := Int.floor_le (β.get * ((2 ^ P.ks : ℕ) : ℚ) + 1 / 2)
    have a3 := Int.lt_floor_add_one (β.get * ((2 ^ P.ks : ℕ) : ℚ) + 1 / 2)
    have a4 := abs_le.1 a1
    have : ((h.natAbs : ℤ) : ℚ) ≤ ((U ^ 7 + 2 : ℕ) : ℚ) := by
      rw [Int.natCast_natAbs, Int.cast_abs]; push_cast
      rw [← hh] at a2 a3
      have e7 : (U : ℚ) ^ 3 * U ^ 4 = U ^ 7 := by ring
      rw [abs_le]; constructor <;> nlinarith
    exact_mod_cast this
  have hhl := ratLen_int_le hhb
  have htg := ratLen_zpow_le h
  -- the bisection loop
  generalize hR : Charged.repeatFor _ P.depth _ = R
  obtain ⟨⟨⟨hb, h0, h8⟩, _⟩, hs⟩ : ((BInt (2 ^ P.depth) R.val.1.get ∧ 0 ≤ R.val.1.get ∧
      R.val.1.get ≤ 8) ∧ (BInt (2 ^ P.depth) R.val.2.get ∧ 0 ≤ R.val.2.get ∧
      R.val.2.get ≤ 8)) ∧ Charged.steps rate R ≤ P.depth * U ^ 16 := by
    subst hR
    refine repeatFor_inv _ (fun r (st : SRat × SRat) => (BInt (2 ^ r) st.1.get ∧
      0 ≤ st.1.get ∧ st.1.get ≤ 8) ∧ (BInt (2 ^ r) st.2.get ∧ 0 ≤ st.2.get ∧ st.2.get ≤ 8))
      (U ^ 16) P.depth _
      ⟨⟨by simp [BInt.zero], by simp, by simp⟩, ⟨by simpa using BInt.natCast 1 8, by simp,
        by norm_num⟩⟩ ?_
    rintro r st hr ⟨⟨b1, l1, u1⟩, ⟨b2, l2, u2⟩⟩
    simp only [Charged.steps_bind, costVb, steps_SRat_add, SRat.get_add, steps_SRat_mul,
      SRat.get_lit, ratLen_half, steps_SRat_le, SRat.val_le]
    simp only [SRat.get_zpow2, SRat.get_floor, SRat.get_add, SRat.get_mul, SNat.get_toRat,
      SRat.get_lit, hP.sPrime, Int.floor_intCast, ← hh]
    have hr2 : r ≤ U ^ 2 := by omega
    have hp0 : (1 : ℚ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
    have hp1 : (1 : ℚ) ≤ 2 ^ (r + 1) := one_le_pow₀ (by norm_num)
    have lb1 : ratLen st.1.get ≤ 8 + 3 * r + 6 :=
      ratLen_dyadic_le b1 (by rw [abs_of_nonneg l1]; push_cast; nlinarith)
    have lb2 : ratLen st.2.get ≤ 8 + 3 * r + 6 :=
      ratLen_dyadic_le b2 (by rw [abs_of_nonneg l2]; push_cast; nlinarith)
    have ls : ratLen (st.1.get + st.2.get) ≤ 16 + 3 * r + 6 :=
      ratLen_dyadic_le (b1.add b2) (by rw [abs_of_nonneg (by linarith)]; push_cast; nlinarith)
    have bm := bint_half (b1.add b2)
    have lm : ratLen ((st.1.get + st.2.get) * (1 / 2)) ≤ 8 + 3 * (r + 1) + 6 :=
      ratLen_dyadic_le bm (by rw [abs_of_nonneg (by linarith)]; push_cast; nlinarith)
    obtain ⟨sq1, sq2⟩ := sq_loop P.ks (4 * U ^ 2) (SRat.mul (SRat.add st.1 st.2).val
      (SRat.lit (1 / 2)).val).val (by simp only [SRat.get_mul, SRat.get_add, SRat.get_lit]; omega)
    generalize Charged.repeatFor (fun _ acc => SRat.mul acc acc) P.ks
      (SRat.mul (SRat.add st.1 st.2).val (SRat.lit (1 / 2)).val).val = PW at sq1 sq2 ⊢
    have e2 : 2 ^ P.ks * (4 * U ^ 2) ≤ 4 * U ^ 6 := by
      have := Nat.mul_le_mul_right (4 * U ^ 2) hsp
      have e : U ^ 4 * (4 * U ^ 2) = 4 * U ^ 6 := by ring
      omega
    have m1 : P.ks * ((2 ^ P.ks * (4 * U ^ 2) + 1) * (2 ^ P.ks * (4 * U ^ 2) + 1)) ≤
        U ^ 2 * ((4 * U ^ 6 + 1) * (4 * U ^ 6 + 1)) :=
      Nat.mul_le_mul hks (Nat.mul_le_mul (by omega) (by omega))
    have e3 : U ^ 2 * ((4 * U ^ 6 + 1) * (4 * U ^ 6 + 1)) = 16 * U ^ 14 + 8 * U ^ 8 + U ^ 2 := by
      ring
    have m2 : (ratLen PW.val.get + 1) * (ratLen ((2 : ℚ) ^ h) + 1) ≤
        (4 * U ^ 6 + 1) * (3 * U ^ 7 + 14) := Nat.mul_le_mul (by omega) (by omega)
    have e4 : (4 * U ^ 6 + 1) * (3 * U ^ 7 + 14) = 12 * U ^ 13 + 3 * U ^ 7 + 56 * U ^ 6 + 14 := by
      ring
    have m3 : (ratLen st.1.get + 1) * (ratLen st.2.get + 1) ≤ (4 * U ^ 2) * (4 * U ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e5 : (4 * U ^ 2) * (4 * U ^ 2) = 16 * U ^ 4 := by ring
    have m4 : (ratLen (st.1.get + st.2.get) + 1) * (5 + 1) ≤ (4 * U ^ 2) * 6 :=
      Nat.mul_le_mul (by omega) le_rfl
    have q16 : U ^ 14 ≤ U ^ 15 := pw_mono (by omega) (by norm_num)
    by_cases hbel : PW.val.get ≤ (2 : ℚ) ^ h
    · simp only [hbel, decide_true, ↓reduceIte, costVp, Charged.steps_pure, SRat.get_mul,
        SRat.get_add, SRat.get_lit]
      refine ⟨⟨⟨bm, by positivity, by linarith⟩, ⟨bint_up b2, l2, u2⟩⟩, by omega⟩
    · simp only [hbel, decide_false, Bool.false_eq_true, ↓reduceIte, costVp, Charged.steps_pure,
        SRat.get_mul, SRat.get_add, SRat.get_lit]
      refine ⟨⟨⟨bint_up b1, l1, u1⟩, ⟨bm, by positivity, by linarith⟩⟩, by omega⟩
  refine ⟨⟨hb, h0, h8⟩, ?_⟩
  have m1 : P.depth * U ^ 16 ≤ U ^ 2 * U ^ 16 := Nat.mul_le_mul_right _ hdep
  have e1 : U ^ 2 * U ^ 16 = U ^ 18 := by ring
  have m2 : (ratLen β.get + 1) * (ratLen ((2 ^ P.ks : ℕ) : ℚ) + 1) ≤ (U ^ 4 + 1) * (U ^ 2 + 5) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e2 : (U ^ 4 + 1) * (U ^ 2 + 5) = U ^ 6 + 5 * U ^ 4 + U ^ 2 + 5 := by ring
  have m3 : (ratLen (β.get * ((2 ^ P.ks : ℕ) : ℚ)) + 1) * (5 + 1) ≤ (2 * U ^ 4) * 6 :=
    Nat.mul_le_mul (by omega) le_rfl
  have m4 : (ratLen (β.get * ((2 ^ P.ks : ℕ) : ℚ) + 1 / 2) + 1) *
      (ratLen (β.get * ((2 ^ P.ks : ℕ) : ℚ) + 1 / 2) + 1) ≤ (5 * U ^ 4) * (5 * U ^ 4) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e4 : (5 * U ^ 4) * (5 * U ^ 4) = 25 * U ^ 8 := by ring
  have hbk : bitLen (2 ^ P.ks) ≤ U ^ 2 + 2 := by rw [bitLen_two_pow]; omega
  omega


/-- INTERNAL: value and price of `Program.clog2`. -/
theorem clog2_spec (x : SNat) : (clog2 x).val.get = Nat.size (x.get - 1) ∧
    Charged.steps rate (clog2 x) ≤ 2 * bitLen x.get + 4 := by
  unfold clog2
  simp only [Charged.steps_bind, costVb, steps_SNat_lit, steps_SNat_sub, steps_SNat_size,
    SNat.get_lit, SNat.get_sub, SNat.get_size]
  refine ⟨trivial, ?_⟩
  have := bitLen_mono (Nat.sub_le x.get 1)
  rw [bitLen_one]
  omega

/-- INTERNAL: `Nat.size (c - 1) ≤ bitLen c`. -/
theorem size_pred_le (c : ℕ) : Nat.size (c - 1) ≤ bitLen c := by
  have := bitLen_mono (Nat.sub_le c 1); unfold bitLen at this ⊢; omega

/-- INTERNAL: value and price of the dyadic integer draw: `⌊M Y/2^k⌋ ≤ M`, and `< M` when
`M > 0`; price `≤ U^32` for `bitLen M ≤ U + 2` and `ratLen ζ ≤ U^15`. -/
theorem dyadicDraw_spec {U : ℕ} (hU : 2 ^ 20 ≤ U) (tape : Coins ℕ) (M : SNat) (ζ : SRat)
    (cur : ℕ) (hM : bitLen M.get ≤ U + 2) (hζ : ratLen ζ.get ≤ U ^ 15) :
    ((dyadicDraw tape M ζ cur).val.1.get ≤ M.get ∧
      (0 < M.get → (dyadicDraw tape M ζ cur).val.1.get < M.get)) ∧
      Charged.steps rate (dyadicDraw tape M ζ cur) ≤ U ^ 32 := by
  have p15 : 100 * U ^ 1 ≤ U ^ 15 := (pw_absorb hU (by norm_num) rfl).trans
    (pw_mono (by omega) (by norm_num))
  have p16 : 100 * U ^ 15 ≤ U ^ 16 := pw_absorb hU (by norm_num) rfl
  have p31 : 100 * U ^ 16 ≤ U ^ 31 := (pw_absorb hU (by norm_num) rfl).trans
    (pw_mono (by omega) (by norm_num))
  have p32 : 100 * U ^ 31 ≤ U ^ 32 := pw_absorb hU (by norm_num) rfl
  rw [pow_one] at p15
  unfold dyadicDraw
  simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SNat_toRat,
    SNat.get_toRat, steps_SRat_div, SRat.get_div, steps_SRat_natCeil, 
    steps_SNat_index, SNat.val_index, steps_SNat_mul, SNat.get_mul, steps_SNat_pow2,
    SNat.get_pow2, steps_SNat_div, SNat.get_div]
  obtain ⟨c1, c2⟩ := clog2_spec (SRat.natCeil (SRat.div (SNat.toRat M).val ζ).val).val
  simp only [SRat.get_natCeil, SRat.get_div, SNat.get_toRat] at c1 c2
  generalize clog2 (SRat.natCeil (SRat.div (SNat.toRat M).val ζ).val).val = PK at c1 c2 ⊢
  rw [c1]
  set q := (M.get : ℚ) / ζ.get with hq
  have lq : ratLen q ≤ U + 4 + U ^ 15 := by
    have := ratLen_div_le (M.get : ℚ) ζ.get
    rw [ratLen_natCast, ← hq] at this; omega
  have lc := bitLen_natCeil_le q
  have hk := size_pred_le ⌈q⌉₊
  set k := Nat.size (⌈q⌉₊ - 1) with hkdef
  obtain ⟨u1, u2, u3⟩ := uniformBits_cost tape k cur
  have hY := bitLen_le_of_lt_two_pow u1
  generalize uniformBits tape k cur = PY at u1 u2 u3 hY ⊢
  refine ⟨⟨Nat.div_le_of_le_mul ((Nat.mul_le_mul_left M.get u1.le).trans_eq (mul_comm _ _)),
    fun hM0 => ?_⟩, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul (by positivity)]
    exact Nat.mul_lt_mul_of_pos_left u1 hM0
  · have hkU : k ≤ 2 * U ^ 15 := by omega
    have hMq : ratLen (M.get : ℚ) = bitLen M.get + 2 := ratLen_natCast _
    have m1 : (ratLen (M.get : ℚ) + 1) * (ratLen ζ.get + 1) ≤ (U + 5) * (U ^ 15 + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have m2 : (ratLen q + 1) * (ratLen q + 1) ≤ (2 * U ^ 15) * (2 * U ^ 15) :=
      Nat.mul_le_mul (by omega) (by omega)
    have m3 : k * (4 * k + 8) ≤ (2 * U ^ 15) * (8 * U ^ 15 + 8) := Nat.mul_le_mul hkU (by omega)
    have m4 : bitLen M.get * bitLen PY.val.1.get ≤ (U + 2) * (2 * U ^ 15 + 1) :=
      Nat.mul_le_mul hM (by omega)
    have hMY := bitLen_mul_le M.get PY.val.1.get
    have m5 : bitLen (M.get * PY.val.1.get) * bitLen (2 ^ k) ≤
        (3 * U ^ 15) * (2 * U ^ 15 + 2) := Nat.mul_le_mul (by omega) (by rw [bitLen_two_pow]; omega)
    have e1 : (U + 5) * (U ^ 15 + 1) = U ^ 16 + 5 * U ^ 15 + U + 5 := by ring
    have e2 : (2 * U ^ 15) * (2 * U ^ 15) = 4 * U ^ 30 := by ring
    have e3 : (2 * U ^ 15) * (8 * U ^ 15 + 8) = 16 * U ^ 30 + 16 * U ^ 15 := by ring
    have e4 : (U + 2) * (2 * U ^ 15 + 1) = 2 * U ^ 16 + 4 * U ^ 15 + U + 2 := by ring
    have e5 : (3 * U ^ 15) * (2 * U ^ 15 + 2) = 6 * U ^ 30 + 6 * U ^ 15 := by ring
    have p30 : 100 * U ^ 16 ≤ U ^ 30 := (pw_absorb hU (by norm_num) rfl).trans
      (pw_mono (by omega) (by norm_num))
    have p31' : 100 * U ^ 30 ≤ U ^ 31 := pw_absorb hU (by norm_num) rfl
    have := bitLen_le_succ k
    omega


/-- INTERNAL: value and price of `ceilDivN`. -/
theorem ceilDivN_spec (a b : SNat) : (ceilDivN a b).val.get = (a.get + b.get - 1) / b.get ∧
    Charged.steps rate (ceilDivN a b) ≤
      2 + (bitLen a.get + bitLen b.get) + (bitLen (a.get + b.get) + 2) +
        bitLen (a.get + b.get) * bitLen b.get := by
  unfold ceilDivN
  simp only [Charged.steps_bind, costVb, steps_SNat_lit, steps_SNat_add, steps_SNat_sub,
    steps_SNat_div, SNat.get_lit, SNat.get_add, SNat.get_sub, SNat.get_div, bitLen_one]
  refine ⟨trivial, ?_⟩
  have := bitLen_mono (Nat.sub_le (a.get + b.get) 1)
  have := Nat.mul_le_mul_right (bitLen b.get) this
  omega

/-- INTERNAL: `⌈a/B⌉ ≤ c` for `a ≤ c B`. -/
theorem ceil_div_le {a B c : ℕ} (hB : 1 ≤ B) (h : a ≤ c * B) : (a + B - 1) / B ≤ c := by
  have : (a + B - 1) / B < c + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    have : (c + 1) * B = c * B + B := by ring
    omega
  omega

/-- INTERNAL: the bin offsets: an integer point of the extended box, the product of the
interval lengths of length `≤ 2U^2`, for `≤ U^35`. -/
theorem binOffsets_spec {U : ℕ} {C : Ctx} {x y : List SNat} (E : Env U C x y) (P : OParams)
    (hP : POK U C P) (tape : Coins ℕ) (v : List SNat) (hv : BoxV C v) (cur : ℕ) :
    (PtOK C (binOffsets C P tape v cur).val.1 ∧
      bitLen (binOffsets C P tape v cur).val.2.1.get ≤ 2 * U ^ 2) ∧
      Charged.steps rate (binOffsets C P tape v cur) ≤ U ^ 35 := by
  have hU := E.big
  have hC := E.size
  have hnF := hC.nFree_le
  have hB1 := hC.B_pos
  have hBU := hC.B_le
  have p2 : 100 * U ^ 1 ≤ U ^ 2 := pw_absorb hU (by norm_num) rfl
  have p3 : 100 * U ^ 2 ≤ U ^ 3 := pw_absorb hU (by norm_num) rfl
  have p4 : 100 * U ^ 3 ≤ U ^ 4 := pw_absorb hU (by norm_num) rfl
  have p32 : 100 * U ^ 4 ≤ U ^ 32 := (pw_absorb hU (by norm_num) rfl).trans
    (pw_mono (by omega) (by norm_num))
  have p33 : 100 * U ^ 32 ≤ U ^ 33 := pw_absorb hU (by norm_num) rfl
  have p34 : 100 * U ^ 33 ≤ U ^ 34 := pw_absorb hU (by norm_num) rfl
  have p35 : 100 * U ^ 34 ≤ U ^ 35 := pw_absorb hU (by norm_num) rfl
  rw [pow_one] at p2
  unfold binOffsets
  simp only [Charged.steps_bind, costVb, steps_SNat_lit, bitLen_one]
  generalize hR : Charged.repeatFor _ C.nFree _ = R
  obtain ⟨⟨_, hz, hpr⟩, hs⟩ : (R.val.1.length = C.nFree ∧ (∀ i < C.nFree,
      0 ≤ (R.val.1.getD i default).get ∧
      (R.val.1.getD i default).get ≤ (C.free.getD i default).2.2.get + 1 ∧
      BInt C.B.get (R.val.1.getD i default).get) ∧
      bitLen R.val.2.1.get ≤ C.nFree * (U + 2) + 2) ∧
      Charged.steps rate R ≤ C.nFree * U ^ 33 := by
    subst hR
    refine repeatFor_inv _ (fun r (st : List SRat × SNat × ℕ) => st.1.length = r ∧
      (∀ i < r, 0 ≤ (st.1.getD i default).get ∧
        (st.1.getD i default).get ≤ (C.free.getD i default).2.2.get + 1 ∧
        BInt C.B.get (st.1.getD i default).get) ∧
      bitLen st.2.1.get ≤ r * (U + 2) + 2) (U ^ 33) C.nFree _
      ⟨rfl, by simp, by simp [bitLen_one]⟩ ?_
    rintro r ⟨zs, pr, c⟩ hr ⟨hlen, hzs, hpr⟩
    dsimp only at hlen hzs hpr ⊢
    simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_get, val_get,
      steps_SNat_add, SNat.get_add, SNat.get_lit, steps_SNat_mul, SNat.get_mul, bitLen_one,
      steps_SNat_sub, SNat.get_sub, steps_SNat_toRat, steps_push, val_push]
    have hb := free_bits hC (by omega) r
    have hvr := hv r hr
    set b := (C.free.getD r default).2.2.get with hbdef
    set w := (v.getD r default).get with hwdef
    obtain ⟨cl1, cl2⟩ := ceilDivN_spec (SNat.mul (SNat.add (C.free.getD r default).2.2
      (SNat.lit 1).val).val (v.getD r default)).val C.B
    obtain ⟨ch1, ch2⟩ := ceilDivN_spec (SNat.mul (SNat.add (C.free.getD r default).2.2
      (SNat.lit 1).val).val (SNat.add (v.getD r default) (SNat.lit 1).val).val).val C.B
    simp only [SNat.get_mul, SNat.get_add, SNat.get_lit] at cl1 cl2 ch1 ch2
    rw [← hbdef, ← hwdef] at cl1 cl2 ch1 ch2
    generalize ceilDivN (SNat.mul (SNat.add (C.free.getD r default).2.2
      (SNat.lit 1).val).val (v.getD r default)).val C.B = PL at cl1 cl2 ⊢
    generalize ceilDivN (SNat.mul (SNat.add (C.free.getD r default).2.2
      (SNat.lit 1).val).val (SNat.add (v.getD r default) (SNat.lit 1).val).val).val C.B = PH
      at ch1 ch2 ⊢
    have hlo : PL.val.get ≤ b + 1 := by
      rw [cl1]; exact ceil_div_le hB1 (Nat.mul_le_mul_left _ (by omega))
    have hhi : PH.val.get ≤ b + 1 := by
      rw [ch1]; exact ceil_div_le hB1 (Nat.mul_le_mul_left _ (by omega))
    have hb1 : bitLen (b + 1) ≤ U + 2 := (bitLen_add_le' b 1).trans (by rw [bitLen_one]; omega)
    have hlen' : bitLen (PH.val.get - PL.val.get) ≤ U + 2 :=
      (bitLen_mono (by omega : PH.val.get - PL.val.get ≤ b + 1)).trans hb1
    obtain ⟨⟨d1, _⟩, d2⟩ := dyadicDraw_spec hU tape (SNat.sub PH.val PL.val).val P.ζ c
      (by rw [SNat.get_sub]; exact hlen') hP.ζ_len
    rw [SNat.get_sub] at d1
    generalize dyadicDraw tape (SNat.sub PH.val PL.val).val P.ζ c = PD at d1 d2 ⊢
    have hzk : PL.val.get + PD.val.1.get ≤ b + 1 := by omega
    refine ⟨⟨by simp [hlen], fun i hi => ?_, ?_⟩, ?_⟩
    · rw [getD_push]
      rcases Nat.lt_or_ge i r with h | h
      · simp only [show i < zs.length by omega, ↓reduceIte]; exact hzs i h
      · obtain rfl : i = r := by omega
        simp only [hlen, lt_irrefl, ↓reduceIte, SNat.get_toRat, SNat.get_add]
        refine ⟨by positivity, by rw [← hbdef]; exact_mod_cast hzk, BInt.natCast _ _⟩
    · have := bitLen_mul_le pr.get (PH.val.get - PL.val.get)
      have : (r + 1) * (U + 2) = r * (U + 2) + (U + 2) := by ring
      omega
    · have hw : bitLen w ≤ U := (bitLen_le_succ w).trans (by omega)
      have hw1 : bitLen (w + 1) ≤ U + 1 := (bitLen_le_succ _).trans (by omega)
      have hBb : bitLen C.B.get ≤ U + 1 := (bitLen_le_succ _).trans (by omega)
      have ht0 : bitLen ((b + 1) * w) ≤ 2 * U + 2 := (bitLen_mul_le _ _).trans (by omega)
      have ht1 : bitLen ((b + 1) * (w + 1)) ≤ 2 * U + 3 := (bitLen_mul_le _ _).trans (by omega)
      have ht0B : bitLen ((b + 1) * w + C.B.get) ≤ 3 * U + 3 :=
        (bitLen_add_le' _ _).trans (by omega)
      have ht1B : bitLen ((b + 1) * (w + 1) + C.B.get) ≤ 3 * U + 4 :=
        (bitLen_add_le' _ _).trans (by omega)
      have m1 : bitLen (b + 1) * bitLen w ≤ (U + 2) * U := Nat.mul_le_mul hb1 hw
      have m2 : bitLen (b + 1) * bitLen (w + 1) ≤ (U + 2) * (U + 1) := Nat.mul_le_mul hb1 hw1
      have m3 : bitLen ((b + 1) * w + C.B.get) * bitLen C.B.get ≤ (3 * U + 3) * (U + 1) :=
        Nat.mul_le_mul ht0B hBb
      have m4 : bitLen ((b + 1) * (w + 1) + C.B.get) * bitLen C.B.get ≤ (3 * U + 4) * (U + 1) :=
        Nat.mul_le_mul ht1B hBb
      have hpb : bitLen pr.get ≤ U ^ 2 + 2 * U + 2 := by
        have : r * (U + 2) ≤ U * (U + 2) := Nat.mul_le_mul_right _ (by omega)
        have e : U * (U + 2) = U ^ 2 + 2 * U := by ring
        omega
      have m5 : bitLen pr.get * bitLen (PH.val.get - PL.val.get) ≤ (U ^ 2 + 2 * U + 2) * (U + 2) :=
        Nat.mul_le_mul hpb hlen'
      have hlob : bitLen PL.val.get ≤ U + 2 := (bitLen_mono hlo).trans hb1
      have hhib : bitLen PH.val.get ≤ U + 2 := (bitLen_mono hhi).trans hb1
      have hoff : bitLen PD.val.1.get ≤ U + 2 := (bitLen_mono (by omega)).trans hb1
      have hzkb : bitLen (PL.val.get + PD.val.1.get) ≤ U + 2 := (bitLen_mono hzk).trans hb1
      have e1 : (U + 2) * U = U ^ 2 + 2 * U := by ring
      have e2 : (U + 2) * (U + 1) = U ^ 2 + 3 * U + 2 := by ring
      have e3 : (3 * U + 3) * (U + 1) = 3 * U ^ 2 + 6 * U + 3 := by ring
      have e4 : (3 * U + 4) * (U + 1) = 3 * U ^ 2 + 7 * U + 4 := by ring
      have e5 : (U ^ 2 + 2 * U + 2) * (U + 2) = U ^ 3 + 4 * U ^ 2 + 6 * U + 4 := by ring
      have q1 : U ^ 2 ≤ U ^ 3 := pw_mono (by omega) (by norm_num)
      generalize bitLen (b + 1) * bitLen w = X1 at m1 ⊢
      generalize bitLen (b + 1) * bitLen (w + 1) = X2 at m2 ⊢
      generalize bitLen ((b + 1) * w + C.B.get) * bitLen C.B.get = X3 at m3 cl2
      generalize bitLen ((b + 1) * (w + 1) + C.B.get) * bitLen C.B.get = X4 at m4 ch2
      generalize bitLen pr.get * bitLen (PH.val.get - PL.val.get) = X5 at m5 ⊢
      rw [e1] at m1; rw [e2] at m2; rw [e3] at m3; rw [e4] at m4; rw [e5] at m5
      have hd2 : Charged.steps rate PD ≤ U ^ 32 := d2
      have hl := hlen
      clear hzs d1 hbdef hwdef cl1 ch1 d2 hlen
      clear_value b w
      linarith
  refine ⟨⟨hz, ?_⟩, ?_⟩
  · have : C.nFree * (U + 2) ≤ U * (U + 2) := Nat.mul_le_mul_right _ hnF
    have e : U * (U + 2) = U ^ 2 + 2 * U := by ring
    omega
  · have : C.nFree * U ^ 33 ≤ U * U ^ 33 := Nat.mul_le_mul_right _ hnF
    have e : U * U ^ 33 = U ^ 34 := by ring
    omega


/-- INTERNAL: the length of a `(1/D)ℤ` value of magnitude `≤ r 2^G`. -/
theorem ratLen_BInt_mag {q : ℚ} {D r G : ℕ} (hD : 1 ≤ D) (hq : BInt D q)
    (hr : |q| ≤ r * 2 ^ G) : ratLen q ≤ r + G + 2 + 2 * bitLen D := by
  have h1 : |q| ≤ 2 ^ (r + G) := by
    have : (r : ℚ) ≤ 2 ^ r := by exact_mod_cast (Nat.lt_two_pow_self).le
    rw [pow_add]; exact hr.trans (mul_le_mul_of_nonneg_right this (by positivity))
  exact ratLen_le_of_BInt hD hq h1

/-- INTERNAL: the length of a difference. -/
theorem ratLen_sub_le (x y : ℚ) : ratLen (x - y) ≤ 2 * (ratLen x + ratLen y) := by
  rw [sub_eq_add_neg]; have := ratLen_add_le x (-y); rwa [ratLen_neg] at this

/-- INTERNAL: one correction sample `(B^e |I| / M_f) · approx` lies in `(1/(max(M_f,1) 2^depth))ℤ`
and has magnitude `≤ 8 B^e |I|`. -/
theorem sample_BInt (Mf L d : ℕ) (ap : ℚ) (hap : BInt (2 ^ d) ap) (h0 : 0 ≤ ap) (h8 : ap ≤ 8) :
    BInt (max Mf 1 * 2 ^ d) ((L : ℚ) / Mf * ap) ∧ |(L : ℚ) / Mf * ap| ≤ 8 * L := by
  rcases Nat.eq_zero_or_pos Mf with hM | hM
  · subst hM; simp [BInt.zero]
  · have hM' : (0 : ℚ) < Mf := by exact_mod_cast hM
    obtain ⟨a, ha⟩ := hap
    refine ⟨⟨L * a, ?_⟩, ?_⟩
    · rw [max_eq_left hM]; push_cast at ha ⊢
      rw [← ha]; field_simp
    · rw [abs_mul, abs_of_nonneg h0, abs_of_nonneg (by positivity)]
      have h1 : (L : ℚ) / Mf ≤ L := div_le_self (by positivity) (by exact_mod_cast hM)
      have h2 : (0 : ℚ) ≤ L / Mf := by positivity
      nlinarith

/-- INTERNAL: value and price of `corrAvg` at a level `j ≤ U`. -/
theorem corrAvg_spec {U : ℕ} {C : Ctx} {x y : List SNat} (E : Env U C x y) (P : OParams)
    (hP : POK U C P) (tape : Coins ℕ) (j : ℕ) (hjU : j ≤ U) (cur : ℕ) :
    ratLen (corrAvg C P tape x y j cur).val.1.get ≤ U ^ 12 ∧
      Charged.steps rate (corrAvg C P tape x y j cur) ≤ U ^ 47 := by
  have hU := E.big
  have hC := E.size
  have hN := hP.N_le
  have hdep := hP.depth_le
  have hnF := hC.nFree_le
  have hBU := hC.B_le
  have hMf := hC.Mf_bits
  have p3 : 100 * U ^ 2 ≤ U ^ 3 := pw_absorb hU (by norm_num) rfl
  have p4 : 100 * U ^ 3 ≤ U ^ 4 := pw_absorb hU (by norm_num) rfl
  have p5 : 100 * U ^ 4 ≤ U ^ 5 := pw_absorb hU (by norm_num) rfl
  have p6 : 100 * U ^ 5 ≤ U ^ 6 := pw_absorb hU (by norm_num) rfl
  have p7 : 100 * U ^ 6 ≤ U ^ 7 := pw_absorb hU (by norm_num) rfl
  have p8 : 100 * U ^ 7 ≤ U ^ 8 := pw_absorb hU (by norm_num) rfl
  have p9 : 100 * U ^ 8 ≤ U ^ 9 := pw_absorb hU (by norm_num) rfl
  have p10 : 100 * U ^ 9 ≤ U ^ 10 := pw_absorb hU (by norm_num) rfl
  have p11 : 100 * U ^ 10 ≤ U ^ 11 := pw_absorb hU (by norm_num) rfl
  have p12 : 100 * U ^ 11 ≤ U ^ 12 := pw_absorb hU (by norm_num) rfl
  have q1 : 100 * U ^ 1 ≤ U ^ 2 := pw_absorb hU (by norm_num) rfl
  rw [pow_one] at q1
  set D := max C.Mf.get 1 * 2 ^ P.depth with hD
  have hD1 : 1 ≤ D := Nat.mul_pos (lt_of_lt_of_le Nat.one_pos (le_max_right _ _)) (by positivity)
  have hDb : bitLen D ≤ U ^ 2 + U + 3 := by
    show bitLen (max C.Mf.get 1 * 2 ^ P.depth) ≤ _
    have h1 := bitLen_mul_le (max C.Mf.get 1) (2 ^ P.depth)
    rw [bitLen_two_pow] at h1
    have h2 : bitLen (max C.Mf.get 1) ≤ U + 1 := by
      rcases le_total C.Mf.get 1 with h | h
      · rw [max_eq_right h, bitLen_one]; omega
      · rw [max_eq_left h]; omega
    omega
  set G := 4 * U ^ 2 + 3 with hG
  have hBe : bitLen P.Be.get ≤ U ^ 2 + U + 2 := by
    rw [hP.Be]
    have := bitLen_pow_le C.B.get C.nFree
    have h2 : bitLen C.B.get ≤ U + 1 := (bitLen_le_succ _).trans (by omega)
    have : C.nFree * bitLen C.B.get ≤ U * (U + 1) := Nat.mul_le_mul hnF h2
    have e : U * (U + 1) = U ^ 2 + U := by ring
    omega
  unfold corrAvg
  simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SNat_lit,
    steps_SNat_toRat, steps_SRat_lit, steps_SRat_div, SRat.get_div, SNat.get_lit,
    ratLen_zero]
  generalize hR : Charged.repeatFor _ P.N _ = R
  obtain ⟨⟨hb, hm⟩, hs⟩ : (BInt D R.val.1.get ∧ |R.val.1.get| ≤ (P.N : ℚ) * 2 ^ G) ∧
      Charged.steps rate R ≤ P.N * U ^ 36 := by
    subst hR
    refine repeatFor_inv _ (fun r (st : SRat × ℕ) => BInt D st.1.get ∧
      |st.1.get| ≤ (r : ℚ) * 2 ^ G) (U ^ 36) P.N _ ⟨by simp [BInt.zero], by simp⟩ ?_
    rintro r st hr ⟨hb, hm⟩
    simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SRat_mul,
      SRat.get_mul, steps_SRat_div, SRat.get_div, steps_SRat_sub, 
      steps_SNat_mul, SNat.get_mul, steps_SNat_toRat, SNat.get_toRat, steps_SRat_add,
      SRat.get_add]
    have hj : (SNat.toRat (SNat.lit j).val).val.get = (j : ℚ) := by simp
    generalize SNat.toRat (SNat.lit j).val = Pj at hj ⊢
    obtain ⟨hv, s1⟩ := sampleBin_spec E P hP tape Pj.val j hj hjU st.2
    generalize sampleBin C P tape Pj.val x y st.2 = PS at hv s1 ⊢
    obtain ⟨⟨kv, hkv, hkvb⟩, s2⟩ := binExp_spec E Pj.val j hj hjU PS.val.1 hv
    generalize binExp C Pj.val x y PS.val.1 = PK at hkv s2 ⊢
    obtain ⟨⟨hz, hlp⟩, s3⟩ := binOffsets_spec E P hP tape PS.val.1 hv PS.val.2
    generalize binOffsets C P tape PS.val.1 PS.val.2 = PO at hz hlp s3 ⊢
    obtain ⟨d1, d2, s4⟩ := penalty_spec E _ hz
    generalize penalty C x y PO.val.1 = PD at d1 d2 s4 ⊢
    simp only [SNat.get_lit]
    have hβv : (SRat.sub PK.val (SRat.div (SRat.mul Pj.val PD.val).val C.Hq).val).val.get =
        (kv : ℚ) - j * PD.val.get / C.H.get := by
      simp only [SRat.get_sub, SRat.get_div, SRat.get_mul, hj, hkv, hC.Hq_eq]
    rw [hkv, hC.Hq_eq]
    have hH1 : (1 : ℚ) ≤ C.H.get := by exact_mod_cast hC.H_pos
    have lj : ratLen (j : ℚ) ≤ U + 3 := ratLen_nat_le hjU
    have lH : ratLen (C.H.get : ℚ) ≤ U + 3 := ratLen_nat_le hC.H_le
    have lk : ratLen (kv : ℚ) ≤ U ^ 2 + 4 := by have := ratLen_int_le hkvb; omega
    have ljD := ratLen_mul_le (j : ℚ) PD.val.get
    have ljDH := ratLen_div_le ((j : ℚ) * PD.val.get) (C.H.get : ℚ)
    have lβ := ratLen_sub_le (kv : ℚ) ((j : ℚ) * PD.val.get / C.H.get)
    have hjD : |(j : ℚ) * PD.val.get / C.H.get| ≤ (U : ℚ) ^ 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ j),
        abs_of_nonneg (by positivity : (0 : ℚ) ≤ C.H.get), div_le_iff₀ (by linarith)]
      have : (j : ℚ) ≤ U := by exact_mod_cast hjU
      have h0 : (0 : ℚ) ≤ U := by positivity
      have : (j : ℚ) * |PD.val.get| ≤ U * U := mul_le_mul this d1 (abs_nonneg _) h0
      nlinarith [abs_nonneg PD.val.get, sq_nonneg (U : ℚ)]
    have hkq : |(kv : ℚ)| ≤ (U : ℚ) ^ 2 + 1 := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs]; exact_mod_cast hkvb
    have hβl : ratLen (SRat.sub PK.val (SRat.div (SRat.mul Pj.val PD.val).val C.Hq).val).val.get
        ≤ U ^ 4 := by rw [hβv]; omega
    have hβa : |(SRat.sub PK.val (SRat.div (SRat.mul Pj.val PD.val).val C.Hq).val).val.get|
        ≤ (U : ℚ) ^ 3 := by
      rw [hβv]
      have h3 : (U : ℚ) ^ 2 * 100 ≤ U ^ 3 := by exact_mod_cast (by linarith : U ^ 2 * 100 ≤ U ^ 3)
      have h2 : (1 : ℚ) ≤ U ^ 2 := by exact_mod_cast Nat.one_le_pow _ _ (by omega)
      calc _ ≤ |(kv : ℚ)| + |(j : ℚ) * PD.val.get / C.H.get| := abs_sub _ _
        _ ≤ _ := by linarith
    obtain ⟨⟨a1, a2, a3⟩, s5⟩ := pow2Approx_spec hU P hP _ hβl hβa
    generalize pow2Approx P (SRat.sub PK.val (SRat.div (SRat.mul Pj.val PD.val).val
      C.Hq).val).val = PA at a1 a2 a3 s5 ⊢
    obtain ⟨b1, b2⟩ := sample_BInt C.Mf.get (P.Be.get * PO.val.2.1.get) P.depth PA.val.get a1 a2 a3
    have hLb : bitLen (P.Be.get * PO.val.2.1.get) ≤ 4 * U ^ 2 :=
      (bitLen_mul_le _ _).trans (by omega)
    have hL : ((P.Be.get * PO.val.2.1.get : ℕ) : ℚ) < 2 ^ (4 * U ^ 2) :=
      lt_two_pow_of_bitLen_le hLb
    refine ⟨⟨hb.add b1, ?_⟩, ?_⟩
    · calc _ ≤ |st.1.get| + |((P.Be.get * PO.val.2.1.get : ℕ) : ℚ) / C.Mf.get * PA.val.get| :=
            abs_add_le _ _
        _ ≤ r * 2 ^ G + 2 ^ G := by
          have : (2 : ℚ) ^ G = 8 * 2 ^ (4 * U ^ 2) := by
            rw [hG, pow_add]; norm_num; ring
          linarith
        _ = ((r + 1 : ℕ) : ℚ) * 2 ^ G := by push_cast; ring
    · have hrN : r ≤ U ^ 10 := by omega
      have ls : ratLen st.1.get ≤ r + G + 2 + 2 * bitLen D := ratLen_BInt_mag hD1 hb hm
      have lA : ratLen PA.val.get ≤ 1 + 3 + 2 + 2 * bitLen (2 ^ P.depth) :=
        ratLen_BInt_mag (r := 1) (G := 3) Nat.one_le_two_pow a1
          (by rw [abs_of_nonneg a2]; norm_num; linarith)
      rw [bitLen_two_pow] at lA
      have lL : ratLen ((P.Be.get * PO.val.2.1.get : ℕ) : ℚ) ≤ 4 * U ^ 2 + 2 := by
        rw [ratLen_natCast]; omega
      have lM : ratLen (C.Mf.get : ℚ) ≤ U + 2 := by rw [ratLen_natCast]; omega
      have lα := ratLen_div_le ((P.Be.get * PO.val.2.1.get : ℕ) : ℚ) (C.Mf.get : ℚ)
      have lsm := ratLen_mul_le (((P.Be.get * PO.val.2.1.get : ℕ) : ℚ) / C.Mf.get) PA.val.get
      have hGD : r + G + 2 + 2 * bitLen D ≤ U ^ 10 + 6 * U ^ 2 + 2 * U + 11 := by omega
      have m1 : (ratLen (j : ℚ) + 1) * (ratLen PD.val.get + 1) ≤ U ^ 4 + 4 * U ^ 3 + U + 4 :=
        (Nat.mul_le_mul (by omega : ratLen (j : ℚ) + 1 ≤ U + 4)
          (by omega : ratLen PD.val.get + 1 ≤ U ^ 3 + 1)).trans (le_of_eq (by ring))
      have m2 : (ratLen ((j : ℚ) * PD.val.get) + 1) * (ratLen (C.H.get : ℚ) + 1) ≤
          U ^ 4 + 4 * U ^ 3 + U ^ 2 + 8 * U + 16 :=
        (Nat.mul_le_mul (by omega : ratLen ((j : ℚ) * PD.val.get) + 1 ≤ U ^ 3 + U + 4)
          (by omega : ratLen (C.H.get : ℚ) + 1 ≤ U + 4)).trans (le_of_eq (by ring))
      have m3 : (ratLen (kv : ℚ) + 1) * (ratLen ((j : ℚ) * PD.val.get / C.H.get) + 1) ≤
          U ^ 5 + 2 * U ^ 3 + 5 * U ^ 3 + 7 * U ^ 2 + 10 * U + 35 :=
        (Nat.mul_le_mul (by omega : ratLen (kv : ℚ) + 1 ≤ U ^ 2 + 5)
          (by omega : ratLen ((j : ℚ) * PD.val.get / C.H.get) + 1 ≤ U ^ 3 + 2 * U + 7)).trans
          (le_of_eq (by ring))
      have m4 : bitLen P.Be.get * bitLen PO.val.2.1.get ≤ 2 * U ^ 4 + 2 * U ^ 3 + 4 * U ^ 2 :=
        (Nat.mul_le_mul hBe hlp).trans (le_of_eq (by ring))
      have m5 : (ratLen ((P.Be.get * PO.val.2.1.get : ℕ) : ℚ) + 1) * (ratLen (C.Mf.get : ℚ) + 1) ≤
          4 * U ^ 3 + 12 * U ^ 2 + 3 * U + 9 :=
        (Nat.mul_le_mul (by omega : ratLen ((P.Be.get * PO.val.2.1.get : ℕ) : ℚ) + 1 ≤ 4 * U ^ 2 + 3)
          (by omega : ratLen (C.Mf.get : ℚ) + 1 ≤ U + 3)).trans (le_of_eq (by ring))
      have m6 : (ratLen (((P.Be.get * PO.val.2.1.get : ℕ) : ℚ) / C.Mf.get) + 1) *
          (ratLen PA.val.get + 1) ≤ (5 * U ^ 2) * (3 * U ^ 2) :=
        Nat.mul_le_mul (by omega) (by omega)
      have m7 : (ratLen st.1.get + 1) *
          (ratLen (((P.Be.get * PO.val.2.1.get : ℕ) : ℚ) / C.Mf.get * PA.val.get) + 1) ≤
          (2 * U ^ 10) * (8 * U ^ 2) := Nat.mul_le_mul (by omega) (by omega)
      have e6 : (5 * U ^ 2) * (3 * U ^ 2) = 15 * U ^ 4 := by ring
      have e7 : (2 * U ^ 10) * (8 * U ^ 2) = 16 * U ^ 12 := by ring
      have p13 : 100 * U ^ 12 ≤ U ^ 13 := pw_absorb hU (by norm_num) rfl
      have p19 : 100 * U ^ 13 ≤ U ^ 19 := (pw_absorb hU (by norm_num) rfl).trans
        (pw_mono (by omega) (by norm_num))
      have p35 : 100 * U ^ 19 ≤ U ^ 35 := (pw_absorb hU (by norm_num) rfl).trans
        (pw_mono (by omega) (by norm_num))
      have p36 : 100 * U ^ 35 ≤ U ^ 36 := pw_absorb hU (by norm_num) rfl
      have hLb' := hLb
      clear_value D G
      linarith
  have ls : ratLen R.val.1.get ≤ P.N + G + 2 + 2 * bitLen D := ratLen_BInt_mag hD1 hb hm
  have lN : ratLen P.Nq.get ≤ U ^ 10 + 3 := by
    rw [hP.Nq, ratLen_natCast]; have := bitLen_le_succ P.N; omega
  have hj0 : bitLen j ≤ U + 1 := (bitLen_le_succ _).trans (by omega)
  have l1 := ratLen_div_le R.val.1.get P.Nq.get
  have hls : ratLen R.val.1.get ≤ U ^ 10 + 6 * U ^ 2 + 2 * U + 11 := by omega
  have m1 : (ratLen R.val.1.get + 1) * (ratLen P.Nq.get + 1) ≤
      (U ^ 10 + 6 * U ^ 2 + 2 * U + 12) * (U ^ 10 + 4) := Nat.mul_le_mul (by omega) (by omega)
  have e1 : (U ^ 10 + 6 * U ^ 2 + 2 * U + 12) * (U ^ 10 + 4) =
      U ^ 20 + 6 * U ^ 12 + 2 * U ^ 11 + 16 * U ^ 10 + 24 * U ^ 2 + 8 * U + 48 := by ring
  have m2 : P.N * U ^ 36 ≤ U ^ 10 * U ^ 36 := Nat.mul_le_mul_right _ hN
  have e2 : U ^ 10 * U ^ 36 = U ^ 46 := by ring
  have q20 : U ^ 12 ≤ U ^ 20 := pw_mono (by omega) (by norm_num)
  have p21 : 100 * U ^ 20 ≤ U ^ 46 := (pw_absorb hU (by norm_num) rfl).trans
    (pw_mono (by omega) (by norm_num))
  have p47 : 100 * U ^ 46 ≤ U ^ 47 := pw_absorb hU (by norm_num) rfl
  clear_value D G
  exact ⟨by omega, by omega⟩


/-- INTERNAL: peel one bind of a straight-line program, carrying a property of its value. -/
theorem bstep {α β : Type} {p : Prog α} {f : α → Prog β} {a acc X : ℕ} {Q : β → Prop}
    (P : α → Prop) (h1 : Charged.steps rate p ≤ a) (hP : P p.val)
    (h2 : ∀ v, P v → Charged.steps rate (f v) + (acc + a) ≤ X ∧ Q (f v).val) :
    Charged.steps rate (p >>= f) + acc ≤ X ∧ Q (p >>= f).val := by
  rw [Charged.steps_bind, costVb]
  obtain ⟨h3, h4⟩ := h2 _ hP
  exact ⟨by omega, h4⟩

/-- INTERNAL: the length of a numeral. -/
theorem ratLen_lit (n : ℕ) : ratLen (OfNat.ofNat n : ℚ) = bitLen n + 2 := by
  rw [show (OfNat.ofNat n : ℚ) = ((n : ℕ) : ℚ) from rfl, ratLen_natCast]

/-- INTERNAL: `2^(size n) ≤ 2n + 1`. -/
theorem two_pow_size_le (n : ℕ) : 2 ^ Nat.size n ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have h1 : Nat.size n - 1 < Nat.size n := by
      have := Nat.size_pos.2 h; omega
    have := Nat.lt_size.1 h1
    have e : 2 ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by
      rw [← pow_succ']; congr 1; have := Nat.size_pos.2 h; omega
    omega

/-- INTERNAL: `4U < 2^U` for `U ≥ 6`. -/
theorem four_mul_lt_two_pow {U : ℕ} (h : 6 ≤ U) : 4 * U < 2 ^ U := by
  obtain ⟨t, rfl⟩ : ∃ t, U = t + 3 := ⟨U - 3, by omega⟩
  have := Nat.lt_two_pow_self (n := t)
  rw [pow_add]; omega

/-- INTERNAL: the loop computing `B^e`. -/
theorem Be_spec {U : ℕ} (C : Ctx) (hU : 2 ^ 20 ≤ U) (hC : CtxSize U C) (one : SNat)
    (h1 : one.get = 1) :
    (Charged.repeatFor (fun _ acc => SNat.mul acc C.B) C.nFree one : Prog SNat).val.get =
      C.B.get ^ C.nFree ∧
    Charged.steps rate (Charged.repeatFor (fun _ acc => SNat.mul acc C.B) C.nFree one : Prog SNat)
      ≤ U ^ 5 := by
  have hnF := hC.nFree_le
  have hBb : bitLen C.B.get ≤ U + 1 := (bitLen_le_succ _).trans (by have := hC.B_le; omega)
  obtain ⟨v, s⟩ := repeatFor_inv (fun _ acc => (SNat.mul acc C.B : Prog SNat))
    (fun r (acc : SNat) => acc.get = C.B.get ^ r) ((U * (U + 1) + 2) * (U + 1)) C.nFree one
    (by simp [h1]) (by
      intro r acc hr hacc
      simp only [steps_SNat_mul, SNat.get_mul, hacc]
      refine ⟨by ring, Nat.mul_le_mul ?_ hBb⟩
      have := bitLen_pow_le C.B.get r
      have : r * bitLen C.B.get ≤ U * (U + 1) := Nat.mul_le_mul (by omega) hBb
      omega)
  refine ⟨v, s.trans ?_⟩
  have m : C.nFree * ((U * (U + 1) + 2) * (U + 1)) ≤ U * ((U * (U + 1) + 2) * (U + 1)) :=
    Nat.mul_le_mul_right _ hnF
  have e : U * ((U * (U + 1) + 2) * (U + 1)) = U ^ 4 + 2 * U ^ 3 + 3 * U ^ 2 + 2 * U := by ring
  have p5 : 100 * U ^ 4 ≤ U ^ 5 := pw_absorb hU (by norm_num) rfl
  have p4 : 100 * U ^ 3 ≤ U ^ 4 := pw_absorb hU (by norm_num) rfl
  have p3 : 100 * U ^ 2 ≤ U ^ 3 := pw_absorb hU (by norm_num) rfl
  have p2 : 100 * U ^ 1 ≤ U ^ 2 := pw_absorb hU (by norm_num) rfl
  rw [pow_one] at p2
  omega


/-- INTERNAL: a product bound in one step. -/
theorem prod_le {x y A B C : ℕ} (hx : x ≤ A) (hy : y ≤ B) (h : A * B = C) : x * y ≤ C :=
  (Nat.mul_le_mul hx hy).trans_eq h

/-- INTERNAL: `ratLen 50 = 9`. -/
theorem rl50 : ratLen (50 : ℚ) = 9 := by rw [ratLen_lit]; decide
/-- INTERNAL: `ratLen 10^6 = 23`. -/
theorem rl1e6 : ratLen (1000000 : ℚ) = 23 := by rw [ratLen_lit]; decide
/-- INTERNAL: `ratLen 16 = 8`. -/
theorem rl16 : ratLen (16 : ℚ) = 8 := by rw [ratLen_lit]; decide
/-- INTERNAL: `ratLen 8 = 7`. -/
theorem rl8 : ratLen (8 : ℚ) = 7 := by rw [ratLen_lit]; decide
/-- INTERNAL: `ratLen 32 = 9`. -/
theorem rl32 : ratLen (32 : ℚ) = 9 := by rw [ratLen_lit]; decide
/-- INTERNAL: `ratLen 512 = 13`. -/
theorem rl512 : ratLen (512 : ℚ) = 13 := by rw [ratLen_lit]; decide
/-- INTERNAL: `bitLen 4 = 4`. -/
theorem bl4 : bitLen 4 = 4 := by decide
/-- INTERNAL: `bitLen 10^4 = 15`. -/
theorem bl1e4 : bitLen 10000 = 15 := by decide

set_option maxHeartbeats 4000000 in
/-- INTERNAL: the oracle parameters are polynomially bounded, and cost `≤ U^6`. -/
theorem oracleParams_spec {U : ℕ} (C : Ctx) (hU : 2 ^ 20 ≤ U) (hC : CtxSize U C) (ξin θ : SRat)
    (hξ : 0 < ξin.get) (hθ : 0 < θ.get) (hξi : ξin.get⁻¹ ≤ U) (hθi : θ.get⁻¹ ≤ U)
    (hξl : ratLen ξin.get ≤ U) (hθl : ratLen θ.get ≤ U) :
    POK U C (oracleParams C ξin θ).val ∧ Charged.steps rate (oracleParams C ξin θ) ≤ U ^ 6 := by
  have hH1 := hC.H_pos
  have hHU := hC.H_le
  have hdU := hC.d_le
  have hBU := hC.B_le
  have hB1 := hC.B_pos
  have hnF := hC.nFree_le
  have hU0 : (0 : ℚ) < U := by exact_mod_cast (show 0 < U by omega)
  have hUq : (2 : ℚ) ^ 20 ≤ U := by exact_mod_cast hU
  have hHb : bitLen C.H.get ≤ U + 1 := (bitLen_le_succ _).trans (by omega)
  have hdb : bitLen C.d.get ≤ U + 1 := (bitLen_le_succ _).trans (by omega)
  have hBb : bitLen C.B.get ≤ U + 1 := (bitLen_le_succ _).trans (by omega)
  have hnb : bitLen C.nFree ≤ U + 1 := (bitLen_le_succ _).trans (by omega)
  suffices h : Charged.steps rate (oracleParams C ξin θ) + 0 ≤ U ^ 6 ∧
      POK U C (oracleParams C ξin θ).val from ⟨h.2, by omega⟩
  unfold oracleParams
  -- one
  refine bstep (a := 2) (fun v : SNat => v.get = 1) (by simp [bitLen_one]) (by simp) ?_
  intro one h_one
  -- H1
  refine bstep (a := U + 3) (fun v : SNat => v.get = C.H.get + 1)
    (by simp [h_one, bitLen_one]; omega) (by simp [h_one]) ?_
  intro H1 h_H1
  have hH1b : bitLen H1.get ≤ U + 2 := (bitLen_le_succ _).trans (by omega)
  -- H1q
  refine bstep (a := U + 2) (fun v : SRat => v.get = (C.H.get + 1 : ℕ))
    (by simp; omega) (by simp [h_H1]) ?_
  intro H1q h_H1q
  have lH1q : ratLen H1q.get ≤ U + 4 := by rw [h_H1q]; exact ratLen_nat_le (U := U + 1) (by omega)
  -- c50
  refine bstep (a := 9) (fun v : SRat => v.get = 50) (by simp [rl50]) (by simp) ?_
  intro c50 h_c50
  -- den
  refine bstep (a := 10 * U + 50) (fun v : SRat => v.get = 50 * (C.H.get + 1 : ℕ))
    ((steps_SRat_mul _ _).trans_le (prod_le (A := 10) (B := U + 5) (by rw [h_c50, rl50])
      (by omega) (by ring))) (by simp [h_c50, h_H1q]) ?_
  intro den h_den
  have lden : ratLen den.get ≤ U + 13 := by
    have h1 := ratLen_mul_le (50 : ℚ) ((C.H.get + 1 : ℕ) : ℚ)
    have h2 := ratLen_nat_le (U := U + 1) (n := C.H.get + 1) (by omega)
    rw [h_den]; rw [rl50] at h1; omega
  -- σ
  refine bstep (a := U ^ 2 + 15 * U + 14) (fun v : SRat => v.get = ξin.get / den.get)
    ((steps_SRat_div _ _).trans_le (prod_le (A := U + 1) (B := U + 14) (by omega)
      (by omega) (by ring))) (by simp) ?_
  intro σ h_σ
  have hσpos : 0 < σ.get := by
    rw [h_σ, h_den]; positivity
  have hσinv : σ.get⁻¹ ≤ 100 * (U : ℚ) ^ 2 := by
    rw [h_σ, h_den, inv_div, div_eq_mul_inv]
    have a1 : ((C.H.get + 1 : ℕ) : ℚ) ≤ 2 * U := by
      have : C.H.get + 1 ≤ 2 * U := by omega
      exact_mod_cast this
    have := mul_le_mul a1 hξi (by positivity) (by positivity)
    nlinarith
  have lσ : ratLen σ.get ≤ 2 * U + 13 := by
    have := ratLen_div_le ξin.get den.get; rw [h_σ]; omega
  -- c1e6
  refine bstep (a := 23) (fun v : SRat => v.get = 1000000) (by simp [rl1e6]) (by simp) ?_
  intro c1e6 h_c1e6
  -- num
  refine bstep (a := 24 * U + 120) (fun v : SRat => v.get = 1000000 * H1q.get)
    ((steps_SRat_mul _ _).trans_le (prod_le (A := 24) (B := U + 5) (by rw [h_c1e6, rl1e6])
      (by omega) (by ring))) (by simp [h_c1e6]) ?_
  intro num h_num
  have lnum : ratLen num.get ≤ U + 27 := by
    have h1 := ratLen_mul_le (1000000 : ℚ) H1q.get; rw [h_num]; rw [rl1e6] at h1; omega
  -- σ2
  refine bstep (a := 4 * U ^ 2 + 56 * U + 196) (fun v : SRat => v.get = σ.get * σ.get)
    ((steps_SRat_mul _ _).trans_le (prod_le (A := 2 * U + 14) (B := 2 * U + 14) (by omega)
      (by omega) (by ring))) (by simp) ?_
  intro σ2 h_σ2
  have lσ2 : ratLen σ2.get ≤ 4 * U + 26 := by
    have := ratLen_mul_le σ.get σ.get; rw [h_σ2]; omega
  -- θσ2
  refine bstep (a := 4 * U ^ 2 + 31 * U + 27) (fun v : SRat => v.get = θ.get * σ2.get)
    ((steps_SRat_mul _ _).trans_le (prod_le (A := U + 1) (B := 4 * U + 27) (by omega)
      (by omega) (by ring))) (by simp) ?_
  intro θσ2 h_θσ2
  have lθσ2 : ratLen θσ2.get ≤ 5 * U + 26 := by
    have := ratLen_mul_le θ.get σ2.get; rw [h_θσ2]; omega
  -- nq
  refine bstep (a := 5 * U ^ 2 + 167 * U + 756) (fun v : SRat => v.get = num.get / θσ2.get)
    ((steps_SRat_div _ _).trans_le (prod_le (A := U + 28) (B := 5 * U + 27) (by omega)
      (by omega) (by ring))) (by simp) ?_
  intro nq h_nq
  have lnq : ratLen nq.get ≤ 6 * U + 53 := by
    have := ratLen_div_le num.get θσ2.get; rw [h_nq]; omega
  have hnqpos : 0 < nq.get := by
    rw [h_nq, h_num, h_θσ2, h_σ2, h_H1q]; positivity
  have hnqle : nq.get ≤ (U : ℚ) ^ 8 := by
    rw [h_nq, h_num, h_θσ2, h_σ2, h_H1q]
    have e : (1000000 : ℚ) * ((C.H.get + 1 : ℕ) : ℚ) / (θ.get * (σ.get * σ.get)) =
        1000000 * ((C.H.get + 1 : ℕ) : ℚ) * θ.get⁻¹ * (σ.get⁻¹ * σ.get⁻¹) := by
      field_simp
    rw [e]
    have a1 : ((C.H.get + 1 : ℕ) : ℚ) ≤ 2 * U := by
      have : C.H.get + 1 ≤ 2 * U := by omega
      exact_mod_cast this
    have a2 : σ.get⁻¹ * σ.get⁻¹ ≤ (100 * (U : ℚ) ^ 2) * (100 * U ^ 2) :=
      mul_le_mul hσinv hσinv (by positivity) (by positivity)
    have a3 : (1000000 : ℚ) * ((C.H.get + 1 : ℕ) : ℚ) * θ.get⁻¹ ≤ 1000000 * (2 * U) * U :=
      mul_le_mul (by linarith) hθi (by positivity) (by positivity)
    have a4 := mul_le_mul a3 a2 (by positivity) (by positivity)
    have e2 : (1000000 : ℚ) * (2 * U) * U * ((100 * (U : ℚ) ^ 2) * (100 * U ^ 2)) =
        20000000000 * U ^ 6 := by ring
    have a5 : (20000000000 : ℚ) * U ^ 6 ≤ U ^ 8 := by
      have : (20000000000 : ℚ) ≤ U ^ 2 := by nlinarith
      have h6 : (0 : ℚ) ≤ U ^ 6 := by positivity
      nlinarith
    linarith
  -- N
  refine bstep (a := 36 * U ^ 2 + 648 * U + 2916) (fun v : SNat => v.get = ⌈nq.get⌉₊ ∧
      1 ≤ v.get ∧ v.get ≤ U ^ 9 ∧ bitLen v.get ≤ 6 * U + 55)
    ((steps_SRat_natCeil _).trans_le (prod_le (A := 6 * U + 54) (B := 6 * U + 54) (by omega)
      (by omega) (by ring))) ?_ ?_
  · rw [SRat.get_natCeil]
    refine ⟨rfl, Nat.one_le_iff_ne_zero.2 (by positivity), ?_, ?_⟩
    · have h1 : (⌈nq.get⌉₊ : ℚ) < nq.get + 1 := Nat.ceil_lt_add_one hnqpos.le
      have h2 : (U : ℚ) ^ 8 + 1 ≤ U ^ 9 := by
        have h3 : (1 : ℚ) ≤ U ^ 8 := one_le_pow₀ (by linarith)
        have h4 : (U : ℚ) ^ 9 = U ^ 8 * U := by ring
        rw [h4]
        have h5 : (2 : ℚ) ≤ U := by linarith
        have h6 : (U : ℚ) ^ 8 * 2 ≤ U ^ 8 * U := mul_le_mul_of_nonneg_left h5 (by positivity)
        linarith
      have h7 : (⌈nq.get⌉₊ : ℚ) ≤ (U : ℚ) ^ 9 := by linarith
      exact_mod_cast h7
    · have := bitLen_natCeil_le nq.get; omega
  rintro N ⟨h_N, hN1, hNU, hNb⟩
  -- NI
  refine bstep (a := 6 * U + 55) (fun v : ℕ => v = N.get)
    ((steps_SNat_index _).trans_le hNb) (by simp) ?_
  intro NI h_NI
  -- Nq
  refine bstep (a := 6 * U + 55) (fun v : SRat => v.get = N.get)
    ((steps_SNat_toRat _).trans_le hNb) (by simp) ?_
  intro Nq h_Nq
  -- d1
  refine bstep (a := U + 3) (fun v : SNat => v.get = C.d.get + 1)
    (by simp [h_one, bitLen_one]; omega) (by simp [h_one]) ?_
  intro d1 h_d1
  -- dH
  refine bstep (a := U ^ 2 + 4 * U + 4) (fun v : SNat => v.get = d1.get * H1.get)
    ((steps_SNat_mul _ _).trans_le (prod_le (A := U + 2) (B := U + 2)
      ((bitLen_le_succ _).trans (by omega)) (by omega) (by ring))) (by simp) ?_
  intro dH h_dH
  have hdHv : dH.get ≤ 4 * U ^ 2 := by
    rw [h_dH, h_d1, h_H1]
    have := Nat.mul_le_mul (show C.d.get + 1 ≤ 2 * U by omega) (show C.H.get + 1 ≤ 2 * U by omega)
    have e : 2 * U * (2 * U) = 4 * U ^ 2 := by ring
    omega
  have hdHb : bitLen dH.get ≤ 2 * U + 4 := by
    rw [h_dH]; have := bitLen_mul_le d1.get H1.get
    have : bitLen d1.get ≤ U + 2 := (bitLen_le_succ _).trans (by omega)
    omega
  have hdH1 : 1 ≤ dH.get := by
    rw [h_dH, h_d1, h_H1]; exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  -- Q
  refine bstep (a := 12 * U ^ 2 + 134 * U + 220) (fun v : SNat => v.get = dH.get * N.get)
    ((steps_SNat_mul _ _).trans_le (prod_le (A := 2 * U + 4) (B := 6 * U + 55) hdHb hNb
      (by ring))) (by simp) ?_
  intro Q h_Q
  have hQ1 : 1 ≤ Q.get := by rw [h_Q]; exact Nat.one_le_iff_ne_zero.2 (by positivity)
  have hQU : Q.get ≤ U ^ 12 := by
    rw [h_Q]
    have := Nat.mul_le_mul hdHv hNU
    have e : 4 * U ^ 2 * U ^ 9 = 4 * U ^ 11 := by ring
    have p : 100 * U ^ 11 ≤ U ^ 12 := pw_absorb hU (by norm_num) rfl
    omega
  have hQb : bitLen Q.get ≤ 8 * U + 59 := by
    rw [h_Q]; have := bitLen_mul_le dH.get N.get; omega
  -- Qq
  refine bstep (a := 8 * U + 59) (fun v : SRat => v.get = Q.get)
    ((steps_SNat_toRat _).trans_le hQb) (by simp) ?_
  intro Qq h_Qq
  have lQq : ratLen Qq.get ≤ 8 * U + 61 := by rw [h_Qq, ratLen_natCast]; omega
  -- d2
  refine bstep (a := U ^ 2 + 2 * U + 1) (fun v : SNat => v.get = C.d.get * C.d.get)
    ((steps_SNat_mul _ _).trans_le (prod_le (A := U + 1) (B := U + 1) hdb hdb (by ring)))
    (by simp) ?_
  intro d2 h_d2
  have hd2b : bitLen d2.get ≤ 2 * U + 2 := by
    rw [h_d2]; have := bitLen_mul_le C.d.get C.d.get; omega
  have hd2v : d2.get ≤ U ^ 2 := by
    rw [h_d2, pow_two]; exact Nat.mul_le_mul hdU hdU
  -- c1e4
  refine bstep (a := 15) (fun v : SNat => v.get = 10000) (by simp [bl1e4]) (by simp) ?_
  intro c1e4 h_c1e4
  -- t
  refine bstep (a := 30 * U + 30) (fun v : SNat => v.get = 10000 * d2.get)
    ((steps_SNat_mul _ _).trans_le (prod_le (A := 15) (B := 2 * U + 2) (by rw [h_c1e4, bl1e4])
      hd2b (by ring))) (by simp [h_c1e4]) ?_
  intro t h_t
  have htb : bitLen t.get ≤ 2 * U + 17 := by
    rw [h_t]; have := bitLen_mul_le 10000 d2.get; rw [bl1e4] at this; omega
  have htv : t.get ≤ 10000 * U ^ 2 := by rw [h_t]; omega
  -- t'
  refine bstep (a := 2 * U ^ 2 + 19 * U + 17) (fun v : SNat => v.get = t.get * C.B.get)
    ((steps_SNat_mul _ _).trans_le (prod_le (A := 2 * U + 17) (B := U + 1) htb hBb (by ring)))
    (by simp) ?_
  intro t' h_t'
  have ht'b : bitLen t'.get ≤ 3 * U + 18 := by
    rw [h_t']; have := bitLen_mul_le t.get C.B.get; omega
  have ht'v : t'.get ≤ 10000 * U ^ 3 := by
    rw [h_t']; have := Nat.mul_le_mul htv hBU
    have e : 10000 * U ^ 2 * U = 10000 * U ^ 3 := by ring
    omega
  -- t2
  refine bstep (a := 9 * U ^ 2 + 108 * U + 324) (fun v : SNat => v.get = t'.get * t'.get)
    ((steps_SNat_mul _ _).trans_le (prod_le (A := 3 * U + 18) (B := 3 * U + 18) ht'b ht'b
      (by ring))) (by simp) ?_
  intro t2 h_t2
  have ht2b : bitLen t2.get ≤ 6 * U + 36 := by
    rw [h_t2]; have := bitLen_mul_le t'.get t'.get; omega
  have ht2v : t2.get ≤ 100000000 * U ^ 6 := by
    rw [h_t2]; have := Nat.mul_le_mul ht'v ht'v
    have e : 10000 * U ^ 3 * (10000 * U ^ 3) = 100000000 * U ^ 6 := by ring
    omega
  -- two
  refine bstep (a := 3) (fun v : SNat => v.get = 2) (by simp [bitLen_two]) (by simp) ?_
  intro two h_two
  -- Kbin
  refine bstep (a := 18 * U + 108) (fun v : SNat => v.get = 2 * t2.get)
    ((steps_SNat_mul _ _).trans_le (prod_le (A := 3) (B := 6 * U + 36) (by rw [h_two, bitLen_two])
      ht2b (by ring))) (by simp [h_two]) ?_
  intro Kbin h_Kbin
  have hKb : bitLen Kbin.get ≤ 6 * U + 39 := by
    rw [h_Kbin]; have := bitLen_mul_le 2 t2.get; rw [bitLen_two] at this; omega
  have hKv : Kbin.get ≤ U ^ 8 := by
    rw [h_Kbin]
    have p : 200000000 * U ^ 6 ≤ U ^ 8 := by
      have h2 : 200000000 ≤ U ^ 2 := by
        have : 2 ^ 40 ≤ U ^ 2 := by
          rw [show 2 ^ 40 = (2 ^ 20) ^ 2 by norm_num]; exact Nat.pow_le_pow_left hU 2
        omega
      have := Nat.mul_le_mul_right (U ^ 6) h2
      have e : U ^ 2 * U ^ 6 = U ^ 8 := by ring
      omega
    omega
  -- dB
  refine bstep (a := U ^ 2 + 2 * U + 1) (fun v : SNat => v.get = C.d.get * C.B.get)
    ((steps_SNat_mul _ _).trans_le (prod_le (A := U + 1) (B := U + 1) hdb hBb (by ring)))
    (by simp) ?_
  intro dB h_dB
  have hdBb : bitLen dB.get ≤ 2 * U + 2 := by
    rw [h_dB]; have := bitLen_mul_le C.d.get C.B.get; omega
  have hdBv : dB.get ≤ U ^ 2 := by rw [h_dB, pow_two]; exact Nat.mul_le_mul hdU hBU
  -- s
  refine bstep (a := 3 * U + 3) (fun v : SNat => v.get = C.H.get + dB.get)
    (by simp only [steps_SNat_add]; omega) (by simp) ?_
  intro sS h_s
  have hsb : bitLen sS.get ≤ 3 * U + 3 := by
    rw [h_s]; have := bitLen_add_le' C.H.get dB.get; omega
  -- s2
  refine bstep (a := 3 * U + 6) (fun v : SNat => v.get = sS.get + 2)
    (by simp only [steps_SNat_add, h_two, bitLen_two]; omega) (by simp [h_two]) ?_
  intro s2 h_s2
  have hs2b : bitLen s2.get ≤ 3 * U + 6 := by
    rw [h_s2]; have := bitLen_add_le' sS.get 2; rw [bitLen_two] at this; omega
  have hs2v : s2.get ≤ 2 * U ^ 2 := by
    rw [h_s2, h_s]
    have : 100 * U ≤ U ^ 2 := by
      have := pw_absorb hU (c := 100) (k := 1) (m := 2) (by norm_num) rfl; rwa [pow_one] at this
    omega
  -- s2q
  refine bstep (a := 3 * U + 6) (fun v : SRat => v.get = s2.get)
    ((steps_SNat_toRat _).trans_le hs2b) (by simp) ?_
  intro s2q h_s2q
  have ls2q : ratLen s2q.get ≤ 3 * U + 8 := by rw [h_s2q, ratLen_natCast]; omega
  -- c16
  refine bstep (a := 8) (fun v : SRat => v.get = 16) (by simp [rl16]) (by simp) ?_
  intro c16 h_c16
  -- q16
  refine bstep (a := 72 * U + 558) (fun v : SRat => v.get = 16 * Qq.get)
    ((steps_SRat_mul _ _).trans_le (prod_le (A := 9) (B := 8 * U + 62) (by rw [h_c16, rl16])
      (by omega) (by ring))) (by simp [h_c16]) ?_
  intro q16 h_q16
  have lq16 : ratLen q16.get ≤ 8 * U + 69 := by
    have h1 := ratLen_mul_le (16 : ℚ) Qq.get; rw [h_q16]; rw [rl16] at h1; omega
  -- q16θ
  refine bstep (a := 8 * U ^ 2 + 78 * U + 70) (fun v : SRat => v.get = q16.get / θ.get)
    ((steps_SRat_div _ _).trans_le (prod_le (A := 8 * U + 70) (B := U + 1) (by omega)
      (by omega) (by ring))) (by simp) ?_
  intro q16θ h_q16θ
  have lq16θ : ratLen q16θ.get ≤ 9 * U + 69 := by
    have := ratLen_div_le q16.get θ.get; rw [h_q16θ]; omega
  have hq16θv : 0 ≤ q16θ.get ∧ q16θ.get ≤ 16 * (U : ℚ) ^ 13 := by
    rw [h_q16θ, h_q16, h_Qq, div_eq_mul_inv]
    refine ⟨by positivity, ?_⟩
    have a1 : (Q.get : ℚ) ≤ (U : ℚ) ^ 12 := by exact_mod_cast hQU
    have := mul_le_mul (mul_le_mul_of_nonneg_left a1 (by norm_num : (0 : ℚ) ≤ 16)) hθi
      (by positivity) (by positivity)
    have e : 16 * (U : ℚ) ^ 12 * U = 16 * U ^ 13 := by ring
    exact this.trans (le_of_eq e)
  -- inner
  refine bstep (a := 27 * U ^ 2 + 291 * U + 630) (fun v : SRat => v.get = s2q.get + q16θ.get)
    ((steps_SRat_add _ _).trans_le (prod_le (A := 3 * U + 9) (B := 9 * U + 70) (by omega)
      (by omega) (by ring))) (by simp) ?_
  intro inner h_inner
  have linner : ratLen inner.get ≤ 24 * U + 154 := by
    have := ratLen_add_le s2q.get q16θ.get; rw [h_inner]; clear * - this ls2q lq16θ; omega
  have hinnerv : 0 ≤ inner.get ∧ inner.get ≤ (U : ℚ) ^ 14 := by
    rw [h_inner, h_s2q]
    have a1 : (s2.get : ℚ) ≤ 2 * (U : ℚ) ^ 2 := by exact_mod_cast hs2v
    have a2 : 18 * (U : ℚ) ^ 13 ≤ U ^ 14 := by
      have : (18 : ℚ) * U ^ 13 ≤ U * U ^ 13 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have e : (U : ℚ) * U ^ 13 = U ^ 14 := by ring
      linarith
    have a3 : (U : ℚ) ^ 2 ≤ U ^ 13 := pow_le_pow_right₀ (by linarith) (by norm_num)
    refine ⟨by have := hq16θv.1; positivity, by linarith [hq16θv.2]⟩
  -- Kq
  refine bstep (a := 6 * U + 39) (fun v : SRat => v.get = Kbin.get)
    ((steps_SNat_toRat _).trans_le hKb) (by simp) ?_
  intro Kq h_Kq
  have lKq : ratLen Kq.get ≤ 6 * U + 41 := by rw [h_Kq, ratLen_natCast]; omega
  -- ellq
  refine bstep (a := 144 * U ^ 2 + 1938 * U + 6510) (fun v : SRat => v.get = Kq.get * inner.get)
    ((steps_SRat_mul _ _).trans_le (prod_le (A := 6 * U + 42) (B := 24 * U + 155) (by omega)
      (by omega) (by ring))) (by simp) ?_
  intro ellq h_ellq
  have lellq : ratLen ellq.get ≤ 30 * U + 195 := by
    have := ratLen_mul_le Kq.get inner.get; rw [h_ellq]; omega
  have hellqv : ellq.get ≤ (U : ℚ) ^ 22 := by
    rw [h_ellq, h_Kq]
    have a1 : (Kbin.get : ℚ) ≤ (U : ℚ) ^ 8 := by exact_mod_cast hKv
    have := mul_le_mul a1 hinnerv.2 hinnerv.1 (by positivity)
    have e : (U : ℚ) ^ 8 * U ^ 14 = U ^ 22 := by ring
    linarith
  -- ellN
  refine bstep (a := 900 * U ^ 2 + 11760 * U + 38416) (fun v : SNat => v.get ≤ U ^ 24 ∧
      bitLen v.get ≤ 30 * U + 197)
    ((steps_SRat_natCeil _).trans_le (prod_le (A := 30 * U + 196) (B := 30 * U + 196)
      (by omega) (by omega) (by ring))) ?_ ?_
  · rw [SRat.get_natCeil]
    refine ⟨Nat.ceil_le.2 ?_, by have := bitLen_natCeil_le ellq.get; omega⟩
    have : (U : ℚ) ^ 22 ≤ U ^ 24 := pow_le_pow_right₀ (by linarith) (by norm_num)
    push_cast; linarith
  rintro ellN ⟨hellN, hellNb⟩
  -- ell
  refine bstep (a := 30 * U + 197) (fun v : ℕ => v ≤ U ^ 24)
    ((steps_SNat_index _).trans_le hellNb) (by simpa using hellN) ?_
  intro ell h_ell
  -- c4
  refine bstep (a := 4) (fun v : SNat => v.get = 4) (by simp [bl4]) (by simp) ?_
  intro c4 h_c4
  -- d4
  refine bstep (a := 4 * U + 4) (fun v : SNat => v.get = 4 * C.d.get)
    ((steps_SNat_mul _ _).trans_le (prod_le (A := 4) (B := U + 1) (by rw [h_c4, bl4]) hdb
      (by ring))) (by simp [h_c4]) ?_
  intro d4 h_d4
  have hd4b : bitLen d4.get ≤ U + 5 := by
    rw [h_d4]; have := bitLen_mul_le 4 C.d.get; rw [bl4] at this; omega
  -- kdN
  obtain ⟨k1v, k1s⟩ := clog2_spec d4
  refine bstep (a := 2 * U + 14) (fun v : SNat => v.get ≤ U) (k1s.trans (by omega)) ?_ ?_
  · rw [k1v, h_d4, Nat.size_le]
    have := four_mul_lt_two_pow (show 6 ≤ U by omega)
    omega
  intro kdN h_kdN
  -- kd
  refine bstep (a := U + 1) (fun v : ℕ => v ≤ U)
    ((steps_SNat_index _).trans_le ((bitLen_le_succ _).trans (by omega))) (by simpa using h_kdN) ?_
  intro kd h_kd
  -- eS
  refine bstep (a := U + 1) (fun v : SNat => v.get = C.nFree) (by simpa using hnb) (by simp) ?_
  intro eS h_eS
  -- twoE
  refine bstep (a := 3 * U + 3) (fun v : SNat => v.get = 2 * C.nFree)
    ((steps_SNat_mul _ _).trans_le (prod_le (A := 3) (B := U + 1) (by rw [h_two, bitLen_two])
      (by rw [h_eS]; exact hnb) (by ring))) (by simp [h_two, h_eS]) ?_
  intro twoE h_twoE
  -- Bm1
  refine bstep (a := U + 3) (fun v : SNat => v.get = C.B.get - 1)
    (by simp only [steps_SNat_sub, h_one, bitLen_one]; omega) (by simp [h_one]) ?_
  intro Bm1 h_Bm1
  -- c8
  refine bstep (a := 7) (fun v : SRat => v.get = 8) (by simp [rl8]) (by simp) ?_
  intro c8 h_c8
  -- q8
  refine bstep (a := 64 * U + 496) (fun v : SRat => v.get = 8 * Q.get)
    ((steps_SRat_mul _ _).trans_le (prod_le (A := 8) (B := 8 * U + 62) (by rw [h_c8, rl8])
      (by omega) (by ring))) (by simp [h_c8, h_Qq]) ?_
  intro q8 h_q8
  have lq8 : ratLen q8.get ≤ 8 * U + 68 := by
    have h1 := ratLen_mul_le (8 : ℚ) Qq.get; rw [h_q8, ← h_Qq]; rw [rl8] at h1; omega
  -- ζ
  refine bstep (a := 8 * U ^ 2 + 77 * U + 69) (fun v : SRat => 0 < v.get ∧
      v.get⁻¹ ≤ U ^ 15 ∧ ratLen v.get ≤ U ^ 15)
    ((steps_SRat_div _ _).trans_le (prod_le (A := U + 1) (B := 8 * U + 69) (by omega)
      (by omega) (by ring))) ?_ ?_
  · rw [SRat.get_div, h_q8]
    have hQ0 : (1 : ℚ) ≤ Q.get := by exact_mod_cast hQ1
    refine ⟨by positivity, ?_, ?_⟩
    · rw [inv_div, div_eq_mul_inv]
      have a1 : (Q.get : ℚ) ≤ (U : ℚ) ^ 12 := by exact_mod_cast hQU
      have := mul_le_mul (mul_le_mul_of_nonneg_left a1 (by norm_num : (0 : ℚ) ≤ 8)) hθi
        (by positivity) (by positivity)
      have e : 8 * (U : ℚ) ^ 12 * U = 8 * U ^ 13 := by ring
      have h15 : 8 * (U : ℚ) ^ 13 ≤ U ^ 15 := by
        have : (8 : ℚ) ≤ U ^ 2 := by nlinarith
        have := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℚ) ≤ U ^ 13)
        have e2 : (U : ℚ) ^ 2 * U ^ 13 = U ^ 15 := by ring
        linarith
      linarith
    · have h1 := ratLen_div_le θ.get (8 * (Q.get : ℚ))
      have lq8' : ratLen (8 * (Q.get : ℚ)) ≤ 8 * U + 68 := by rw [← h_q8]; exact lq8
      have h2 : 9 * U + 68 ≤ U ^ 15 := by
        have h3 := pw_absorb hU (c := 100) (k := 1) (m := 2) (by norm_num) rfl
        have h4 := pw_mono (show 1 ≤ U by omega) (show 2 ≤ 15 by norm_num)
        rw [pow_one] at h3; omega
      omega
  rintro ζ ⟨hζ0, hζi, hζl⟩
  -- c32
  refine bstep (a := 9) (fun v : SRat => v.get = 32) (by simp [rl32]) (by simp) ?_
  intro c32 h_c32
  -- r32
  refine bstep (a := 20 * U + 140) (fun v : SRat => v.get = 32 / σ.get)
    ((steps_SRat_div _ _).trans_le (prod_le (A := 10) (B := 2 * U + 14) (by rw [h_c32, rl32])
      (by omega) (by ring))) (by simp [h_c32]) ?_
  intro r32 h_r32
  have lr32 : ratLen r32.get ≤ 2 * U + 22 := by
    have h1 := ratLen_div_le (32 : ℚ) σ.get; rw [h_r32]; rw [rl32] at h1; omega
  have hr32v : r32.get ≤ 3200 * (U : ℚ) ^ 2 := by
    rw [h_r32, div_eq_mul_inv]; linarith
  -- c32N
  refine bstep (a := 4 * U ^ 2 + 92 * U + 529) (fun v : SNat => v.get ≤ 3201 * U ^ 2 ∧
      bitLen v.get ≤ 2 * U + 24)
    ((steps_SRat_natCeil _).trans_le (prod_le (A := 2 * U + 23) (B := 2 * U + 23)
      (by omega) (by omega) (by ring))) ?_ ?_
  · rw [SRat.get_natCeil]
    refine ⟨Nat.ceil_le.2 ?_, by have := bitLen_natCeil_le r32.get; omega⟩
    have : (1 : ℚ) ≤ U ^ 2 := one_le_pow₀ (by linarith)
    push_cast; linarith
  rintro c32N ⟨hc32v, hc32b⟩
  -- ksN
  obtain ⟨k2v, k2s⟩ := clog2_spec c32N
  refine bstep (a := 4 * U + 52) (fun v : SNat => v.get ≤ 2 * U + 24 ∧ 2 ^ v.get ≤ U ^ 4)
    (k2s.trans (by omega)) ?_ ?_
  · rw [k2v]
    refine ⟨(size_pred_le _).trans hc32b, ?_⟩
    have := two_pow_size_le (c32N.get - 1)
    have h4 : 6402 * U ^ 2 ≤ U ^ 4 := by
      have := pw_absorb hU (c := 6402) (k := 2) (m := 3) (by norm_num) rfl
      have := pw_mono (show 1 ≤ U by omega) (show 3 ≤ 4 by norm_num)
      omega
    omega
  rintro ksN ⟨hksv, hks4⟩
  -- ks
  refine bstep (a := 2 * U + 25) (fun v : ℕ => v = ksN.get)
    ((steps_SNat_index _).trans_le ((bitLen_le_succ _).trans (by omega))) (by simp) ?_
  intro ks h_ks
  -- sPrime
  refine bstep (a := 2 * U + 25) (fun v : SNat => v.get = 2 ^ ksN.get)
    ((steps_SNat_pow2 _).trans_le (by omega)) (by simp) ?_
  intro sPrime h_sPrime
  -- c512
  refine bstep (a := 13) (fun v : SRat => v.get = 512) (by simp [rl512]) (by simp) ?_
  intro c512 h_c512
  -- r512
  refine bstep (a := 28 * U + 196) (fun v : SRat => v.get = 512 / σ.get)
    ((steps_SRat_div _ _).trans_le (prod_le (A := 14) (B := 2 * U + 14) (by rw [h_c512, rl512])
      (by omega) (by ring))) (by simp [h_c512]) ?_
  intro r512 h_r512
  have lr512 : ratLen r512.get ≤ 2 * U + 26 := by
    have h1 := ratLen_div_le (512 : ℚ) σ.get; rw [h_r512]; rw [rl512] at h1; omega
  -- c512N
  refine bstep (a := 4 * U ^ 2 + 108 * U + 729) (fun v : SNat => bitLen v.get ≤ 2 * U + 28)
    ((steps_SRat_natCeil _).trans_le (prod_le (A := 2 * U + 27) (B := 2 * U + 27)
      (by omega) (by omega) (by ring))) ?_ ?_
  · rw [SRat.get_natCeil]; have := bitLen_natCeil_le r512.get; omega
  intro c512N hc512b
  -- depN
  obtain ⟨k3v, k3s⟩ := clog2_spec c512N
  refine bstep (a := 4 * U + 60) (fun v : SNat => v.get ≤ 2 * U + 28)
    (k3s.trans (by omega)) (by rw [k3v]; exact (size_pred_le _).trans hc512b) ?_
  intro depN h_depN
  -- depth
  refine bstep (a := 2 * U + 29) (fun v : ℕ => v ≤ 2 * U + 28)
    ((steps_SNat_index _).trans_le ((bitLen_le_succ _).trans (by omega))) (by simpa using h_depN) ?_
  intro depth h_depth
  -- Be
  obtain ⟨bev, bes⟩ := Be_spec C hU hC one h_one
  refine bstep (a := U ^ 5) (fun v : SNat => v.get = C.B.get ^ C.nFree) bes bev ?_
  intro Be h_Be
  simp only [costVp, Charged.steps_pure]
  have p2 := pw_absorb hU (c := 100) (k := 1) (m := 2) (by norm_num) rfl
  have p3 : 100 * U ^ 2 ≤ U ^ 3 := pw_absorb hU (by norm_num) rfl
  have p4 : 100 * U ^ 3 ≤ U ^ 4 := pw_absorb hU (by norm_num) rfl
  have p5 : 100 * U ^ 4 ≤ U ^ 5 := pw_absorb hU (by norm_num) rfl
  have p6 : 100 * U ^ 5 ≤ U ^ 6 := pw_absorb hU (by norm_num) rfl
  rw [pow_one] at p2
  have q2 : 2 * U + 28 ≤ U ^ 2 := by omega
  refine ⟨by clear * - hU p2 p3 p4 p5 p6; omega, ?_⟩
  have hN10 : N.get ≤ U ^ 10 := hNU.trans (pw_mono (by omega) (by norm_num))
  exact ⟨⟨h_kd, by simp [h_twoE], h_Bm1⟩, show NI ≤ U ^ 10 by rw [h_NI]; exact hN10,
    h_Nq.trans (by simp [h_NI]), h_ell, hζ0, hζi, hζl, show ks ≤ U ^ 2 by omega,
    by rw [h_sPrime, h_ks], by rw [h_ks]; exact hks4, show depth ≤ U ^ 2 by omega, h_Be⟩


/-- INTERNAL: the whole oracle call at size `U`: price `≤ U^50`, output length `≤ U^14`. -/
theorem oracle_spec {U : ℕ} {C : Ctx} {x y : List SNat} (E : Env U C x y) (tape : Coins ℕ)
    (j : ℕ) (hj : j ≤ U) (ξin θ : SRat) (hξ : 0 < ξin.get) (hθ : 0 < θ.get)
    (hξi : ξin.get⁻¹ ≤ U) (hθi : θ.get⁻¹ ≤ U) (hξl : ratLen ξin.get ≤ U)
    (hθl : ratLen θ.get ≤ U) (cur : ℕ) :
    Charged.steps rate (oracle C tape x y j ξin θ cur) ≤ U ^ 50 ∧
      ratLen (oracle C tape x y j ξin θ cur).val.1.get ≤ U ^ 14 := by
  have hU := E.big
  have hC := E.size
  obtain ⟨hP, s0⟩ := oracleParams_spec C hU hC ξin θ hξ hθ hξi hθi hξl hθl
  unfold oracle
  simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SRat_lit,
    steps_SNat_toRat, SNat.get_toRat, steps_SRat_mul, SRat.get_mul]
  generalize oracleParams C ξin θ = PP at hP s0 ⊢
  have p13 : 100 * U ^ 12 ≤ U ^ 13 := pw_absorb hU (by norm_num) rfl
  have p14 : 100 * U ^ 13 ≤ U ^ 14 := pw_absorb hU (by norm_num) rfl
  have p26 : 100 * U ^ 14 ≤ U ^ 26 := (pw_absorb hU (by norm_num) rfl).trans
    (pw_mono (by omega) (by norm_num))
  have p47 : 100 * U ^ 26 ≤ U ^ 47 := (pw_absorb hU (by norm_num) rfl).trans
    (pw_mono (by omega) (by norm_num))
  have p48 : 100 * U ^ 47 ≤ U ^ 48 := pw_absorb hU (by norm_num) rfl
  have p49 : 100 * U ^ 48 ≤ U ^ 49 := pw_absorb hU (by norm_num) rfl
  have p50 : 100 * U ^ 49 ≤ U ^ 50 := pw_absorb hU (by norm_num) rfl
  have q6 : U ^ 6 ≤ U ^ 47 := pw_mono (by omega) (by norm_num)
  have q1 : 100 * U ^ 1 ≤ U ^ 13 := (pw_absorb hU (by norm_num) rfl).trans
    (pw_mono (by omega) (by norm_num))
  rw [pow_one] at q1
  have r1 : ratLen (1 : ℚ) = 4 := by rw [ratLen_lit]; decide
  generalize hR : Charged.repeatFor _ j _ = R
  obtain ⟨hl, hs⟩ : ratLen R.val.1.get ≤ 4 + j * U ^ 12 ∧
      Charged.steps rate R ≤ j * U ^ 48 := by
    subst hR
    refine repeatFor_inv _ (fun r (st : SRat × ℕ) => ratLen st.1.get ≤ 4 + r * U ^ 12)
      (U ^ 48) j _ (by simp [r1]) ?_
    rintro r st hr hst
    simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SRat_mul,
      SRat.get_mul]
    obtain ⟨a1, a2⟩ := ratioAvg_spec E PP.val hP tape r (by omega) st.2
    generalize ratioAvg C PP.val tape x y r st.2 = PR at a1 a2 ⊢
    have h1 := ratLen_mul_le st.1.get PR.val.1.get
    have hrU : r * U ^ 12 ≤ U * U ^ 12 := Nat.mul_le_mul_right _ (by omega)
    have e : U * U ^ 12 = U ^ 13 := by ring
    refine ⟨by rw [Nat.add_mul, one_mul]; omega, ?_⟩
    have m : (ratLen st.1.get + 1) * (ratLen PR.val.1.get + 1) ≤ (U ^ 13 + 5) * (U ^ 12 + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e2 : (U ^ 13 + 5) * (U ^ 12 + 1) = U ^ 25 + U ^ 13 + 5 * U ^ 12 + 5 := by ring
    have p25 : 100 * U ^ 25 ≤ U ^ 26 := pw_absorb hU (by norm_num) rfl
    omega
  have hlR : ratLen R.val.1.get ≤ U ^ 13 + 4 := by
    have : j * U ^ 12 ≤ U * U ^ 12 := Nat.mul_le_mul_right _ hj
    have e : U * U ^ 12 = U ^ 13 := by ring
    omega
  have hsR : Charged.steps rate R ≤ U ^ 49 := by
    have : j * U ^ 48 ≤ U * U ^ 48 := Nat.mul_le_mul_right _ hj
    have e : U * U ^ 48 = U ^ 49 := by ring
    omega
  obtain ⟨c1, c2⟩ := corrAvg_spec E PP.val hP tape j hj R.val.2
  generalize corrAvg C PP.val tape x y j R.val.2 = PC at c1 c2 ⊢
  have hMf := hC.Mf_bits
  have lM : ratLen (C.Mf.get : ℚ) ≤ U + 2 := by rw [ratLen_natCast]; omega
  have l1 := ratLen_mul_le (C.Mf.get : ℚ) R.val.1.get
  have l2 := ratLen_mul_le ((C.Mf.get : ℚ) * R.val.1.get) PC.val.1.get
  have m1 : (ratLen (C.Mf.get : ℚ) + 1) * (ratLen R.val.1.get + 1) ≤ (U + 3) * (U ^ 13 + 5) :=
    Nat.mul_le_mul (by omega) (by omega)
  have m2 : (ratLen ((C.Mf.get : ℚ) * R.val.1.get) + 1) * (ratLen PC.val.1.get + 1) ≤
      (2 * U ^ 13) * (U ^ 12 + 1) := Nat.mul_le_mul (by omega) (by omega)
  have e1 : (U + 3) * (U ^ 13 + 5) = U ^ 14 + 3 * U ^ 13 + 5 * U + 15 := by ring
  have e2 : (2 * U ^ 13) * (U ^ 12 + 1) = 2 * U ^ 25 + 2 * U ^ 13 := by ring
  have p25 : 100 * U ^ 25 ≤ U ^ 26 := pw_absorb hU (by norm_num) rfl
  have hr1 : ratLen (1 : ℚ) ≤ 4 := by rw [r1]
  refine ⟨?_, by omega⟩
  omega


end OCost

open OCost in
/-- **Oracle cost.**
PAPER: sections/evaluation.tex:27-28 ("On every execution its bit cost is bounded
by a fixed polynomial in `L, ε⁻¹, ξ_in⁻¹, θ⁻¹` and the encoding lengths of the
parameters", `prop:weight-oracle`); proof at sections/evaluation.tex:386-470. -/
theorem oracle_cost : ∃ k : ℕ, ∀ (S : ℕ) (C : Ctx), 2 ≤ S → CtxSize S C → PenaltyOK S C →
    ∀ (x y : List SNat), ProfileValid C x y → ∀ (j : ℕ), j ≤ S →
    ∀ (ξin θ : SRat), 0 < ξin.get → 0 < θ.get → ξin.get⁻¹ ≤ S → θ.get⁻¹ ≤ S →
    ratLen ξin.get ≤ S → ratLen θ.get ≤ S →
    ∀ (tape : Coins ℕ) (cur : ℕ),
      Charged.steps rate (oracle C tape x y j ξin θ cur) ≤ S ^ k ∧
      ratLen (oracle C tape x y j ξin θ cur).val.1.get ≤ S ^ k := by
  refine ⟨1000, ?_⟩
  intro S C hS hC hpen x y hxy j hj ξin θ hξ hθ hξi hθi hξl hθl tape cur
  have hU : 2 ^ 20 ≤ S ^ 20 := Nat.pow_le_pow_left hS 20
  have hSU : S ≤ S ^ 20 := Nat.le_self_pow (by norm_num) S
  have hSUq : (S : ℚ) ≤ ((S ^ 20 : ℕ) : ℚ) := by exact_mod_cast hSU
  have E : Env (S ^ 20) C x y := ⟨hU, hC.mono hSU, hpen.mono hSU, hxy⟩
  obtain ⟨h1, h2⟩ := oracle_spec E tape j (hj.trans hSU) ξin θ hξ hθ (hξi.trans hSUq)
    (hθi.trans hSUq) (hξl.trans hSU) (hθl.trans hSU) cur
  have e : (S ^ 20) ^ 50 = S ^ 1000 := by rw [← pow_mul]
  have m : (S ^ 20) ^ 14 ≤ (S ^ 20) ^ 50 := Nat.pow_le_pow_right (by positivity) (by norm_num)
  exact ⟨h1.trans e.le, (h2.trans m).trans e.le⟩

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r4 · proved · `oracle_cost` closed (k = 1000) through the `OCost` sub-procedure bounds and
  `penalty_cost` (`PenaltyCost.lean`); no open goals
* r3 · blocked · build run without the Lake-build slot; no proof progress
-/
