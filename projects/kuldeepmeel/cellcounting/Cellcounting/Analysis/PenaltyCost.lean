import Cellcounting.Analysis.CostScale

/-!
# One penalty evaluation costs a polynomial number of bit operations

`Cellcounting.Analysis.penalty_cost`: under `CtxSize S C` (with `S ≥ 2^20`), on a
box-valid small profile and a free vector `zf` whose first `nFree` entries lie in
`[0, b_e + 1]` and in `(1/B)ℤ`, `Program.penalty C x y zf` costs at most `S ^ 6` bit
operations and returns a rational of length at most `S ^ 3`.

The free vectors the oracle feeds the penalty are of exactly this kind: bin points
`(b_e + 1) v_e / B` and integer offset points.

Route.  Every intermediate value of the leaf elimination lies in `(1/B)ℤ`
(`BInt C.B.get`).  The vertex accumulator after the small cells has entries
`≤ 2 S²`, after the free cells `≤ 2^{2S}`, and each elimination step at most
quadruples the largest entry, so after `i ≤ S` steps every entry is `≤ 2^{2S+2i}`.
Hence every intermediate has length `O(S)` (`ratLen_le_of_BInt`).  The root sum stays in
`(1/B)ℤ`; the distance sum `Σ dist(z_t,[0,b_t])/b_t` has the common denominator
`B ∏_{t<r} max(b_t,1)` (`treeDen`), of length `O(S²)`.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Program
open Cellcounting.Model.Operations
open Cellcounting.Interface

namespace OC

/-- INTERNAL: `q ∈ (1/D)ℤ`. -/
def BInt (D : ℕ) (q : ℚ) : Prop := ∃ a : ℤ, q * D = a

theorem BInt.add {D : ℕ} {q r : ℚ} (hq : BInt D q) (hr : BInt D r) : BInt D (q + r) := by
  obtain ⟨a, ha⟩ := hq; obtain ⟨b, hb⟩ := hr
  exact ⟨a + b, by push_cast; rw [← ha, ← hb]; ring⟩

theorem BInt.neg {D : ℕ} {q : ℚ} (hq : BInt D q) : BInt D (-q) := by
  obtain ⟨a, ha⟩ := hq
  exact ⟨-a, by push_cast; rw [← ha]; ring⟩

theorem BInt.sub {D : ℕ} {q r : ℚ} (hq : BInt D q) (hr : BInt D r) : BInt D (q - r) := by
  rw [sub_eq_add_neg]; exact hq.add hr.neg

theorem BInt.abs {D : ℕ} {q : ℚ} (hq : BInt D q) : BInt D |q| := by
  rcases abs_choice q with h | h <;> rw [h]
  · exact hq
  · exact hq.neg

theorem BInt.intCast (D : ℕ) (n : ℤ) : BInt D n := ⟨n * D, by push_cast; ring⟩

theorem BInt.natCast (D : ℕ) (n : ℕ) : BInt D n := ⟨n * D, by push_cast; ring⟩

theorem BInt.zero (D : ℕ) : BInt D 0 := ⟨0, by simp⟩

theorem BInt.mul_nat {D : ℕ} {q : ℚ} (hq : BInt D q) (E : ℕ) : BInt (D * E) q := by
  obtain ⟨a, ha⟩ := hq
  exact ⟨a * E, by push_cast; rw [← ha]; ring⟩

/-- INTERNAL: a rational in `(1/D)ℤ` of magnitude `≤ 2^E` has length `≤ E + 2 + 2 bitLen D`. -/
theorem ratLen_le_of_BInt {q : ℚ} {D : ℕ} (hD : 1 ≤ D) (hq : BInt D q) {E : ℕ}
    (hE : |q| ≤ 2 ^ E) : ratLen q ≤ E + 2 + 2 * bitLen D := by
  obtain ⟨a, ha⟩ := hq
  have h1 := ratLen_le_of_mul_eq (by omega) ha
  have h2 : a.natAbs ≤ 2 ^ E * D := by
    have : (|a| : ℚ) ≤ 2 ^ E * D := by
      have : (|a| : ℚ) = |q| * D := by
        rw [← ha, abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ D)]
      rw [this]; exact mul_le_mul_of_nonneg_right hE (by positivity)
    have : ((a.natAbs : ℤ) : ℚ) ≤ ((2 ^ E * D : ℕ) : ℚ) := by
      rw [Int.natCast_natAbs]; push_cast; exact this
    exact_mod_cast this
  have h3 := (bitLen_mono h2).trans (bitLen_mul_le _ _)
  rw [bitLen_two_pow] at h3
  omega

/-- INTERNAL: a read (default past the end) from a list whose members satisfy `P`
satisfies `P`, if the default does. -/
theorem getD_pred {α : Type} [Inhabited α] (P : α → Prop) (l : List α) (i : ℕ)
    (hl : ∀ x ∈ l, P x) (hd : P default) : P (l.getD i default) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => simpa using hd
  | some x => simpa using hl x (List.mem_of_getElem? h)

/-- INTERNAL: a write of a value satisfying `P` keeps "every member satisfies `P`". -/
theorem forall_mem_set {α : Type} (P : α → Prop) (l : List α) (i : ℕ) (a : α)
    (hl : ∀ x ∈ l, P x) (ha : P a) : ∀ x ∈ l.set i a, P x := by
  intro x hx
  rcases List.mem_or_eq_of_mem_set hx with h | h
  · exact hl x h
  · exact h ▸ ha

/-- INTERNAL: value of `addAt`. -/
theorem addAt_val (acc : List SRat) (v : ℕ) (x : SRat) :
    (addAt acc v x).val = acc.set v (SRat.add (acc.getD v default) x).val := by
  unfold addAt; simp only [costVb, val_get, val_set]

/-- INTERNAL: price of `addAt`. -/
theorem addAt_steps (acc : List SRat) (v : ℕ) (x : SRat) :
    Charged.steps rate (addAt acc v x) =
      (v + 1) + ((ratLen (acc.getD v default).get + 1) * (ratLen x.get + 1) + (v + 1)) := by
  unfold addAt
  simp only [Charged.steps_bind, steps_get, steps_SRat_add, steps_set, val_get]

/-- INTERNAL: `addAt` keeps a list invariant when the updated entry satisfies it. -/
theorem addAt_inv (P : ℚ → Prop) (acc : List SRat) (v : ℕ) (x : SRat)
    (hl : ∀ q ∈ acc, P q.get) (hnew : P ((acc.getD v default).get + x.get)) :
    ∀ q ∈ (addAt acc v x).val, P q.get := by
  rw [addAt_val]
  exact forall_mem_set (fun q : SRat => P q.get) _ _ _ hl (by simpa using hnew)

end OC

end Cellcounting.Analysis

namespace Cellcounting.Analysis
namespace OC
open Arlib.Computation Cellcounting.Program Cellcounting.Model.Operations Cellcounting.Interface

theorem two_mul_le_two_pow (S : ℕ) : 2 * S ≤ 2 ^ S := by
  induction S with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have : 1 ≤ 2 ^ n := Nat.one_le_two_pow; omega

/-- INTERNAL: the length of a read from a list of `(1/D)ℤ`-values of magnitude `≤ 2^E`. -/
theorem ratLen_getD_le {l : List SRat} {D E : ℕ} (hD : 1 ≤ D)
    (hl : ∀ q ∈ l, BInt D q.get ∧ |q.get| ≤ 2 ^ E) (i : ℕ) :
    ratLen (l.getD i default).get ≤ E + 2 + 2 * bitLen D := by
  have := getD_pred (fun q : SRat => BInt D q.get ∧ |q.get| ≤ 2 ^ E) l i hl
    (by simp [BInt.zero])
  exact ratLen_le_of_BInt hD this.1 this.2

/-- INTERNAL: magnitude arithmetic. -/
theorem two_mul_add_le_pow (S r : ℕ) (hrS : (r : ℚ) + 1 ≤ S) :
    (2 * r * S + S : ℚ) ≤ 2 ^ (2 * S) := by
  have h1 : ((2 * S : ℕ) : ℚ) ≤ 2 ^ S := by exact_mod_cast two_mul_le_two_pow S
  have h2 : (2 ^ (2 * S) : ℚ) = 2 ^ S * 2 ^ S := by rw [two_mul, pow_add]
  have h0 : (0 : ℚ) ≤ S := by positivity
  push_cast at h1
  rw [h2]
  nlinarith

/-- INTERNAL: cost arithmetic. -/
theorem cost_arith1 (S : ℕ) (hS : 2 ^ 20 ≤ S) :
    2 * ((4 * S + 5) * (S + 4)) + 14 * S + 8 ≤ S ^ 3 := by
  have : S ^ 3 = S * S * S := by ring
  rw [this]; nlinarith

/-- INTERNAL: the small-cell loop of `penalty`. -/
theorem penalty_small_loop (S : ℕ) (C : Ctx) (hS : 2 ^ 20 ≤ S) (hC : CtxSize S C)
    (x y : List SNat) (hxy : ProfileValid C x y) (acc0 : List SRat)
    (h0 : ∀ q ∈ acc0, BInt C.B.get q.get ∧ |q.get| ≤ 0) :
    (∀ q ∈ (Charged.repeatFor (fun k acc => do
        let s ← Model.Operations.get C.small k
        let xs ← Model.Operations.get x k
        let ys ← Model.Operations.get y k
        let xq ← xs.toRat
        let acc' ← addAt acc s.1 xq
        let cv ← s.2.2.sub ys
        let cq ← cv.toRat
        addAt acc' (C.m + s.2.1) cq) C.nSmall acc0).val,
        BInt C.B.get q.get ∧ |q.get| ≤ 2 * C.nSmall * S) ∧
    Charged.steps rate (Charged.repeatFor (fun k acc => do
        let s ← Model.Operations.get C.small k
        let xs ← Model.Operations.get x k
        let ys ← Model.Operations.get y k
        let xq ← xs.toRat
        let acc' ← addAt acc s.1 xq
        let cv ← s.2.2.sub ys
        let cq ← cv.toRat
        addAt acc' (C.m + s.2.1) cq) C.nSmall acc0) ≤ C.nSmall * S ^ 3 := by
  refine repeatFor_inv _ (fun r (acc : List SRat) =>
    ∀ q ∈ acc, BInt C.B.get q.get ∧ |q.get| ≤ 2 * r * S) (S ^ 3) C.nSmall acc0
    (by simpa using h0) ?_
  intro r acc hr hacc
  simp only [Charged.steps_bind, costVb, val_get, steps_get, steps_SNat_toRat,
    steps_SNat_sub, SNat.get_sub]
  have hB1 : 1 ≤ C.B.get := hC.B_pos
  have hBS : C.B.get ≤ S := hC.B_le
  have hsm := getD_pred (fun e : Entry => e.1 ≤ S ∧ e.2.1 ≤ S ∧ e.2.2.get ≤ S) C.small r
    hC.small_le (by refine ⟨Nat.zero_le _, Nat.zero_le _, ?_⟩; show (default : SNat).get ≤ S; simp)
  obtain ⟨hx, hy⟩ := hxy r hr
  generalize C.small.getD r default = s at hsm hx hy
  generalize x.getD r default = xs at hx
  generalize y.getD r default = ys at hy
  obtain ⟨hs1, hs2, hs3⟩ := hsm
  have hxs : xs.get ≤ S := hx.trans hs3
  have hcv : s.2.2.get - ys.get ≤ S := (Nat.sub_le _ _).trans hs3
  -- after the first update
  have hacc1 : ∀ q ∈ (addAt acc s.1 (SNat.toRat xs).val).val,
      BInt C.B.get q.get ∧ |q.get| ≤ 2 * r * S + S := by
    refine addAt_inv (fun q => BInt C.B.get q ∧ |q| ≤ 2 * r * S + S) _ _ _ ?_ ?_
    · intro q hq; obtain ⟨h1, h2⟩ := hacc q hq; exact ⟨h1, by linarith⟩
    · have hg := getD_pred (fun q : SRat => BInt C.B.get q.get ∧ |q.get| ≤ 2 * r * S) acc s.1 hacc
        (by simp [BInt.zero] <;> positivity)
      simp only [SNat.get_toRat]
      refine ⟨hg.1.add (BInt.natCast _ _), ?_⟩
      calc |(acc.getD s.1 default).get + (xs.get : ℚ)|
          ≤ |(acc.getD s.1 default).get| + |(xs.get : ℚ)| := abs_add_le _ _
        _ ≤ 2 * r * S + S := by
          rw [abs_of_nonneg (by positivity : (0 : ℚ) ≤ xs.get)]
          have : (xs.get : ℚ) ≤ S := by exact_mod_cast hxs
          linarith [hg.2]
  have hrS : (r : ℚ) + 1 ≤ S := by
    have : r + 1 ≤ S := by have := hC.nSmall_le; omega
    exact_mod_cast this
  have hmag : (2 * r * S + S : ℚ) ≤ 2 ^ (2 * S) := (two_mul_add_le_pow S r hrS)
  have hacc2 : ∀ q ∈ (addAt (addAt acc s.1 (SNat.toRat xs).val).val (C.m + s.2.1)
      (SNat.toRat (s.2.2.sub ys).val).val).val,
      BInt C.B.get q.get ∧ |q.get| ≤ 2 * ((r + 1 : ℕ) : ℚ) * S := by
    refine addAt_inv (fun q => BInt C.B.get q ∧ |q| ≤ 2 * ((r + 1 : ℕ) : ℚ) * S) _ _ _ ?_ ?_
    · intro q hq; obtain ⟨h1, h2⟩ := hacc1 q hq; exact ⟨h1, by push_cast; linarith⟩
    · have hg := getD_pred (fun q : SRat => BInt C.B.get q.get ∧ |q.get| ≤ 2 * r * S + S) _
        (C.m + s.2.1) hacc1 (by simp [BInt.zero] <;> positivity)
      simp only [SNat.get_toRat, SNat.get_sub]
      refine ⟨hg.1.add (BInt.natCast _ _), ?_⟩
      generalize (Charged.val (addAt acc s.1 (SNat.toRat xs).val)).getD (C.m + s.2.1) default = u
        at hg ⊢
      have ht := abs_add_le u.get ((s.2.2.get - ys.get : ℕ) : ℚ)
      rw [abs_of_nonneg (by positivity : (0 : ℚ) ≤ ((s.2.2.get - ys.get : ℕ) : ℚ))] at ht
      have : ((s.2.2.get - ys.get : ℕ) : ℚ) ≤ S := by exact_mod_cast hcv
      push_cast at ht this ⊢; linarith [hg.2]
  refine ⟨hacc2, ?_⟩
  rw [addAt_steps, addAt_steps]
  have hL1 := ratLen_getD_le hB1 (E := 2 * S) (fun q hq => ⟨(hacc q hq).1,
    (hacc q hq).2.trans (by linarith)⟩) s.1
  have hL2 := ratLen_getD_le hB1 (E := 2 * S) (fun q hq => ⟨(hacc1 q hq).1,
    (hacc1 q hq).2.trans hmag⟩) (C.m + s.2.1)
  simp only [SNat.get_toRat, SNat.get_sub, ratLen_natCast] at hL1 hL2 ⊢
  have hbB : bitLen C.B.get ≤ S + 1 := (bitLen_le_succ _).trans (by omega)
  have e1 : bitLen xs.get ≤ S + 1 := (bitLen_le_succ _).trans (by omega)
  have e2 : bitLen (s.2.2.get - ys.get) ≤ S + 1 := (bitLen_le_succ _).trans (by omega)
  have e3 : bitLen s.2.2.get ≤ S + 1 := (bitLen_le_succ _).trans (by omega)
  have e4 : bitLen ys.get ≤ S + 1 := (bitLen_le_succ _).trans (by omega)
  have hm : C.m ≤ S := hC.m_le
  have hrS' : r + 1 ≤ S := by have := hC.nSmall_le; omega
  generalize ratLen ((acc.getD s.1 default).get) = a1 at *
  generalize ratLen (((addAt acc s.1 (SNat.toRat xs).val).val.getD (C.m + s.2.1) default).get)
    = a2 at *
  have f1 : (a1 + 1) * (bitLen xs.get + 2 + 1) ≤ (4 * S + 5) * (S + 4) :=
    Nat.mul_le_mul (by omega) (by omega)
  have f2 : (a2 + 1) * (bitLen (s.2.2.get - ys.get) + 2 + 1) ≤ (4 * S + 5) * (S + 4) :=
    Nat.mul_le_mul (by omega) (by omega)
  have f3 := cost_arith1 S hS
  omega
/-- INTERNAL: magnitude arithmetic. -/
theorem free_mag_le (S r : ℕ) (hS : 4 ≤ S) (hrS : r + 1 ≤ S) :
    (2 * S * S + ((r + 1 : ℕ) : ℚ) * 2 ^ (S + 1) : ℚ) ≤ 2 ^ (3 * S) := by
  have h1 : ((2 * S : ℕ) : ℚ) ≤ 2 ^ S := by exact_mod_cast two_mul_le_two_pow S
  have h3 : (2 ^ (3 * S) : ℚ) = 2 ^ S * 2 ^ S * 2 ^ S := by
    rw [show 3 * S = S + S + S by ring, pow_add, pow_add]
  have h4 : (2 : ℚ) ^ (S + 1) = 2 ^ S * 2 := pow_succ _ _
  have h5 : (16 : ℚ) ≤ 2 ^ S := by
    have : (2 : ℚ) ^ 4 ≤ 2 ^ S := pow_le_pow_right₀ (by norm_num) hS
    norm_num at this; exact this
  have hr : ((r + 1 : ℕ) : ℚ) ≤ S := by exact_mod_cast hrS
  have h0 : (0 : ℚ) ≤ S := by positivity
  push_cast at h1 hr
  rw [h3, h4]
  have hS2 : (S : ℚ) ≤ 2 ^ S := by linarith
  have hp : (0 : ℚ) ≤ 2 ^ S := by positivity
  push_cast
  set X : ℚ := 2 ^ S
  have hXX : X * X * 16 ≤ X * X * X := by nlinarith
  have hSS : (S : ℚ) * S ≤ X * X := mul_le_mul hS2 hS2 h0 hp
  have hrX : ((r : ℚ) + 1) * X ≤ S * X := mul_le_mul_of_nonneg_right hr hp
  have hSX : (S : ℚ) * X ≤ X * X := mul_le_mul_of_nonneg_right hS2 hp
  nlinarith

/-- INTERNAL: cost arithmetic. -/
theorem cost_arith2 (S : ℕ) (hS : 2 ^ 20 ≤ S) :
    8 * S + 2 * ((5 * S + 5) * (3 * S + 5)) + 8 ≤ S ^ 3 := by
  have : S ^ 3 = S * S * S := by ring
  rw [this]; nlinarith

/-- INTERNAL: the free-cell loop of `penalty`. -/
theorem penalty_free_loop (S : ℕ) (C : Ctx) (hS : 2 ^ 20 ≤ S) (hC : CtxSize S C)
    (zf : List SRat)
    (hz : ∀ k < C.nFree, 0 ≤ (zf.getD k default).get ∧
      (zf.getD k default).get ≤ (C.free.getD k default).2.2.get + 1 ∧
      BInt C.B.get (zf.getD k default).get)
    (acc1 : List SRat) (h1 : ∀ q ∈ acc1, BInt C.B.get q.get ∧ |q.get| ≤ 2 * S * S) :
    (∀ q ∈ (Charged.repeatFor (fun k acc => do
        let e ← Model.Operations.get C.free k
        let ze ← Model.Operations.get zf k
        let acc' ← addAt acc e.1 ze
        addAt acc' (C.m + e.2.1) ze) C.nFree acc1).val,
        BInt C.B.get q.get ∧ |q.get| ≤ 2 ^ (3 * S)) ∧
    Charged.steps rate (Charged.repeatFor (fun k acc => do
        let e ← Model.Operations.get C.free k
        let ze ← Model.Operations.get zf k
        let acc' ← addAt acc e.1 ze
        addAt acc' (C.m + e.2.1) ze) C.nFree acc1) ≤ C.nFree * S ^ 3 := by
  have key := repeatFor_inv (fun k acc => do
        let e ← Model.Operations.get C.free k
        let ze ← Model.Operations.get zf k
        let acc' ← addAt acc e.1 ze
        addAt acc' (C.m + e.2.1) ze) (fun r (acc : List SRat) =>
    ∀ q ∈ acc, BInt C.B.get q.get ∧ |q.get| ≤ 2 * S * S + (r : ℚ) * 2 ^ (S + 1)) (S ^ 3)
    C.nFree acc1 (by simpa using h1) ?_
  · refine ⟨fun q hq => ⟨(key.1 q hq).1, (key.1 q hq).2.trans ?_⟩, key.2⟩
    rcases Nat.eq_zero_or_pos C.nFree with h | h
    · rw [h]; simp only [CharP.cast_eq_zero, zero_mul, add_zero]
      have := free_mag_le S 0 (by omega) (by omega)
      have hp : (0 : ℚ) ≤ ((0 + 1 : ℕ) : ℚ) * 2 ^ (S + 1) := by positivity
      linarith
    · have := free_mag_le S (C.nFree - 1) (by omega) (by have := hC.nFree_le; omega)
      have e : ((C.nFree - 1 + 1 : ℕ) : ℚ) = C.nFree := by congr 1; omega
      rw [e] at this; exact this
  intro r acc hr hacc
  simp only [Charged.steps_bind, costVb, val_get, steps_get]
  have hB1 : 1 ≤ C.B.get := hC.B_pos
  have hBS : C.B.get ≤ S := hC.B_le
  have hfr := getD_pred (fun e : Entry => e.1 ≤ S ∧ e.2.1 ≤ S ∧ bitLen e.2.2.get ≤ S) C.free r
    hC.free_le (by refine ⟨Nat.zero_le _, Nat.zero_le _, ?_⟩
                   show bitLen (default : SNat).get ≤ S; simp [bitLen]; omega)
  obtain ⟨hz0, hz1, hzB⟩ := hz r hr
  generalize C.free.getD r default = e at hfr hz1
  generalize zf.getD r default = ze at hz0 hz1 hzB
  obtain ⟨he1, he2, he3⟩ := hfr
  have hb : (e.2.2.get : ℚ) + 1 ≤ 2 ^ S := by
    have := lt_two_pow_bitLen e.2.2.get
    have : e.2.2.get + 1 ≤ 2 ^ S :=
      Nat.succ_le_of_lt (lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) he3))
    exact_mod_cast this
  have hze : |ze.get| ≤ 2 ^ S := by rw [abs_of_nonneg hz0]; linarith
  have hS1 : (2 : ℚ) ^ (S + 1) = 2 ^ S + 2 ^ S := by rw [pow_succ]; ring
  have hacc1 : ∀ q ∈ (addAt acc e.1 ze).val,
      BInt C.B.get q.get ∧ |q.get| ≤ 2 * S * S + (r : ℚ) * 2 ^ (S + 1) + 2 ^ S := by
    refine addAt_inv (fun q => BInt C.B.get q ∧ |q| ≤ 2 * S * S + (r : ℚ) * 2 ^ (S + 1) + 2 ^ S)
      _ _ _ ?_ ?_
    · intro q hq; obtain ⟨h1, h2⟩ := hacc q hq
      exact ⟨h1, by have : (0 : ℚ) ≤ 2 ^ S := by positivity
                    linarith⟩
    · have hg := getD_pred (fun q : SRat => BInt C.B.get q.get ∧
        |q.get| ≤ 2 * S * S + (r : ℚ) * 2 ^ (S + 1)) acc e.1 hacc
        (by simp [BInt.zero] <;> positivity)
      refine ⟨hg.1.add hzB, ?_⟩
      have := abs_add_le (acc.getD e.1 default).get ze.get
      linarith [hg.2]
  have hacc2 : ∀ q ∈ (addAt (addAt acc e.1 ze).val (C.m + e.2.1) ze).val,
      BInt C.B.get q.get ∧ |q.get| ≤ 2 * S * S + ((r + 1 : ℕ) : ℚ) * 2 ^ (S + 1) := by
    refine addAt_inv (fun q => BInt C.B.get q ∧
      |q| ≤ 2 * S * S + ((r + 1 : ℕ) : ℚ) * 2 ^ (S + 1)) _ _ _ ?_ ?_
    · intro q hq; obtain ⟨h1, h2⟩ := hacc1 q hq
      exact ⟨h1, by push_cast; linarith⟩
    · have hg := getD_pred (fun q : SRat => BInt C.B.get q.get ∧
        |q.get| ≤ 2 * S * S + (r : ℚ) * 2 ^ (S + 1) + 2 ^ S) _ (C.m + e.2.1) hacc1
        (by simp [BInt.zero] <;> positivity)
      refine ⟨hg.1.add hzB, ?_⟩
      have := abs_add_le ((addAt acc e.1 ze).val.getD (C.m + e.2.1) default).get ze.get
      push_cast; linarith [hg.2]
  refine ⟨hacc2, ?_⟩
  rw [addAt_steps, addAt_steps]
  have hrS : r + 1 ≤ S := by have := hC.nFree_le; omega
  have hmag := free_mag_le S r (by omega) hrS
  have hL1 := ratLen_getD_le hB1 (E := 3 * S) (fun q hq => ⟨(hacc q hq).1,
    (hacc q hq).2.trans (by
      have : (r : ℚ) * 2 ^ (S + 1) ≤ ((r + 1 : ℕ) : ℚ) * 2 ^ (S + 1) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity); push_cast; linarith
      linarith)⟩) e.1
  have hL2 := ratLen_getD_le hB1 (E := 3 * S) (fun q hq => ⟨(hacc1 q hq).1,
    (hacc1 q hq).2.trans (by push_cast at hmag ⊢; linarith)⟩) (C.m + e.2.1)
  have hLz := ratLen_le_of_BInt hB1 hzB hze
  have hbB : bitLen C.B.get ≤ S + 1 := (bitLen_le_succ _).trans (by omega)
  have hm : C.m ≤ S := hC.m_le
  generalize ratLen ((acc.getD e.1 default).get) = a1 at *
  generalize ratLen (((addAt acc e.1 ze).val.getD (C.m + e.2.1) default).get) = a2 at *
  generalize ratLen ze.get = z at *
  have f1 : (a1 + 1) * (z + 1) ≤ (5 * S + 5) * (3 * S + 5) :=
    Nat.mul_le_mul (by omega) (by omega)
  have f2 : (a2 + 1) * (z + 1) ≤ (5 * S + 5) * (3 * S + 5) :=
    Nat.mul_le_mul (by omega) (by omega)
  have f3 := cost_arith2 S hS
  omega

/-- INTERNAL: a margin is a natural of length `≤ S`, read for `≤ 4S + 3`. -/
theorem margin_spec (S : ℕ) (C : Ctx) (hC : CtxSize S C) (v : ℕ) (hv : v ≤ S) :
    (∃ n : ℕ, (margin C v).val.get = n ∧ bitLen n ≤ S) ∧
      Charged.steps rate (margin C v) ≤ 4 * S + 3 := by
  have hm : C.m ≤ S := hC.m_le
  have hvb : bitLen v ≤ S + 1 := (bitLen_le_succ _).trans (by omega)
  have hmb : bitLen C.m ≤ S + 1 := (bitLen_le_succ _).trans (by omega)
  have hS1 : 1 ≤ S := by
    have := hC.H_pos; have := hC.H_le; omega
  unfold margin
  simp only [Charged.steps_bind, costVb, steps_idxLt, val_idxLt]
  rcases Nat.lt_or_ge v C.m with h | h
  · simp only [h, decide_true, ↓reduceIte]
    simp only [Charged.steps_bind, costVb, steps_get, val_get, steps_SNat_toRat, SNat.get_toRat]
    have := getD_pred (fun x : SNat => bitLen x.get ≤ S) C.rows v hC.rows_bits
      (by show bitLen (default : SNat).get ≤ S; simp [bitLen]; omega)
    exact ⟨⟨_, rfl, this⟩, by omega⟩
  · simp only [show ¬ v < C.m by omega, decide_false, Bool.false_eq_true, ↓reduceIte]
    simp only [Charged.steps_bind, costVb, steps_get, val_get, steps_SNat_toRat, SNat.get_toRat]
    have := getD_pred (fun x : SNat => bitLen x.get ≤ S) C.cols (v - C.m) hC.cols_bits
      (by show bitLen (default : SNat).get ≤ S; simp [bitLen]; omega)
    exact ⟨⟨_, rfl, this⟩, by omega⟩

/-- INTERNAL: a natural of length `≤ S` is `< 2^S`. -/
theorem lt_two_pow_of_bitLen_le {n S : ℕ} (h : bitLen n ≤ S) : (n : ℚ) < 2 ^ S := by
  have := lt_of_lt_of_le (lt_two_pow_bitLen n) (Nat.pow_le_pow_right (by norm_num) h)
  exact_mod_cast this

/-- INTERNAL: cost arithmetic. -/
theorem cost_arith3 (S : ℕ) (hS : 2 ^ 20 ≤ S) :
    20 * S + 20 + 2 * ((8 * S + 1) * (8 * S + 1)) ≤ S ^ 3 := by
  have : S ^ 3 = S * S * S := by ring
  rw [this]; nlinarith

/-- INTERNAL: the leaf-elimination fold of `penalty`. -/
theorem penalty_tree_loop (S : ℕ) (C : Ctx) (hS : 2 ^ 20 ≤ S) (hC : CtxSize S C)
    (st0 : List SRat × List SRat)
    (h0 : ∀ q ∈ st0.1, BInt C.B.get q.get ∧ |q.get| ≤ 2 ^ (3 * S + 2 * 0))
    (h0' : ∀ q ∈ st0.2, BInt C.B.get q.get ∧ |q.get| ≤ 2 ^ (3 * S + 2 * 0)) :
    ((∀ q ∈ (Charged.foldl (fun (st : List SRat × List SRat) (vt : ℕ × ℕ) => do
        let e ← Model.Operations.get C.tree vt.2
        let marg ← margin C vt.1
        let av ← Model.Operations.get st.1 vt.1
        let ztv ← marg.sub av
        let zt ← Model.Operations.set st.2 vt.2 ztv
        let atRow ← idxEq vt.1 e.1
        if atRow = true then do
            let acc ← addAt st.1 (C.m + e.2.1) ztv
            pure (acc, zt)
          else do
            let acc ← addAt st.1 e.1 ztv
            pure (acc, zt)) C.order st0).val.1,
        BInt C.B.get q.get ∧ |q.get| ≤ 2 ^ (5 * S)) ∧
     (∀ q ∈ (Charged.foldl (fun (st : List SRat × List SRat) (vt : ℕ × ℕ) => do
        let e ← Model.Operations.get C.tree vt.2
        let marg ← margin C vt.1
        let av ← Model.Operations.get st.1 vt.1
        let ztv ← marg.sub av
        let zt ← Model.Operations.set st.2 vt.2 ztv
        let atRow ← idxEq vt.1 e.1
        if atRow = true then do
            let acc ← addAt st.1 (C.m + e.2.1) ztv
            pure (acc, zt)
          else do
            let acc ← addAt st.1 e.1 ztv
            pure (acc, zt)) C.order st0).val.2,
        BInt C.B.get q.get ∧ |q.get| ≤ 2 ^ (5 * S))) ∧
    Charged.steps rate (Charged.foldl (fun (st : List SRat × List SRat) (vt : ℕ × ℕ) => do
        let e ← Model.Operations.get C.tree vt.2
        let marg ← margin C vt.1
        let av ← Model.Operations.get st.1 vt.1
        let ztv ← marg.sub av
        let zt ← Model.Operations.set st.2 vt.2 ztv
        let atRow ← idxEq vt.1 e.1
        if atRow = true then do
            let acc ← addAt st.1 (C.m + e.2.1) ztv
            pure (acc, zt)
          else do
            let acc ← addAt st.1 e.1 ztv
            pure (acc, zt)) C.order st0) ≤ C.order.length * S ^ 3 := by
  have hB1 : 1 ≤ C.B.get := hC.B_pos
  have hBS : C.B.get ≤ S := hC.B_le
  have hbB : bitLen C.B.get ≤ S + 1 := (bitLen_le_succ _).trans (by omega)
  have hm : C.m ≤ S := hC.m_le
  have key := foldl_inv (fun (st : List SRat × List SRat) (vt : ℕ × ℕ) => do
        let e ← Model.Operations.get C.tree vt.2
        let marg ← margin C vt.1
        let av ← Model.Operations.get st.1 vt.1
        let ztv ← marg.sub av
        let zt ← Model.Operations.set st.2 vt.2 ztv
        let atRow ← idxEq vt.1 e.1
        if atRow = true then do
            let acc ← addAt st.1 (C.m + e.2.1) ztv
            pure (acc, zt)
          else do
            let acc ← addAt st.1 e.1 ztv
            pure (acc, zt))
    (fun i (st : List SRat × List SRat) =>
      (∀ q ∈ st.1, BInt C.B.get q.get ∧ |q.get| ≤ 2 ^ (3 * S + 2 * i)) ∧
      (∀ q ∈ st.2, BInt C.B.get q.get ∧ |q.get| ≤ 2 ^ (3 * S + 2 * i))) (S ^ 3) C.order 0 st0
    ⟨h0, h0'⟩ ?_
  · have hl : C.order.length ≤ S := hC.order_length
    have hpow : (2 : ℚ) ^ (3 * S + 2 * (0 + C.order.length)) ≤ 2 ^ (5 * S) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    refine ⟨⟨fun q hq => ⟨(key.1.1 q hq).1, (key.1.1 q hq).2.trans hpow⟩,
      fun q hq => ⟨(key.1.2 q hq).1, (key.1.2 q hq).2.trans hpow⟩⟩, key.2⟩
  rintro i ⟨acc, zt⟩ vt - hi hvt ⟨hacc, hzt⟩
  simp only [zero_add] at hi
  dsimp only at hacc hzt
  have hvt' := hC.order_le vt hvt
  have hi' : i + 1 ≤ S := by have := hC.order_length; omega
  obtain ⟨⟨mg, hmg, hmgb⟩, hmc⟩ := margin_spec S C hC vt.1 hvt'.1
  have he := getD_pred (fun e : Entry => e.1 ≤ S ∧ e.2.1 ≤ S ∧ bitLen e.2.2.get ≤ S) C.tree vt.2
    hC.tree_le (by refine ⟨Nat.zero_le _, Nat.zero_le _, ?_⟩
                   show bitLen (default : SNat).get ≤ S; simp [bitLen]; omega)
  simp only [Charged.steps_bind, costVb, val_get, steps_get, steps_set, val_set, steps_idxEq,
    val_idxEq, steps_SRat_sub]
  generalize C.tree.getD vt.2 default = e at he ⊢
  obtain ⟨he1, he2, -⟩ := he
  generalize margin C vt.1 = M at hmg hmc ⊢
  have hav := getD_pred (fun q : SRat => BInt C.B.get q.get ∧
    |q.get| ≤ 2 ^ (3 * S + 2 * i)) acc vt.1 hacc (by simp [BInt.zero] <;> positivity)
  generalize acc.getD vt.1 default = av at hav ⊢
  have hX : (0 : ℚ) < 2 ^ (3 * S + 2 * i) := by positivity
  have hmgS : (mg : ℚ) ≤ 2 ^ (3 * S + 2 * i) := by
    have := lt_two_pow_of_bitLen_le hmgb
    have : (2 : ℚ) ^ S ≤ 2 ^ (3 * S + 2 * i) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hp2 : (2 : ℚ) ^ (3 * S + 2 * (i + 1)) = 4 * 2 ^ (3 * S + 2 * i) := by
    rw [show 3 * S + 2 * (i + 1) = 3 * S + 2 * i + 2 by ring, pow_add]; norm_num; ring
  -- the solved tree value
  have hz : BInt C.B.get (SRat.sub M.val av).val.get ∧
      |(SRat.sub M.val av).val.get| ≤ 2 * 2 ^ (3 * S + 2 * i) := by
    rw [SRat.get_sub, hmg]
    refine ⟨(BInt.natCast _ _).sub hav.1, ?_⟩
    have := abs_sub (mg : ℚ) av.get
    rw [abs_of_nonneg (by positivity : (0 : ℚ) ≤ mg)] at this
    linarith [hav.2]
  -- the update, at either endpoint
  have hupd : ∀ v, (∀ q ∈ (addAt acc v (SRat.sub M.val av).val).val,
      BInt C.B.get q.get ∧ |q.get| ≤ 2 ^ (3 * S + 2 * (i + 1))) ∧
      Charged.steps rate (addAt acc v (SRat.sub M.val av).val) ≤
        2 * (v + 1) + (8 * S + 1) * (8 * S + 1) := by
    intro v
    refine ⟨addAt_inv (fun q => BInt C.B.get q ∧ |q| ≤ 2 ^ (3 * S + 2 * (i + 1))) _ _ _
      (fun q hq => ⟨(hacc q hq).1, (hacc q hq).2.trans (by rw [hp2]; linarith)⟩) ?_, ?_⟩
    · have hg := getD_pred (fun q : SRat => BInt C.B.get q.get ∧
        |q.get| ≤ 2 ^ (3 * S + 2 * i)) acc v hacc (by simp [BInt.zero] <;> positivity)
      refine ⟨hg.1.add hz.1, ?_⟩
      have := abs_add_le (acc.getD v default).get (SRat.sub M.val av).val.get
      rw [hp2]; linarith [hg.2, hz.2]
    · rw [addAt_steps]
      have h1 := ratLen_getD_le hB1 (E := 3 * S + 2 * i) hacc v
      have h2 := ratLen_le_of_BInt hB1 hz.1 (E := 3 * S + 2 * i + 1)
        (by rw [pow_succ]; linarith [hz.2])
      have f : (ratLen (acc.getD v default).get + 1) * (ratLen (SRat.sub M.val av).val.get + 1) ≤
          (8 * S + 1) * (8 * S + 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
  have hzt' : ∀ q ∈ zt.set vt.2 (SRat.sub M.val av).val,
      BInt C.B.get q.get ∧ |q.get| ≤ 2 ^ (3 * S + 2 * (i + 1)) :=
    forall_mem_set (fun q : SRat => BInt C.B.get q.get ∧ |q.get| ≤ 2 ^ (3 * S + 2 * (i + 1)))
      _ _ _ (fun q hq => ⟨(hzt q hq).1, (hzt q hq).2.trans (by rw [hp2]; linarith)⟩)
      ⟨hz.1, hz.2.trans (by rw [hp2]; linarith)⟩
  have hmr : ratLen M.val.get ≤ 8 * S := by
    rw [hmg, ratLen_natCast]; omega
  have har : ratLen av.get ≤ 8 * S := by
    have := ratLen_le_of_BInt hB1 hav.1 hav.2; omega
  have fs : (ratLen M.val.get + 1) * (ratLen av.get + 1) ≤ (8 * S + 1) * (8 * S + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hb1 : bitLen vt.1 ≤ S + 1 := (bitLen_le_succ _).trans (by omega)
  have hb2 : bitLen e.1 ≤ S + 1 := (bitLen_le_succ _).trans (by omega)
  have f3 := cost_arith3 S hS
  by_cases hrow : vt.1 = e.1
  · obtain ⟨u1, u2⟩ := hupd (C.m + e.2.1)
    simp only [show decide (vt.1 = e.1) = true from decide_eq_true hrow, ↓reduceIte,
      Charged.steps_bind, costVb, costVp, Charged.steps_pure]
    refine ⟨⟨u1, hzt'⟩, ?_⟩
    omega
  · obtain ⟨u1, u2⟩ := hupd e.1
    simp only [show decide (vt.1 = e.1) = false from decide_eq_false hrow, Bool.false_eq_true,
      ↓reduceIte, Charged.steps_bind, costVb, costVp, Charged.steps_pure]
    refine ⟨⟨u1, hzt'⟩, ?_⟩
    omega

/-- INTERNAL: the length of a sum is at most twice the sum of the lengths. -/
theorem ratLen_add_le (x y : ℚ) : ratLen (x + y) ≤ 2 * (ratLen x + ratLen y) := by
  have hD : 0 < x.den * y.den := Nat.mul_pos x.den_pos y.den_pos
  have h : (x + y) * ((x.den * y.den : ℕ) : ℚ) = ((x.num * y.den + y.num * x.den : ℤ) : ℚ) := by
    push_cast
    have hx := Rat.mul_den_eq_num x
    have hy := Rat.mul_den_eq_num y
    calc (x + y) * (↑x.den * ↑y.den) = (x * ↑x.den) * ↑y.den + (y * ↑y.den) * ↑x.den := by ring
      _ = _ := by rw [hx, hy]
  have h1 := ratLen_le_of_mul_eq hD h
  have h2 : (x.num * y.den + y.num * x.den).natAbs ≤
      x.num.natAbs * y.den + y.num.natAbs * x.den := by
    have := Int.natAbs_add_le (x.num * y.den) (y.num * x.den)
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at this; exact this
  have h3 := (bitLen_mono h2).trans (bitLen_add_le' _ _)
  have h4 := bitLen_mul_le x.num.natAbs y.den
  have h5 := bitLen_mul_le y.num.natAbs x.den
  have h6 := bitLen_mul_le x.den y.den
  unfold ratLen at *; omega

/-- INTERNAL: value and price of `absQ`. -/
theorem absQ_spec (x : SRat) : (absQ x).val.get = |x.get| ∧
    Charged.steps rate (absQ x) ≤ 3 + 8 * (ratLen x.get + 1) := by
  unfold absQ
  simp only [Charged.steps_bind, costVb, steps_SRat_lit, steps_SRat_lt, SRat.val_lt,
    SRat.get_lit, ratLen_zero]
  by_cases h : x.get < 0
  · simp only [h, decide_true, ↓reduceIte, steps_SRat_sub, SRat.get_sub, SRat.get_lit,
      ratLen_zero]
    refine ⟨by rw [abs_of_neg h]; ring, by nlinarith⟩
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, costVp, Charged.steps_pure]
    refine ⟨(abs_of_nonneg (not_lt.1 h)).symm, by nlinarith⟩

/-- INTERNAL: value bounds and price of `distQ` against a nonnegative bound `b`. -/
theorem distQ_spec (x b : SRat) (hb : 0 ≤ b.get) (D : ℕ) (hx : BInt D x.get) (hbD : BInt D b.get) :
    BInt D (distQ x b).val.get ∧ |(distQ x b).val.get| ≤ |x.get| ∧ 0 ≤ (distQ x b).val.get ∧
    Charged.steps rate (distQ x b) ≤ 3 + 8 * (ratLen x.get + 1) +
      2 * ((ratLen b.get + 1) * (ratLen x.get + 1)) := by
  unfold distQ
  simp only [Charged.steps_bind, costVb, steps_SRat_lit, steps_SRat_lt, SRat.val_lt,
    SRat.get_lit, ratLen_zero]
  by_cases h : x.get < 0
  · simp only [h, decide_true, ↓reduceIte, steps_SRat_sub, SRat.get_sub, SRat.get_lit,
      ratLen_zero, zero_sub]
    refine ⟨hx.neg, by rw [abs_neg], by linarith, by nlinarith⟩
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, Charged.steps_bind, costVb,
      steps_SRat_lt, SRat.val_lt]
    have hx0 : 0 ≤ x.get := not_lt.1 h
    by_cases h2 : b.get < x.get
    · simp only [h2, decide_true, ↓reduceIte, steps_SRat_sub, SRat.get_sub]
      refine ⟨hx.sub hbD, ?_, by linarith, by nlinarith⟩
      rw [abs_of_nonneg (by linarith), abs_of_nonneg hx0]; linarith
    · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte, costVp, Charged.steps_pure,
        SRat.get_lit]
      refine ⟨BInt.zero _, by simp, le_rfl, by nlinarith⟩

/-- INTERNAL: cost arithmetic. -/
theorem cost_arith4 (S : ℕ) (hS : 2 ^ 20 ≤ S) :
    8 * S + 3 + 3 + 8 * (8 * S + 1) + 4 * ((9 * S + 1) * (8 * S + 1)) ≤ S ^ 3 := by
  have : S ^ 3 = S * S * S := by ring
  rw [this]; nlinarith

/-- INTERNAL: the root-sum fold of `penalty`. -/
theorem penalty_root_loop (S : ℕ) (C : Ctx) (hS : 2 ^ 20 ≤ S) (hC : CtxSize S C)
    (acc : List SRat) (hacc : ∀ q ∈ acc, BInt C.B.get q.get ∧ |q.get| ≤ 2 ^ (5 * S)) (s0 : SRat)
    (hs0 : s0.get = 0) :
    (BInt C.B.get (Charged.foldl (fun s v => do
        let av ← Model.Operations.get acc v
        let marg ← margin C v
        let dv ← SRat.sub av marg
        let a ← absQ dv
        SRat.add s a) C.roots s0).val.get ∧
     |(Charged.foldl (fun s v => do
        let av ← Model.Operations.get acc v
        let marg ← margin C v
        let dv ← SRat.sub av marg
        let a ← absQ dv
        SRat.add s a) C.roots s0).val.get| ≤ 2 ^ (6 * S + 1)) ∧
    Charged.steps rate (Charged.foldl (fun s v => do
        let av ← Model.Operations.get acc v
        let marg ← margin C v
        let dv ← SRat.sub av marg
        let a ← absQ dv
        SRat.add s a) C.roots s0) ≤ C.roots.length * S ^ 3 := by
  have hB1 : 1 ≤ C.B.get := hC.B_pos
  have hBS : C.B.get ≤ S := hC.B_le
  have hbB : bitLen C.B.get ≤ S + 1 := (bitLen_le_succ _).trans (by omega)
  have hl : C.roots.length ≤ S := hC.roots_length
  have key := foldl_inv (fun s v => do
        let av ← Model.Operations.get acc v
        let marg ← margin C v
        let dv ← SRat.sub av marg
        let a ← absQ dv
        SRat.add s a)
    (fun i (s : SRat) => BInt C.B.get s.get ∧ |s.get| ≤ (i : ℚ) * 2 ^ (5 * S + 1)) (S ^ 3)
    C.roots 0 s0 ⟨by rw [hs0]; exact BInt.zero _, by simp [hs0]⟩ ?_
  · refine ⟨⟨key.1.1, key.1.2.trans ?_⟩, key.2⟩
    have h1 : ((0 + C.roots.length : ℕ) : ℚ) ≤ 2 ^ S := by
      have := (Nat.lt_two_pow_self (n := S)).le
      have : 0 + C.roots.length ≤ 2 ^ S := by omega
      exact_mod_cast this
    have : (2 : ℚ) ^ (6 * S + 1) = 2 ^ S * 2 ^ (5 * S + 1) := by
      rw [← pow_add]; congr 1; ring
    rw [this]; exact mul_le_mul_of_nonneg_right h1 (by positivity)
  rintro i s v - hi hv hs
  simp only [zero_add] at hi
  have hvS : v ≤ S := hC.roots_le v hv
  obtain ⟨⟨mg, hmg, hmgb⟩, hmc⟩ := margin_spec S C hC v hvS
  simp only [Charged.steps_bind, costVb, val_get, steps_get, steps_SRat_sub, steps_SRat_add,
    SRat.get_add]
  have hav := getD_pred (fun q : SRat => BInt C.B.get q.get ∧
    |q.get| ≤ 2 ^ (5 * S)) acc v hacc (by simp [BInt.zero])
  generalize acc.getD v default = av at hav ⊢
  generalize margin C v = M at hmg hmc ⊢
  obtain ⟨ha1, ha2⟩ := absQ_spec (SRat.sub av M.val).val
  rw [ha1]
  have hm2 : (mg : ℚ) ≤ 2 ^ (5 * S) := by
    have := lt_two_pow_of_bitLen_le hmgb
    have : (2 : ℚ) ^ S ≤ 2 ^ (5 * S) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hp : (2 : ℚ) ^ (5 * S + 1) = 2 * 2 ^ (5 * S) := by rw [pow_succ]; ring
  have hd : BInt C.B.get (SRat.sub av M.val).val.get ∧
      |(SRat.sub av M.val).val.get| ≤ 2 ^ (5 * S + 1) := by
    rw [SRat.get_sub, hmg]
    refine ⟨hav.1.sub (BInt.natCast _ _), ?_⟩
    have := abs_sub av.get (mg : ℚ)
    rw [abs_of_nonneg (by positivity : (0 : ℚ) ≤ mg)] at this
    rw [hp]; linarith [hav.2]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact hs.1.add hd.1.abs
  · have := abs_add_le s.get |(SRat.sub av M.val).val.get|
    rw [abs_abs] at this
    push_cast; linarith [hs.2, hd.2]
  · have hsS : (i : ℚ) * 2 ^ (5 * S + 1) ≤ 2 ^ (6 * S + 1) := by
      have h1 : (i : ℚ) ≤ 2 ^ S := by
        have := (Nat.lt_two_pow_self (n := S)).le
        exact_mod_cast (show i ≤ 2 ^ S by omega)
      have : (2 : ℚ) ^ (6 * S + 1) = 2 ^ S * 2 ^ (5 * S + 1) := by
        rw [← pow_add]; congr 1; ring
      rw [this]; exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have r1 := ratLen_le_of_BInt hB1 hs.1 (hs.2.trans hsS)
    have r2 := ratLen_le_of_BInt hB1 hd.1 hd.2
    have r3 : ratLen |(SRat.sub av M.val).val.get| = ratLen (SRat.sub av M.val).val.get := by
      rcases abs_choice (SRat.sub av M.val).val.get with h | h <;> rw [h]; rw [ratLen_neg]
    have r4 := ratLen_le_of_BInt hB1 hav.1 hav.2
    have r5 : ratLen M.val.get ≤ S + 2 := by rw [hmg, ratLen_natCast]; omega
    have f1 : (ratLen av.get + 1) * (ratLen M.val.get + 1) ≤ (9 * S + 1) * (8 * S + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have f2 : (ratLen s.get + 1) * (ratLen |(SRat.sub av M.val).val.get| + 1) ≤
        (9 * S + 1) * (8 * S + 1) := Nat.mul_le_mul (by omega) (by omega)
    have f3 := cost_arith4 S hS
    have hvS' : v + 1 ≤ S + 1 := by omega
    omega

/-- INTERNAL: the common denominator `B ∏_{t<r} max(b_t, 1)` of the first `r` terms of the
distance sum. -/
noncomputable def treeDen (C : Ctx) (r : ℕ) : ℕ :=
  C.B.get * ∏ t ∈ Finset.range r, max (C.tree.getD t default).2.2.get 1

theorem treeDen_succ (C : Ctx) (r : ℕ) :
    treeDen C (r + 1) = treeDen C r * max (C.tree.getD r default).2.2.get 1 := by
  unfold treeDen; rw [Finset.prod_range_succ, mul_assoc]

theorem treeDen_pos (C : Ctx) (hB : 1 ≤ C.B.get) (r : ℕ) : 1 ≤ treeDen C r := by
  unfold treeDen
  have : 0 < ∏ t ∈ Finset.range r, max (C.tree.getD t default).2.2.get 1 :=
    Finset.prod_pos (fun t _ => by omega)
  nlinarith

theorem treeDen_le (S : ℕ) (C : Ctx) (hC : CtxSize S C) (r : ℕ) :
    treeDen C r ≤ 2 ^ (S * (r + 1)) := by
  unfold treeDen
  have h1 : C.B.get ≤ 2 ^ S := hC.B_le.trans (Nat.lt_two_pow_self).le
  have h2 : ∏ t ∈ Finset.range r, max (C.tree.getD t default).2.2.get 1 ≤ (2 ^ S) ^ r := by
    have := Finset.prod_le_pow_card (Finset.range r)
      (fun t => max (C.tree.getD t default).2.2.get 1) (2 ^ S) ?_
    · simpa using this
    intro t _
    have he := getD_pred (fun e : Entry => bitLen e.2.2.get ≤ S) C.tree t
      (fun e he => (hC.tree_le e he).2.2)
      (by show bitLen (default : SNat).get ≤ S
          simp [bitLen]; have := hC.H_pos; have := hC.H_le; omega)
    have := lt_of_lt_of_le (lt_two_pow_bitLen _) (Nat.pow_le_pow_right (by norm_num) he)
    exact max_le this.le Nat.one_le_two_pow
  calc C.B.get * _ ≤ 2 ^ S * (2 ^ S) ^ r := Nat.mul_le_mul h1 h2
    _ = 2 ^ (S * (r + 1)) := by rw [← pow_mul, ← pow_add]; congr 1; ring

theorem BInt.div_nat {D : ℕ} {q : ℚ} (hq : BInt D q) (P b : ℕ) :
    BInt (D * P * max b 1) (q / b) := by
  rcases Nat.eq_zero_or_pos b with h | h
  · subst h; simp [BInt.zero]
  · obtain ⟨a, ha⟩ := hq
    refine ⟨a * P, ?_⟩
    rw [max_eq_left h]
    have hb : (b : ℚ) ≠ 0 := by exact_mod_cast h.ne'
    push_cast; rw [← ha]; field_simp

/-- INTERNAL: cost arithmetic. -/
theorem cost_arith5 (S : ℕ) (hS : 2 ^ 20 ≤ S) :
    3 * S + 3 + (3 + 8 * (8 * S + 1) + 2 * ((S + 3) * (8 * S + 1))) + (8 * S + 1) * (S + 3) +
      (3 * S * S + 1) * (9 * S + 1) ≤ S ^ 4 := by
  have : S ^ 4 = S * S * S * S := by ring
  rw [this]
  have a1 : 1048576 * (S * S * S) ≤ S * S * S * S := by
    have := Nat.mul_le_mul_left (S * S * S) hS; linarith
  have a2 : 1048576 * (S * S) ≤ S * S * S := by
    have := Nat.mul_le_mul_left (S * S) hS; linarith
  have a3 : 1048576 * S ≤ S * S := by
    have := Nat.mul_le_mul_left S hS; linarith
  nlinarith

/-- INTERNAL: the distance-sum loop of `penalty`. -/
theorem penalty_dist_loop (S : ℕ) (C : Ctx) (hS : 2 ^ 20 ≤ S) (hC : CtxSize S C)
    (zt : List SRat) (hzt : ∀ q ∈ zt, BInt C.B.get q.get ∧ |q.get| ≤ 2 ^ (5 * S)) (s0 : SRat)
    (hs0 : s0.get = 0) :
    (BInt (treeDen C C.nTree) (Charged.repeatFor (fun t s => do
        let e ← Model.Operations.get C.tree t
        let zv ← Model.Operations.get zt t
        let bq ← e.2.2.toRat
        let dd ← distQ zv bq
        let q ← dd.div bq
        s.add q) C.nTree s0).val.get ∧
     |(Charged.repeatFor (fun t s => do
        let e ← Model.Operations.get C.tree t
        let zv ← Model.Operations.get zt t
        let bq ← e.2.2.toRat
        let dd ← distQ zv bq
        let q ← dd.div bq
        s.add q) C.nTree s0).val.get| ≤ 2 ^ (6 * S)) ∧
    Charged.steps rate (Charged.repeatFor (fun t s => do
        let e ← Model.Operations.get C.tree t
        let zv ← Model.Operations.get zt t
        let bq ← e.2.2.toRat
        let dd ← distQ zv bq
        let q ← dd.div bq
        s.add q) C.nTree s0) ≤ C.nTree * S ^ 4 := by
  have hB1 : 1 ≤ C.B.get := hC.B_pos
  have hBS : C.B.get ≤ S := hC.B_le
  have hbB : bitLen C.B.get ≤ S + 1 := (bitLen_le_succ _).trans (by omega)
  have hl : C.nTree ≤ S := hC.nTree_le
  have key := repeatFor_inv (fun t s => do
        let e ← Model.Operations.get C.tree t
        let zv ← Model.Operations.get zt t
        let bq ← e.2.2.toRat
        let dd ← distQ zv bq
        let q ← dd.div bq
        s.add q)
    (fun r (s : SRat) => BInt (treeDen C r) s.get ∧ |s.get| ≤ (r : ℚ) * 2 ^ (5 * S)) (S ^ 4)
    C.nTree s0 ⟨by rw [hs0]; exact BInt.zero _, by simp [hs0]⟩ ?_
  · refine ⟨⟨key.1.1, key.1.2.trans ?_⟩, key.2⟩
    have h1 : (C.nTree : ℚ) ≤ 2 ^ S := by
      have := (Nat.lt_two_pow_self (n := S)).le
      exact_mod_cast (show C.nTree ≤ 2 ^ S by omega)
    have : (2 : ℚ) ^ (6 * S) = 2 ^ S * 2 ^ (5 * S) := by
      rw [← pow_add]; congr 1; ring
    rw [this]; exact mul_le_mul_of_nonneg_right h1 (by positivity)
  intro r s hr hs
  simp only [Charged.steps_bind, costVb, val_get, steps_get, steps_SNat_toRat, SNat.get_toRat,
    steps_SRat_div, steps_SRat_add, SRat.get_add, SRat.get_div]
  have he := getD_pred (fun e : Entry => bitLen e.2.2.get ≤ S) C.tree r
    (fun e he => (hC.tree_le e he).2.2)
    (by show bitLen (default : SNat).get ≤ S
        simp [bitLen]; have := hC.H_pos; have := hC.H_le; omega)
  have hzv := getD_pred (fun q : SRat => BInt C.B.get q.get ∧
    |q.get| ≤ 2 ^ (5 * S)) zt r hzt (by simp [BInt.zero])
  have hden := treeDen_succ C r
  generalize C.tree.getD r default = e at he hden ⊢
  generalize zt.getD r default = zv at hzv ⊢
  obtain ⟨d1, d2, d3, d4⟩ := distQ_spec zv (SNat.toRat e.2.2).val (by simp)
    C.B.get hzv.1 (by simpa using BInt.natCast C.B.get e.2.2.get)
  simp only [SNat.get_toRat] at d1 d2 d3 d4 ⊢
  generalize distQ zv (SNat.toRat e.2.2).val = DD at d1 d2 d3 d4 ⊢
  have hq : BInt (treeDen C (r + 1)) (DD.val.get / e.2.2.get) := by
    rw [hden]
    have := d1.div_nat (∏ t ∈ Finset.range r, max (C.tree.getD t default).2.2.get 1) e.2.2.get
    unfold treeDen; rwa [mul_assoc] at this ⊢
  have hqa : |DD.val.get / e.2.2.get| ≤ 2 ^ (5 * S) := by
    rcases Nat.eq_zero_or_pos e.2.2.get with h | h
    · simp [h]
    · rw [abs_div, abs_of_pos (by exact_mod_cast h : (0 : ℚ) < e.2.2.get)]
      have : (1 : ℚ) ≤ e.2.2.get := by exact_mod_cast h
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hzv.2, abs_nonneg DD.val.get]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hden]; exact (hs.1.mul_nat _).add (hden ▸ hq)
  · have := abs_add_le s.get (DD.val.get / e.2.2.get)
    push_cast; linarith [hs.2]
  · have hsS : (r : ℚ) * 2 ^ (5 * S) ≤ 2 ^ (6 * S) := by
      have h1 : (r : ℚ) ≤ 2 ^ S := by
        have := (Nat.lt_two_pow_self (n := S)).le
        exact_mod_cast (show r ≤ 2 ^ S by omega)
      have : (2 : ℚ) ^ (6 * S) = 2 ^ S * 2 ^ (5 * S) := by
        rw [← pow_add]; congr 1; ring
      rw [this]; exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have r1 := ratLen_le_of_BInt (treeDen_pos C hB1 r) hs.1 (hs.2.trans hsS)
    have hTD : bitLen (treeDen C r) ≤ S * S + S + 1 := by
      have := bitLen_le_of_lt_two_pow (lt_of_le_of_lt (treeDen_le S C hC r)
        (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)))
      have : S * (r + 1) ≤ S * S := Nat.mul_le_mul_left _ (by omega)
      omega
    have r2 := ratLen_le_of_BInt hB1 hzv.1 hzv.2
    have r3 := ratLen_le_of_BInt hB1 d1 (d2.trans hzv.2)
    have r4 : ratLen (e.2.2.get : ℚ) ≤ S + 2 := by rw [ratLen_natCast]; omega
    have r5 := ratLen_div_le DD.val.get (e.2.2.get : ℚ)
    have f1 : (ratLen (e.2.2.get : ℚ) + 1) * (ratLen zv.get + 1) ≤ (S + 3) * (8 * S + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have f2 : (ratLen DD.val.get + 1) * (ratLen (e.2.2.get : ℚ) + 1) ≤ (8 * S + 1) * (S + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    have f3 : (ratLen s.get + 1) * (ratLen (DD.val.get / e.2.2.get) + 1) ≤
        (3 * S * S + 1) * (9 * S + 1) := Nat.mul_le_mul (by nlinarith) (by omega)
    have f4 := cost_arith5 S hS
    have hb' : bitLen e.2.2.get ≤ S := he
    omega

/-- INTERNAL: cost arithmetic. -/
theorem cost_arith6 (S : ℕ) (hS : 2 ^ 20 ≤ S) :
    3 + (3 * S + 1) + 4 * (S * S ^ 3) + (S + 1) + S * S ^ 4 + (9 * S) * (3 * S * S + 1) +
      (S + 4) * (7 * S * S + 1) ≤ S ^ 6 := by
  have e3 : S * S ^ 3 = S * S * S * S := by ring
  have e4 : S * S ^ 4 = S * S * S * S * S := by ring
  have e6 : S ^ 6 = S * S * S * S * S * S := by ring
  rw [e3, e4, e6]
  have a1 : 1048576 * (S * S * S * S * S) ≤ S * S * S * S * S * S := by
    have := Nat.mul_le_mul_left (S * S * S * S * S) hS; linarith
  have a2 : 1048576 * (S * S * S * S) ≤ S * S * S * S * S := by
    have := Nat.mul_le_mul_left (S * S * S * S) hS; linarith
  have a3 : 1048576 * (S * S * S) ≤ S * S * S * S := by
    have := Nat.mul_le_mul_left (S * S * S) hS; linarith
  have a4 : 1048576 * (S * S) ≤ S * S * S := by
    have := Nat.mul_le_mul_left (S * S) hS; linarith
  have a5 : 1048576 * S ≤ S * S := by
    have := Nat.mul_le_mul_left S hS; linarith
  nlinarith

end OC

open Arlib.Computation Cellcounting.Program Cellcounting.Model.Operations Cellcounting.Interface

open OC in
/-- **One penalty evaluation is polynomial.**
INTERNAL: the penalty part of the bit-cost bound of `prop:weight-oracle`; each bin step
and each correction sample evaluates `D` once on a point of the extended free box.
TEXLINE: sections/evaluation.tex:386-393 -/
theorem penalty_cost (S : ℕ) (C : Ctx) (hS : 2 ^ 20 ≤ S) (hC : CtxSize S C)
    (x y : List SNat) (hxy : ProfileValid C x y) (zf : List SRat)
    (hz : ∀ k < C.nFree, 0 ≤ (zf.getD k default).get ∧
      (zf.getD k default).get ≤ (C.free.getD k default).2.2.get + 1 ∧
      BInt C.B.get (zf.getD k default).get) :
    Charged.steps rate (penalty C x y zf) ≤ S ^ 6 ∧
      ratLen (penalty C x y zf).val.get ≤ S ^ 3 := by
  have hB1 : 1 ≤ C.B.get := hC.B_pos
  have hBS : C.B.get ≤ S := hC.B_le
  have hbB : bitLen C.B.get ≤ S + 1 := (bitLen_le_succ _).trans (by omega)
  obtain ⟨l1v, l1s⟩ := penalty_small_loop S C hS hC x y hxy
    (List.replicate (C.m + C.n) (SRat.lit 0).val) (by
      intro q hq; rw [List.eq_of_mem_replicate hq]; simp [BInt.zero])
  unfold penalty
  simp only [Charged.steps_bind, costVb, steps_SRat_lit, steps_replicate, val_replicate,
    steps_SRat_add, steps_SRat_mul, SRat.get_add, SRat.get_mul, ratLen_zero]
  generalize hA1 : Charged.repeatFor _ C.nSmall _ = A1
  rw [hA1] at l1v l1s
  obtain ⟨l2v, l2s⟩ := penalty_free_loop S C hS hC zf hz A1.val (fun q hq =>
    ⟨(l1v q hq).1, (l1v q hq).2.trans (by
      have : (C.nSmall : ℚ) ≤ S := by exact_mod_cast hC.nSmall_le
      have h0 : (0 : ℚ) ≤ S := by positivity
      nlinarith)⟩)
  generalize hA2 : Charged.repeatFor _ C.nFree A1.val = A2
  rw [hA2] at l2v l2s
  obtain ⟨⟨l3v, l3v'⟩, l3s⟩ := penalty_tree_loop S C hS hC
    (A2.val, List.replicate C.nTree (SRat.lit 0).val) (by simpa using l2v) (by
      intro q hq; rw [List.eq_of_mem_replicate hq]; simp [BInt.zero])
  generalize hA3 : Charged.foldl _ C.order (A2.val, _) = A3
  rw [hA3] at l3v l3v' l3s
  obtain ⟨⟨l4b, l4v⟩, l4s⟩ := penalty_root_loop S C hS hC A3.val.1 l3v (SRat.lit 0).val
    (by simp)
  generalize hA4 : Charged.foldl _ C.roots (SRat.lit 0).val = A4
  rw [hA4] at l4b l4v l4s
  obtain ⟨⟨l5b, l5v⟩, l5s⟩ := penalty_dist_loop S C hS hC A3.val.2 l3v' (SRat.lit 0).val
    (by simp)
  generalize hA5 : Charged.repeatFor _ C.nTree (SRat.lit 0).val = A5
  rw [hA5] at l5b l5v l5s
  obtain ⟨A, hA, hAS⟩ := hC.Aq_eq
  have r1 := ratLen_le_of_BInt hB1 l4b l4v
  have hTD : bitLen (treeDen C C.nTree) ≤ S * S + S + 2 := by
    have := bitLen_le_of_lt_two_pow (lt_of_le_of_lt (treeDen_le S C hC C.nTree)
      (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)))
    have : S * (C.nTree + 1) ≤ S * (S + 1) := Nat.mul_le_mul_left _ (by have := hC.nTree_le; omega)
    have : S * (S + 1) = S * S + S := by ring
    omega
  have r2 := ratLen_le_of_BInt (treeDen_pos C hB1 _) l5b l5v
  have r3 := ratLen_add_le A4.val.get A5.val.get
  have r4 : ratLen C.Aq.get ≤ S + 3 := by
    rw [hA, ratLen_natCast]; have := bitLen_le_succ A; omega
  have r5 := ratLen_mul_le C.Aq.get (A4.val.get + A5.val.get)
  have h1 : ratLen A4.val.get ≤ 9 * S := by omega
  have h2 : ratLen A5.val.get ≤ 3 * S * S := by nlinarith
  have h3 : ratLen (A4.val.get + A5.val.get) ≤ 7 * S * S := by nlinarith
  refine ⟨?_, ?_⟩
  · have f1 : (ratLen A4.val.get + 1) * (ratLen A5.val.get + 1) ≤ (9 * S) * (3 * S * S + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have f2 : (ratLen C.Aq.get + 1) * (ratLen (A4.val.get + A5.val.get) + 1) ≤
        (S + 4) * (7 * S * S + 1) := Nat.mul_le_mul (by omega) (by omega)
    have g1 : C.nSmall * S ^ 3 ≤ S * S ^ 3 := Nat.mul_le_mul_right _ hC.nSmall_le
    have g2 : C.nFree * S ^ 3 ≤ S * S ^ 3 := Nat.mul_le_mul_right _ hC.nFree_le
    have g3 : C.order.length * S ^ 3 ≤ S * S ^ 3 := Nat.mul_le_mul_right _ hC.order_length
    have g4 : C.roots.length * S ^ 3 ≤ S * S ^ 3 := Nat.mul_le_mul_right _ hC.roots_length
    have g5 : C.nTree * S ^ 4 ≤ S * S ^ 4 := Nat.mul_le_mul_right _ hC.nTree_le
    have hm := hC.m_le; have hn := hC.n_le; have ht := hC.nTree_le
    have f3 := cost_arith6 S hS
    omega
  · have : S + 3 + 7 * S * S ≤ S ^ 3 := by
      have e : S ^ 3 = S * S * S := by ring
      rw [e]; nlinarith
    omega

end Cellcounting.Analysis
