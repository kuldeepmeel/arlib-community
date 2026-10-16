import Cellcounting.Analysis.OracleCost
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Size interface of the annealing chain

INTERNAL.  `Cellcounting.Analysis.anneal_cost` splits the setup `Program.chainSetup` (S8)
from the run `Program.annealRun` (S9–S11).  This file fixes what the run's cost proof
needs to know about the setup's output: `ChainSize T C K Ph` bounds every loop count,
index and parameter of the chain `K` and the phase parameters `Ph` by `T`, records
that the pair labels list each small cell `s` exactly `b_s` times (so every profile is
box-valid), and `WSize T w` bounds the length of every stored multiplier.

It also proves the shared pieces used by more than one part of the run:
`dyadicDraw_cost`, `profile_cost` (value box-valid, price polynomial), `kind_cost`,
`factQ_cost` (the exact factorials of the lifts).
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Model
open Cellcounting.Program
open Cellcounting.Model.Operations
open Cellcounting.Interface

/-- INTERNAL: the sizes of a chain `K` and phase parameters `Ph` that the price of an
annealing run depends on, bounded by `T`; and the pair-label structure that makes every
small-count profile box-valid.
TEXLINE: sections/algorithm.tex:600-603 -/
structure ChainSize (T : ℕ) (C : Ctx) (K : Chain) (Ph : Phase) : Prop where
  p_le : K.p ≤ T
  pS_le : K.pS.get ≤ T
  nsm_eq : K.nsm = C.nSmall
  nsm_le : K.nsm ≤ T
  pairCell_length : K.pairCell.length = K.p
  pairCell_lt : ∀ s ∈ K.pairCell, s < K.nsm
  pairCell_count : ∀ s < K.nsm, K.pairCell.count s ≤ (C.small.getD s default).2.2.get
  cellFirst_le : ∀ f ∈ K.cellFirst, f ≤ T
  smallB_le : ∀ b ∈ K.smallB, b.get ≤ T
  ξ_pos : 0 < K.ξ.get
  ξ_inv_le : K.ξ.get⁻¹ ≤ T
  ξ_len : ratLen K.ξ.get ≤ T
  kAcc_le : K.kAcc ≤ T
  kAccS_le : K.kAccS.get ≤ T
  τ_le : Ph.τ.get ≤ T
  Bret_le : Ph.Bret.get ≤ T
  BretN_le : Ph.BretN ≤ T
  Nav_le : Ph.Nav.get ≤ T
  NavN_le : Ph.NavN ≤ T
  Hn_le : Ph.Hn ≤ T

/-- INTERNAL: `ChainSize` is monotone in the bound. -/
theorem ChainSize.mono {T T' : ℕ} {C : Ctx} {K : Chain} {Ph : Phase} (h : ChainSize T C K Ph)
    (hT : T ≤ T') : ChainSize T' C K Ph where
  p_le := h.p_le.trans hT
  pS_le := h.pS_le.trans hT
  nsm_eq := h.nsm_eq
  nsm_le := h.nsm_le.trans hT
  pairCell_length := h.pairCell_length
  pairCell_lt := h.pairCell_lt
  pairCell_count := h.pairCell_count
  cellFirst_le f hf := (h.cellFirst_le f hf).trans hT
  smallB_le b hb := (h.smallB_le b hb).trans hT
  ξ_pos := h.ξ_pos
  ξ_inv_le := h.ξ_inv_le.trans (by exact_mod_cast hT)
  ξ_len := h.ξ_len.trans hT
  kAcc_le := h.kAcc_le.trans hT
  kAccS_le := h.kAccS_le.trans hT
  τ_le := h.τ_le.trans hT
  Bret_le := h.Bret_le.trans hT
  BretN_le := h.BretN_le.trans hT
  Nav_le := h.Nav_le.trans hT
  NavN_le := h.NavN_le.trans hT
  Hn_le := h.Hn_le.trans hT

/-- INTERNAL: every stored multiplier of a table has length at most `T`. -/
def WSize (T : ℕ) (w : List (List SRat)) : Prop :=
  ∀ row ∈ w, ∀ x ∈ row, ratLen x.get ≤ T

/-- INTERNAL: `WSize` is monotone in the bound. -/
theorem WSize.mono {T T' : ℕ} {w : List (List SRat)} (h : WSize T w) (hT : T ≤ T') :
    WSize T' w := fun row hr x hx => (h row hr x hx).trans hT

/-- INTERNAL: a read (default past the end) from a list whose members satisfy `P`
satisfies `P`, if the default does. -/
theorem getD_pred_of_forall {α : Type} [Inhabited α] (P : α → Prop) (l : List α) (i : ℕ)
    (hl : ∀ x ∈ l, P x) (hd : P default) : P (l.getD i default) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => simpa using hd
  | some x => simpa using hl x (List.mem_of_getElem? h)

/-- INTERNAL: a read from a multiplier table (default `0` past the end) has length at
most `T`, for `T ≥ 3`. -/
theorem WSize.get2 {T : ℕ} {w : List (List SRat)} (h : WSize T w) (hT : 3 ≤ T) (i l : ℕ) :
    ratLen ((w.getD i default).getD l default).get ≤ T := by
  apply getD_pred_of_forall (fun x : SRat => ratLen x.get ≤ T) _ l _ (by simp [ratLen_zero, hT])
  apply getD_pred_of_forall (fun row : List SRat => ∀ x ∈ row, ratLen x.get ≤ T) w i h
  simp [default]

/-- INTERNAL: one dyadic integer draw on `[0, M)` with accuracy `ζ` returns at most `M`
and costs `O((bitLen M + ratLen ζ)²)`.
TEXLINE: sections/evaluation.tex:356-371 -/
theorem dyadicDraw_cost (tape : Coins ℕ) (M : SNat) (ζ : SRat) (cur : ℕ) :
    (dyadicDraw tape M ζ cur).val.1.get ≤ M.get ∧
    Charged.steps rate (dyadicDraw tape M ζ cur) ≤ 30 * (bitLen M.get + ratLen ζ.get + 6) ^ 2 := by
  unfold dyadicDraw clog2
  simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SNat_toRat, steps_SRat_div,
    steps_SRat_natCeil, steps_SNat_lit, steps_SNat_sub, steps_SNat_size, steps_SNat_index,
    steps_SNat_mul, steps_SNat_pow2, steps_SNat_div, SNat.get_toRat, SRat.get_div, SRat.get_natCeil,
    SNat.get_lit, SNat.get_sub, SNat.get_size, SNat.val_index, SNat.get_mul, SNat.get_pow2, SNat.get_div]
  generalize hq : (M.get : ℚ) / ζ.get = q
  generalize hc : ⌈q⌉₊ = c
  generalize hk : (c - 1).size = k
  obtain ⟨hY, -, hU⟩ := uniformBits_cost tape k cur
  generalize (uniformBits tape k cur) = U at hY hU ⊢
  generalize hYd : (Charged.val U).1.get = Y at hY ⊢
  have hMr : ratLen (M.get : ℚ) = bitLen M.get + 2 := ratLen_natCast _
  have hqr : ratLen q ≤ bitLen M.get + 2 + ratLen ζ.get := by
    rw [← hq, ← hMr]; exact ratLen_div_le _ _
  have hcb : bitLen c ≤ ratLen q + 2 := hc ▸ bitLen_natCeil_le q
  have hc1 : bitLen (c - 1) ≤ bitLen c := bitLen_mono (Nat.sub_le c 1)
  have hkb : k + 1 = bitLen (c - 1) := by rw [← hk]; simp [bitLen]
  have hbk : bitLen k ≤ k + 1 := bitLen_le_succ k
  have hYb : bitLen Y ≤ k + 1 := bitLen_le_of_lt_two_pow hY
  have hMY : bitLen (M.get * Y) ≤ bitLen M.get + bitLen Y := bitLen_mul_le _ _
  have h2k : bitLen (2 ^ k) = k + 2 := bitLen_two_pow k
  have hb1 : bitLen 1 = 2 := by decide
  refine ⟨?_, ?_⟩
  · apply Nat.div_le_of_le_mul
    calc M.get * Y ≤ M.get * 2 ^ k := Nat.mul_le_mul_left _ hY.le
      _ = 2 ^ k * M.get := Nat.mul_comm _ _
  · generalize bitLen M.get = x at *
    generalize ratLen ζ.get = z at *
    generalize ratLen q = r at *
    have e1 : (x + 2 + 1) * (z + 1) ≤ (x + z + 6) * (x + z + 6) := Nat.mul_le_mul (by omega) (by omega)
    have e2 : (r + 1) * (r + 1) ≤ (x + z + 6) * (x + z + 6) := Nat.mul_le_mul (by omega) (by omega)
    have e3 : k * (4 * k + 8) ≤ (x + z + 6) * (4 * (x + z + 6)) := Nat.mul_le_mul (by omega) (by omega)
    have e4 : x * bitLen Y ≤ (x + z + 6) * (x + z + 6) := Nat.mul_le_mul (by omega) (by omega)
    have e5 : bitLen (M.get * Y) * bitLen (2 ^ k) ≤ (2 * (x + z + 6)) * (x + z + 6) :=
      Nat.mul_le_mul (by omega) (by omega)
    rw [hMr]
    generalize bitLen (M.get * Y) * bitLen (2 ^ k) = P5 at *
    generalize x * bitLen Y = P4 at *
    generalize Charged.steps rate U = SU at *
    have e7 : (x + z + 6) ^ 2 = (x + z + 6) * (x + z + 6) := sq _
    rw [e7]
    nlinarith

/-- INTERNAL: reading a list after one in-range write. -/
theorem getD_set_get (l : List SNat) (s₀ s : ℕ) (v : SNat) (h : s₀ < l.length) :
    ((l.set s₀ v).getD s default).get = if s = s₀ then v.get else (l.getD s default).get := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hs : s₀ = s
  · subst hs; simp [h]
  · simp [hs, Ne.symm hs]

/-- INTERNAL: the profile `(x_s, y_s)` of any state counts, for each cell `s`, at most the
number of pair labels of `s`; its price is quadratic in `p + #small`.
TEXLINE: sections/signatures.tex:1-80 -/
theorem profile_count (K : Chain) (S : List Bool) (hlen : K.pairCell.length = K.p) (hlt : ∀ s ∈ K.pairCell, s < K.nsm) :
    (∀ s, ((profile K S).val.1.getD s default).get ≤ K.pairCell.count s ∧
      ((profile K S).val.2.getD s default).get ≤ K.pairCell.count s) ∧
    Charged.steps rate (profile K S) ≤ 10 * (K.p + K.nsm + 2) ^ 2 := by
  unfold profile
  simp only [Charged.steps_bind, costVb, costVp, steps_SNat_lit, steps_replicate, val_replicate]
  obtain ⟨h1, h2⟩ := repeatFor_inv (fun i (st : List SNat × List SNat) => (do
    let s ← Operations.get K.pairCell i
    let rowIn ← Operations.get S (2 * i)
    let colIn ← Operations.get S (2 * i + 1)
    let x ← if rowIn then do
        let a ← Operations.get st.1 s
        let a' ← SNat.add a (SNat.lit 1).val
        Operations.set st.1 s a'
      else pure st.1
    let y ← if colIn then do
        let a ← Operations.get st.2 s
        let a' ← SNat.add a (SNat.lit 1).val
        Operations.set st.2 s a'
      else pure st.2
    pure (x, y) : Prog (List SNat × List SNat)))
    (fun r (st : List SNat × List SNat) => st.1.length = K.nsm ∧ st.2.length = K.nsm ∧
      ∀ s, (st.1.getD s default).get ≤ (K.pairCell.take r).count s ∧
        (st.2.getD s default).get ≤ (K.pairCell.take r).count s)
    (8 * (K.p + K.nsm + 2)) K.p
    (List.replicate K.nsm (SNat.lit 0).val, List.replicate K.nsm (SNat.lit 0).val)
    (by
      have h0 := fun s => getD_pred_of_forall (fun x : SNat => x.get = 0)
        (List.replicate K.nsm (SNat.lit 0).val) s (by simp) (by simp)
      exact ⟨by simp, by simp, fun s => ⟨by rw [h0]; exact Nat.zero_le _,
        by rw [h0]; exact Nat.zero_le _⟩⟩)
    (by
      rintro r ⟨x, y⟩ hr ⟨hx, hy, hc⟩
      simp only [Charged.steps_bind, costVb, costVp, val_get, steps_get] at hx hy hc ⊢
      have hrl : r < K.pairCell.length := by omega
      have hs₀ : K.pairCell.getD r default = K.pairCell[r] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrl]; rfl
      have hlt₀ : K.pairCell[r] < K.nsm := hlt _ (List.getElem_mem hrl)
      have hct : ∀ s, List.count s (List.take (r + 1) K.pairCell) =
          List.count s (List.take r K.pairCell) + if K.pairCell[r] = s then 1 else 0 := by
        intro s
        rw [List.take_add_one, List.getElem?_eq_getElem hrl]
        rw [Option.toList_some, List.count_append, List.count_singleton]
        by_cases h : K.pairCell[r] = s
        · simp [h]
        · simp [h, Ne.symm h]
      have hcr : ∀ s, List.count s (List.take r K.pairCell) ≤ r := fun s =>
        (List.count_le_length).trans (by simp)
      rw [hs₀]
      generalize K.pairCell[r] = s₀ at hlt₀ hct
      have hb1 : bitLen 1 = 2 := by decide
      have hxa : bitLen (x.getD s₀ default).get ≤ r + 1 :=
        (bitLen_le_succ _).trans (by have := (hc s₀).1; have := hcr s₀; omega)
      have hya : bitLen (y.getD s₀ default).get ≤ r + 1 :=
        (bitLen_le_succ _).trans (by have := (hc s₀).2; have := hcr s₀; omega)
      rcases Bool.eq_false_or_eq_true (S.getD (2 * r) default) with h1 | h1 <;>
      rcases Bool.eq_false_or_eq_true (S.getD (2 * r + 1) default) with h2 | h2 <;>
        simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Charged.steps_bind, costVb, costVp,
          Charged.steps_pure, val_get, steps_get, val_set, steps_set, SNat.get_add, SNat.get_lit,
          steps_SNat_add, steps_SNat_lit, List.length_set, hx, hy, hb1] <;>
        refine ⟨⟨trivial, trivial, fun s => ?_⟩, by omega⟩ <;>
        simp only [getD_set_get _ _ _ _ (hx ▸ hlt₀), getD_set_get _ _ _ _ (hy ▸ hlt₀), hct,
          SNat.get_add, SNat.get_lit] <;>
        have := hc s <;> have := hc s₀ <;> split_ifs <;> subst_vars <;> omega)
  rw [List.take_of_length_le (by omega)] at h1
  refine ⟨fun s => h1.2.2 s, ?_⟩
  have hb0 : bitLen 0 = 1 := by decide
  have hb1 : bitLen 1 = 2 := by decide
  rw [hb0, hb1]
  have : K.p * (8 * (K.p + K.nsm + 2)) + (1 + (2 + (K.nsm + 1 + (K.nsm + 1)))) ≤ 10 * (K.p + K.nsm + 2) ^ 2 := by
    nlinarith
  linarith

/-- INTERNAL: under `ChainSize`, every profile is box-valid (`ProfileValid`), its
entries are at most `T`, and it costs at most `40 (T + 1)²`. -/
theorem profile_cost {T : ℕ} {C : Ctx} {K : Chain} {Ph : Phase} (hK : ChainSize T C K Ph)
    (S : List Bool) :
    ProfileValid C (profile K S).val.1 (profile K S).val.2 ∧
      (∀ s, ((profile K S).val.1.getD s default).get ≤ T ∧
        ((profile K S).val.2.getD s default).get ≤ T) ∧
      Charged.steps rate (profile K S) ≤ 40 * (T + 1) ^ 2 := by
  obtain ⟨h1, h2⟩ := profile_count K S hK.pairCell_length hK.pairCell_lt
  have hcnt : ∀ s, K.pairCell.count s ≤ T := fun s =>
    List.count_le_length.trans (hK.pairCell_length ▸ hK.p_le)
  refine ⟨fun k hk => ?_, fun s => ⟨(h1 s).1.trans (hcnt s), (h1 s).2.trans (hcnt s)⟩, ?_⟩
  · have hk' : k < K.nsm := hK.nsm_eq ▸ hk
    exact ⟨(h1 k).1.trans (hK.pairCell_count k hk'), (h1 k).2.trans (hK.pairCell_count k hk')⟩
  · have hp := hK.p_le
    have hn := hK.nsm_le
    have : (K.p + K.nsm + 2) ^ 2 ≤ (2 * (T + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith

/-- INTERNAL: `kind` names only pairs `i, l < p`, and costs `O(p²)`. -/
theorem kind_cost (K : Chain) (S : List Bool) :
    (∀ i l, (kind K S).val = .defect i l → i < K.p ∧ l < K.p) ∧
    Charged.steps rate (kind K S) ≤ 6 * (K.p + 2) ^ 2 := by
  unfold kind
  simp only [Charged.steps_bind, costVb]
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := repeatFor_inv (fun i (st : (ℕ × ℕ) × (ℕ × ℕ)) => (do
    let rowIn ← Operations.get S (2 * i)
    let colIn ← Operations.get S (2 * i + 1)
    if rowIn then
      if colIn then pure (st.1, (st.2.1 + 1, i)) else pure st
    else
      if colIn then pure st else pure ((st.1.1 + 1, i), st.2) : Prog ((ℕ × ℕ) × (ℕ × ℕ))))
    (fun r (st : (ℕ × ℕ) × (ℕ × ℕ)) => st.1.1 ≤ r ∧ st.2.1 ≤ r ∧
      (st.1.2 < r ∨ st.1.2 = 0) ∧ (st.2.2 < r ∨ st.2.2 = 0))
    (4 * K.p + 3) K.p ((0, 0), (0, 0)) (by simp)
    (by
      rintro r ⟨⟨e, ie⟩, ⟨f, i_f⟩⟩ hr ⟨he, hf, hie, hif⟩
      rcases Bool.eq_false_or_eq_true (S.getD (2 * r) default) with g1 | g1 <;>
      rcases Bool.eq_false_or_eq_true (S.getD (2 * r + 1) default) with g2 | g2 <;>
        simp only [g1, g2, Bool.false_eq_true, ↓reduceIte, Charged.steps_bind, costVb, costVp,
          Charged.steps_pure, val_get, steps_get] at he hf hie hif ⊢ <;> omega)
  generalize (Charged.repeatFor _ K.p ((0, 0), (0, 0))).val = st at h1 h2 h3 h4 ⊢
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := st
  dsimp only at h1 h2 h3 h4 ⊢
  have ha := bitLen_le_succ a
  have hc := bitLen_le_succ c
  have hb0 : bitLen 0 = 1 := by decide
  have hb1 : bitLen 1 = 2 := by decide
  have hq : K.p * (4 * K.p + 3) + 4 * (K.p + 3) ≤ 6 * (K.p + 2) ^ 2 := by nlinarith
  by_cases e0 : a = 0 <;> by_cases f0 : c = 0 <;> by_cases e1 : a = 1 <;> by_cases f1 : c = 1 <;>
    simp only [val_idxEq, steps_idxEq, e0, f0, e1, f1, decide_true, decide_false, ↓reduceIte,
      Bool.false_eq_true, Charged.steps_bind, costVb, costVp, Charged.steps_pure, Charged.val_pure,
      reduceCtorEq, false_imp_iff, implies_true, true_and, hb0, hb1] <;>
    (try subst_vars) <;> (try simp only [Kind.defect.injEq]) <;>
    first
    | (refine ⟨?_, by omega⟩; rintro i l ⟨rfl, rfl⟩; omega)
    | omega

/-- INTERNAL: `r!` has at most `r² + 2` bits. -/
theorem bitLen_factorial_le (r : ℕ) : bitLen r.factorial ≤ r * r + 2 := by
  apply bitLen_le_of_lt_two_pow
  calc r.factorial ≤ r ^ r := Nat.factorial_le_pow r
    _ ≤ (2 ^ r) ^ r := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le r
    _ = 2 ^ (r * r) := by rw [← pow_mul]
    _ < 2 ^ (r * r + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- INTERNAL: the exact factorial `Program.factQ k` used in the lifts `∏ x_s! y_s!/b_s!`
(`eq:lifts`): its value is `k!`, its length is at most `k² + 4`, and it costs at most
`(k + 4)^4`.  Small bounds satisfy `b_s < W`, so `k` is polynomial.
TEXLINE: sections/algorithm.tex:428-460 -/
theorem factQ_cost (k : SNat) :
    (factQ k).val.get = (k.get.factorial : ℚ) ∧ ratLen (factQ k).val.get ≤ k.get * k.get + 4 ∧
    Charged.steps rate (factQ k) ≤ (k.get + 4) ^ 4 := by
  unfold factQ
  simp only [Charged.steps_bind, costVb, steps_SNat_index, steps_SRat_lit, SNat.val_index]
  obtain ⟨⟨h1, h2⟩, h3⟩ := repeatFor_inv (fun i (acc : SRat) => (do
      let iS ← SNat.lit (i + 1)
      let iq ← SNat.toRat iS
      SRat.mul acc iq : Prog SRat))
    (fun r (acc : SRat) => acc.get = (r.factorial : ℚ) ∧ r ≤ k.get)
    ((k.get + 4) ^ 3) k.get (SRat.lit 1).val (by simp)
    (by
      rintro r acc hr ⟨hacc, -⟩
      simp only [Charged.steps_bind, costVb, steps_SNat_lit, steps_SNat_toRat, steps_SRat_mul,
        SRat.get_mul, SNat.get_toRat, SNat.get_lit, hacc]
      refine ⟨⟨by push_cast [Nat.factorial_succ]; ring, by omega⟩, ?_⟩
      have e1 : ratLen ((r.factorial : ℕ) : ℚ) ≤ k.get * k.get + 4 := by
        rw [ratLen_natCast]
        have := bitLen_factorial_le r
        have : r * r ≤ k.get * k.get := Nat.mul_le_mul (by omega) (by omega)
        omega
      have e2 : ratLen (((r + 1 : ℕ) : ℚ)) ≤ k.get + 3 := by
        rw [ratLen_natCast]; have := bitLen_le_succ (r + 1); omega
      have e3 : bitLen (r + 1) ≤ k.get + 1 := by have := bitLen_le_succ (r + 1); omega
      have e4 : (ratLen ((r.factorial : ℕ) : ℚ) + 1) * (ratLen (((r + 1 : ℕ) : ℚ)) + 1) ≤
          (k.get * k.get + 5) * (k.get + 4) := Nat.mul_le_mul (by omega) (by omega)
      have e5 : (k.get * k.get + 5) * (k.get + 4) + 2 * (k.get + 1) ≤ (k.get + 4) ^ 3 := by
        ring_nf; nlinarith
      push_cast at e4 ⊢
      omega)
  refine ⟨h1, ?_, ?_⟩
  · rw [h1, ratLen_natCast]
    have := bitLen_factorial_le k.get; omega
  · have e1 : ratLen (1 : ℚ) ≤ 4 := by
      have h := ratLen_natCast 1; have h' := bitLen_le_succ 1; push_cast at h; omega
    have e2 := bitLen_le_succ k.get
    have e3 : k.get * (k.get + 4) ^ 3 + (k.get + 1) + 4 ≤ (k.get + 4) ^ 4 := by
      have : (k.get + 4) ^ 4 = (k.get + 4) * (k.get + 4) ^ 3 := by ring
      rw [this]
      have h4 : k.get + 4 ≤ (k.get + 4) ^ 3 := by
        calc k.get + 4 = (k.get + 4) ^ 1 := (pow_one _).symm
          _ ≤ (k.get + 4) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      have : (k.get + 4) * (k.get + 4) ^ 3 = k.get * (k.get + 4) ^ 3 + 4 * (k.get + 4) ^ 3 := by
        ring
      omega
    omega

/-- INTERNAL: `(8T)^a ≤ T^(4a)` for `T ≥ 2`. -/
theorem eight_mul_pow_le (T : ℕ) (hT : 2 ≤ T) (a : ℕ) : (8 * T) ^ a ≤ T ^ (4 * a) := by
  rw [pow_mul]
  apply Nat.pow_le_pow_left
  have : 2 ^ 3 ≤ T ^ 3 := Nat.pow_le_pow_left hT 3
  have : T ^ 4 = T * T ^ 3 := by ring
  nlinarith

/-- INTERNAL: a matrix write keeps a property of all entries that the new entry has. -/
theorem set2_pred {α : Type} [Inhabited α] (P : α → Prop) (M : List (List α)) (u v : ℕ) (a : α)
    (hM : ∀ row ∈ M, ∀ c ∈ row, P c) (ha : P a) :
    ∀ row ∈ (set2 M u v a).val, ∀ c ∈ row, P c := by
  simp only [set2, costVb, val_get, val_set]
  intro row hrow c hc
  rcases List.mem_or_eq_of_mem_set hrow with h | h
  · exact hM row h c hc
  · subst h
    rcases List.mem_or_eq_of_mem_set hc with h' | h'
    · exact getD_pred_of_forall (fun r : List α => ∀ c ∈ r, P c) M u hM (by simp [default]) c h'
    · exact h' ▸ ha

/-- INTERNAL: price of a matrix write. -/
theorem steps_set2 {α : Type} [Inhabited α] (M : List (List α)) (u v : ℕ) (a : α) :
    Charged.steps rate (set2 M u v a) = (u + 1) + ((v + 1) + (u + 1)) := by
  simp [set2, Charged.steps_bind, costVb]

/-- INTERNAL: price of a matrix read. -/
theorem steps_get2 {α : Type} [Inhabited α] (M : List (List α)) (u v : ℕ) :
    Charged.steps rate (get2 M u v) = (u + 1) + (v + 1) := by
  simp [get2, Charged.steps_bind, costVb]

/-- INTERNAL: a matrix read returns an entry or the default. -/
theorem get2_pred {α : Type} [Inhabited α] (P : α → Prop) (M : List (List α)) (u v : ℕ)
    (hM : ∀ row ∈ M, ∀ c ∈ row, P c) (hd : P default) : P (get2 M u v).val := by
  simp only [get2, costVb, val_get]
  exact getD_pred_of_forall P _ v
    (getD_pred_of_forall (fun r : List α => ∀ c ∈ r, P c) M u hM (by simp [default])) hd

end Cellcounting.Analysis
