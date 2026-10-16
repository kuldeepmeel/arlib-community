import Cellcounting.Analysis.FeasibleCost

/-!
# Tightening S2 runs in polynomial bit cost, and keeps sizes

`Cellcounting.Analysis.tighten_cost`: for `m + n + 2 ≤ S` and margins and bounds of
binary length at most `S`, `Program.tighten` costs at most `S ^ k`; its tightened
margins have the input lengths `m`, `n` and binary length at most `S`, and it keeps
at most `m n` cells `(i, j, w)` with `i < m`, `j < n` and `bitLen w ≤ S`.

Cost: `m n` cells, each two binary searches of `bitLen b_ij ≤ S` rounds, each round
one `feasible` call (`feasible_cost`) on an instance whose entries never exceed the
input ones (search values stay in `[0, b_ij]`, margins are only decreased).  The
searches are `tc_cellMin` and `tc_cellMax` (`tc_feasibleAtLeast` for the lower-bounded
test); one cell is `tc_inner`, whose invariant `TcInv` keeps the accumulated minima
below `2 ^ (S + t)` after `t` cells; the double loop is `tc_loop`, the final margin
subtraction `tc_subLists`, and the exponent is `16 + k_feasible` (`tc_final_arith`).
The loop bodies are restated verbatim (`tcMinStep`, `tcMaxStep`, `tcInner`) with
definitional equations, as in `FeasibleCost`.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Program
open Cellcounting.Model.Operations
open Cellcounting.Interface

/-- INTERNAL: margins and bounds of size `S`: list lengths and binary lengths at most `S`. -/
def TcOK (S : ℕ) (r c : List SNat) (b : List (List SNat)) : Prop :=
  r.length ≤ S ∧ c.length ≤ S ∧ (∀ x ∈ r, bitLen x.get ≤ S) ∧ (∀ x ∈ c, bitLen x.get ≤ S) ∧
    (∀ row ∈ b, ∀ x ∈ row, bitLen x.get ≤ S)

/-- INTERNAL: a matrix read returns an entry with a property shared by the default. -/
theorem tc_get2_prop {P : SNat → Prop} {M : List (List SNat)} (h : ∀ row ∈ M, ∀ x ∈ row, P x)
    (hd : P default) (u v : ℕ) : P (get2 M u v).val := by
  unfold get2; simp only [costVb, val_get]
  exact getD_prop _ _ _
    (getD_prop (P := fun row : List SNat => ∀ x ∈ row, P x) _ _ _ h (fun x hx => by cases hx)) hd

/-- INTERNAL: a matrix write of a value with a property keeps it for all entries. -/
theorem tc_set2_prop {P : SNat → Prop} {M : List (List SNat)} (h : ∀ row ∈ M, ∀ x ∈ row, P x)
    (u v : ℕ) (a : SNat) (ha : P a) : ∀ row ∈ (set2 M u v a).val, ∀ x ∈ row, P x := by
  unfold set2; simp only [costVb, val_get, val_set]
  exact set_prop (P := fun row : List SNat => ∀ x ∈ row, P x) _ _ _ h
    (set_prop (P := P) _ _ _
      (getD_prop (P := fun row : List SNat => ∀ x ∈ row, P x) _ _ _ h (fun x hx => by cases hx)) ha)

/-- INTERNAL: `bitLen 0 = 1`. -/
theorem tc_bitLen_zero : bitLen 0 = 1 := by decide

/-- INTERNAL: the round count of a binary search over `[0, x]` is `bitLen x`. -/
theorem tc_searchRounds_val (x : SNat) : (searchRounds x).val = bitLen x.get := rfl

/-- INTERNAL: price of `searchRounds`. -/
theorem tc_searchRounds_steps (x : SNat) :
    Charged.steps rate (searchRounds x) = bitLen x.get + bitLen (bitLen x.get) := by
  unfold searchRounds; simp only [Charged.steps_bind, steps_SNat_bitLen, steps_SNat_index,
    SNat.get_bitLen]

/-- INTERNAL: the loop body of `Program.cellMin`, verbatim. -/
def tcMinStep (m n : ℕ) (r c : List SNat) (b : List (List SNat)) (i j : ℕ) (_k : ℕ)
    (st : SNat × SNat) : Prog (SNat × SNat) := do
  let isOpen ← SNat.lt st.1 st.2
  if isOpen then do
    let s ← SNat.add st.1 st.2
    let mid ← half s
    let b' ← set2 b i j mid
    let ok ← feasible m n r c b'
    if ok then pure (st.1, mid) else do
      let one ← SNat.lit 1
      let lo' ← SNat.add mid one
      pure (lo', st.2)
  else pure st

/-- INTERNAL: `Program.cellMin` in terms of `tcMinStep` (definitional). -/
theorem tc_cellMin_eq (m n : ℕ) (r c : List SNat) (b : List (List SNat)) (i j : ℕ) :
    cellMin m n r c b i j = (do
      let bij ← get2 b i j
      let lo ← SNat.lit 0
      let k ← searchRounds bij
      let st ← Charged.repeatFor (tcMinStep m n r c b i j) k (lo, bij)
      pure st.2) := rfl

/-- INTERNAL: one round of `cellMin`: the search interval stays in `[0, B]`, price `≤ F + 16 S`. -/
theorem tc_minStep (S F m n : ℕ) (r c : List SNat) (b : List (List SNat)) (i j k B : ℕ)
    (st : SNat × SNat) (hij : i + j + 2 ≤ S) (hok : TcOK S r c b)
    (hF : ∀ r' c' b', TcOK S r' c' b' → Charged.steps rate (feasible m n r' c' b') ≤ F)
    (hB : bitLen B ≤ S) (h1 : st.1.get ≤ B) (h2 : st.2.get ≤ B) :
    (tcMinStep m n r c b i j k st).val.1.get ≤ B ∧ (tcMinStep m n r c b i j k st).val.2.get ≤ B ∧
      Charged.steps rate (tcMinStep m n r c b i j k st) ≤ F + 16 * S := by
  obtain ⟨hrl, hcl, hr, hc, hb⟩ := hok
  have hB2 : B < 2 ^ S := (lt_two_pow_bitLen B).trans_le (Nat.pow_le_pow_right (by norm_num) hB)
  have b1 : bitLen st.1.get ≤ S := (bitLen_mono h1).trans hB
  have b2 : bitLen st.2.get ≤ S := (bitLen_mono h2).trans hB
  have l2 : bitLen 2 = 3 := by decide
  have l1 : bitLen 1 = 2 := by decide
  unfold tcMinStep
  simp only [Charged.steps_bind, costVb, steps_SNat_lt, SNat.val_lt]
  by_cases ho : st.1.get < st.2.get
  · have hs : bitLen (st.1.get + st.2.get) ≤ S + 1 := by
      have := bitLen_add_le st.1.get st.2.get; omega
    have hmid : (st.1.get + st.2.get) / 2 < st.2.get := by omega
    have bm : bitLen ((st.1.get + st.2.get) / 2) ≤ S :=
      (bitLen_mono (show (st.1.get + st.2.get) / 2 ≤ B by omega)).trans hB
    have hb' := tc_set2_prop (P := fun x : SNat => bitLen x.get ≤ S) hb i j
      ((half ((st.1.add st.2).val)).val) (by simpa [half, costVb] using bm)
    have hfe := hF _ _ _ ⟨hrl, hcl, hr, hc, hb'⟩
    simp only [ho, decide_true, ite_true, Charged.steps_bind, costVb, steps_SNat_add,
      fc_set2_steps]
    simp only [half, Charged.steps_bind, costVb, steps_SNat_lit, steps_SNat_div, SNat.get_lit,
      SNat.get_add, l2] at hfe ⊢
    split
    · simp only [costVp, Charged.steps_pure, SNat.get_div, SNat.get_add, SNat.get_lit]
      refine ⟨h1, by omega, by omega⟩
    · simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SNat_lit,
        steps_SNat_add, SNat.get_add, SNat.get_lit, SNat.get_div, l1]
      refine ⟨by omega, h2, by omega⟩
  · simp only [ho, decide_false, Bool.false_eq_true, ite_false, costVp, Charged.steps_pure]
    exact ⟨h1, h2, by omega⟩

/-- INTERNAL: `cellMin` returns a value in `[0, b_ij]` at price `≤ 4 S + 2 + S (F + 16 S)`. -/
theorem tc_cellMin (S F m n : ℕ) (r c : List SNat) (b : List (List SNat)) (i j : ℕ)
    (hij : i + j + 2 ≤ S) (hok : TcOK S r c b)
    (hF : ∀ r' c' b', TcOK S r' c' b' → Charged.steps rate (feasible m n r' c' b') ≤ F) :
    (cellMin m n r c b i j).val.get ≤ (get2 b i j).val.get ∧
      Charged.steps rate (cellMin m n r c b i j) ≤ 4 * S + 2 + S * (F + 16 * S) := by
  have hB : bitLen (get2 b i j).val.get ≤ S :=
    tc_get2_prop (P := fun x : SNat => bitLen x.get ≤ S) hok.2.2.2.2
      (by show bitLen (default : SNat).get ≤ S; rw [SNat.get_default, tc_bitLen_zero]; omega) i j
  rw [tc_cellMin_eq]
  obtain ⟨⟨-, h2⟩, h3⟩ := repeatFor_inv (tcMinStep m n r c b i j)
    (fun _ (st : SNat × SNat) => st.1.get ≤ (get2 b i j).val.get ∧ st.2.get ≤ (get2 b i j).val.get)
    (F + 16 * S) (searchRounds (get2 b i j).val).val ((SNat.lit 0).val, (get2 b i j).val)
    ⟨by simp, le_rfl⟩ (by
      rintro k st - ⟨h1, h2⟩
      obtain ⟨g1, g2, g3⟩ := tc_minStep S F m n r c b i j k _ st hij hok hF hB h1 h2
      exact ⟨⟨g1, g2⟩, g3⟩)
  rw [tc_searchRounds_val] at h2 h3
  have hk : bitLen (get2 b i j).val.get ≤ S := hB
  have hkk := Nat.mul_le_mul_right (F + 16 * S) hk
  have hbb := bitLen_le_succ (bitLen (get2 b i j).val.get)
  simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, fc_get2_steps,
    steps_SNat_lit, tc_bitLen_zero, tc_searchRounds_steps, tc_searchRounds_val]
  refine ⟨h2, ?_⟩
  omega

/-- INTERNAL: a value of length `≤ S` read from a list of such values (or the default `0`). -/
theorem tc_getD_len {S : ℕ} (hS : 1 ≤ S) {l : List SNat} (h : ∀ x ∈ l, bitLen x.get ≤ S) (i : ℕ) :
    bitLen (l.getD i default).get ≤ S :=
  getD_prop (P := fun x : SNat => bitLen x.get ≤ S) _ _ _ h
    (by rw [SNat.get_default, tc_bitLen_zero]; omega)

/-- INTERNAL: `feasibleAtLeast` costs at most `F + 20 S` when `bitLen v ≤ S`. -/
theorem tc_feasibleAtLeast (S F m n : ℕ) (r c : List SNat) (b : List (List SNat)) (i j : ℕ)
    (v : SNat) (hij : i + j + 2 ≤ S) (hok : TcOK S r c b)
    (hF : ∀ r' c' b', TcOK S r' c' b' → Charged.steps rate (feasible m n r' c' b') ≤ F)
    (hv : bitLen v.get ≤ S) :
    Charged.steps rate (feasibleAtLeast m n r c b i j v) ≤ F + 20 * S := by
  obtain ⟨hrl, hcl, hr, hc, hb⟩ := hok
  have hri := tc_getD_len (by omega) hr i
  have hcj := tc_getD_len (by omega) hc j
  have hbij : bitLen (get2 b i j).val.get ≤ S :=
    tc_get2_prop (P := fun x : SNat => bitLen x.get ≤ S) hb
      (by rw [SNat.get_default, tc_bitLen_zero]; omega) i j
  unfold feasibleAtLeast
  simp only [Charged.steps_bind, steps_get, val_get, fc_get2_steps, steps_SNat_le,
    SNat.val_le]
  by_cases h1 : v.get ≤ (r.getD i default).get
  · simp only [h1, decide_true, ite_true, Charged.steps_bind, steps_SNat_le, SNat.val_le]
    by_cases h2 : v.get ≤ (c.getD j default).get
    · simp only [h2, decide_true, ite_true, Charged.steps_bind, steps_SNat_le, SNat.val_le]
      by_cases h3 : v.get ≤ (get2 b i j).val.get
      · simp only [h3, decide_true, ite_true, Charged.steps_bind, steps_SNat_sub,
          steps_set, val_set, fc_set2_steps]
        have hfe := hF (r.set i ((r.getD i default).sub v).val)
          (c.set j ((c.getD j default).sub v).val) (set2 b i j ((get2 b i j).val.sub v).val).val
          ⟨by simpa using hrl, by simpa using hcl,
            set_prop (P := fun x : SNat => bitLen x.get ≤ S) _ _ _ hr
              (by rw [SNat.get_sub]; exact (bitLen_mono (Nat.sub_le _ _)).trans hri),
            set_prop (P := fun x : SNat => bitLen x.get ≤ S) _ _ _ hc
              (by rw [SNat.get_sub]; exact (bitLen_mono (Nat.sub_le _ _)).trans hcj),
            tc_set2_prop (P := fun x : SNat => bitLen x.get ≤ S) hb i j _
              (by rw [SNat.get_sub]; exact (bitLen_mono (Nat.sub_le _ _)).trans hbij)⟩
        omega
      · simp only [h3, decide_false, Bool.false_eq_true, ite_false, Charged.steps_pure]
        omega
    · simp only [h2, decide_false, Bool.false_eq_true, ite_false, Charged.steps_pure]
      omega
  · simp only [h1, decide_false, Bool.false_eq_true, ite_false, Charged.steps_pure]
    omega

/-- INTERNAL: the loop body of `Program.cellMax`, verbatim. -/
def tcMaxStep (m n : ℕ) (r c : List SNat) (b : List (List SNat)) (i j : ℕ) (_k : ℕ)
    (st : SNat × SNat) : Prog (SNat × SNat) := do
  let isOpen ← SNat.lt st.1 st.2
  if isOpen then do
    let one ← SNat.lit 1
    let s ← SNat.add st.1 st.2
    let s1 ← SNat.add s one
    let mid ← half s1
    let ok ← feasibleAtLeast m n r c b i j mid
    if ok then pure (mid, st.2) else do
      let hi' ← SNat.sub mid one
      pure (st.1, hi')
  else pure st

/-- INTERNAL: `Program.cellMax` in terms of `tcMaxStep` (definitional). -/
theorem tc_cellMax_eq (m n : ℕ) (r c : List SNat) (b : List (List SNat)) (i j : ℕ) (lo : SNat) :
    cellMax m n r c b i j lo = (do
      let bij ← get2 b i j
      let k ← searchRounds bij
      let st ← Charged.repeatFor (tcMaxStep m n r c b i j) k (lo, bij)
      pure st.1) := rfl

/-- INTERNAL: one round of `cellMax`: the search interval stays in `[0, B]`, price `≤ F + 40 S`. -/
theorem tc_maxStep (S F m n : ℕ) (r c : List SNat) (b : List (List SNat)) (i j k B : ℕ)
    (st : SNat × SNat) (hij : i + j + 2 ≤ S) (hok : TcOK S r c b)
    (hF : ∀ r' c' b', TcOK S r' c' b' → Charged.steps rate (feasible m n r' c' b') ≤ F)
    (hB : bitLen B ≤ S) (h1 : st.1.get ≤ B) (h2 : st.2.get ≤ B) :
    (tcMaxStep m n r c b i j k st).val.1.get ≤ B ∧ (tcMaxStep m n r c b i j k st).val.2.get ≤ B ∧
      Charged.steps rate (tcMaxStep m n r c b i j k st) ≤ F + 40 * S := by
  have b1 : bitLen st.1.get ≤ S := (bitLen_mono h1).trans hB
  have b2 : bitLen st.2.get ≤ S := (bitLen_mono h2).trans hB
  have l2 : bitLen 2 = 3 := by decide
  have l1 : bitLen 1 = 2 := by decide
  unfold tcMaxStep
  simp only [Charged.steps_bind, costVb, steps_SNat_lt, SNat.val_lt]
  by_cases ho : st.1.get < st.2.get
  · have hs : bitLen (st.1.get + st.2.get) ≤ S + 1 := by
      have := bitLen_add_le st.1.get st.2.get; omega
    have hs1 : bitLen (st.1.get + st.2.get + 1) ≤ S + 2 := by
      have := bitLen_add_le (st.1.get + st.2.get) 1; omega
    have bm : bitLen ((st.1.get + st.2.get + 1) / 2) ≤ S :=
      (bitLen_mono (show (st.1.get + st.2.get + 1) / 2 ≤ B by omega)).trans hB
    have hfe := tc_feasibleAtLeast S F m n r c b i j
      ((half (((st.1.add st.2).val.add (SNat.lit 1).val).val)).val) hij hok hF
      (by simpa [half, costVb] using bm)
    simp only [ho, decide_true, ite_true, Charged.steps_bind, costVb, steps_SNat_add,
      steps_SNat_lit, SNat.get_add, SNat.get_lit, l1]
    simp only [half, Charged.steps_bind, costVb, steps_SNat_lit, steps_SNat_div, SNat.get_lit,
      SNat.get_add, l2] at hfe ⊢
    split
    · simp only [costVp, Charged.steps_pure, SNat.get_div, SNat.get_add, SNat.get_lit]
      refine ⟨by omega, h2, by omega⟩
    · simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SNat_sub,
        SNat.get_sub, SNat.get_lit, SNat.get_div, SNat.get_add, l1]
      have := bitLen_mono (show (st.1.get + st.2.get + 1) / 2 ≤ B by omega)
      refine ⟨h1, by omega, by omega⟩
  · simp only [ho, decide_false, Bool.false_eq_true, ite_false, costVp, Charged.steps_pure]
    exact ⟨h1, h2, by omega⟩

/-- INTERNAL: `cellMax` from `lo ≤ b_ij` returns a value in `[0, b_ij]` at price
`≤ 3 S + 1 + S (F + 40 S)`. -/
theorem tc_cellMax (S F m n : ℕ) (r c : List SNat) (b : List (List SNat)) (i j : ℕ) (lo : SNat)
    (hij : i + j + 2 ≤ S) (hok : TcOK S r c b)
    (hF : ∀ r' c' b', TcOK S r' c' b' → Charged.steps rate (feasible m n r' c' b') ≤ F)
    (hlo : lo.get ≤ (get2 b i j).val.get) :
    (cellMax m n r c b i j lo).val.get ≤ (get2 b i j).val.get ∧
      Charged.steps rate (cellMax m n r c b i j lo) ≤ 3 * S + 1 + S * (F + 40 * S) := by
  have hB : bitLen (get2 b i j).val.get ≤ S :=
    tc_get2_prop (P := fun x : SNat => bitLen x.get ≤ S) hok.2.2.2.2
      (by show bitLen (default : SNat).get ≤ S; rw [SNat.get_default, tc_bitLen_zero]; omega) i j
  rw [tc_cellMax_eq]
  obtain ⟨⟨h1, -⟩, h3⟩ := repeatFor_inv (tcMaxStep m n r c b i j)
    (fun _ (st : SNat × SNat) => st.1.get ≤ (get2 b i j).val.get ∧ st.2.get ≤ (get2 b i j).val.get)
    (F + 40 * S) (searchRounds (get2 b i j).val).val (lo, (get2 b i j).val)
    ⟨hlo, le_rfl⟩ (by
      rintro k st - ⟨h1, h2⟩
      obtain ⟨g1, g2, g3⟩ := tc_maxStep S F m n r c b i j k _ st hij hok hF hB h1 h2
      exact ⟨⟨g1, g2⟩, g3⟩)
  rw [tc_searchRounds_val] at h1 h3
  have hkk := Nat.mul_le_mul_right (F + 40 * S) hB
  have hbb := bitLen_le_succ (bitLen (get2 b i j).val.get)
  simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, fc_get2_steps,
    tc_searchRounds_steps, tc_searchRounds_val]
  refine ⟨h1, ?_⟩
  omega

/-- INTERNAL: the inner (cell) loop body of `Program.tighten`, verbatim. -/
def tcInner (m n : ℕ) (r c : List SNat) (b : List (List SNat)) (z : SNat) (i j : ℕ)
    (st : List SNat × List SNat × List Entry) : Prog (List SNat × List SNat × List Entry) := do
  let l ← cellMin m n r c b i j
  let u ← cellMax m n r c b i j l
  let w ← SNat.sub u l
  let lr ← Model.Operations.get st.1 i
  let lr' ← SNat.add lr l
  let lowR ← Model.Operations.set st.1 i lr'
  let lc ← Model.Operations.get st.2.1 j
  let lc' ← SNat.add lc l
  let lowC ← Model.Operations.set st.2.1 j lc'
  let keep ← SNat.lt z w
  if keep then do
    let cells ← Model.Operations.push st.2.2 (i, j, w)
    pure (lowR, lowC, cells)
  else pure (lowR, lowC, st.2.2)

/-- INTERNAL: `Program.tighten` in terms of `tcInner` (definitional). -/
theorem tc_tighten_eq (m n : ℕ) (r c : List SNat) (b : List (List SNat)) :
    tighten m n r c b = (do
      let z ← SNat.lit 0
      let lowR0 ← Model.Operations.replicate m z
      let lowC0 ← Model.Operations.replicate n z
      let st ← Charged.repeatFor (fun i st0 => Charged.repeatFor (tcInner m n r c b z i) n st0) m
        (lowR0, lowC0, [])
      let rows ← subLists r st.1 m
      let cols ← subLists c st.2.1 n
      pure (Tight.mk rows cols st.2.2)) := rfl

/-- INTERNAL: the state invariant of the cell loop after `t` cells: accumulated minima
below `2 ^ (S + t)`, at most `t` retained cells, each in range with bound of length `≤ S`. -/
def TcInv (S m n t : ℕ) (st : List SNat × List SNat × List Entry) : Prop :=
  (∀ x ∈ st.1, x.get < 2 ^ (S + t)) ∧ (∀ x ∈ st.2.1, x.get < 2 ^ (S + t)) ∧
    st.2.2.length ≤ t ∧ ∀ e ∈ st.2.2, e.1 < m ∧ e.2.1 < n ∧ bitLen e.2.2.get ≤ S

/-- INTERNAL: adding a value below `2 ^ S` to an entry below `2 ^ (S + t)` stays below
`2 ^ (S + t + 1)`. -/
theorem tc_acc_lt {S t x y : ℕ} (hx : x < 2 ^ (S + t)) (hy : y < 2 ^ S) : x + y < 2 ^ (S + (t + 1)) := by
  have h1 : 2 ^ S ≤ 2 ^ (S + t) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (S + (t + 1)) = 2 ^ (S + t) + 2 ^ (S + t) := by
    rw [← Nat.add_assoc, pow_succ]; ring
  omega

/-- INTERNAL: one cell of `tighten`: the invariant advances from `t` to `t + 1`, price
`≤ S (F + 16 S) + S (F + 40 S) + 20 S + 3 t + 10`. -/
theorem tc_inner (S F m n t : ℕ) (r c : List SNat) (b : List (List SNat)) (z : SNat) (i j : ℕ)
    (st : List SNat × List SNat × List Entry) (hS : 2 ≤ S) (hmn : m + n + 2 ≤ S)
    (hi : i < m) (hj : j < n) (hz : z.get = 0) (hok : TcOK S r c b)
    (hF : ∀ r' c' b', TcOK S r' c' b' → Charged.steps rate (feasible m n r' c' b') ≤ F)
    (hI : TcInv S m n t st) :
    TcInv S m n (t + 1) (tcInner m n r c b z i j st).val ∧
      Charged.steps rate (tcInner m n r c b z i j st) ≤
        S * (F + 16 * S) + S * (F + 40 * S) + 20 * S + 3 * t + 10 := by
  obtain ⟨hR, hC, hL, hE⟩ := hI
  have hij : i + j + 2 ≤ S := by omega
  have hB : bitLen (get2 b i j).val.get ≤ S :=
    tc_get2_prop (P := fun x : SNat => bitLen x.get ≤ S) hok.2.2.2.2
      (by show bitLen (default : SNat).get ≤ S; rw [SNat.get_default, tc_bitLen_zero]; omega) i j
  have hB2 : (get2 b i j).val.get < 2 ^ S :=
    (lt_two_pow_bitLen _).trans_le (Nat.pow_le_pow_right (by norm_num) hB)
  obtain ⟨l1, l2⟩ := tc_cellMin S F m n r c b i j hij hok hF
  obtain ⟨u1, u2⟩ := tc_cellMax S F m n r c b i j _ hij hok hF l1
  have bl : bitLen (cellMin m n r c b i j).val.get ≤ S := (bitLen_mono l1).trans hB
  have bu : bitLen (cellMax m n r c b i j (cellMin m n r c b i j).val).val.get ≤ S :=
    (bitLen_mono u1).trans hB
  have bw : bitLen ((cellMax m n r c b i j (cellMin m n r c b i j).val).val.get -
      (cellMin m n r c b i j).val.get) ≤ S :=
    (bitLen_mono (Nat.sub_le _ _)).trans bu
  have hlr : (st.1.getD i default).get < 2 ^ (S + t) :=
    getD_prop (P := fun x : SNat => x.get < 2 ^ (S + t)) _ _ _ hR (by simp)
  have hlc : (st.2.1.getD j default).get < 2 ^ (S + t) :=
    getD_prop (P := fun x : SNat => x.get < 2 ^ (S + t)) _ _ _ hC (by simp)
  have blr := bitLen_le_of_lt_two_pow hlr
  have blc := bitLen_le_of_lt_two_pow hlc
  have hmono : S * (F + 16 * S) ≤ S * (F + 40 * S) := Nat.mul_le_mul_left S (by omega)
  have hRt : ∀ x ∈ st.1, x.get < 2 ^ (S + (t + 1)) := fun x hx =>
    (hR x hx).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hCt : ∀ x ∈ st.2.1, x.get < 2 ^ (S + (t + 1)) := fun x hx =>
    (hC x hx).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  unfold tcInner
  simp only [Charged.steps_bind, costVb, steps_SNat_sub, steps_get, val_get, steps_SNat_add,
    steps_set, val_set, steps_SNat_lt, SNat.val_lt, SNat.get_sub, hz, tc_bitLen_zero]
  have hR' := set_prop (P := fun x : SNat => x.get < 2 ^ (S + (t + 1))) _ i _ hRt
    (by rw [SNat.get_add]; exact tc_acc_lt hlr (l1.trans_lt hB2))
  have hC' := set_prop (P := fun x : SNat => x.get < 2 ^ (S + (t + 1))) _ j _ hCt
    (by rw [SNat.get_add]; exact tc_acc_lt hlc (l1.trans_lt hB2))
  split
  · simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_push, val_push]
    refine ⟨⟨hR', hC', by simp; omega, ?_⟩, by omega⟩
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact hE e he
    · simp only [List.mem_singleton] at he
      subst he
      exact ⟨hi, hj, by simpa using bw⟩
  · simp only [costVp, Charged.steps_pure]
    exact ⟨⟨hR', hC', show st.2.2.length ≤ t + 1 by omega, hE⟩, by omega⟩

/-- INTERNAL: `subLists a d k` with entries of `a` of length `≤ S` and of `d` of length `≤ E`:
entries of length `≤ S` (truncated subtraction), price `≤ k (3k + S + E + 3)`. -/
theorem tc_subLists (S E k : ℕ) (a d : List SNat) (hS : 1 ≤ S) (hE : 1 ≤ E)
    (ha : ∀ x ∈ a, bitLen x.get ≤ S) (hd : ∀ x ∈ d, bitLen x.get ≤ E) :
    (∀ x ∈ (subLists a d k).val, bitLen x.get ≤ S) ∧
      Charged.steps rate (subLists a d k) ≤ k * (3 * k + S + E + 3) := by
  unfold subLists
  obtain ⟨⟨-, h2⟩, h3⟩ := repeatFor_inv (fun i (acc : List SNat) => (do
      let x ← Model.Operations.get a i
      let y ← Model.Operations.get d i
      let e ← SNat.sub x y
      Model.Operations.push acc e : Prog (List SNat)))
    (fun i (acc : List SNat) => acc.length = i ∧ ∀ x ∈ acc, bitLen x.get ≤ S)
    (3 * k + S + E + 3) k [] ⟨rfl, by simp⟩ (by
      rintro i acc hi ⟨h1, h2⟩
      have hx := tc_getD_len hS ha i
      have hy := tc_getD_len hE hd i
      simp only [Charged.steps_bind, costVb, steps_get, val_get, steps_SNat_sub, steps_push,
        val_push]
      refine ⟨⟨by simp [h1], ?_⟩, by omega⟩
      intro x hx'
      rcases List.mem_append.1 hx' with h | h
      · exact h2 x h
      · simp only [List.mem_singleton] at h
        subst h
        rw [SNat.get_sub]
        exact (bitLen_mono (Nat.sub_le _ _)).trans hx)
  exact ⟨h2, h3⟩

/-- INTERNAL: the arithmetic closing `tighten_cost`. -/
theorem tc_final_arith (S F m n : ℕ) (hS : 2 ≤ S) (hmn : m + n + 2 ≤ S) (hF : 1 ≤ F) :
    1 + (m + 1) + (n + 1) +
      m * (n * (S * (F + 16 * S) + S * (F + 40 * S) + 20 * S + 3 * (m * n) + 10)) +
      m * (3 * m + S + (S + m * n + 1) + 3) + n * (3 * n + S + (S + m * n + 1) + 3) ≤
      S ^ 16 * F := by
  have hm : m ≤ S := by omega
  have hn : n ≤ S := by omega
  calc 1 + (m + 1) + (n + 1) +
      m * (n * (S * (F + 16 * S) + S * (F + 40 * S) + 20 * S + 3 * (m * n) + 10)) +
      m * (3 * m + S + (S + m * n + 1) + 3) + n * (3 * n + S + (S + m * n + 1) + 3)
      ≤ 1 + (S + 1) + (S + 1) +
      S * (S * (S * (F + 16 * S) + S * (F + 40 * S) + 20 * S + 3 * (S * S) + 10)) +
      S * (3 * S + S + (S + S * S + 1) + 3) + S * (3 * S + S + (S + S * S + 1) + 3) := by
        gcongr
    _ ≤ 128 * (S ^ 4 * F) := by
        have a1 : S ≤ S ^ 4 * F := by
          have : S ≤ S ^ 4 := by
            calc S = S ^ 1 := (pow_one S).symm
              _ ≤ S ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
          nlinarith
        have a2 : S ^ 2 ≤ S ^ 4 * F := by
          have : S ^ 2 ≤ S ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
          nlinarith
        have a3 : S ^ 3 ≤ S ^ 4 * F := by
          have : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
          nlinarith
        have a4 : S ^ 4 ≤ S ^ 4 * F := Nat.le_mul_of_pos_right _ hF
        have a5 : S ^ 3 * F ≤ S ^ 4 * F := Nat.mul_le_mul_right F (Nat.pow_le_pow_right (by omega) (by norm_num))
        have a6 : 1 ≤ S ^ 4 * F := Nat.one_le_iff_ne_zero.mpr (by positivity)
        ring_nf
        nlinarith
    _ ≤ S ^ 7 * (S ^ 4 * F) := Nat.mul_le_mul_right _
        ((show 128 = 2 ^ 7 by norm_num) ▸ Nat.pow_le_pow_left hS 7)
    _ ≤ S ^ 16 * F := by
        rw [← mul_assoc, ← pow_add]
        exact Nat.mul_le_mul_right F (Nat.pow_le_pow_right (by omega) (by norm_num))

/-- INTERNAL: the double cell loop of `tighten` keeps `TcInv` up to `t = m n`, price
`≤ m (n X)` with `X` the per-cell price at `t ≤ m n`. -/
theorem tc_loop (S F m n : ℕ) (r c : List SNat) (b : List (List SNat)) (z : SNat)
    (hS : 2 ≤ S) (hmn : m + n + 2 ≤ S) (hz : z.get = 0) (hok : TcOK S r c b)
    (hF : ∀ r' c' b', TcOK S r' c' b' → Charged.steps rate (feasible m n r' c' b') ≤ F) :
    TcInv S m n (m * n) (Charged.repeatFor (fun i st0 =>
      Charged.repeatFor (tcInner m n r c b z i) n st0) m
        (List.replicate m z, List.replicate n z, [])).val ∧
    Charged.steps rate (Charged.repeatFor (fun i st0 =>
      Charged.repeatFor (tcInner m n r c b z i) n st0) m
        (List.replicate m z, List.replicate n z, [])) ≤
      m * (n * (S * (F + 16 * S) + S * (F + 40 * S) + 20 * S + 3 * (m * n) + 10)) := by
  have h0 : TcInv S m n 0 (List.replicate m z, List.replicate n z, []) := by
    refine ⟨?_, ?_, by simp, by simp⟩ <;>
    · intro x hx
      rw [List.eq_of_mem_replicate hx, hz]
      positivity
  obtain ⟨h1, h2⟩ := repeatFor_inv (fun i st0 => Charged.repeatFor (tcInner m n r c b z i) n st0)
    (fun i st => TcInv S m n (i * n) st)
    (n * (S * (F + 16 * S) + S * (F + 40 * S) + 20 * S + 3 * (m * n) + 10)) m _
    (by simpa using h0) (by
      rintro i st hi hI
      obtain ⟨t1, t2⟩ := repeatFor_inv (tcInner m n r c b z i) (fun j st => TcInv S m n (i * n + j) st)
        (S * (F + 16 * S) + S * (F + 40 * S) + 20 * S + 3 * (m * n) + 10) n st
        (by simpa using hI) (by
          rintro j st' hj hI'
          have hlt : i * n + j < m * n := by
            have := Nat.mul_le_mul_right n (show i + 1 ≤ m by omega)
            rw [Nat.succ_mul] at this; omega
          obtain ⟨g1, g2⟩ := tc_inner S F m n (i * n + j) r c b z i j st' hS hmn hi hj hz hok hF hI'
          exact ⟨g1, by omega⟩)
      refine ⟨?_, t2⟩
      rw [Nat.succ_mul]
      exact t1)
  exact ⟨h1, h2⟩

/-- INTERNAL: tightening costs a fixed power of a size bound `S`, and its output is
bounded by the same `S`.
TEXLINE: sections/scales.tex:24-44 -/
theorem tighten_cost : ∃ k : ℕ, ∀ (S m n : ℕ) (r c : List SNat) (b : List (List SNat)),
    2 ≤ S → m + n + 2 ≤ S → r.length ≤ S → c.length ≤ S →
    (∀ x ∈ r, bitLen x.get ≤ S) → (∀ x ∈ c, bitLen x.get ≤ S) →
    (∀ row ∈ b, ∀ x ∈ row, bitLen x.get ≤ S) →
    Charged.steps rate (tighten m n r c b) ≤ S ^ k ∧
    (∀ x ∈ (tighten m n r c b).val.rows, bitLen x.get ≤ S) ∧
    (∀ x ∈ (tighten m n r c b).val.cols, bitLen x.get ≤ S) ∧
    (tighten m n r c b).val.cells.length ≤ m * n ∧
    (∀ e ∈ (tighten m n r c b).val.cells, e.1 < m ∧ e.2.1 < n ∧ bitLen e.2.2.get ≤ S) := by
  obtain ⟨kF, hF⟩ := feasible_cost
  refine ⟨16 + kF, ?_⟩
  intro S m n r c b hS hmn hrl hcl hrb hcb hbb
  have hok : TcOK S r c b := ⟨hrl, hcl, hrb, hcb, hbb⟩
  have hF' : ∀ r' c' b', TcOK S r' c' b' → Charged.steps rate (feasible m n r' c' b') ≤ S ^ kF :=
    fun r' c' b' h => hF S m n r' c' b' hS hmn h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  obtain ⟨⟨hR, hC, hL, hE⟩, hst⟩ :=
    tc_loop S (S ^ kF) m n r c b (SNat.lit 0).val hS hmn (SNat.get_lit 0) hok hF'
  have hlen : ∀ l : List SNat, (∀ x ∈ l, x.get < 2 ^ (S + m * n)) →
      ∀ x ∈ l, bitLen x.get ≤ S + m * n + 1 := fun l h x hx => bitLen_le_of_lt_two_pow (h x hx)
  obtain ⟨r1, r2⟩ := tc_subLists S (S + m * n + 1) m r _ (by omega) (by omega) hrb (hlen _ hR)
  obtain ⟨c1, c2⟩ := tc_subLists S (S + m * n + 1) n c _ (by omega) (by omega) hcb (hlen _ hC)
  have ar := tc_final_arith S (S ^ kF) m n hS hmn (Nat.one_le_pow _ _ (by omega))
  rw [tc_tighten_eq]
  simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SNat_lit,
    tc_bitLen_zero, steps_replicate, val_replicate]
  refine ⟨?_, r1, c1, hL, hE⟩
  rw [pow_add]
  omega


end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `tighten_cost` with `k = 16 + k_feasible`, via `tc_cellMin`, `tc_cellMax`,
  `tc_inner`, `tc_loop`, `tc_subLists`
-/
