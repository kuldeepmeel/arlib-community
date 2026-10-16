import Cellcounting.Analysis.CostScale
import Cellcounting.Analysis.CostLadder
import Cellcounting.Analysis.TightenCost
import Cellcounting.Analysis.BuildCtxCost

/-!
# The preprocessing S0–S4 runs in polynomial bit cost

`Cellcounting.Analysis.prep_cost`: reading the input, the feasibility test
(Edmonds–Karp with at most `V³` augmentations), tightening by binary search, the
parameters of `eq:parameters`, and the forest construction cost at most a fixed
power of `costScale I ε δ`; the context they produce has sizes bounded by the
same power (`CtxSize`, `PmSize`), and so does `p`.

This is a statement about sizes only.  It does not need the feasibility test to
be correct: every residual capacity grows by at most a factor `V + 1` per
augmentation, so `V³` augmentations keep binary lengths polynomial; tightened
bounds and margins never exceed the input ones; small bounds are `< W`.

Proved here so far: `readList_cost`.  The route for `prep_cost`: `readMatrix` as
`readList`; `feasible` via `network` and `maxFlow` (use `repeatWhile_inv` with the
invariant "every residual entry has length `≤ ℓ₀ + t·(bitLen V + 1)` after `t`
augmentations" — `bottleneck` is a minimum of path entries and `pushFlow` touches at
most `V` entries per augmentation); `tighten` (`m n` cells × `bitLen b_ij` rounds × one
`feasible`/`feasibleAtLeast`, search values stay in `[0, b_ij]`); `params` (values from
`eq:parameters`, using `ε⁻¹ ≤ ⌈ε⁻¹⌉ ≤ costScale` and `d ≤ 3L + 2`); `buildCtx`
(`splitCells`, insertion sort, Kruskal, `rootsOf`, `orient`, `M_f`); and the sum `p`.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Program
open Cellcounting.Model.Operations
open Cellcounting.Interface

/-- INTERNAL: reading a list of input naturals (S0) costs at most
`|l| (B + |l| + 1)` when every entry has length at most `B`, and returns `|l|` sealed
numbers of length at most `B`. -/
theorem readList_cost (B : ℕ) (l : List ℕ) (hl : ∀ k ∈ l, bitLen k ≤ B) :
    (readList l).val.length = l.length ∧ (∀ x ∈ (readList l).val, bitLen x.get ≤ B) ∧
    Charged.steps rate (readList l) ≤ l.length * (B + l.length + 1) := by
  unfold readList
  obtain ⟨⟨h1, h2⟩, h3⟩ := foldl_inv (fun (acc : List SNat) (k : ℕ) => (do
      let x ← SNat.lit k
      Model.Operations.push acc x : Prog (List SNat)))
    (fun i (acc : List SNat) => acc.length = i ∧ ∀ x ∈ acc, bitLen x.get ≤ B)
    (B + l.length + 1) l 0 [] (by simp)
    (by
      rintro i acc a - hi ha ⟨hlen, hall⟩
      simp only [Charged.steps_bind, costVb, steps_SNat_lit, steps_push, val_push]
      refine ⟨⟨by simp [hlen], ?_⟩, ?_⟩
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hall x hx
        · simpa using hl a ha
      · have := hl a ha; omega)
  exact ⟨by simpa using h1, h2, h3⟩

/-- INTERNAL: reading a matrix of input naturals (S0) costs at most
`|rows| (W (B + W + 1) + |rows| + 1)` when every row has length at most `W` and every
entry length at most `B`, and returns rows of sealed numbers of length at most `B`. -/
theorem readMatrix_cost (B W : ℕ) (rows : List (List ℕ))
    (hb : ∀ row ∈ rows, ∀ k ∈ row, bitLen k ≤ B) (hw : ∀ row ∈ rows, row.length ≤ W) :
    (∀ row ∈ (readMatrix rows).val, ∀ x ∈ row, bitLen x.get ≤ B) ∧
    Charged.steps rate (readMatrix rows) ≤
      rows.length * (W * (B + W + 1) + rows.length + 1) := by
  unfold readMatrix
  obtain ⟨⟨-, h2⟩, h3⟩ := foldl_inv (fun (acc : List (List SNat)) (row : List ℕ) => (do
      let xs ← readList row
      Model.Operations.push acc xs : Prog (List (List SNat))))
    (fun i (acc : List (List SNat)) => acc.length = i ∧ ∀ r ∈ acc, ∀ x ∈ r, bitLen x.get ≤ B)
    (W * (B + W + 1) + rows.length + 1) rows 0 [] (by simp)
    (by
      rintro i acc row - hi hrow ⟨hlen, hall⟩
      obtain ⟨-, hr2, hr3⟩ := readList_cost B row (hb row hrow)
      simp only [Charged.steps_bind, costVb, steps_push, val_push]
      refine ⟨⟨by simp [hlen], ?_⟩, ?_⟩
      · intro r hr x hx
        simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact hall r hr x hx
        · exact hr2 x hx
      · have h1 := hw row hrow
        have h2 : row.length * (B + row.length + 1) ≤ W * (B + W + 1) :=
          Nat.mul_le_mul h1 (by omega)
        omega)
  exact ⟨h2, h3⟩

/-- INTERNAL: the value of `Program.clog2`. -/
theorem prep_clog2_get (x : SNat) : (clog2 x).val.get = Nat.size (x.get - 1) := by
  unfold clog2; simp only [costVb, SNat.get_size, SNat.get_sub, SNat.get_lit]

/-- INTERNAL: the price of `Program.clog2`. -/
theorem prep_clog2_steps (x : SNat) :
    Charged.steps rate (clog2 x) = bitLen 1 + (bitLen x.get + bitLen 1) + bitLen (x.get - 1) := by
  unfold clog2
  simp only [Charged.steps_bind, steps_SNat_lit, steps_SNat_sub, steps_SNat_size,
    SNat.get_sub, SNat.get_lit]
  omega

/-- INTERNAL: S3, the parameters of `eq:parameters`, cost at most `S ^ 266` and are at
most `S ^ 266`, for any `S ≥ 2` bounding `m + n + 2`, `L`, `ε⁻¹` and the length of `ε`;
`B, H ≥ 1`.  Values: `d ≤ S⁵, K ≤ S¹³, A ≤ S⁴³, B ≤ S⁵⁷, W ≤ S⁶⁹, H ≤ S¹²⁷`.
TEXLINE: sections/scales.tex:46-77 -/
theorem params_cost (S m n : ℕ) (L : SNat) (ε : SRat) (hS : 2 ≤ S) (hmn : m + n + 2 ≤ S) (hL : L.get ≤ S)
    (hε : 0 < ε.get) (hεS : ε.get⁻¹ ≤ S) (hεl : ratLen ε.get ≤ S) :
    Charged.steps rate (params m n L ε) ≤ S ^ 266 ∧ PmSize (S ^ 266) (params m n L ε).val ∧
      1 ≤ (params m n L ε).val.B.get ∧ 1 ≤ (params m n L ε).val.H.get := by
  unfold params
  simp only [Charged.steps_bind, costVb, costVp]
  generalize hmS : (SNat.lit m).val = mS
  generalize hnS : (SNat.lit n).val = nS
  generalize hmn' : (mS.mul nS).val = mn
  generalize ht1 : (mn.add mS).val = t1
  generalize ht2 : (t1.add nS).val = t2
  generalize htwo : (SNat.lit 2).val = two
  generalize hd : (t2.add two).val = d
  generalize hoQ : (SRat.lit 1).val = oQ
  generalize hinv : (oQ.div ε).val = inv
  generalize hce : inv.natCeil.val = ce
  generalize hlg : (clog2 ce).val = lg
  generalize hone : (SNat.lit 1).val = one
  generalize hs1 : (L.add d).val = s1
  generalize hs2 : (s1.add lg).val = s2
  generalize hs3 : (s2.add one).val = s3
  generalize hc20 : (SNat.lit 20).val = c20
  generalize hK : (c20.mul s3).val = K
  generalize hc512 : (SNat.lit 512).val = c512
  generalize hdK : (d.mul K).val = dK
  generalize hden : (c512.mul dK).val = den
  generalize hdenQ : den.toRat.val = denQ
  generalize hγ : (ε.div denQ).val = γ
  generalize hc4 : (SNat.lit 4).val = c4
  generalize hfK : (c4.mul K).val = fK
  generalize hfKq : fK.toRat.val = fKq
  generalize hq : (fKq.div γ).val = q
  generalize hA : q.natCeil.val = A
  generalize hd2 : (d.mul d).val = d2
  generalize hc16 : (SNat.lit 16).val = c16
  generalize ha16 : (c16.mul A).val = a16
  generalize hB : (a16.mul d2).val = B
  generalize hc100 : (SNat.lit 100).val = c100
  generalize hd100 : (c100.mul d).val = d100
  generalize hW : (d100.mul B).val = W
  generalize hc10 : (SNat.lit 10).val = c10
  generalize ha10 : (c10.mul A).val = a10
  generalize had2 : (a10.mul d2).val = ad2
  generalize hW1 : (W.add one).val = W1
  generalize hH : (ad2.mul W1).val = H
  -- values
  have hm : m ≤ S ^ 1 := by rw [pow_one]; omega
  have hn : n ≤ S ^ 1 := by rw [pow_one]; omega
  have gm : mS.get = m := by rw [← hmS]; simp
  have gn : nS.get = n := by rw [← hnS]; simp
  have vmn : mn.get ≤ S ^ 2 := by rw [← hmn']; simp only [SNat.get_mul, gm, gn]; exact pw_mul hm hn
  have vt1 : t1.get ≤ S ^ 3 := by
    rw [← ht1]; simp only [SNat.get_add, gm]; exact pw_add hS vmn (pw_mono hS hm (by norm_num))
  have vt2 : t2.get ≤ S ^ 4 := by
    rw [← ht2]; simp only [SNat.get_add, gn]; exact pw_add hS vt1 (pw_mono hS hn (by norm_num))
  have gtwo : two.get = 2 := by rw [← htwo]; simp
  have vtwo : two.get ≤ S ^ 4 := by rw [gtwo]; exact pw_const hS (by norm_num)
  have vd : d.get ≤ S ^ 5 := by rw [← hd]; simp only [SNat.get_add]; exact pw_add hS vt2 vtwo
  have hd2le : 2 ≤ d.get := by rw [← hd]; simp only [SNat.get_add, gtwo]; omega
  have goQ : oQ.get = 1 := by rw [← hoQ]; simp
  have ginv : inv.get = ε.get⁻¹ := by rw [← hinv]; simp [goQ]
  have vce : ce.get ≤ S ^ 1 := by
    rw [← hce, pow_one]; simp only [SRat.get_natCeil, ginv]; exact Nat.ceil_le.2 hεS
  have vlg : lg.get ≤ S ^ 1 := by
    rw [← hlg, prep_clog2_get]
    exact (Nat.size_le.2 Nat.lt_two_pow_self).trans ((Nat.sub_le _ _).trans vce)
  have gone : one.get = 1 := by rw [← hone]; simp
  have vone : ∀ j, one.get ≤ S ^ j := fun j => gone ▸ pw_one hS
  have vs1 : s1.get ≤ S ^ 6 := by
    rw [← hs1]; simp only [SNat.get_add]; exact pw_add hS (pw_mono hS (hL.trans_eq (pow_one S).symm) (by norm_num)) vd
  have vs2 : s2.get ≤ S ^ 7 := by
    rw [← hs2]; simp only [SNat.get_add]; exact pw_add hS vs1 (pw_mono hS vlg (by norm_num))
  have vs3 : s3.get ≤ S ^ 8 := by
    rw [← hs3]; simp only [SNat.get_add]; exact pw_add hS vs2 (vone 7)
  have gc20 : c20.get = 20 := by rw [← hc20]; simp
  have vK : K.get ≤ S ^ 13 := by
    rw [← hK]; simp only [SNat.get_mul]
    exact pw_mul (j := 8) (gc20 ▸ pw_const hS (by norm_num)) vs3
  have hKpos : 0 < K.get := by
    rw [← hK, ← hs3]; simp only [SNat.get_mul, SNat.get_add, gc20, gone]; positivity
  have gc512 : c512.get = 512 := by rw [← hc512]; simp
  have vdK : dK.get ≤ S ^ 18 := by rw [← hdK]; simp only [SNat.get_mul]; exact pw_mul vd vK
  have vden : den.get ≤ S ^ 27 := by
    rw [← hden]; simp only [SNat.get_mul]
    exact pw_mul (gc512 ▸ pw_const hS (by norm_num)) vdK
  have hdenpos : 0 < den.get := by
    rw [← hden, ← hdK]; simp only [SNat.get_mul, gc512]; positivity
  have gdenQ : denQ.get = (den.get : ℚ) := by rw [← hdenQ]; simp
  have gγ : γ.get = ε.get / den.get := by rw [← hγ]; simp [gdenQ]
  have gc4 : c4.get = 4 := by rw [← hc4]; simp
  have vfK : fK.get ≤ S ^ 15 := by
    rw [← hfK]; simp only [SNat.get_mul]
    exact pw_mul (gc4 ▸ pw_const hS (by norm_num)) vK
  have gfKq : fKq.get = (fK.get : ℚ) := by rw [← hfKq]; simp
  have gq : q.get = fK.get * den.get * ε.get⁻¹ := by
    rw [← hq]; simp only [SRat.get_div, gfKq, gγ]; field_simp
  have hqpos : 0 < q.get := by
    rw [gq]
    have : 0 < fK.get := by rw [← hfK]; simp only [SNat.get_mul, gc4]; positivity
    positivity
  have vA : A.get ≤ S ^ 43 := by
    rw [← hA]; simp only [SRat.get_natCeil]
    apply Nat.ceil_le.2
    have h1 : (fK.get * den.get : ℕ) ≤ S ^ 42 := pw_mul vfK vden
    rw [gq]
    calc (fK.get : ℚ) * den.get * ε.get⁻¹ ≤ (fK.get * den.get : ℕ) * (S : ℚ) := by
          push_cast; exact mul_le_mul_of_nonneg_left hεS (by positivity)
      _ ≤ ((S ^ 42 * S : ℕ) : ℚ) := by push_cast; gcongr; exact_mod_cast h1
      _ = ((S ^ 43 : ℕ) : ℚ) := by rw [← pow_succ]
  have hApos : 1 ≤ A.get := by
    rw [← hA]; simp only [SRat.get_natCeil]; exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hqpos).ne'
  have vd2 : d2.get ≤ S ^ 10 := by rw [← hd2]; simp only [SNat.get_mul]; exact pw_mul vd vd
  have gc16 : c16.get = 16 := by rw [← hc16]; simp
  have va16 : a16.get ≤ S ^ 47 := by
    rw [← ha16]; simp only [SNat.get_mul]; exact pw_mul (gc16 ▸ pw_const hS (by norm_num)) vA
  have vB : B.get ≤ S ^ 57 := by rw [← hB]; simp only [SNat.get_mul]; exact pw_mul va16 vd2
  have hBpos : 1 ≤ B.get := by
    rw [← hB, ← ha16, ← hd2]; simp only [SNat.get_mul, gc16]
    have := Nat.mul_le_mul (Nat.mul_le_mul (le_refl 16) hApos) (Nat.mul_le_mul hd2le hd2le)
    omega
  have gc100 : c100.get = 100 := by rw [← hc100]; simp
  have vd100 : d100.get ≤ S ^ 12 := by
    rw [← hd100]; simp only [SNat.get_mul]; exact pw_mul (gc100 ▸ pw_const hS (by norm_num)) vd
  have vW : W.get ≤ S ^ 69 := by rw [← hW]; simp only [SNat.get_mul]; exact pw_mul vd100 vB
  have gc10 : c10.get = 10 := by rw [← hc10]; simp
  have va10 : a10.get ≤ S ^ 47 := by
    rw [← ha10]; simp only [SNat.get_mul]; exact pw_mul (gc10 ▸ pw_const hS (by norm_num)) vA
  have vad2 : ad2.get ≤ S ^ 57 := by rw [← had2]; simp only [SNat.get_mul]; exact pw_mul va10 vd2
  have vW1 : W1.get ≤ S ^ 70 := by
    rw [← hW1]; simp only [SNat.get_add]; exact pw_add hS vW (vone 69)
  have vH : H.get ≤ S ^ 127 := by rw [← hH]; simp only [SNat.get_mul]; exact pw_mul vad2 vW1
  have hHpos : 1 ≤ H.get := by
    rw [← hH, ← had2, ← ha10, ← hd2, ← hW1]; simp only [SNat.get_mul, SNat.get_add, gc10, gone]
    have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (le_refl 10) hApos)
      (Nat.mul_le_mul hd2le hd2le)) (Nat.le_add_left 1 W.get)
    omega
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hBpos, hHpos⟩
  rotate_left
  · exact pw_mono hS vd (by norm_num)
  · exact pw_mono hS vK (by norm_num)
  · exact pw_mono hS vA (by norm_num)
  · exact pw_mono hS vB (by norm_num)
  · exact pw_mono hS vW (by norm_num)
  · exact pw_mono hS vH (by norm_num)
  -- costs: every value is at most `X = S ^ 127`, every rational length at most `S ^ 31`
  have X : ∀ {a : ℕ} {i : ℕ}, a ≤ S ^ i → i ≤ 127 → bitLen a ≤ S ^ 128 := fun ha hi =>
    pw_bitLen hS (pw_mono hS ha hi)
  have cA : ∀ {a b i j : ℕ}, a ≤ S ^ i → b ≤ S ^ j → i ≤ 127 → j ≤ 127 →
      bitLen a + bitLen b ≤ S ^ 256 := fun ha hb hi hj =>
    pw_mono hS (pw_add hS (X ha hi) (X hb hj)) (by norm_num)
  have cM : ∀ {a b i j : ℕ}, a ≤ S ^ i → b ≤ S ^ j → i ≤ 127 → j ≤ 127 →
      bitLen a * bitLen b ≤ S ^ 256 := fun ha hb hi hj => pw_mul (X ha hi) (X hb hj)
  have cL : ∀ {a i : ℕ}, a ≤ S ^ i → i ≤ 127 → bitLen a ≤ S ^ 256 := fun ha hi =>
    pw_mono hS (X ha hi) (by norm_num)
  have cQ : ∀ {a b : ℚ}, ratLen a ≤ S ^ 31 → ratLen b ≤ S ^ 31 →
      (ratLen a + 1) * (ratLen b + 1) ≤ S ^ 256 := fun ha hb =>
    pw_mono hS (pw_mul (pw_add hS ha (pw_one hS)) (pw_add hS hb (pw_one hS))) (by norm_num)
  have hS1 : S ≤ S ^ 1 := (pow_one S).ge
  have rε : ratLen ε.get ≤ S ^ 31 := pw_mono hS (hεl.trans hS1) (by norm_num)
  have r1 : ratLen (1 : ℚ) ≤ S ^ 2 := by
    have h := ratLen_natCast 1; have h' := bitLen_le_succ 1; push_cast at h
    exact pw_const hS (by norm_num; omega)
  have roQ : ratLen oQ.get ≤ S ^ 31 := by rw [goQ]; exact pw_mono hS r1 (by norm_num)
  have rinv : ratLen inv.get ≤ S ^ 31 := by
    rw [ginv, inv_eq_one_div]
    exact pw_mono hS ((ratLen_div_le 1 ε.get).trans
      (pw_add hS r1 (pw_mono hS (hεl.trans hS1) (by norm_num)))) (by norm_num)
  have rdenQ : ratLen denQ.get ≤ S ^ 29 := by
    rw [gdenQ, ratLen_natCast]
    exact (pw_add hS (pw_bitLen hS vden) (pw_const hS (by norm_num : 2 ≤ 2 ^ 28)))
  have rγ : ratLen γ.get ≤ S ^ 30 := by
    rw [← hγ, SRat.get_div]
    exact (ratLen_div_le _ _).trans (pw_add hS (pw_mono hS (hεl.trans hS1) (by norm_num)) rdenQ)
  have rfKq : ratLen fKq.get ≤ S ^ 30 := by
    rw [gfKq, ratLen_natCast]
    exact pw_mono hS (pw_add hS (pw_bitLen hS vfK) (pw_const hS (by norm_num : 2 ≤ 2 ^ 16)))
      (by norm_num)
  have rq : ratLen q.get ≤ S ^ 31 := by
    rw [← hq, SRat.get_div]; exact (ratLen_div_le _ _).trans (pw_add hS rfKq rγ)
  have k1 : Charged.steps rate (SNat.lit m) ≤ S ^ 256 := by rw [steps_SNat_lit]; exact cL hm (by norm_num)
  have k2 : Charged.steps rate (SNat.lit n) ≤ S ^ 256 := by rw [steps_SNat_lit]; exact cL hn (by norm_num)
  have k3 : Charged.steps rate (mS.mul nS) ≤ S ^ 256 := by
    rw [steps_SNat_mul, gm, gn]; exact cM hm hn (by norm_num) (by norm_num)
  have k4 : Charged.steps rate (mn.add mS) ≤ S ^ 256 := by
    rw [steps_SNat_add, gm]; exact cA vmn hm (by norm_num) (by norm_num)
  have k5 : Charged.steps rate (t1.add nS) ≤ S ^ 256 := by
    rw [steps_SNat_add, gn]; exact cA vt1 hn (by norm_num) (by norm_num)
  have k6 : Charged.steps rate (SNat.lit 2) ≤ S ^ 256 := by
    rw [steps_SNat_lit]; exact cL (gtwo ▸ vtwo) (by norm_num)
  have k7 : Charged.steps rate (t2.add two) ≤ S ^ 256 := by
    rw [steps_SNat_add]; exact cA vt2 vtwo (by norm_num) (by norm_num)
  have k8 : Charged.steps rate (SRat.lit 1) ≤ S ^ 256 := by
    rw [steps_SRat_lit]; exact pw_mono hS r1 (by norm_num)
  have k9 : Charged.steps rate (oQ.div ε) ≤ S ^ 256 := by rw [steps_SRat_div]; exact cQ roQ rε
  have k10 : Charged.steps rate inv.natCeil ≤ S ^ 256 := by rw [steps_SRat_natCeil]; exact cQ rinv rinv
  have k11 : Charged.steps rate (clog2 ce) ≤ S ^ 256 := by
    rw [prep_clog2_steps]
    have h4 : bitLen 1 ≤ S ^ 2 := pw_mono hS (pw_const hS (by decide : bitLen 1 ≤ 2 ^ 1)) (by norm_num)
    have h5 : bitLen ce.get ≤ S ^ 2 := pw_bitLen hS vce
    have h6 : bitLen (ce.get - 1) ≤ S ^ 2 := pw_bitLen hS ((Nat.sub_le ce.get 1).trans vce)
    have h7 : 4 * S ^ 2 ≤ S ^ 256 := by
      rw [show 256 = 2 + 254 by rfl, pow_add, Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (pw_const hS (by norm_num))
    omega
  have k12 : Charged.steps rate (SNat.lit 1) ≤ S ^ 256 := by
    rw [steps_SNat_lit]; exact cL (pw_one hS (j := 0)) (by norm_num)
  have hL1 : L.get ≤ S ^ 1 := hL.trans hS1
  have k13 : Charged.steps rate (L.add d) ≤ S ^ 256 := by
    rw [steps_SNat_add]; exact cA hL1 vd (by norm_num) (by norm_num)
  have k14 : Charged.steps rate (s1.add lg) ≤ S ^ 256 := by
    rw [steps_SNat_add]; exact cA vs1 vlg (by norm_num) (by norm_num)
  have k15 : Charged.steps rate (s2.add one) ≤ S ^ 256 := by
    rw [steps_SNat_add]; exact cA vs2 (vone 0) (by norm_num) (by norm_num)
  have v20 : 20 ≤ S ^ 5 := pw_const hS (by norm_num)
  have k16 : Charged.steps rate (SNat.lit 20) ≤ S ^ 256 := by
    rw [steps_SNat_lit]; exact cL v20 (by norm_num)
  have k17 : Charged.steps rate (c20.mul s3) ≤ S ^ 256 := by
    rw [steps_SNat_mul, gc20]; exact cM v20 vs3 (by norm_num) (by norm_num)
  have v512 : 512 ≤ S ^ 9 := pw_const hS (by norm_num)
  have k18 : Charged.steps rate (SNat.lit 512) ≤ S ^ 256 := by
    rw [steps_SNat_lit]; exact cL v512 (by norm_num)
  have k19 : Charged.steps rate (d.mul K) ≤ S ^ 256 := by
    rw [steps_SNat_mul]; exact cM vd vK (by norm_num) (by norm_num)
  have k20 : Charged.steps rate (c512.mul dK) ≤ S ^ 256 := by
    rw [steps_SNat_mul, gc512]; exact cM v512 vdK (by norm_num) (by norm_num)
  have k21 : Charged.steps rate den.toRat ≤ S ^ 256 := by
    rw [steps_SNat_toRat]; exact cL vden (by norm_num)
  have k22 : Charged.steps rate (ε.div denQ) ≤ S ^ 256 := by
    rw [steps_SRat_div]; exact cQ rε (pw_mono hS rdenQ (by norm_num))
  have v4 : 4 ≤ S ^ 2 := pw_const hS (by norm_num)
  have k23 : Charged.steps rate (SNat.lit 4) ≤ S ^ 256 := by
    rw [steps_SNat_lit]; exact cL v4 (by norm_num)
  have k24 : Charged.steps rate (c4.mul K) ≤ S ^ 256 := by
    rw [steps_SNat_mul, gc4]; exact cM v4 vK (by norm_num) (by norm_num)
  have k25 : Charged.steps rate fK.toRat ≤ S ^ 256 := by
    rw [steps_SNat_toRat]; exact cL vfK (by norm_num)
  have k26 : Charged.steps rate (fKq.div γ) ≤ S ^ 256 := by
    rw [steps_SRat_div]; exact cQ (pw_mono hS rfKq (by norm_num)) (pw_mono hS rγ (by norm_num))
  have k27 : Charged.steps rate q.natCeil ≤ S ^ 256 := by rw [steps_SRat_natCeil]; exact cQ rq rq
  have k28 : Charged.steps rate (d.mul d) ≤ S ^ 256 := by
    rw [steps_SNat_mul]; exact cM vd vd (by norm_num) (by norm_num)
  have v16 : 16 ≤ S ^ 4 := pw_const hS (by norm_num)
  have k29 : Charged.steps rate (SNat.lit 16) ≤ S ^ 256 := by
    rw [steps_SNat_lit]; exact cL v16 (by norm_num)
  have k30 : Charged.steps rate (c16.mul A) ≤ S ^ 256 := by
    rw [steps_SNat_mul, gc16]; exact cM v16 vA (by norm_num) (by norm_num)
  have k31 : Charged.steps rate (a16.mul d2) ≤ S ^ 256 := by
    rw [steps_SNat_mul]; exact cM va16 vd2 (by norm_num) (by norm_num)
  have v100 : 100 ≤ S ^ 7 := pw_const hS (by norm_num)
  have k32 : Charged.steps rate (SNat.lit 100) ≤ S ^ 256 := by
    rw [steps_SNat_lit]; exact cL v100 (by norm_num)
  have k33 : Charged.steps rate (c100.mul d) ≤ S ^ 256 := by
    rw [steps_SNat_mul, gc100]; exact cM v100 vd (by norm_num) (by norm_num)
  have k34 : Charged.steps rate (d100.mul B) ≤ S ^ 256 := by
    rw [steps_SNat_mul]; exact cM vd100 vB (by norm_num) (by norm_num)
  have v10 : 10 ≤ S ^ 4 := pw_const hS (by norm_num)
  have k35 : Charged.steps rate (SNat.lit 10) ≤ S ^ 256 := by
    rw [steps_SNat_lit]; exact cL v10 (by norm_num)
  have k36 : Charged.steps rate (c10.mul A) ≤ S ^ 256 := by
    rw [steps_SNat_mul, gc10]; exact cM v10 vA (by norm_num) (by norm_num)
  have k37 : Charged.steps rate (a10.mul d2) ≤ S ^ 256 := by
    rw [steps_SNat_mul]; exact cM va10 vd2 (by norm_num) (by norm_num)
  have k38 : Charged.steps rate (W.add one) ≤ S ^ 256 := by
    rw [steps_SNat_add]; exact cA vW (vone 0) (by norm_num) (by norm_num)
  have k39 : Charged.steps rate (ad2.mul W1) ≤ S ^ 256 := by
    rw [steps_SNat_mul]; exact cM vad2 vW1 (by norm_num) (by norm_num)
  rw [Charged.steps_pure, add_zero]
  have hfin : 64 * S ^ 256 ≤ S ^ 266 := by
    rw [show 266 = 10 + 256 by rfl, pow_add]
    exact Nat.mul_le_mul_right _ (pw_const hS (by norm_num))
  linarith

/-- INTERNAL: what the input length gives the preprocessing: `m + n + 2 ≤ L < costScale`,
every margin, bound and `ε` has length at most `L`, and `ε⁻¹ ≤ costScale`.
TEXLINE: sections/scales.tex:57-77 -/
theorem prep_input_facts (I : Instance) (ε δ : ℚ) :
    I.m + I.n + 2 ≤ inputLength I ε δ ∧ inputLength I ε δ + 1 ≤ costScale I ε δ ∧
    (∀ i, bitLen (I.r i) ≤ inputLength I ε δ) ∧ (∀ j, bitLen (I.c j) ≤ inputLength I ε δ) ∧
    (∀ i j, bitLen (I.b i j) ≤ inputLength I ε δ) ∧ ratLen ε ≤ inputLength I ε δ ∧
    ε⁻¹ ≤ (costScale I ε δ : ℚ) := by
  have hr : I.m ≤ ∑ i, bitLen (I.r i) := by
    have := Finset.card_nsmul_le_sum Finset.univ (fun i => bitLen (I.r i)) 1
      (fun i _ => one_le_bitLen _)
    simpa using this
  have hc : I.n ≤ ∑ j, bitLen (I.c j) := by
    have := Finset.card_nsmul_le_sum Finset.univ (fun j => bitLen (I.c j)) 1
      (fun j _ => one_le_bitLen _)
    simpa using this
  have h1 := one_le_bitLen I.m
  have h2 := one_le_bitLen I.n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold inputLength; omega
  · unfold costScale; omega
  · intro i
    have := Finset.single_le_sum (f := fun i => bitLen (I.r i)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
    unfold inputLength; omega
  · intro j
    have := Finset.single_le_sum (f := fun j => bitLen (I.c j)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
    unfold inputLength; omega
  · intro i j
    have h3 := Finset.single_le_sum (f := fun j => bitLen (I.b i j)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
    have h4 := Finset.single_le_sum (f := fun i => ∑ j, bitLen (I.b i j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    unfold inputLength; omega
  · unfold inputLength; omega
  · have h5 : ε⁻¹ ≤ (⌈ε⁻¹⌉₊ : ℚ) := Nat.le_ceil _
    have h6 : ⌈ε⁻¹⌉₊ ≤ costScale I ε δ := by unfold costScale; omega
    exact h5.trans (by exact_mod_cast h6)

/-- **Preprocessing cost.**  The prefix S0–S4 of `Program.fpras` (through the
computation of `p`) costs at most `costScale ^ k` bit operations, and its outputs
have sizes bounded by the same power.
PAPER: sections/scales.tex:8-99 (polynomial feasibility test, tightening by binary
search, `eq:parameters` and its size bounds `A, B, W, H = poly(L, ε⁻¹)`, the
forest "in polynomial time"); sections/algorithm.tex:692-706. -/
theorem prep_cost : ∃ k : ℕ, ∀ (I : Instance) (ε δ : ℚ), 0 < I.m → 0 < I.n → 0 < ε →
    ε < 1 → 0 < δ → δ < 1 →
    prepCost I ε δ ≤ costScale I ε δ ^ k ∧
    CtxSize (costScale I ε δ ^ k) (prepCtx I ε δ) ∧
    PmSize (costScale I ε δ ^ k) (prepPm I ε δ) ∧
    (prepPS I ε δ).get ≤ costScale I ε δ ^ k := by
  obtain ⟨kF, hF⟩ := feasible_cost
  obtain ⟨kT, hT⟩ := tighten_cost
  obtain ⟨kB, hB⟩ := buildCtx_cost
  refine ⟨kF + kT + 266 * kB + 300 + 4, ?_⟩
  intro I ε δ hm hn hε hε1 hδ hδ1
  obtain ⟨hmnL, hLN, hrL, hcL, hbL, hεL, hεN⟩ := prep_input_facts I ε δ
  generalize hE : kF + kT + 266 * kB + 300 = E
  generalize hNdef : costScale I ε δ = N at hLN hεN ⊢
  generalize hLdef : inputLength I ε δ = L at hmnL hLN hrL hcL hbL hεL
  have hN2 : 2 ≤ N := by omega
  have hmn : I.m + I.n + 2 ≤ N := by omega
  have hmN : I.m ≤ N ^ 1 := pw_self (by omega)
  have hnN : I.n ≤ N ^ 1 := pw_self (by omega)
  have hup : ∀ {a i : ℕ}, a ≤ N ^ i → i ≤ E → a ≤ N ^ E := fun ha hi => pw_mono hN2 ha hi
  -- S0: reading the input
  have hLE : inputLength I ε δ ≤ N ^ E := by
    rw [hLdef]; exact hup (pw_self (by omega)) (by omega)
  obtain ⟨hrlen, hrbits, hrcost⟩ := readList_cost N (List.ofFn I.r) (by
    intro k hk; obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hk; exact (hrL i).trans (by omega))
  obtain ⟨hclen, hcbits, hccost⟩ := readList_cost N (List.ofFn I.c) (by
    intro k hk; obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hk; exact (hcL j).trans (by omega))
  obtain ⟨hbbits, hbcost⟩ := readMatrix_cost N N (List.ofFn fun i => List.ofFn fun j => I.b i j)
    (by
      intro row hrow k hk
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hrow
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hk
      exact (hbL i j).trans (by omega))
    (by intro row hrow; obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hrow; simp; omega)
  simp only [List.length_ofFn] at hrlen hclen hrcost hccost hbcost
  have hNN : N + I.m + 1 ≤ N ^ 3 :=
    pw_add hN2 (pw_add hN2 (pw_self le_rfl) hmN) (pw_one hN2)
  have hNN' : N + I.n + 1 ≤ N ^ 3 :=
    pw_add hN2 (pw_add hN2 (pw_self le_rfl) hnN) (pw_one hN2)
  have c2 : Charged.steps rate (readList (List.ofFn I.r)) ≤ N ^ E :=
    hup (hrcost.trans (pw_mul hmN hNN)) (by omega)
  have c3 : Charged.steps rate (readList (List.ofFn I.c)) ≤ N ^ E :=
    hup (hccost.trans (pw_mul hnN hNN')) (by omega)
  have c4 : Charged.steps rate (readMatrix (List.ofFn fun i => List.ofFn fun j => I.b i j)) ≤
      N ^ E := by
    refine hup (hbcost.trans (pw_mul hmN (pw_add hN2 (pw_add hN2 (pw_mul (pw_self le_rfl)
      (pw_add hN2 (pw_add hN2 (pw_self le_rfl) (pw_self le_rfl)) (pw_one hN2)))
      (pw_mono hN2 hmN (by norm_num))) (pw_one hN2)))) (by omega)
  have hRlen : (prepR I).length = I.m := hrlen
  have hClen : (prepC I).length = I.n := hclen
  -- S1: the feasibility test
  have c5 : Charged.steps rate (feasible I.m I.n (prepR I) (prepC I) (prepB I)) ≤ N ^ E :=
    hup (hF N I.m I.n (prepR I) (prepC I) (prepB I) hN2 hmn (by omega) (by omega)
      hrbits hcbits hbbits) (by omega)
  -- S2: tightening
  obtain ⟨hTc, hTrows, hTcols, hTlen, hTcells⟩ :=
    hT N I.m I.n (prepR I) (prepC I) (prepB I) hN2 hmn (by omega) (by omega)
      hrbits hcbits hbbits
  have c6 : Charged.steps rate (tighten I.m I.n (prepR I) (prepC I) (prepB I)) ≤ N ^ E :=
    hup hTc (by omega)
  -- S3: the parameters
  have c7 : Charged.steps rate (SRat.lit ε) ≤ N ^ E := by
    rw [steps_SRat_lit]; exact hup (pw_self (by omega)) (by omega)
  obtain ⟨hPc, hPm, hB1, hH1⟩ := params_cost N I.m I.n (inputLen I ε δ).val (SRat.lit ε).val
    hN2 hmn (by simp [inputLen, hLdef]; omega) (by simpa using hε) (by simpa using hεN)
    (by simp; omega)
  have c8 : Charged.steps rate (params I.m I.n (inputLen I ε δ).val (SRat.lit ε).val) ≤ N ^ E :=
    hup hPc (by omega)
  -- S4: the forest and the context
  have hN266 : N ≤ N ^ 266 := pw_mono hN2 (pw_self le_rfl) (by norm_num)
  have hcells : (prepT I).cells.length ≤ N ^ 266 :=
    hTlen.trans (pw_mono hN2 (pw_mul hmN hnN) (by norm_num))
  obtain ⟨hBc, hctx, hsmallLen, hsmallW⟩ := hB (N ^ 266) I.m I.n (prepT I) (prepPm I ε δ)
    (by have := pw_one hN2 (j := 266); omega) (hmn.trans hN266)
    (fun x hx => (hTrows x hx).trans hN266) (fun x hx => (hTcols x hx).trans hN266) hcells
    (fun e he => by
      obtain ⟨h1, h2, h3⟩ := hTcells e he; exact ⟨h1, h2, h3.trans hN266⟩)
    hPm hB1 hH1
  rw [← pow_mul] at hBc hctx
  have c9 : Charged.steps rate (buildCtx I.m I.n (prepT I) (prepPm I ε δ)) ≤ N ^ E :=
    hup hBc (by omega)
  have c10 : Charged.steps rate (SNat.lit 0) ≤ N ^ E := by
    rw [steps_SNat_lit]; exact hup (pw_one hN2 (j := 0)) (by omega)
  -- the sum `p` of the small bounds
  have hsmall : (prepCtx I ε δ).small.length ≤ N ^ 2 :=
    hsmallLen.trans (hTlen.trans (pw_mul hmN hnN))
  have hW : (prepPm I ε δ).W.get ≤ N ^ 266 := hPm.W_le
  obtain ⟨hpv, hpc⟩ := foldl_inv (fun acc (e : Entry) => SNat.add acc e.2.2)
    (fun i (acc : SNat) => acc.get ≤ i * N ^ 266) (N ^ 270) (prepCtx I ε δ).small 0
    (SNat.lit 0).val (by simp)
    (by
      intro i acc e _ hi he hacc
      have hew := hsmallW e he
      refine ⟨?_, ?_⟩
      · simp only [SNat.get_add]; rw [Nat.add_mul, one_mul]; omega
      · rw [steps_SNat_add]
        have hi2 : i ≤ N ^ 2 := by omega
        have h1 : acc.get ≤ N ^ 268 := hacc.trans (pw_mul hi2 le_rfl)
        have h2 : e.2.2.get ≤ N ^ 268 := pw_mono hN2 (hew.le.trans hW) (by norm_num)
        exact pw_add hN2 (pw_bitLen hN2 h1) (pw_bitLen hN2 h2))
  have c11 : Charged.steps rate (Charged.foldl (fun acc (e : Entry) => SNat.add acc e.2.2)
      (prepCtx I ε δ).small (SNat.lit 0).val) ≤ N ^ E :=
    hup (hpc.trans (pw_mul hsmall le_rfl)) (by omega)
  have hfin : 16 * N ^ E ≤ N ^ (E + 4) := by
    rw [pow_add, Nat.mul_comm]; exact Nat.mul_le_mul_left _ (pw_const hN2 (by norm_num))
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold prepCost
    have c1 : Charged.steps rate (inputLen I ε δ) ≤ N ^ E := by
      rw [inputLen, steps_SNat_inputLength]; exact hLE
    linarith
  · exact hctx.mono (pw_mono hN2 le_rfl (by omega))
  · exact hPm.mono (pw_mono hN2 le_rfl (by omega))
  · have : (prepPS I ε δ).get ≤ N ^ 268 := by
      have h := hpv; simp only [zero_add] at h
      exact h.trans (pw_mul hsmall le_rfl)
    exact pw_mono hN2 this (by omega)

end Cellcounting.Analysis
