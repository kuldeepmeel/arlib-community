import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Tails of a log-concave marginal with two heavy endpoints

The counting step in the proof of `prop:contamination`
(`integer-signatures.tex:500-535`): a nonnegative sequence `a` on `ℤ` that
interpolates log-concavely between positive values (`eq:tree-marginal-interpolation`),
is at least `1` at `0` and at `b`, at most `2^K` everywhere, and has total mass at
most `C`, satisfies `a(k) ≤ 2 K C / b` at every `k` outside `[0, b]`.

`interp_of_logconcave` is the passage from adjacent log-concavity on a positive
integer interval to the interpolation inequality.
-/

namespace Cellcounting.Analysis

open Finset

/-- INTERNAL: adjacent log-concavity of a positive sequence on `[v, w]` gives the
interpolation inequality between `v` and `w`.
TEXLINE: sections/integer-signatures.tex:455-460 -/
theorem interp_of_logconcave (a : ℤ → ℝ) (v w : ℤ) (hvw : v < w)
    (hpos : ∀ j, v ≤ j → j ≤ w → 0 < a j)
    (hlc : ∀ j, v < j → j < w → a (j - 1) * a (j + 1) ≤ a j ^ 2) (k : ℤ) (hk1 : v < k)
    (hk2 : k < w) :
    a v ^ (((w - k : ℤ) : ℝ) / ((w - v : ℤ) : ℝ)) * a w ^ (((k - v : ℤ) : ℝ) / ((w - v : ℤ) : ℝ))
      ≤ a k := by
  -- logarithms have nonincreasing increments
  set g : ℤ → ℝ := fun j => Real.log (a j) with hg
  have hinc : ∀ j, v < j → j < w → g (j + 1) - g j ≤ g j - g (j - 1) := by
    intro j h1 h2
    have p0 := hpos (j - 1) (by omega) (by omega)
    have p1 := hpos j (by omega) (by omega)
    have p2 := hpos (j + 1) (by omega) (by omega)
    have := Real.log_le_log (by positivity) (hlc j h1 h2)
    rw [Real.log_mul p0.ne' p2.ne', Real.log_pow] at this
    simp only [hg]; push_cast at this; linarith
  -- increment `d j = g j - g (j-1)` is antitone on `(v, w]`
  have hmono : ∀ i j, v < i → i ≤ j → j ≤ w → g j - g (j - 1) ≤ g i - g (i - 1) := by
    intro i j hi hij hjw
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = i + n := ⟨(j - i).toNat, by omega⟩
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := ih (by omega) (by omega)
      have h2 := hinc (i + n) (by omega) (by omega)
      push_cast at h2 ⊢
      rw [show i + (n + 1 : ℤ) - 1 = i + n by ring, show i + (n + 1 : ℤ) = i + n + 1 by ring]
      linarith
  -- telescoping sums of increments
  have htel : ∀ p q, p ≤ q → g q - g p = ∑ j ∈ Finset.Ioc p q, (g j - g (j - 1)) := by
    intro p q hpq
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = p + n := ⟨(q - p).toNat, by omega⟩
    induction n with
    | zero => simp
    | succ n ih =>
      have h := ih (by omega)
      push_cast
      rw [show p + ((n : ℤ) + 1) = (p + n) + 1 by ring]
      rw [show Finset.Ioc p (p + n + 1) = insert (p + n + 1) (Finset.Ioc p (p + n)) by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega]
      rw [Finset.sum_insert (by simp), ← h]
      rw [show p + ↑n + 1 - 1 = p + n by ring]; ring
  have hA : g k - g v ≥ (k - v) * (g k - g (k - 1)) := by
    rw [htel v k hk1.le]
    have : ∑ j ∈ Finset.Ioc v k, (g k - g (k - 1)) ≤ ∑ j ∈ Finset.Ioc v k, (g j - g (j - 1)) :=
      Finset.sum_le_sum fun j hj => by
        simp only [Finset.mem_Ioc] at hj
        exact hmono j k hj.1 hj.2 hk2.le
    rw [Finset.sum_const, Int.card_Ioc, nsmul_eq_mul] at this
    rw [show ((k - v).toNat : ℝ) = ((k - v : ℤ) : ℝ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]] at this
    push_cast at this; linarith
  have hB : g w - g k ≤ (w - k) * (g k - g (k - 1)) := by
    rw [htel k w hk2.le]
    have : ∑ j ∈ Finset.Ioc k w, (g j - g (j - 1)) ≤ ∑ j ∈ Finset.Ioc k w, (g k - g (k - 1)) :=
      Finset.sum_le_sum fun j hj => by
        simp only [Finset.mem_Ioc] at hj
        exact hmono k j hk1 hj.1.le hj.2
    rw [Finset.sum_const, Int.card_Ioc, nsmul_eq_mul] at this
    rw [show ((w - k).toNat : ℝ) = ((w - k : ℤ) : ℝ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]] at this
    push_cast at this; linarith
  -- combine: `(w - v) g k ≥ (w - k) g v + (k - v) g w`
  have hwv : (0 : ℝ) < ((w - v : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < w - v)
  have hkv : (0 : ℝ) ≤ ((k - v : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ k - v)
  have hwk : (0 : ℝ) ≤ ((w - k : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ w - k)
  have hcomb : ((w - k : ℤ) : ℝ) * g v + ((k - v : ℤ) : ℝ) * g w ≤ ((w - v : ℤ) : ℝ) * g k := by
    push_cast at hkv hwk ⊢
    nlinarith
  have pv := hpos v le_rfl hvw.le
  have pw := hpos w hvw.le le_rfl
  have pk := hpos k hk1.le hk2.le
  rw [← Real.exp_log pk, ← Real.exp_log pv, ← Real.exp_log pw, ← Real.exp_mul, ← Real.exp_mul,
    ← Real.exp_add]
  apply Real.exp_le_exp.2
  rw [mul_div_assoc', mul_div_assoc', ← add_div, div_le_iff₀ hwv]
  simp only [hg] at hcomb
  linarith

/-- INTERNAL: one interpolation step loses at most a factor two when the
exponent on the heavy endpoint is at most `1/K`. -/
theorem half_le_interp (x y : ℝ) (K : ℕ) (hx : 0 < x) (hy : 1 ≤ y) (hxK : x ≤ 2 ^ K) (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθK : (K : ℝ) * θ ≤ 1) : x / 2 ≤ x ^ (1 - θ) * y ^ θ := by
  have h2K : (0 : ℝ) < 2 ^ K := by positivity
  have hxy : x / 2 ^ K ≤ y := by
    rw [div_le_iff₀ h2K]; nlinarith
  have h1 : (x / 2 ^ K) ^ θ ≤ y ^ θ :=
    Real.rpow_le_rpow (by positivity) hxy hθ0
  have h2 : x ^ (1 - θ) * (x / 2 ^ K) ^ θ = x / (2 : ℝ) ^ ((K : ℝ) * θ) := by
    rw [Real.div_rpow hx.le h2K.le, ← mul_div_assoc, ← Real.rpow_add hx, sub_add_cancel,
      Real.rpow_one, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have h3 : (2 : ℝ) ^ ((K : ℝ) * θ) ≤ 2 := by
    calc (2 : ℝ) ^ ((K : ℝ) * θ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hθK
      _ = 2 := Real.rpow_one 2
  have h4 : x / 2 ≤ x / (2 : ℝ) ^ ((K : ℝ) * θ) :=
    div_le_div_of_nonneg_left hx.le (by positivity) h3
  calc x / 2 ≤ x ^ (1 - θ) * (x / 2 ^ K) ^ θ := by rw [h2]; exact h4
    _ ≤ x ^ (1 - θ) * y ^ θ := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- **Tail bound for a log-concave marginal** (`integer-signatures.tex:509-535`):
outside `[0, b]`, `a(k) ≤ 2 K C / b`.
PAPER: sections/integer-signatures.tex:509-535 -/
theorem marginal_tail (a : ℤ → ℝ) (Ctot : ℝ) (K b : ℕ) (hK : 1 ≤ K) (hb : 0 < b)
    (ha0 : ∀ k, 0 ≤ a k) (hsum : ∀ S : Finset ℤ, ∑ k ∈ S, a k ≤ Ctot)
    (hle : ∀ k, a k ≤ 2 ^ K) (hlo : 1 ≤ a 0) (hhi : 1 ≤ a b)
    (hinterp : ∀ v k w : ℤ, v < k → k < w → 0 < a v → 0 < a w →
      a v ^ (((w - k : ℤ) : ℝ) / ((w - v : ℤ) : ℝ)) *
        a w ^ (((k - v : ℤ) : ℝ) / ((w - v : ℤ) : ℝ)) ≤ a k)
    (k : ℤ) (hk : k < 0 ∨ (b : ℤ) < k) : a k ≤ 2 * K * Ctot / b := by
  have hC : 0 ≤ Ctot := by simpa using hsum ∅
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  rcases (ha0 k).lt_or_eq with hak | hak
  swap
  · rw [← hak]; positivity
  -- the far endpoint `e` and the distance `D = |e - k| ≥ b`
  set e : ℤ := if k < 0 then (b : ℤ) else 0 with he
  have hea : 1 ≤ a e := by simp only [he]; split_ifs <;> assumption
  set D : ℤ := |e - k| with hD
  have hDb : (b : ℤ) ≤ D := by
    simp only [hD, he]; split_ifs with h <;> rcases hk with hk | hk <;> rw [abs_eq_max_neg] <;>
      omega
  have hDpos : 0 < D := lt_of_lt_of_le (by exact_mod_cast hb) hDb
  set n : ℕ := (D / K).toNat with hn
  have hnK : (n : ℤ) * K ≤ D := by
    have h1 : 0 ≤ D / K := Int.ediv_nonneg hDpos.le (by positivity)
    rw [hn, Int.toNat_of_nonneg h1]
    exact Int.ediv_mul_le D (by positivity)
  have hnD : (D : ℝ) / K < n + 1 := by
    have h1 : 0 ≤ D / K := Int.ediv_nonneg hDpos.le (by positivity)
    have h2 : D < (D / K + 1) * K := by
      have := Int.lt_ediv_add_one_mul_self D (show (0 : ℤ) < K by exact_mod_cast hK)
      linarith
    rw [div_lt_iff₀ (by positivity)]
    have : ((n : ℤ) : ℝ) = ((D / K : ℤ) : ℝ) := by rw [hn, Int.toNat_of_nonneg h1]
    have h3 : (D : ℝ) < (((D / K : ℤ) : ℝ) + 1) * K := by exact_mod_cast h2
    rw [← this] at h3; exact_mod_cast h3
  -- the run of `n + 1` integers from `k` toward `e`
  set S : Finset ℤ := (Finset.range (n + 1)).image
    (fun r : ℕ => if k < e then k + r else k - r) with hS
  have hScard : S.card = n + 1 := by
    rw [hS, Finset.card_image_of_injective]
    · simp
    · intro r r' h
      simp only at h
      split_ifs at h <;> omega
  have hSbound : ∀ j ∈ S, a k / 2 ≤ a j := by
    intro j hj
    simp only [hS, Finset.mem_image, Finset.mem_range] at hj
    obtain ⟨r, hr, rfl⟩ := hj
    have hrn : r ≤ n := Nat.lt_succ_iff.1 hr
    have hrK : (r : ℤ) * K ≤ D := le_trans (by gcongr) hnK
    by_cases hr0 : r = 0
    · subst hr0; simp only [Nat.cast_zero, add_zero, sub_zero, ite_self]; linarith
    have hrpos : (0 : ℤ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr0
    have hθK : (K : ℝ) * ((r : ℝ) / D) ≤ 1 := by
      rw [mul_div_assoc', div_le_one (by exact_mod_cast hDpos)]
      have : ((r : ℤ) * K : ℝ) ≤ (D : ℝ) := by exact_mod_cast hrK
      push_cast at this; linarith
    have hθ0 : (0 : ℝ) ≤ (r : ℝ) / D := by positivity
    by_cases hke : k < e
    · -- toward `e = b`, above `k`
      rw [if_pos hke]
      have hDe : D = e - k := by rw [hD, abs_of_pos (by omega)]
      rcases lt_or_eq_of_le (show k + r ≤ e by
          have : (r : ℤ) ≤ D := le_trans (by nlinarith) hrK
          omega) with hlt | heq
      · have := hinterp k (k + r) e (by omega) hlt hak (lt_of_lt_of_le one_pos hea)
        refine le_trans ?_ this
        have hx := half_le_interp (a k) (a e) K hak hea (hle k) ((r : ℝ) / D) hθ0 hθK
        have hne : (e : ℝ) - k ≠ 0 := by
          have : (k : ℝ) < e := by exact_mod_cast hke
          linarith
        convert hx using 3
        · rw [hDe]; push_cast; field_simp; ring
        · rw [hDe]; push_cast; ring
      · -- `k + r = e` forces `K = 1`
        rw [heq]
        have hK1 : K = 1 := by
          have : (r : ℤ) = D := by omega
          rw [this] at hrK
          have : (K : ℤ) ≤ 1 := by nlinarith
          omega
        have := hle k; rw [hK1] at this; linarith
    · -- toward `e = 0`, below `k`
      rw [if_neg hke]
      have hDe : D = k - e := by
        rw [hD, abs_of_neg (show e - k < 0 by
          rcases hk with hk | hk
          · exfalso; simp only [he, if_pos hk] at hke; omega
          · simp only [he, if_neg (show ¬ k < 0 by omega)]; omega)]; ring
      have hek : e < k := by omega
      rcases lt_or_eq_of_le (show e ≤ k - r by
          have : (r : ℤ) ≤ D := le_trans (by nlinarith) hrK
          omega) with hlt | heq
      · have := hinterp e (k - r) k hlt (by omega) (lt_of_lt_of_le one_pos hea) hak
        refine le_trans ?_ this
        have hx := half_le_interp (a k) (a e) K hak hea (hle k) ((r : ℝ) / D) hθ0 hθK
        rw [mul_comm] at hx
        have hne : (k : ℝ) - e ≠ 0 := by
          have : (e : ℝ) < k := by exact_mod_cast hek
          linarith
        convert hx using 3
        · rw [hDe]; push_cast; ring
        · rw [hDe]; push_cast; field_simp; ring
      · rw [← heq]
        have hK1 : K = 1 := by
          have : (r : ℤ) = D := by omega
          rw [this] at hrK
          have : (K : ℤ) ≤ 1 := by nlinarith
          omega
        have := hle k; rw [hK1] at this; linarith
  -- sum over the run
  have hsumS := hsum S
  have hlow : (n + 1 : ℝ) * (a k / 2) ≤ ∑ j ∈ S, a j := by
    have := Finset.card_nsmul_le_sum S a (a k / 2) hSbound
    rw [hScard, nsmul_eq_mul] at this; push_cast at this; exact this
  have hbn : (b : ℝ) / K ≤ n + 1 := by
    have : (b : ℝ) ≤ D := by exact_mod_cast hDb
    have h1 : (b : ℝ) / K ≤ (D : ℝ) / K := div_le_div_of_nonneg_right this (by positivity)
    linarith
  rw [le_div_iff₀ hbr]
  have h2 : (b : ℝ) / K * (a k / 2) ≤ Ctot := by
    have := mul_le_mul_of_nonneg_right hbn (show 0 ≤ a k / 2 by positivity)
    linarith
  have h3 : (b : ℝ) / K * (a k / 2) * (2 * K) = a k * b := by field_simp
  nlinarith

end Cellcounting.Analysis
