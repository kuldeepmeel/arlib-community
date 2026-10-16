import Cellcounting.Analysis.DyadicDraw
import Cellcounting.Analysis.ContaminationBoxes
import Mathlib.Data.Fin.Tuple.Finset

/-!
# The ideal laws behind the weight oracle

`evaluation.tex:66-104`: the bin space `𝒱 = {0, …, B-1}^e` (`binSet`, as vectors
`ℕ → ℕ` vanishing past `e`), the dyadic bin weights `V_a(v) = 2^{-⌊aD(v)/H⌋}`
(`binV`), their sum `S_a` (`binS`) and the bin law `π_a = V_a / S_a` (`binLaw`).

`idealOffsets v` is `Pseudocode.binOffsets` with every dyadic draw replaced by an
exact uniform draw (`idealDraw`); `binOffsets_close` bounds the difference by
`e ζ` (`lem:dyadic-integer-draw`), and `pexp_idealOffsets` computes its law: the
uniform law on the integer points `z_k = lo_k + o_k`, `o_k < |I_{v_k}|`, of the bin.
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal
open Classical

section
variable (I : Instance) (ε δ : ℚ)

/-- INTERNAL: the bin space `{0, …, B-1}^e`, as vectors `ℕ → ℕ` vanishing past `e`.
TEXLINE: sections/evaluation.tex:52 -/
noncomputable def binSet : Finset (ℕ → ℕ) :=
  (Fintype.piFinset fun _ : Fin (nFree I ε δ) => Finset.range (BParam I ε δ)).image extendN

/-- INTERNAL: the dyadic bin weight `V_a(v) = 2^{-⌊aD(v)/H⌋}`.
TEXLINE: sections/evaluation.tex:72-77 -/
noncomputable def binV (a : ℕ) (x y v : ℕ → ℕ) : ℝ := (2 : ℝ) ^ (-binExp I ε δ a x y v)

/-- INTERNAL: the bin partition function `S_a = Σ_v V_a(v)`.
TEXLINE: sections/evaluation.tex:90-93 -/
noncomputable def binS (a : ℕ) (x y : ℕ → ℕ) : ℝ := ∑ v ∈ binSet I ε δ, binV I ε δ a x y v

theorem binV_pos (a : ℕ) (x y v : ℕ → ℕ) : 0 < binV I ε δ a x y v := by
  unfold binV; positivity

theorem binS_pos (a : ℕ) (x y : ℕ → ℕ) (h : (binSet I ε δ).Nonempty) : 0 < binS I ε δ a x y :=
  Finset.sum_pos (fun v _ => binV_pos I ε δ a x y v) h

/-- INTERNAL: the bin law `π_a(v) = V_a(v) / S_a` (a point mass if `𝒱` is empty,
which happens only when `B = 0`).
TEXLINE: sections/evaluation.tex:90-93 -/
noncomputable def binLaw (a : ℕ) (x y : ℕ → ℕ) : PMF (ℕ → ℕ) :=
  if h : (binSet I ε δ).Nonempty then
    PMF.ofFinset (fun v => if v ∈ binSet I ε δ then
        ENNReal.ofReal (binV I ε δ a x y v / binS I ε δ a x y) else 0) (binSet I ε δ)
      (by
        rw [Finset.sum_congr rfl fun v hv => if_pos hv,
          ← ENNReal.ofReal_sum_of_nonneg fun v _ =>
            div_nonneg (binV_pos I ε δ a x y v).le (binS_pos I ε δ a x y h).le,
          ← Finset.sum_div]
        rw [show ∑ v ∈ binSet I ε δ, binV I ε δ a x y v = binS I ε δ a x y from rfl,
          div_self (binS_pos I ε δ a x y h).ne', ENNReal.ofReal_one])
      (fun v hv => if_neg hv)
  else PMF.pure fun _ => 0

theorem binSet_nonempty (hB : 0 < BParam I ε δ) : (binSet I ε δ).Nonempty :=
  ⟨extendN fun _ => 0, Finset.mem_image_of_mem _ (by simp [Fintype.mem_piFinset, hB])⟩

/-- INTERNAL: expectations under the bin law are finite sums over the bins. -/
theorem pexp_binLaw (a : ℕ) (x y : ℕ → ℕ) (h : (binSet I ε δ).Nonempty) (f : (ℕ → ℕ) → ℝ≥0∞) :
    pexp (binLaw I ε δ a x y) f =
      ∑ v ∈ binSet I ε δ, ENNReal.ofReal (binV I ε δ a x y v / binS I ε δ a x y) * f v := by
  unfold pexp binLaw
  rw [dif_pos h, tsum_eq_sum (s := binSet I ε δ) (fun v hv => by
    rw [PMF.ofFinset_apply, if_neg hv, zero_mul])]
  exact Finset.sum_congr rfl fun v hv => by rw [PMF.ofFinset_apply, if_pos hv]

theorem binLaw_support (a : ℕ) (x y : ℕ → ℕ) (h : (binSet I ε δ).Nonempty) :
    ∀ v ∈ (binLaw I ε δ a x y).support, v ∈ binSet I ε δ := by
  intro v hv
  by_contra hn
  rw [PMF.mem_support_iff] at hv
  apply hv
  unfold binLaw
  rw [dif_pos h, PMF.ofFinset_apply, if_neg hn]

/-! ### Offsets -/

/-- INTERNAL: the lower end `⌈(b_k+1) v_k / B⌉` of the integer interval of bin index `v_k`.
TEXLINE: sections/evaluation.tex:54-61 -/
noncomputable def binLo (k : ℕ) (v : ℕ → ℕ) : ℕ :=
  ((freeAt I ε δ k).2.2 + 1) * v k ⌈/⌉ BParam I ε δ

/-- INTERNAL: the upper end (exclusive) `⌈(b_k+1)(v_k+1) / B⌉`. -/
noncomputable def binHi (k : ℕ) (v : ℕ → ℕ) : ℕ :=
  ((freeAt I ε δ k).2.2 + 1) * (v k + 1) ⌈/⌉ BParam I ε δ

/-- INTERNAL: `|I_{v_k}|`. -/
noncomputable def binLen (k : ℕ) (v : ℕ → ℕ) : ℕ := binHi I ε δ k v - binLo I ε δ k v

/-- INTERNAL: `binOffsets` with exact uniform offset draws.
TEXLINE: sections/evaluation.tex:373-388 -/
noncomputable def idealOffsets (v : ℕ → ℕ) : PMF ((ℕ → ℚ) × ℕ) :=
  loop (fun k st => (idealDraw (binLen I ε δ k v)).map fun off =>
      (Function.update st.1 k ((binLo I ε δ k v + off : ℕ) : ℚ), st.2 * binLen I ε δ k v))
    (nFree I ε δ) (fun _ => 0, 1)

/-- INTERNAL: the dyadic offsets are within `e ζ` of the exact ones.
TEXLINE: sections/evaluation.tex:373-388 -/
theorem binOffsets_close (ξin θ : ℚ) (v : ℕ → ℕ) (hζ : 0 < oZeta I ε δ ξin θ) :
    PClose (binOffsets I ε δ ξin θ v) (idealOffsets I ε δ v)
      (nFree I ε δ * ENNReal.ofReal (oZeta I ε δ ξin θ)) := by
  have := PClose.loop (ζ := fun _ => ENNReal.ofReal (oZeta I ε δ ξin θ))
    (f := fun k st => (dyadicDraw (binLen I ε δ k v) (oZeta I ε δ ξin θ)).map fun off =>
      (Function.update st.1 k ((binLo I ε δ k v + off : ℕ) : ℚ), st.2 * binLen I ε δ k v))
    (g := fun k st => (idealDraw (binLen I ε δ k v)).map fun off =>
      (Function.update st.1 k ((binLo I ε δ k v + off : ℕ) : ℚ), st.2 * binLen I ε δ k v))
    (fun k st => (dyadicDraw_close _ _ hζ).symm.map _) (nFree I ε δ) (fun _ => 0, 1)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  exact this

end

/-! ### The law of a loop of independent coordinate draws -/

/-- INTERNAL: the point `z_k = lo_k + o_k` (`k < n`), zero elsewhere. -/
noncomputable def drawPt (lo : ℕ → ℕ) (n : ℕ) (o : Fin n → ℕ) : ℕ → ℚ :=
  fun k => if h : k < n then ((lo k + o ⟨k, h⟩ : ℕ) : ℚ) else 0

theorem update_drawPt (lo : ℕ → ℕ) (n : ℕ) (o : Fin n → ℕ) (t : ℕ) :
    Function.update (drawPt lo n o) n ((lo n + t : ℕ) : ℚ) =
      drawPt lo (n + 1) (Fin.snoc (α := fun _ => ℕ) o t) := by
  funext k
  rcases lt_trichotomy k n with hk | rfl | hk
  · rw [Function.update_of_ne hk.ne]
    simp only [drawPt, dif_pos hk, dif_pos (hk.trans (Nat.lt_succ_self n))]
    simp [Fin.snoc, hk]
  · simp [drawPt, Fin.snoc]
  · rw [Function.update_of_ne hk.ne']
    simp only [drawPt, dif_neg (show ¬ k < n by omega), dif_neg (show ¬ k < n + 1 by omega)]

/-- INTERNAL: expectation under the exact uniform draw. -/
theorem pexp_idealDraw (M : ℕ) (hM : 0 < M) (f : ℕ → ℝ≥0∞) :
    pexp (idealDraw M) f = ∑ t ∈ Finset.range M, ENNReal.ofReal (1 / (M : ℝ)) * f t := by
  unfold pexp idealDraw
  rw [dif_pos hM, tsum_eq_sum (s := Finset.range M) (fun b hb => by
    rw [PMF.uniformOfFinset_apply, if_neg hb, zero_mul])]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [PMF.uniformOfFinset_apply, if_pos ht, Finset.card_range, one_div,
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast hM), ENNReal.ofReal_natCast]

/-- INTERNAL: a loop of `n` independent uniform coordinate draws `z_k = lo_k + o_k`,
`o_k < len_k`, multiplying the lengths, is uniform on the product of the intervals. -/
theorem pexp_loop_draws (lo len : ℕ → ℕ) (n : ℕ) (hlen : ∀ k < n, 0 < len k)
    (g : (ℕ → ℚ) × ℕ → ℝ≥0∞) :
    pexp (loop (fun k st => (idealDraw (len k)).map fun off =>
        (Function.update st.1 k ((lo k + off : ℕ) : ℚ), st.2 * len k)) n (fun _ => 0, 1)) g =
      ∑ o ∈ Fintype.piFinset (fun k : Fin n => Finset.range (len k)),
        ENNReal.ofReal (1 / ∏ k ∈ Finset.range n, (len k : ℝ)) *
          g (drawPt lo n o, ∏ k ∈ Finset.range n, len k) := by
  induction n generalizing g with
  | zero =>
    rw [loop_zero, pexp_pure]
    simp only [Finset.range_zero, Finset.prod_empty]
    rw [Finset.sum_eq_single_of_mem (fun i => Fin.elim0 i)
      (Fintype.mem_piFinset.2 fun i => Fin.elim0 i) (fun b _ hb =>
      absurd (funext fun i => Fin.elim0 i) hb)]
    have : drawPt lo 0 (fun i => Fin.elim0 i) = fun _ => 0 := by
      funext k; simp [drawPt]
    rw [this]; simp
  | succ n ih =>
    rw [loop_succ, pexp_bind, ih (fun k hk => hlen k (hk.trans (Nat.lt_succ_self n)))]
    have hn := hlen n (Nat.lt_succ_self n)
    simp_rw [pexp_map, pexp_idealDraw _ hn, Function.comp_apply, update_drawPt,
      Finset.mul_sum]
    -- reindex the `(n+1)`-tuples as `(last, init)`
    have hpi := Finset.filter_piFinset_eq_map_snocEquiv (fun k : Fin (n + 1) => Finset.range (len k))
      (fun _ => True)
    simp only [Finset.filter_true] at hpi
    rw [hpi, Finset.sum_map, Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun t _ => ?_
    have hL : (0 : ℝ) < ∏ k ∈ Finset.range n, (len k : ℝ) :=
      Finset.prod_pos fun k hk => by
        exact_mod_cast hlen k ((Finset.mem_range.1 hk).trans (Nat.lt_succ_self n))
    have hn' : (0 : ℝ) < len n := by exact_mod_cast hn
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    field_simp

end Cellcounting.Analysis
