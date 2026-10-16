import Cellcounting.Analysis.BinLaw
import Cellcounting.Analysis.BinConductance
import Cellcounting.Analysis.CheegerHard

/-!
# The bin walk samples its law to within `ζ` (`eq:bin-mixing`)

`Cellcounting.Analysis.sampleBin_close`: one bin sample of the weight oracle
(`Pseudocode.sampleBin`, a fresh lazy Metropolis walk of `ℓ_in` steps on
`{0, …, B-1}^e` for the dyadic weights `V_a`, started at bin `0`) is within total
variation `ζ = θ / (8 Q_in)` of the bin law `π_a = V_a / S_a` (`binLaw`).

This is `evaluation.tex:205-330`: the walk is reversible for `π_a` and lazy; its
conductance is at least `κ = 1/(10⁴ d² B)` (`lem:bin-conductance`, via the
finite-box Prékopa–Leindler inequality `lem:integral-interpolation` applied to the
log-concave density `ϱ_a = 2^{-aD/H}` on `[0, B]^e`); the cut bound gives inverse
spectral gap at most `K_bin = 2/κ²`; with `π_{a,min}^{-1} ≤ 2^H B^e` this gives
`‖P_a^ℓ(v, ·) - π_a‖_TV ≤ 2^{H+dB} exp(-ℓ/K_bin)` (`eq:bin-mixing`), and
`ℓ_in = ⌈K_bin (H + dB + 16 Q_in/θ + 2)⌉` makes this at most `θ / (8 Q_in)`.

The proof here assembles that argument from its parts:
* `bin_conductance` (`BinConductance.lean`, `lem:bin-conductance`) gives the cut bound
  `κ π_a(A) ≤ Q(A, Aᶜ)` for `P_a`, hence `2κ` for `2P_a - I` (`binQ_cut`);
* `spectralGap_of_cut` (`CheegerHard.lean`) turns it into the gap `(2κ)²/2` for `2P_a - I`;
* Arlib's `tvDist_iter_row_lazy_le` bounds the lazy chain `P_a = (2P_a - I).lazy`;
* `loop_walkStep_pclose` (`BinChain.lean`) bounds `PClose` by total variation;
* `binMix_numeric` closes `½(1-κ²)^ℓ √(π_a(0)⁻¹-1) ≤ θ/(8Q_in)` from
  `π_a(0)⁻¹ ≤ 2^H B^e ≤ e^{H+dB}` (`binDist_zero_inv_le`, `nFree_le_dParam`).
The only open input is `bin_conductance` itself (Prékopa–Leindler on boxes and the
cut covering), which lives in its own file.
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal
open Classical
open Arlib.Probability Arlib.MarkovChains

/-- INTERNAL: with no free cell the bin space is the single empty vector. -/
theorem binSet_of_nFree_zero (I : Instance) (ε δ : ℚ) (he : nFree I ε δ = 0) :
    binSet I ε δ = {fun _ => 0} := by
  ext v
  simp only [binSet, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨u, -, rfl⟩
    funext k
    simp [extendN, he]
  · rintro rfl
    refine ⟨fun _ => 0, Fintype.mem_piFinset.2 fun i => absurd i.isLt (by omega), ?_⟩
    funext k
    simp [extendN]

/-- INTERNAL: with no free cell the bin law is the point mass at the empty vector. -/
theorem binLaw_of_nFree_zero (I : Instance) (ε δ : ℚ) (he : nFree I ε δ = 0) (a : ℕ)
    (x y : ℕ → ℕ) : binLaw I ε δ a x y = PMF.pure fun _ => 0 := by
  have hset := binSet_of_nFree_zero I ε δ he
  have hne : (binSet I ε δ).Nonempty := by rw [hset]; exact Finset.singleton_nonempty _
  ext v
  unfold binLaw
  rw [dif_pos hne, PMF.ofFinset_apply, PMF.pure_apply]
  by_cases hv : v = fun _ => 0
  · have hS : binS I ε δ a x y = binV I ε δ a x y v := by
      unfold binS; rw [hset, Finset.sum_singleton, hv]
    rw [if_pos (by rw [hset, hv]; exact Finset.mem_singleton_self _), if_pos hv, hS,
      div_self (binV_pos I ε δ a x y v).ne', ENNReal.ofReal_one]
  · rw [if_neg (by rw [hset]; simpa using hv), if_neg hv]

/-- INTERNAL: the numeric end of `eq:bin-mixing`: with `κ = 1/κ'`, gap `(2κ)²/2` for
`2P - I`, `π(0)⁻¹ ≤ e^{H + D}` and `ℓ ≥ 2κ'²(H + D + 2 + 16u)`, the lazy-chain bound
`½ (1 - κ²)^ℓ √(π(0)⁻¹ - 1)` is at most `1/(8u)`.
TEXLINE: sections/evaluation.tex:313-346 -/
theorem binMix_numeric (κ' P0 H D u : ℝ) (ℓ : ℕ) (hκ : 1 ≤ κ') (hP0 : 0 < P0)
    (hP0le : P0⁻¹ ≤ Real.exp (H + D)) (hH : 0 ≤ H) (hD : 0 ≤ D) (hu : 0 < u)
    (hℓ : 2 * κ' ^ 2 * (H + D + 2 + 16 * u) ≤ ℓ) :
    1 / 2 * (1 - (2 * (1 / κ')) ^ 2 / 2 / 2) ^ ℓ * Real.sqrt (1 / P0 - 1) ≤ 1 / (8 * u) := by
  have hκ2 : 0 < κ' ^ 2 := by positivity
  have hx : (2 * (1 / κ')) ^ 2 / 2 / 2 = 1 / κ' ^ 2 := by field_simp
  rw [hx]
  have hx1 : 1 / κ' ^ 2 ≤ 1 := by rw [div_le_one hκ2]; nlinarith
  have hpow : (1 - 1 / κ' ^ 2) ^ ℓ ≤ Real.exp (-(2 * (H + D + 2 + 16 * u))) := by
    calc (1 - 1 / κ' ^ 2) ^ ℓ ≤ Real.exp (-(1 / κ' ^ 2)) ^ ℓ :=
          pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg _) ℓ
      _ = Real.exp (ℓ * -(1 / κ' ^ 2)) := (Real.exp_nat_mul _ ℓ).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.2
        have : 2 * (H + D + 2 + 16 * u) ≤ ℓ * (1 / κ' ^ 2) := by
          rw [mul_one_div, le_div_iff₀ hκ2]; linarith
        linarith
  have hsq : Real.sqrt (1 / P0 - 1) ≤ Real.exp (H + D) := by
    have h1 : Real.sqrt (1 / P0 - 1) ≤ 1 / P0 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [sq_nonneg (1 / P0 - 1)]
    exact h1.trans (by rw [one_div]; exact hP0le)
  have hpos1 : 0 ≤ (1 - 1 / κ' ^ 2) ^ ℓ := pow_nonneg (by linarith) _
  calc 1 / 2 * (1 - 1 / κ' ^ 2) ^ ℓ * Real.sqrt (1 / P0 - 1)
      ≤ 1 / 2 * Real.exp (-(2 * (H + D + 2 + 16 * u))) * Real.exp (H + D) := by
        gcongr
    _ = 1 / 2 * Real.exp (-(H + D + 4 + 32 * u)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ 1 / 2 * Real.exp (-(32 * u)) := by gcongr; linarith
    _ ≤ 1 / (8 * u) := by
        have he := Real.add_one_le_exp (32 * u)
        have hep : 0 < Real.exp (32 * u) := Real.exp_pos _
        rw [Real.exp_neg, ← div_eq_mul_inv, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith

/-- INTERNAL: `e ≤ d` (a local copy; `WeightOracle.nFree_le_d` imports this file). -/
theorem nFree_le_dParam (I : Instance) (ε δ : ℚ) : nFree I ε δ ≤ dParam I := by
  have := cells_count_le I ε δ
  unfold dParam
  omega

/-- **Bin-walk mixing** (`eq:bin-mixing` with `eq:inner-walk-length`): one bin sample
is within total variation `ζ = θ/(8 Q_in)` of `π_a`.
PAPER: sections/evaluation.tex:322-344 -/
theorem sampleBin_close (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (hε1 : ε < 1)
    (hfeas : feasible I) (x y : ℕ → ℕ)
    (hbox : ∀ s < nSmall I ε δ, x s ≤ smallB I ε δ s ∧ y s ≤ smallB I ε δ s)
    (a : ℕ) (ha : a ≤ HParam I ε δ) (ξin θ : ℚ) (hξ : 0 < ξin) (hξ1 : ξin < 1 / 4)
    (hθ : 0 < θ) (hθ1 : θ < 1 / 4) :
    PClose (sampleBin I ε δ ξin θ a x y) (binLaw I ε δ a x y)
      (ENNReal.ofReal (oZeta I ε δ ξin θ)) := by
  by_cases he : nFree I ε δ = 0
  · -- no free cell: both laws are the point mass at the empty vector
    unfold sampleBin
    rw [if_pos he, binLaw_of_nFree_zero I ε δ he]
    exact PClose.refl _ _
  -- `e ≥ 1`: the conductance bound `lem:bin-conductance` and `eq:bin-mixing`
  have h0 := zero_mem_binSet I ε δ hε
  have hne : (binSet I ε δ).Nonempty := ⟨_, h0⟩
  let v0 : binSet I ε δ := ⟨fun _ => 0, h0⟩
  have hS : sampleBin I ε δ ξin θ a x y =
      loop (fun _ v => walkStep I ε δ a x y v) (oEll I ε δ ξin θ) v0.1 := by
    unfold sampleBin; rw [if_neg he]
  rw [hS]
  refine (loop_walkStep_pclose I ε δ a x y hne v0 _).mono (ENNReal.ofReal_le_ofReal ?_)
  have hd := dParam_ge I
  have hB : 0 < BParam I ε δ := by
    have := AParam_pos I ε δ hε
    unfold BParam; positivity
  set κ' : ℝ := 10000 * (dParam I : ℝ) ^ 2 * BParam I ε δ with hκ'
  have hκ1 : 1 ≤ κ' := by
    have : (1 : ℝ) ≤ dParam I := by exact_mod_cast (by omega : 1 ≤ dParam I)
    have : (1 : ℝ) ≤ BParam I ε δ := by exact_mod_cast hB
    rw [hκ']; nlinarith
  have hrev := binQ_reversible I ε δ a x y hne
  have hgap : SpectralGapAtLeast (binDist I ε δ a x y hne) (binQ I ε δ a x y)
      ((2 * (1 / κ')) ^ 2 / 2) :=
    spectralGap_of_cut hrev (by positivity) fun A hA => by
      rw [binQ_cut]
      have := bin_conductance I ε δ hε hε1 hfeas x y hbox a ha he hne A hA
      rw [← hκ'] at this
      linarith
  have hpos : ∀ v, 0 < binDist I ε δ a x y hne v := fun v =>
    div_pos (binV_pos I ε δ a x y v.1) (binS_pos I ε δ a x y hne)
  have hγ : (2 * (1 / κ')) ^ 2 / 2 ≤ 2 := by
    have : 1 / κ' ≤ 1 := by rw [div_le_one (by linarith)]; exact hκ1
    have : 0 ≤ 1 / κ' := by positivity
    nlinarith
  have hmix := tvDist_iter_row_lazy_le hrev hpos hgap hγ v0 (oEll I ε δ ξin θ)
  rw [binQ_lazy] at hmix
  refine hmix.trans ?_
  -- the numeric step: `π_a(0)⁻¹ ≤ 2^H B^e ≤ e^{H + dB}` and the length of `ℓ_in`
  set H := HParam I ε δ
  set Q := oQ I ε δ ξin θ
  have hN : 0 < oN I ε δ ξin θ := by
    unfold oN oSigma
    exact Nat.ceil_pos.2 (by positivity)
  have hQ : 0 < Q := by
    simp only [Q, oQ]; positivity
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hθr : (0 : ℝ) < θ := by exact_mod_cast hθ
  have hBr : (1 : ℝ) ≤ BParam I ε δ := by exact_mod_cast hB
  have hP0 : (binDist I ε δ a x y hne v0)⁻¹ ≤
      Real.exp ((H : ℝ) + (dParam I : ℝ) * BParam I ε δ) := by
    refine (binDist_zero_inv_le I ε δ hε hfeas a ha x y hbox hne).trans ?_
    rw [Real.exp_add]
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    gcongr
    · calc (2 : ℝ) ^ H ≤ Real.exp 1 ^ H := pow_le_pow_left₀ (by norm_num) he1 H
        _ = Real.exp (H : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
    · calc (BParam I ε δ : ℝ) ^ nFree I ε δ ≤ (BParam I ε δ : ℝ) ^ dParam I :=
            pow_le_pow_right₀ hBr (nFree_le_dParam I ε δ)
        _ ≤ Real.exp (BParam I ε δ : ℝ) ^ dParam I :=
            pow_le_pow_left₀ (by positivity)
              (by linarith [Real.add_one_le_exp (BParam I ε δ : ℝ)]) _
        _ = Real.exp ((dParam I : ℝ) * BParam I ε δ) := by rw [← Real.exp_nat_mul]
  have hℓ : 2 * κ' ^ 2 * ((H : ℝ) + (dParam I : ℝ) * BParam I ε δ + 2 + 16 * ((Q : ℝ) / θ)) ≤
      (oEll I ε δ ξin θ : ℝ) := by
    have h := Nat.le_ceil ((oKbin I ε δ : ℚ) * (((H + dParam I * BParam I ε δ + 2 : ℕ) : ℚ) +
      16 * (Q : ℚ) / θ))
    have h' : (((oKbin I ε δ : ℚ) * (((H + dParam I * BParam I ε δ + 2 : ℕ) : ℚ) +
        16 * (Q : ℚ) / θ) : ℚ) : ℝ) ≤ (oEll I ε δ ξin θ : ℝ) := by
      unfold oEll; exact_mod_cast h
    refine le_trans (le_of_eq ?_) h'
    simp only [oKbin, hκ']
    push_cast
    ring
  have key := binMix_numeric κ' (binDist I ε δ a x y hne v0) (H : ℝ)
    ((dParam I : ℝ) * BParam I ε δ) ((Q : ℝ) / θ) (oEll I ε δ ξin θ) hκ1 (hpos v0) hP0
    (by positivity) (by positivity) (by positivity) hℓ
  refine key.trans (le_of_eq ?_)
  rw [show oZeta I ε δ ξin θ = θ / (8 * (Q : ℚ)) from rfl]
  push_cast
  field_simp

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r6 · proved · `sampleBin_close` assembled; rests only on `bin_conductance` (open, own file)
-/
