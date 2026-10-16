import Cellcounting.Analysis.BinLaw
import Cellcounting.Analysis.ForestPenaltyBound
import Arlib.MarkovChains.Techniques.MixingTime
import Arlib.MarkovChains.Techniques.Conductance

/-!
# The bin walk as a finite reversible lazy chain

The weight oracle's bin sampler (`Pseudocode.sampleBin`) runs `walkStep`, a lazy
Metropolis walk on the bin space `𝒱 = {0, …, B-1}^e` (`binSet`) for the dyadic weights
`V_a`. This file puts it in Arlib's finite-chain language, which is what the mixing
argument of `evaluation.tex:205-318` needs.
* `binKernel`/`binDist`: the kernel `P_a` and the law `π_a` (`binLaw`) on the subtype `𝒱`.
* `binKernel_reversible`: detailed balance, by `binProp_card_symm` (each move and its
  reverse are proposed by one bit pattern each) and `binV_mul_acc`.
* `walkStep_self_ge`: laziness, `P_a(v, v) ≥ 1/2`. `binQ` is `2P_a - I`, with
  `binQ_lazy : Q.lazy = P_a`. `binQ_cut` says it has twice the cut flow.
* `loop_walkStep_apply`, `loop_walkStep_pclose`: the PMF walk of `t` steps is row `v₀`
  of `P_a^t`, and its `PClose` distance to `binLaw` is at most their total variation.
* `binDist_zero_inv_le`: `π_a(0)^{-1} ≤ 2^H B^e`.
-/

namespace Cellcounting.Analysis
open Pseudocode
open scoped ENNReal
open Classical
open Arlib.Probability Arlib.MarkovChains

variable (I : Instance) (ε δ : ℚ)

/-- INTERNAL: membership in `𝒱 = {0..B-1}^e`, as vectors vanishing past `e`. -/
theorem mem_binSet_iff (v : ℕ → ℕ) :
    v ∈ binSet I ε δ ↔ (∀ k < nFree I ε δ, v k < BParam I ε δ) ∧ ∀ k, nFree I ε δ ≤ k → v k = 0 := by
  simp only [binSet, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · simp only [extendN, dif_pos hk]; exact hu _
    · simp only [extendN, dif_neg (not_lt.2 hk)]
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => v i, fun i => h1 i i.isLt, ?_⟩
    funext k
    simp only [extendN]
    split_ifs with hk
    · rfl
    · exact (h2 k (not_lt.1 hk)).symm

/-- INTERNAL: the law of `k` fair bits, pointwise. -/
theorem uniformBits_apply (k u : ℕ) :
    uniformBits k u = if u < 2 ^ k then ((2 : ℝ≥0∞) ^ k)⁻¹ else 0 := by
  simp only [uniformBits]
  split_ifs with h
  · rw [PMF.uniformOfFinset_apply_of_mem (hs := ⟨0, Finset.mem_range.2 (Nat.two_pow_pos k)⟩)
      (Finset.mem_range.2 h), Finset.card_range]; push_cast; rfl
  · exact PMF.uniformOfFinset_apply_of_notMem _ (by simpa using h)

/-- INTERNAL: the proposal of `walkStep` from `v` on bit pattern `u`: a step in signed
coordinate direction `u`, or `none` for a hold (unused pattern or a move off the box).
TEXLINE: sections/evaluation.tex:205-210 -/
noncomputable def binProp (v : ℕ → ℕ) (u : ℕ) : Option (ℕ → ℕ) :=
  if u < 2 * nFree I ε δ then
    if u % 2 = 1 then
      if v (u / 2) = BParam I ε δ - 1 then none
      else some (Function.update v (u / 2) (v (u / 2) + 1))
    else
      if v (u / 2) = 0 then none
      else some (Function.update v (u / 2) (v (u / 2) - 1))
  else none

/-- INTERNAL: what `walkStep` does with a proposal: hold, or the Metropolis decision. -/
noncomputable def binBody (a : ℕ) (x y : ℕ → ℕ) (v : ℕ → ℕ) (o : Option (ℕ → ℕ)) : PMF (ℕ → ℕ) :=
  match o with
  | none => PMF.pure v
  | some w => binAccept I ε δ a x y v w

/-- INTERNAL: `walkStep` in proposal-then-decide form. -/
theorem walkStep_eq (a : ℕ) (x y v : ℕ → ℕ) :
    walkStep I ε δ a x y v =
      (uniformBits (oKd I)).bind fun u => binBody I ε δ a x y v (binProp I ε δ v u) := by
  unfold walkStep
  show PMF.bind _ _ = _
  congr 1
  funext u
  unfold binProp
  split_ifs <;> rfl

/-- INTERNAL: a dyadic trial of `k` bits succeeds with probability `2^{-k}`. -/
theorem dyadicTrial_true (k : ℕ) : dyadicTrial k true = ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  unfold dyadicTrial
  rw [PMF.map_apply, tsum_eq_single 0 (fun b hb => by simp [hb])]
  simp only [uniformBits, decide_true, if_true]
  rw [PMF.uniformOfFinset_apply_of_mem (hs := ⟨0, Finset.mem_range.2 (Nat.two_pow_pos k)⟩)
    (Finset.mem_range.2 (Nat.two_pow_pos k)), Finset.card_range]
  push_cast; rfl

/-- INTERNAL: the Metropolis decision moves to `w` with probability
`min{1, V_a(w)/V_a(v)}`. -/
theorem binAccept_apply_ne (a : ℕ) (x y v w w' : ℕ → ℕ) (hw : w ≠ v) (hw' : w' ≠ v) :
    binAccept I ε δ a x y v w w' =
      if w' = w then
        (if binExp I ε δ a x y w ≤ binExp I ε δ a x y v then 1
          else ((2 : ℝ≥0∞) ^ (binExp I ε δ a x y w - binExp I ε δ a x y v).toNat)⁻¹)
      else 0 := by
  unfold binAccept
  split_ifs with h1 h2 h2
  · subst h2; simp
  · simp [PMF.pure_apply, h2]
  · subst h2
    rw [PMF.map_apply, tsum_fintype, Fintype.sum_bool]
    simp only [if_true, Bool.false_eq_true, if_false]
    rw [if_neg hw', add_zero, dyadicTrial_true]
  · rw [PMF.map_apply, tsum_fintype, Fintype.sum_bool]
    simp [h2, hw']

/-- INTERNAL: the acceptance probability `min{1, V_a(w)/V_a(v)} = 2^{-max(0, k_a(w)-k_a(v))}`. -/
noncomputable def binAcc (a : ℕ) (x y v w : ℕ → ℕ) : ℝ≥0∞ :=
  if binExp I ε δ a x y w ≤ binExp I ε δ a x y v then 1
  else ((2 : ℝ≥0∞) ^ (binExp I ε δ a x y w - binExp I ε δ a x y v).toNat)⁻¹

/-- INTERNAL: a proposal moves. -/
theorem binProp_ne {v w : ℕ → ℕ} {u : ℕ} (h : binProp I ε δ v u = some w) : w ≠ v := by
  unfold binProp at h
  split_ifs at h with h1 h2 h3 h4 <;> simp only [Option.some.injEq] at h <;> subst h
  · intro h'; have := congrFun h' (u / 2); simp at this
  · intro h'; have := congrFun h' (u / 2); simp at this; omega

/-- INTERNAL: from a bin, every proposal is a bin. -/
theorem binProp_mem {v w : ℕ → ℕ} {u : ℕ} (hv : v ∈ binSet I ε δ)
    (h : binProp I ε δ v u = some w) : w ∈ binSet I ε δ := by
  rw [mem_binSet_iff] at hv ⊢
  obtain ⟨hv1, hv2⟩ := hv
  unfold binProp at h
  split_ifs at h with h1 h2 h3 h4 <;> simp only [Option.some.injEq] at h <;> subst h
  · have hi : u / 2 < nFree I ε δ := by omega
    have := hv1 _ hi
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rcases eq_or_ne k (u / 2) with rfl | hne
      · simp; omega
      · rw [Function.update_of_ne hne]; exact hv1 k hk
    · rw [Function.update_of_ne (by omega)]; exact hv2 k hk
  · have hi : u / 2 < nFree I ε δ := by omega
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rcases eq_or_ne k (u / 2) with rfl | hne
      · simp; have := hv1 _ hi; omega
      · rw [Function.update_of_ne hne]; exact hv1 k hk
    · rw [Function.update_of_ne (by omega)]; exact hv2 k hk

/-- INTERNAL: the off-diagonal transition probabilities of the bin walk. -/
theorem walkStep_apply_ne (a : ℕ) (x y v w : ℕ → ℕ) (hw : w ≠ v) :
    walkStep I ε δ a x y v w =
      ((2 : ℝ≥0∞) ^ oKd I)⁻¹ * binAcc I ε δ a x y v w *
        ((Finset.range (2 ^ oKd I)).filter fun u => binProp I ε δ v u = some w).card := by
  rw [walkStep_eq, PMF.bind_apply, tsum_eq_sum (s := Finset.range (2 ^ oKd I)) (fun u hu => by
    rw [uniformBits_apply, if_neg (by simpa using hu), zero_mul])]
  have hu : ∀ u ∈ Finset.range (2 ^ oKd I), uniformBits (oKd I) u = ((2 : ℝ≥0∞) ^ oKd I)⁻¹ :=
    fun u hu => by rw [uniformBits_apply, if_pos (by simpa using hu)]
  have hb : ∀ u, binBody I ε δ a x y v (binProp I ε δ v u) w =
      if binProp I ε δ v u = some w then binAcc I ε δ a x y v w else 0 := by
    intro u
    rcases hp : binProp I ε δ v u with _ | w'
    · simp [binBody, PMF.pure_apply, hw]
    · simp only [binBody, Option.some.injEq]
      rw [binAccept_apply_ne I ε δ a x y v w' w (binProp_ne I ε δ hp) hw]
      by_cases hww : w = w'
      · subst hww; simp [binAcc]
      · rw [if_neg hww, if_neg (Ne.symm hww)]
  rw [Finset.sum_congr rfl fun u h => by rw [hu u h, hb u, mul_ite, mul_zero],
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  ring

/-- INTERNAL: `4e ≤ 4d ≤ 2^{⌈log₂ 4d⌉}`, so directional proposals have total
probability at most `1/2`. -/
theorem four_nFree_le : 4 * nFree I ε δ ≤ 2 ^ oKd I := by
  have h1 := cells_count_le I ε δ
  have h2 := Nat.le_pow_clog (b := 2) (by norm_num) (4 * dParam I)
  unfold oKd
  unfold dParam at h2 ⊢
  omega

/-- INTERNAL: the opposite direction of a signed coordinate direction. -/
def binFlip (u : ℕ) : ℕ := if u % 2 = 1 then u - 1 else u + 1

/-- INTERNAL: `binFlip` is an involution. -/
theorem binFlip_binFlip (u : ℕ) : binFlip (binFlip u) = u := by
  unfold binFlip; split_ifs <;> omega

/-- INTERNAL: the reverse of a valid move is a valid move. -/
theorem binProp_flip {v w : ℕ → ℕ} {u : ℕ} (hv : v ∈ binSet I ε δ)
    (h : binProp I ε δ v u = some w) : binProp I ε δ w (binFlip u) = some v := by
  rw [mem_binSet_iff] at hv
  unfold binProp at h
  split_ifs at h with h1 h2 h3 h4 <;> simp only [Option.some.injEq] at h <;> subst h
  · have hf : binFlip u = u - 1 := by unfold binFlip; rw [if_pos h2]
    have hi : (u - 1) / 2 = u / 2 := by omega
    unfold binProp
    rw [hf, if_pos (by omega), if_neg (by omega), hi, if_neg (by simp)]
    simp
  · have hf : binFlip u = u + 1 := by unfold binFlip; rw [if_neg h2]
    have hi : (u + 1) / 2 = u / 2 := by omega
    have hlt := hv.1 (u / 2) (by omega)
    unfold binProp
    rw [hf, if_pos (by omega), if_pos (by omega), hi, if_neg (by simp; omega)]
    simp only [Function.update_self, Function.update_idem, Option.some.injEq]
    rw [show v (u / 2) - 1 + 1 = v (u / 2) by omega, Function.update_eq_self]

/-- INTERNAL: only directional patterns propose a move. -/
theorem binProp_lt {v w : ℕ → ℕ} {u : ℕ} (h : binProp I ε δ v u = some w) :
    u < 2 * nFree I ε δ := by
  by_contra hc
  unfold binProp at h
  rw [if_neg hc] at h
  simp at h

/-- INTERNAL: moves `v → w` and `w → v` are proposed equally often. -/
theorem binProp_card_symm {v w : ℕ → ℕ} (hv : v ∈ binSet I ε δ) (hw : w ∈ binSet I ε δ) :
    ((Finset.range (2 ^ oKd I)).filter fun u => binProp I ε δ v u = some w).card =
      ((Finset.range (2 ^ oKd I)).filter fun u => binProp I ε δ w u = some v).card := by
  have h4 := four_nFree_le I ε δ
  have hflt : ∀ {v w : ℕ → ℕ} {u : ℕ}, binProp I ε δ v u = some w →
      binFlip u < 2 ^ oKd I := by
    intro v w u h
    have := binProp_lt I ε δ h
    unfold binFlip; split_ifs <;> omega
  refine Finset.card_bij' (fun u _ => binFlip u) (fun u _ => binFlip u) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_range] at hu ⊢
    exact ⟨hflt hu.2, binProp_flip I ε δ hv hu.2⟩
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_range] at hu ⊢
    exact ⟨hflt hu.2, binProp_flip I ε δ hw hu.2⟩
  · intro u _; exact binFlip_binFlip u
  · intro u _; exact binFlip_binFlip u

/-- INTERNAL: the walk stays in `𝒱`. -/
theorem walkStep_apply_notMem (a : ℕ) (x y v w : ℕ → ℕ) (hv : v ∈ binSet I ε δ)
    (hw : w ∉ binSet I ε δ) : walkStep I ε δ a x y v w = 0 := by
  have hne : w ≠ v := fun h => hw (h ▸ hv)
  rw [walkStep_apply_ne I ε δ a x y v w hne]
  have : ((Finset.range (2 ^ oKd I)).filter fun u => binProp I ε δ v u = some w) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun u _ h => hw (binProp_mem I ε δ hv h)
  rw [this, Finset.card_empty, Nat.cast_zero, mul_zero]

/-- INTERNAL: one step from a bin has total mass `1` on `𝒱`. -/
theorem walkStep_sum (a : ℕ) (x y v : ℕ → ℕ) (hv : v ∈ binSet I ε δ) :
    ∑ w ∈ binSet I ε δ, walkStep I ε δ a x y v w = 1 := by
  have := PMF.tsum_coe (walkStep I ε δ a x y v)
  rwa [tsum_eq_sum (s := binSet I ε δ) (fun w hw => walkStep_apply_notMem I ε δ a x y v w hv hw)]
    at this

/-- INTERNAL: the bin walk `P_a` as an Arlib finite chain on `𝒱`.
TEXLINE: sections/evaluation.tex:205-213 -/
noncomputable def binKernel (a : ℕ) (x y : ℕ → ℕ) : FinChain (binSet I ε δ) where
  P v w := (walkStep I ε δ a x y v.1 w.1).toReal
  P_nonneg _ _ := ENNReal.toReal_nonneg
  P_sum v := by
    rw [Finset.sum_coe_sort (binSet I ε δ) (fun w => (walkStep I ε δ a x y v.1 w).toReal),
      ← ENNReal.toReal_sum (fun w _ => PMF.apply_ne_top _ _), walkStep_sum I ε δ a x y v.1 v.2,
      ENNReal.toReal_one]

/-- INTERNAL: the bin law `π_a = V_a / S_a` as an Arlib finite distribution on `𝒱`.
TEXLINE: sections/evaluation.tex:96-99 -/
noncomputable def binDist (a : ℕ) (x y : ℕ → ℕ) (hne : (binSet I ε δ).Nonempty) :
    FinDist (binSet I ε δ) where
  p v := binV I ε δ a x y v.1 / binS I ε δ a x y
  p_nonneg v := div_nonneg (binV_pos I ε δ a x y v.1).le (binS_pos I ε δ a x y hne).le
  p_sum := by
    rw [Finset.sum_coe_sort (binSet I ε δ) (fun w => binV I ε δ a x y w / binS I ε δ a x y),
      ← Finset.sum_div]
    exact div_self (binS_pos I ε δ a x y hne).ne'

/-- INTERNAL: `V_a(v) min{1, V_a(w)/V_a(v)} = min{V_a(v), V_a(w)}`. -/
theorem binV_mul_acc (a : ℕ) (x y v w : ℕ → ℕ) :
    binV I ε δ a x y v * (binAcc I ε δ a x y v w).toReal =
      (2 : ℝ) ^ (-(max (binExp I ε δ a x y v) (binExp I ε δ a x y w))) := by
  unfold binV binAcc
  split_ifs with h
  · rw [max_eq_left h, ENNReal.toReal_one, mul_one]
  · push Not at h
    rw [max_eq_right h.le, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      ← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_neg, ← zpow_add₀ (by norm_num)]
    congr 1; ring

/-- **The bin walk is reversible for `π_a`.**
PAPER: sections/evaluation.tex:210-212 ("The chain is reversible for `π_a`") -/
theorem binKernel_reversible (a : ℕ) (x y : ℕ → ℕ) (hne : (binSet I ε δ).Nonempty) :
    Reversible (binDist I ε δ a x y hne) (binKernel I ε δ a x y) := by
  intro v w
  by_cases hvw : v = w
  · subst hvw; rfl
  have hne' : w.1 ≠ v.1 := fun h => hvw (Subtype.ext h).symm
  show binV I ε δ a x y v.1 / binS I ε δ a x y * (walkStep I ε δ a x y v.1 w.1).toReal =
    binV I ε δ a x y w.1 / binS I ε δ a x y * (walkStep I ε δ a x y w.1 v.1).toReal
  rw [walkStep_apply_ne I ε δ a x y v.1 w.1 hne', walkStep_apply_ne I ε δ a x y w.1 v.1
    (Ne.symm hne'), binProp_card_symm I ε δ v.2 w.2]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have h1 := binV_mul_acc I ε δ a x y v.1 w.1
  have h2 := binV_mul_acc I ε δ a x y w.1 v.1
  rw [max_comm] at h2
  have key : ∀ A B C D E : ℝ, A / C * (D * B * E) = (A * B) * (D * E / C) := by
    intros; ring
  rw [key, key, h1, h2]

/-- **The bin walk is lazy**: it holds with probability at least `1/2`.
PAPER: sections/evaluation.tex:211-213 ("and is lazy, since the total probability of
directional proposals is at most `1/2`") -/
theorem walkStep_self_ge (a : ℕ) (x y v : ℕ → ℕ) :
    (1 : ℝ) / 2 ≤ (walkStep I ε δ a x y v v).toReal := by
  have h4 := four_nFree_le I ε δ
  set N := 2 ^ oKd I with hN
  have hlow : (((Finset.Ico (2 * nFree I ε δ) N).card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ oKd I)⁻¹) ≤
      walkStep I ε δ a x y v v := by
    rw [walkStep_eq, PMF.bind_apply, ← nsmul_eq_mul, ← Finset.sum_const]
    refine le_trans (Finset.sum_le_sum fun u hu => ?_) (ENNReal.sum_le_tsum (Finset.Ico (2 * nFree I ε δ) N))
    have hu' := Finset.mem_Ico.1 hu
    have hp : binProp I ε δ v u = none := by unfold binProp; rw [if_neg (by omega)]
    rw [uniformBits_apply, if_pos (by omega), hp]
    simp [binBody]
  have hfin : walkStep I ε δ a x y v v ≠ ⊤ := PMF.apply_ne_top _ _
  have := ENNReal.toReal_mono hfin hlow
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, Nat.card_Ico, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat] at this
  refine le_trans ?_ this
  have hNpos : (0 : ℝ) < 2 ^ oKd I := by positivity
  rw [Nat.cast_sub (by omega), le_mul_inv_iff₀ hNpos]
  have : ((2 * nFree I ε δ : ℕ) : ℝ) * 2 ≤ (N : ℝ) := by exact_mod_cast (by omega : _ ≤ N)
  push_cast [hN] at this ⊢
  linarith

/-- INTERNAL: the non-lazy chain `Q_a = 2P_a - I`, so that `P_a = ½(I + Q_a)` (Arlib's `lazy`).
TEXLINE: sections/evaluation.tex:313-314 ("`2P - I` is a reversible stochastic contraction") -/
noncomputable def binQ (a : ℕ) (x y : ℕ → ℕ) : FinChain (binSet I ε δ) where
  P v w := if v = w then 2 * binKernel I ε δ a x y v w - 1 else 2 * binKernel I ε δ a x y v w
  P_nonneg v w := by
    split_ifs with h
    · subst h; have := walkStep_self_ge I ε δ a x y v.1
      show 0 ≤ 2 * (walkStep I ε δ a x y v.1 v.1).toReal - 1; linarith
    · exact mul_nonneg zero_le_two ((binKernel I ε δ a x y).coe_nonneg v w)
  P_sum v := by
    have h := (binKernel I ε δ a x y).sum_coe v
    have : ∀ w, (if v = w then 2 * binKernel I ε δ a x y v w - 1 else
        2 * binKernel I ε δ a x y v w) =
        2 * binKernel I ε δ a x y v w - (if v = w then 1 else 0) := by
      intro w; split_ifs <;> ring
    rw [Finset.sum_congr rfl fun w _ => this w, Finset.sum_sub_distrib, ← Finset.mul_sum, h]
    simp; norm_num

/-- INTERNAL: `P_a` is the lazy version of `Q_a`. -/
theorem binQ_lazy (a : ℕ) (x y : ℕ → ℕ) :
    (binQ I ε δ a x y).lazy = binKernel I ε δ a x y := by
  refine finKernel_ext fun v w => ?_
  rw [FinChain.lazy_apply]
  show _ + (if v = w then 2 * binKernel I ε δ a x y v w - 1 else
    2 * binKernel I ε δ a x y v w) / 2 = _
  split_ifs <;> ring

/-- INTERNAL: `Q_a` is reversible for `π_a`. -/
theorem binQ_reversible (a : ℕ) (x y : ℕ → ℕ) (hne : (binSet I ε δ).Nonempty) :
    Reversible (binDist I ε δ a x y hne) (binQ I ε δ a x y) := by
  intro v w
  have h := binKernel_reversible I ε δ a x y hne v w
  show _ * (if v = w then _ else _) = _ * (if w = v then _ else _)
  by_cases hvw : v = w
  · subst hvw; rfl
  · rw [if_neg hvw, if_neg (Ne.symm hvw)]
    linear_combination 2 * h

/-- INTERNAL: `Q_a` has twice the cut flow of `P_a`. -/
theorem binQ_cut (a : ℕ) (x y : ℕ → ℕ) (hne : (binSet I ε δ).Nonempty)
    (A : Finset (binSet I ε δ)) :
    cut (binDist I ε δ a x y hne) (binQ I ε δ a x y) A =
      2 * cut (binDist I ε δ a x y hne) (binKernel I ε δ a x y) A := by
  rw [cut_apply, cut_apply, flow_apply, flow_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hvw : v ≠ w := fun h => (Finset.mem_compl.1 hw) (h ▸ hv)
  show _ * (if v = w then _ else _) = _
  rw [if_neg hvw]; ring

/-- INTERNAL: `t` steps of the PMF walk from a bin have the law of the `t`-th kernel power. -/
theorem loop_walkStep_apply (a : ℕ) (x y : ℕ → ℕ) (v0 : binSet I ε δ) (t : ℕ) (w : ℕ → ℕ) :
    loop (fun _ v => walkStep I ε δ a x y v) t v0.1 w =
      if h : w ∈ binSet I ε δ then
        ENNReal.ofReal (((binKernel I ε δ a x y).iter t) v0 ⟨w, h⟩) else 0 := by
  induction t generalizing w with
  | zero =>
    rw [loop_zero, PMF.pure_apply]
    split_ifs with h1 h2 h2
    · subst h1; simp [FinKernel.iter_zero, FinKernel.id]
    · exact absurd (h1 ▸ v0.2) h2
    · show 0 = ENNReal.ofReal (if v0 = ⟨w, h2⟩ then 1 else 0)
      rw [if_neg (fun h => h1 (congrArg Subtype.val h).symm), ENNReal.ofReal_zero]
    · rfl
  | succ t ih =>
    rw [loop_succ, PMF.bind_apply, tsum_eq_sum (s := binSet I ε δ) (fun u hu => by
      rw [ih u, dif_neg hu, zero_mul])]
    rw [← Finset.sum_coe_sort (binSet I ε δ)]
    simp_rw [ih, Finset.coe_mem, dif_pos]
    split_ifs with hw
    · rw [FinKernel.iter_succ', FinKernel.comp_apply,
        ENNReal.ofReal_sum_of_nonneg fun u _ =>
          mul_nonneg ((((binKernel I ε δ a x y).iter t)).coe_nonneg _ _)
            ((binKernel I ε δ a x y).coe_nonneg _ _)]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [ENNReal.ofReal_mul ((((binKernel I ε δ a x y).iter t)).coe_nonneg _ _)]
      congr 1
      show _ = ENNReal.ofReal (walkStep I ε δ a x y u.1 w).toReal
      rw [ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
    · exact Finset.sum_eq_zero fun u _ => by
        rw [walkStep_apply_notMem I ε δ a x y u.1 w u.2 hw, mul_zero]

/-- INTERNAL: `binLaw` pointwise, through `binDist`. -/
theorem binLaw_apply (a : ℕ) (x y : ℕ → ℕ) (hne : (binSet I ε δ).Nonempty) (w : ℕ → ℕ) :
    binLaw I ε δ a x y w =
      if h : w ∈ binSet I ε δ then ENNReal.ofReal (binDist I ε δ a x y hne ⟨w, h⟩) else 0 := by
  unfold binLaw
  rw [dif_pos hne, PMF.ofFinset_apply]
  split_ifs <;> rfl

/-- INTERNAL: total variation between the walk law and `π_a` bounds the `PClose` defect. -/
theorem loop_walkStep_pclose (a : ℕ) (x y : ℕ → ℕ) (hne : (binSet I ε δ).Nonempty)
    (v0 : binSet I ε δ) (t : ℕ) :
    PClose (loop (fun _ v => walkStep I ε δ a x y v) t v0.1) (binLaw I ε δ a x y)
      (ENNReal.ofReal (tvDist (((binKernel I ε δ a x y).iter t).row v0)
        (binDist I ε δ a x y hne))) := by
  set ν := ((binKernel I ε δ a x y).iter t).row v0
  set π := binDist I ε δ a x y hne
  refine PClose.of_pointwise (fun w => if h : w ∈ binSet I ε δ then
      ENNReal.ofReal (ν ⟨w, h⟩ - π ⟨w, h⟩) else 0) (fun w => ?_) ?_
  · rw [loop_walkStep_apply, binLaw_apply I ε δ a x y hne]
    split_ifs with h
    · calc ENNReal.ofReal (((binKernel I ε δ a x y).iter t) v0 ⟨w, h⟩)
          = ENNReal.ofReal (π ⟨w, h⟩ + (ν ⟨w, h⟩ - π ⟨w, h⟩)) := by
            congr 1; simp only [ν, FinKernel.row_apply]; ring
        _ ≤ _ := ENNReal.ofReal_add_le
    · simp
  · rw [tsum_eq_sum (s := binSet I ε δ) (fun w hw => dif_neg hw),
      ← Finset.sum_coe_sort (binSet I ε δ)]
    simp_rw [Finset.coe_mem, dif_pos]
    rw [tvDist_eq_sum_posPart, ENNReal.ofReal_sum_of_nonneg fun _ _ => le_max_right _ _]
    refine Finset.sum_le_sum fun w _ => ?_
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)

/-- INTERNAL: the penalty is nonnegative.
TEXLINE: sections/evaluation.tex:46-51 -/
theorem binPenalty_nonneg (x y : ℕ → ℕ) (z : ℕ → ℚ) : 0 ≤ penalty I ε δ x y z := by
  unfold penalty
  apply mul_nonneg (by positivity)
  apply add_nonneg
  · apply List.sum_nonneg
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨v, -, rfl⟩ := hc
    exact abs_nonneg _
  · exact Finset.sum_nonneg fun t _ => div_nonneg (by unfold boxDist; split_ifs <;> linarith)
      (by positivity)

/-- INTERNAL: `⌊aD/H⌋ ≥ 0`, so `V_a ≤ 1`. -/
theorem binExp_nonneg (a : ℕ) (x y v : ℕ → ℕ) : 0 ≤ binExp I ε δ a x y v := by
  unfold binExp levelExp
  exact Int.floor_nonneg.2 (div_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (binPenalty_nonneg I ε δ x y _)) (Nat.cast_nonneg _))

/-- INTERNAL: `V_a ≤ 1`. -/
theorem binV_le_one (a : ℕ) (x y v : ℕ → ℕ) : binV I ε δ a x y v ≤ 1 := by
  unfold binV
  exact zpow_le_one_of_nonpos₀ (by norm_num) (by linarith [binExp_nonneg I ε δ a x y v])

/-- INTERNAL: `|𝒱| ≤ B^e`. -/
theorem binSet_card_le : (binSet I ε δ).card ≤ BParam I ε δ ^ nFree I ε δ := by
  unfold binSet
  refine Finset.card_image_le.trans ?_
  simp

/-- INTERNAL: the walk's starting bin `0` is a bin. -/
theorem zero_mem_binSet (hε : 0 < ε) : (fun _ => 0 : ℕ → ℕ) ∈ binSet I ε δ := by
  have hA := AParam_pos I ε δ hε
  have hd := dParam_ge I
  rw [mem_binSet_iff]
  refine ⟨fun k _ => ?_, fun _ _ => rfl⟩
  unfold BParam; positivity

/-- INTERNAL: `V_a(0) ≥ 2^{-H}`, from `D ≤ H` and `a ≤ H`.
TEXLINE: sections/evaluation.tex:314-315 ("Since `2^{-H} ≤ V_a ≤ 1`") -/
theorem binExp_zero_le (hε : 0 < ε) (hfeas : feasible I) (a : ℕ) (ha : a ≤ HParam I ε δ)
    (x y : ℕ → ℕ)
    (hbox : ∀ s < nSmall I ε δ, x s ≤ smallB I ε δ s ∧ y s ≤ smallB I ε δ s) :
    binExp I ε δ a x y (fun _ => 0) ≤ HParam I ε δ := by
  have hD := pseudo_penalty_le_H I ε δ hε hfeas x y (binPoint I ε δ fun _ => 0)
    (fun k hk => hbox k hk) (fun k _ => by simp [binPoint]; positivity)
  have hD0 := binPenalty_nonneg I ε δ x y (binPoint I ε δ fun _ => 0)
  unfold binExp levelExp
  rcases Nat.eq_zero_or_pos (HParam I ε δ) with hH | hH
  · rw [hH]; simp
  have hHq : (0 : ℚ) < HParam I ε δ := by exact_mod_cast hH
  have h1 : (a : ℚ) * penalty I ε δ x y (binPoint I ε δ fun _ => 0) / HParam I ε δ ≤ a := by
    rw [div_le_iff₀ hHq]
    exact mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg _)
  have h2 : (a : ℚ) ≤ HParam I ε δ := by exact_mod_cast ha
  have := Int.floor_le_floor (h1.trans h2)
  rw [Int.floor_natCast] at this
  exact this

/-- INTERNAL: `π_a(0)^{-1} ≤ 2^H B^e`.
TEXLINE: sections/evaluation.tex:314-315 -/
theorem binDist_zero_inv_le (hε : 0 < ε) (hfeas : feasible I) (a : ℕ) (ha : a ≤ HParam I ε δ)
    (x y : ℕ → ℕ)
    (hbox : ∀ s < nSmall I ε δ, x s ≤ smallB I ε δ s ∧ y s ≤ smallB I ε δ s)
    (hne : (binSet I ε δ).Nonempty) :
    (binDist I ε δ a x y hne ⟨fun _ => 0, zero_mem_binSet I ε δ hε⟩)⁻¹ ≤
      (2 : ℝ) ^ HParam I ε δ * (BParam I ε δ : ℝ) ^ nFree I ε δ := by
  show (binV I ε δ a x y (fun _ => 0) / binS I ε δ a x y)⁻¹ ≤ _
  have hS := binS_pos I ε δ a x y hne
  have hV := binV_pos I ε δ a x y (fun _ => 0)
  rw [inv_div, div_le_iff₀ hV]
  have hSle : binS I ε δ a x y ≤ (BParam I ε δ : ℝ) ^ nFree I ε δ := by
    unfold binS
    calc ∑ v ∈ binSet I ε δ, binV I ε δ a x y v ≤ ∑ v ∈ binSet I ε δ, (1 : ℝ) :=
          Finset.sum_le_sum fun v _ => binV_le_one I ε δ a x y v
      _ = (binSet I ε δ).card := by simp
      _ ≤ _ := by exact_mod_cast binSet_card_le I ε δ
  have hVge : (2 : ℝ) ^ (-(HParam I ε δ : ℤ)) ≤ binV I ε δ a x y (fun _ => 0) := by
    unfold binV
    exact zpow_le_zpow_right₀ (by norm_num)
      (neg_le_neg (binExp_zero_le I ε δ hε hfeas a ha x y hbox))
  have h2 : (1 : ℝ) ≤ 2 ^ HParam I ε δ * binV I ε δ a x y (fun _ => 0) := by
    have := mul_le_mul_of_nonneg_left hVge (by positivity : (0 : ℝ) ≤ 2 ^ HParam I ε δ)
    rwa [zpow_neg, zpow_natCast, mul_inv_cancel₀ (by positivity)] at this
  calc binS I ε δ a x y ≤ (BParam I ε δ : ℝ) ^ nFree I ε δ := hSle
    _ ≤ (BParam I ε δ : ℝ) ^ nFree I ε δ * (2 ^ HParam I ε δ * binV I ε δ a x y (fun _ => 0)) :=
        le_mul_of_one_le_right (by positivity) h2
    _ = _ := by ring

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · chain bridge for `sampleBin_close`, no `sorry`
-/
