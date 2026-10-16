import Mathlib

/-!
# Pointwise relative mixing of a lazy reversible chain from a Poincaré inequality

The spectral half of `lem:trace` (`transport.tex:647-760`), stated for an abstract finite
chain: a kernel `r` on a finite set `A`, stochastic, reversible with respect to a law `μ`
on `A`, with holding probability at least `1/2`.  If `Var_μ(h) ≤ K 𝓔(h)` for every `h`,
then for every `t`

`r^{2t}(x, y) ≤ μ(y) (1 + (1 - 1/K)^{2t} / m)`, where `m ≤ μ` on `A`.

The paper's route is the spectral decomposition of the self-adjoint operator; here it is
replaced by an elementary `L²(μ)` argument with no spectral theorem: laziness gives
`‖T f‖² ≤ ⟨f, T f⟩` (`kerOp_norm_le`), the Poincaré inequality gives
`⟨f, T f⟩ ≤ c ‖f‖²` on mean-zero `f` with `c = 1 - 1/K` (`kerOp_form_le`), and positivity
of `⟨g, T g⟩` at `g = c f - T f` upgrades this to `‖T f‖ ≤ c ‖f‖` (`kerOp_contract`).
Finally `r^{2t}(x, y)/μ(y) - 1 = ⟨T^t e_x, T^t e_y⟩` with `‖e_x‖² ≤ 1/μ(x)`.
-/

namespace Cellcounting.Analysis

open Finset

section LazyMixing

set_option linter.unusedSectionVars false

variable {β : Type*} [DecidableEq β]

/-- INTERNAL: the averaging operator `(T f)(x) = Σ_{y ∈ A} r(x, y) f(y)` of a kernel on `A`.
TEXLINE: sections/transport.tex:700-735 -/
noncomputable def kerOp (A : Finset β) (r : β → β → ℝ) : Module.End ℝ (β → ℝ) where
  toFun f x := ∑ y ∈ A, r x y * f y
  map_add' f g := by
    funext x
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring

/-- INTERNAL: the `L²(μ)` inner product on `A`. -/
noncomputable def wip (A : Finset β) (μ : β → ℝ) (f g : β → ℝ) : ℝ :=
  ∑ x ∈ A, μ x * f x * g x

/-- INTERNAL: a finite stochastic kernel on `A`, reversible with respect to the law `μ`,
with holding probability at least `1/2`.
TEXLINE: sections/transport.tex:672-676 -/
structure LazyRev (A : Finset β) (μ : β → ℝ) (r : β → β → ℝ) : Prop where
  μ_pos : ∀ x ∈ A, 0 < μ x
  μ_sum : ∑ x ∈ A, μ x = 1
  r_nonneg : ∀ x ∈ A, ∀ y ∈ A, 0 ≤ r x y
  stoch : ∀ x ∈ A, ∑ y ∈ A, r x y = 1
  rev : ∀ x ∈ A, ∀ y ∈ A, μ x * r x y = μ y * r y x
  lazy : ∀ x ∈ A, 1 / 2 ≤ r x x

theorem kerOp_apply (A : Finset β) (r : β → β → ℝ) (f : β → ℝ) (x : β) :
    kerOp A r f x = ∑ y ∈ A, r x y * f y := rfl

theorem kerOp_pow_succ (A : Finset β) (r : β → β → ℝ) (s : ℕ) (f : β → ℝ) :
    (kerOp A r ^ (s + 1)) f = kerOp A r ((kerOp A r ^ s) f) := by
  rw [pow_succ']; rfl

theorem wip_comm (A : Finset β) (μ : β → ℝ) (f g : β → ℝ) : wip A μ f g = wip A μ g f := by
  unfold wip; exact Finset.sum_congr rfl fun x _ => by ring

theorem wip_add_left (A : Finset β) (μ : β → ℝ) (f g h : β → ℝ) :
    wip A μ (f + g) h = wip A μ f h + wip A μ g h := by
  unfold wip; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by simp only [Pi.add_apply]; ring

theorem wip_add_right (A : Finset β) (μ : β → ℝ) (f g h : β → ℝ) :
    wip A μ f (g + h) = wip A μ f g + wip A μ f h := by
  rw [wip_comm, wip_add_left, wip_comm A μ g, wip_comm A μ h]

theorem wip_congr_right (A : Finset β) (μ : β → ℝ) (f g g' : β → ℝ)
    (h : ∀ x ∈ A, g x = g' x) : wip A μ f g = wip A μ f g' := by
  unfold wip; exact Finset.sum_congr rfl fun x hx => by rw [h x hx]

/-- INTERNAL: `T` is self-adjoint in `L²(μ)` (reversibility). -/
theorem wip_kerOp (A : Finset β) (μ : β → ℝ) (r : β → β → ℝ)
    (hrev : ∀ x ∈ A, ∀ y ∈ A, μ x * r x y = μ y * r y x) (f g : β → ℝ) :
    wip A μ f (kerOp A r g) = wip A μ (kerOp A r f) g := by
  unfold wip
  simp only [kerOp_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := A) (t := A) (f := fun x y => μ x * (r x y * f y) * g x)]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  linear_combination (f x * g y) * hrev x hx y hy

theorem wip_kerOp_pow (A : Finset β) (μ : β → ℝ) (r : β → β → ℝ)
    (hrev : ∀ x ∈ A, ∀ y ∈ A, μ x * r x y = μ y * r y x) (s : ℕ) (f g : β → ℝ) :
    wip A μ f ((kerOp A r ^ s) g) = wip A μ ((kerOp A r ^ s) f) g := by
  induction s generalizing f g with
  | zero => rfl
  | succ s ih =>
    rw [kerOp_pow_succ, wip_kerOp A μ r hrev, ih, pow_succ, Module.End.mul_apply]

variable {A : Finset β} {μ : β → ℝ} {r : β → β → ℝ}

theorem LazyRev.kerOp_pow_one (hC : LazyRev A μ r) (s : ℕ) :
    ∀ x ∈ A, (kerOp A r ^ s) (fun _ => 1) x = 1 := by
  induction s with
  | zero => intro x _; rfl
  | succ s ih =>
    intro x hx
    rw [kerOp_pow_succ, kerOp_apply, Finset.sum_congr rfl fun y hy => by rw [ih y hy, mul_one]]
    exact hC.stoch x hx

theorem LazyRev.wip_one_pow (hC : LazyRev A μ r) (s : ℕ) (f : β → ℝ) :
    wip A μ (fun _ => 1) ((kerOp A r ^ s) f) = wip A μ (fun _ => 1) f := by
  rw [wip_kerOp_pow A μ r hC.rev, wip_comm, wip_comm A μ _ f]
  exact wip_congr_right A μ f _ _ (hC.kerOp_pow_one s)

theorem LazyRev.kerOp_pow_nonneg (hC : LazyRev A μ r) (s : ℕ) (f : β → ℝ)
    (hf : ∀ x ∈ A, 0 ≤ f x) : ∀ x ∈ A, 0 ≤ (kerOp A r ^ s) f x := by
  induction s with
  | zero => exact hf
  | succ s ih =>
    intro x hx
    rw [kerOp_pow_succ, kerOp_apply]
    exact Finset.sum_nonneg fun y hy => mul_nonneg (hC.r_nonneg x hx y hy) (ih y hy)

/-- INTERNAL: laziness makes `T` a positive contraction: `‖T f‖² ≤ ⟨f, T f⟩`.
TEXLINE: sections/transport.tex:612-616 -/
theorem LazyRev.kerOp_norm_le (hC : LazyRev A μ r) (f : β → ℝ) :
    wip A μ (kerOp A r f) (kerOp A r f) ≤ wip A μ f (kerOp A r f) := by
  -- pointwise: `2 (T f)(x)² ≤ (T f²)(x) + 2 f(x) (T f)(x) - f(x)²`
  have hpt : ∀ x ∈ A, 2 * (kerOp A r f x) ^ 2 ≤
      kerOp A r (fun y => f y ^ 2) x + 2 * f x * kerOp A r f x - f x ^ 2 := by
    intro x hx
    set c := kerOp A r f x with hc
    set a := 2 * c - f x
    have hsum : ∑ y ∈ A, r x y * (f y - a) ^ 2 =
        kerOp A r (fun y => f y ^ 2) x - 2 * a * c + a ^ 2 := by
      have : ∀ y ∈ A, r x y * (f y - a) ^ 2 =
          r x y * f y ^ 2 - 2 * a * (r x y * f y) + a ^ 2 * r x y := fun y _ => by ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, hC.stoch x hx, hc, kerOp_apply, kerOp_apply]
      ring
    have hge : r x x * (f x - a) ^ 2 ≤ ∑ y ∈ A, r x y * (f y - a) ^ 2 := by
      rw [← Finset.add_sum_erase A _ hx]
      have : 0 ≤ ∑ y ∈ A.erase x, r x y * (f y - a) ^ 2 :=
        Finset.sum_nonneg fun y hy =>
          mul_nonneg (hC.r_nonneg x hx y (Finset.mem_of_mem_erase hy)) (sq_nonneg _)
      linarith
    have hl : (1 / 2) * (f x - a) ^ 2 ≤ r x x * (f x - a) ^ 2 :=
      mul_le_mul_of_nonneg_right (hC.lazy x hx) (sq_nonneg _)
    nlinarith
  have hF2 : wip A μ (fun _ => 1) (kerOp A r (fun y => f y ^ 2)) = wip A μ f f := by
    have := hC.wip_one_pow 1 (fun y => f y ^ 2)
    rw [pow_one] at this
    rw [this]; unfold wip; exact Finset.sum_congr rfl fun x _ => by ring
  have hsum : 2 * wip A μ (kerOp A r f) (kerOp A r f) ≤
      wip A μ (fun _ => 1) (kerOp A r (fun y => f y ^ 2)) + 2 * wip A μ f (kerOp A r f) -
        wip A μ f f := by
    unfold wip
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun x hx => ?_
    have := mul_le_mul_of_nonneg_left (hpt x hx) (hC.μ_pos x hx).le
    nlinarith
  rw [hF2] at hsum
  linarith

/-- INTERNAL: on mean-zero functions, `⟨f, T f⟩ ≤ (1 - 1/K) ‖f‖²`, given the Poincaré
inequality `Var_μ ≤ K 𝓔`.
TEXLINE: sections/transport.tex:735-745 -/
theorem LazyRev.kerOp_form_le (_hC : LazyRev A μ r) (K : ℝ) (hK : 1 ≤ K)
    (hP : ∀ h : β → ℝ, ∑ x ∈ A, μ x * (h x - ∑ y ∈ A, μ y * h y) ^ 2 ≤
      K * ∑ x ∈ A, μ x * h x * (h x - ∑ y ∈ A, r x y * h y))
    (f : β → ℝ) (hf : wip A μ (fun _ => 1) f = 0) :
    wip A μ f (kerOp A r f) ≤ (1 - 1 / K) * wip A μ f f := by
  have hmean : ∑ y ∈ A, μ y * f y = 0 := by
    rw [← hf]; unfold wip; exact Finset.sum_congr rfl fun x _ => by ring
  have h1 := hP f
  rw [hmean] at h1
  have hL : ∑ x ∈ A, μ x * (f x - 0) ^ 2 = wip A μ f f := by
    unfold wip; exact Finset.sum_congr rfl fun x _ => by ring
  have hR : ∑ x ∈ A, μ x * f x * (f x - ∑ y ∈ A, r x y * f y) =
      wip A μ f f - wip A μ f (kerOp A r f) := by
    unfold wip; rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [kerOp_apply]; ring
  rw [hL, hR] at h1
  have hK0 : 0 < K := by linarith
  have : wip A μ f f / K ≤ wip A μ f f - wip A μ f (kerOp A r f) := by
    rw [div_le_iff₀ hK0]; linarith
  have e : (1 - 1 / K) * wip A μ f f = wip A μ f f - wip A μ f f / K := by ring
  linarith

/-- INTERNAL: on mean-zero functions, `‖T f‖² ≤ (1 - 1/K)² ‖f‖²`.  With `c = 1 - 1/K`,
positivity of `⟨g, T g⟩` at `g = c f - T f` gives `‖T f‖² ≤ c ⟨f, T f⟩` (no spectral
theorem needed).
TEXLINE: sections/transport.tex:747-756 -/
theorem LazyRev.kerOp_contract (hC : LazyRev A μ r) (K : ℝ) (hK : 1 ≤ K)
    (hP : ∀ h : β → ℝ, ∑ x ∈ A, μ x * (h x - ∑ y ∈ A, μ y * h y) ^ 2 ≤
      K * ∑ x ∈ A, μ x * h x * (h x - ∑ y ∈ A, r x y * h y))
    (f : β → ℝ) (hf : wip A μ (fun _ => 1) f = 0) :
    wip A μ (kerOp A r f) (kerOp A r f) ≤ (1 - 1 / K) ^ 2 * wip A μ f f := by
  set c := 1 - 1 / K with hc
  have hc0 : 0 ≤ c := by rw [hc, sub_nonneg, div_le_one (by linarith)]; exact hK
  have hTf : wip A μ (fun _ => 1) (kerOp A r f) = 0 := by
    have := hC.wip_one_pow 1 f; rw [pow_one] at this; rw [this, hf]
  have h1 := hC.kerOp_form_le K hK hP f hf
  rw [← hc] at h1
  have h2 := hC.kerOp_form_le K hK hP (kerOp A r f) hTf
  have h3 := hC.kerOp_norm_le f
  have hsym : wip A μ f (kerOp A r (kerOp A r f)) = wip A μ (kerOp A r f) (kerOp A r f) := wip_kerOp A μ r hC.rev f (kerOp A r f)
  -- positivity of the form at `g = c f - T f`
  have hg := (hC.kerOp_norm_le (c • f - kerOp A r f))
  have hsq : 0 ≤ wip A μ (kerOp A r (c • f - kerOp A r f)) (kerOp A r (c • f - kerOp A r f)) := by
    unfold wip
    exact Finset.sum_nonneg fun x hx => by
      rw [mul_assoc]; exact mul_nonneg (hC.μ_pos x hx).le (mul_self_nonneg _)
  have hexp : wip A μ (c • f - kerOp A r f) (kerOp A r (c • f - kerOp A r f)) =
      c ^ 2 * wip A μ f (kerOp A r f) - c * wip A μ f (kerOp A r (kerOp A r f)) - c * wip A μ (kerOp A r f) (kerOp A r f) +
        wip A μ (kerOp A r f) (kerOp A r (kerOp A r f)) := by
    rw [map_sub, map_smul]
    unfold wip
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hpos : 0 ≤ c ^ 2 * wip A μ f (kerOp A r f) - c * wip A μ (kerOp A r f) (kerOp A r f) := by
    have := hc0
    nlinarith
  have hff : 0 ≤ wip A μ f f := by
    unfold wip
    exact Finset.sum_nonneg fun x hx => by
      rw [mul_assoc]; exact mul_nonneg (hC.μ_pos x hx).le (mul_self_nonneg _)
  rcases hc0.lt_or_eq with hcpos | hczero
  · have : wip A μ (kerOp A r f) (kerOp A r f) ≤ c * wip A μ f (kerOp A r f) := by
      by_contra hcon
      push Not at hcon
      nlinarith
    calc _ ≤ c * wip A μ f (kerOp A r f) := this
      _ ≤ c * (c * wip A μ f f) := mul_le_mul_of_nonneg_left h1 hc0
      _ = _ := by ring
  · rw [← hczero] at h1 ⊢
    simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h1 ⊢
    linarith

theorem LazyRev.kerOp_pow_contract (hC : LazyRev A μ r) (K : ℝ) (hK : 1 ≤ K)
    (hP : ∀ h : β → ℝ, ∑ x ∈ A, μ x * (h x - ∑ y ∈ A, μ y * h y) ^ 2 ≤
      K * ∑ x ∈ A, μ x * h x * (h x - ∑ y ∈ A, r x y * h y))
    (f : β → ℝ) (hf : wip A μ (fun _ => 1) f = 0) (t : ℕ) :
    wip A μ ((kerOp A r ^ t) f) ((kerOp A r ^ t) f) ≤ ((1 - 1 / K) ^ 2) ^ t * wip A μ f f := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [kerOp_pow_succ]
    have hmean : wip A μ (fun _ => 1) ((kerOp A r ^ t) f) = 0 := by
      rw [hC.wip_one_pow, hf]
    have h := hC.kerOp_contract K hK hP _ hmean
    have hK' : 0 ≤ (1 - 1 / K) ^ 2 := sq_nonneg _
    calc _ ≤ (1 - 1 / K) ^ 2 * wip A μ ((kerOp A r ^ t) f) ((kerOp A r ^ t) f) := h
      _ ≤ (1 - 1 / K) ^ 2 * (((1 - 1 / K) ^ 2) ^ t * wip A μ f f) :=
          mul_le_mul_of_nonneg_left ih hK'
      _ = _ := by ring

theorem wip_le_half (A : Finset β) (μ : β → ℝ) (hμ : ∀ x ∈ A, 0 ≤ μ x) (f g : β → ℝ) :
    wip A μ f g ≤ (wip A μ f f + wip A μ g g) / 2 := by
  unfold wip
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_le_sum fun x hx => ?_
  have := mul_nonneg (hμ x hx) (sq_nonneg (f x - g x))
  nlinarith

/-- INTERNAL: **pointwise relative mixing** of a lazy reversible chain: after `2t` steps
the transition probability to `y` is at most `μ(y) (1 + (1 - 1/K)^{2t} / m)`, when
`Var_μ ≤ K 𝓔` and `m ≤ μ` on `A`.
TEXLINE: sections/transport.tex:747-756 -/
theorem LazyRev.pow_le (hC : LazyRev A μ r) (K : ℝ) (hK : 1 ≤ K)
    (hP : ∀ h : β → ℝ, ∑ x ∈ A, μ x * (h x - ∑ y ∈ A, μ y * h y) ^ 2 ≤
      K * ∑ x ∈ A, μ x * h x * (h x - ∑ y ∈ A, r x y * h y))
    (m : ℝ) (hm : 0 < m) (hμm : ∀ x ∈ A, m ≤ μ x) (t : ℕ) (x y : β) (hx : x ∈ A)
    (hy : y ∈ A) :
    (kerOp A r ^ (2 * t)) (fun z => if z = y then 1 else 0) x ≤
      μ y * (1 + (1 - 1 / K) ^ (2 * t) / m) := by
  have hμ0 : ∀ z ∈ A, 0 ≤ μ z := fun z hz => (hC.μ_pos z hz).le
  set e : β → β → ℝ := fun u z => (if z = u then 1 / μ u else 0) - 1 with he
  set one : β → ℝ := fun _ => 1
  -- the point evaluation at `x` as an inner product
  have heval : ∀ g : β → ℝ, g x = wip A μ (one + e x) g := by
    intro g
    unfold wip
    rw [Finset.sum_eq_single x]
    · simp only [he, one, Pi.add_apply, ite_true]
      field_simp [(hC.μ_pos x hx).ne']
      ring
    · intro z _ hzx
      simp [he, one, hzx]
    · intro h; exact absurd hx h
  have hind : (fun z => if z = y then (1 : ℝ) else 0) = μ y • (one + e y) := by
    funext z
    simp only [he, one, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    split_ifs with h
    · field_simp [(hC.μ_pos y hy).ne']; ring
    · ring
  have hmean : ∀ u ∈ A, wip A μ one (e u) = 0 := by
    intro u hu
    unfold wip
    simp only [he, one, mul_one, mul_sub, Finset.sum_sub_distrib, hC.μ_sum]
    rw [Finset.sum_eq_single u]
    · simp [(hC.μ_pos u hu).ne']
    · intro z _ hzu; simp [hzu]
    · intro h; exact absurd hu h
  have hnorm : ∀ u ∈ A, wip A μ (e u) (e u) ≤ 1 / m := by
    intro u hu
    have hval : wip A μ (e u) (e u) = 1 / μ u - 1 := by
      have : wip A μ (e u) (e u) = ∑ z ∈ A, μ z * (if z = u then 1 / μ u else 0) ^ 2 -
          2 * wip A μ one (e u) - ∑ z ∈ A, μ z := by
        unfold wip
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun z _ => by simp only [he, one]; ring
      rw [this, hmean u hu, hC.μ_sum, Finset.sum_eq_single u]
      · simp only [ite_true]; field_simp [(hC.μ_pos u hu).ne']; ring
      · intro z _ hzu; simp [hzu]
      · intro h; exact absurd hu h
    rw [hval]
    have : 1 / μ u ≤ 1 / m := one_div_le_one_div_of_le hm (hμm u hu)
    linarith
  set T := kerOp A r
  have hK0 : 0 ≤ ((1 - 1 / K) ^ 2) ^ t := pow_nonneg (sq_nonneg _) t
  rw [hind, map_smul, Pi.smul_apply, smul_eq_mul, heval ((T ^ (2 * t)) (one + e y)), map_add,
    wip_add_left,
    wip_add_right, wip_add_right]
  have h1 : wip A μ one ((T ^ (2 * t)) one) = 1 := by
    rw [hC.wip_one_pow]; unfold wip; simpa [one] using hC.μ_sum
  have h2 : wip A μ one ((T ^ (2 * t)) (e y)) = 0 := by rw [hC.wip_one_pow, hmean y hy]
  have h3 : wip A μ (e x) ((T ^ (2 * t)) one) = 0 := by
    rw [wip_congr_right A μ _ _ one (hC.kerOp_pow_one (2 * t)), wip_comm, hmean x hx]
  have h4 : wip A μ (e x) ((T ^ (2 * t)) (e y)) ≤ (1 - 1 / K) ^ (2 * t) / m := by
    rw [show (1 - 1 / K) ^ (2 * t) = ((1 - 1 / K) ^ 2) ^ t from pow_mul _ 2 t]
    rw [two_mul, pow_add, Module.End.mul_apply, wip_kerOp_pow A μ r hC.rev]
    refine (wip_le_half A μ hμ0 _ _).trans ?_
    have hx' := hC.kerOp_pow_contract K hK hP (e x) (hmean x hx) t
    have hy' := hC.kerOp_pow_contract K hK hP (e y) (hmean y hy) t
    have := mul_le_mul_of_nonneg_left (hnorm x hx) hK0
    have := mul_le_mul_of_nonneg_left (hnorm y hy) hK0
    have : ((1 - 1 / K) ^ 2) ^ t * (1 / m) = ((1 - 1 / K) ^ 2) ^ t / m := by ring
    linarith
  rw [h1, h2, h3]
  have hμy := hμ0 y hy
  nlinarith

end LazyMixing

end Cellcounting.Analysis
