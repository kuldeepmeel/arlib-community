import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/-!
# Autocovariances of a finite lazy reversible chain (`lem:time-average`, spectral step)

An abstract finite chain: a state set `X`, weights `π ≥ 0` and a kernel `P ≥ 0` on
`X` with unit row sums, detailed balance `π(S) P(S, S') = π(S') P(S', S)` and
laziness `P(S, S) ≥ 1/2`.  With `(P f)(S) = Σ_{S' ∈ X} P(S, S') f(S')` (`lraOp`) and
`⟨f, g⟩_π = Σ_X π f g` (`lraInner`):

* `P` is self-adjoint in `⟨·,·⟩_π`, and so is every power `P^t`;
* `⟨f, P f⟩_π ≥ 0` (laziness), hence every autocovariance `c_t = ⟨f, P^t f⟩_π ≥ 0`;
* `lra_autocov_sum_le`: if `⟨f, g⟩_π² ≤ A 𝓔(g)` for every `g`, where
  `𝓔(g) = ⟨g, (I - P) g⟩_π`, then `Σ_{t<n} c_t ≤ A` for every `n`.

The last item is the step of `transport.tex:600-614` that bounds
`a = ⟨G_c, (I - P)^{-1} G_c⟩_π` by `K_obs Var_π(G)`.  The paper takes
`g = (I - P)^{-1} G_c` on the mean-zero subspace and sums the whole series via the
spectral decomposition.  Here `g` is the truncated Neumann sum
`h_n = Σ_{t<n} P^t f`, so no inverse and no spectral theorem is needed: since
`(I - P) h_n = f - P^n f` and `⟨h_n, P^n f⟩_π = Σ_{t<n} c_{t+n} ≥ 0`, we get
`𝓔(h_n) ≤ ⟨f, h_n⟩_π = Σ_{t<n} c_t`, and `a_n² ≤ A a_n` gives `a_n ≤ A`.
-/

namespace Cellcounting.Analysis

open Finset

variable {α : Type*} (X : Finset α) (π : α → ℝ) (P : α → α → ℝ)

/-- INTERNAL: the Markov operator `(P f)(S) = Σ_{S' ∈ X} P(S, S') f(S')`.
TEXLINE: sections/transport.tex:86-96 -/
noncomputable def lraOp (f : α → ℝ) (S : α) : ℝ := ∑ S' ∈ X, P S S' * f S'

/-- INTERNAL: the inner product `⟨f, g⟩_π = Σ_{S ∈ X} π(S) f(S) g(S)`.
TEXLINE: sections/transport.tex:86-96 -/
noncomputable def lraInner (f g : α → ℝ) : ℝ := ∑ S ∈ X, π S * f S * g S

/-- INTERNAL: the energy `𝓔(g) = ⟨g, (I - P) g⟩_π`.
TEXLINE: sections/transport.tex:86-96 -/
noncomputable def lraEnergy (g : α → ℝ) : ℝ :=
  ∑ S ∈ X, π S * g S * (g S - ∑ S' ∈ X, P S S' * g S')

variable {X π P}

theorem lraInner_comm (f g : α → ℝ) : lraInner X π f g = lraInner X π g f := by
  unfold lraInner; exact sum_congr rfl fun S _ => by ring

/-- INTERNAL: `P` is self-adjoint in `⟨·,·⟩_π` under detailed balance. -/
theorem lra_inner_op_symm (hrev : ∀ S ∈ X, ∀ S' ∈ X, π S * P S S' = π S' * P S' S)
    (f g : α → ℝ) : lraInner X π f (lraOp X P g) = lraInner X π (lraOp X P f) g := by
  unfold lraInner lraOp
  simp_rw [mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun S hS => sum_congr rfl fun S' hS' => ?_
  have := hrev S' hS' S hS
  calc π S' * f S' * (P S' S * g S) = (π S' * P S' S) * f S' * g S := by ring
    _ = (π S * P S S') * f S' * g S := by rw [this]
    _ = π S * (P S S' * f S') * g S := by ring

/-- INTERNAL: every power `P^t` is self-adjoint in `⟨·,·⟩_π`. -/
theorem lra_inner_iter_symm (hrev : ∀ S ∈ X, ∀ S' ∈ X, π S * P S S' = π S' * P S' S)
    (t : ℕ) (f g : α → ℝ) :
    lraInner X π f ((lraOp X P)^[t] g) = lraInner X π ((lraOp X P)^[t] f) g := by
  induction t generalizing f g with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply, ih, lra_inner_op_symm hrev,
      ← Function.iterate_succ_apply' (lraOp X P)]

/-- INTERNAL: `Σ_{S ∈ X} π(S) P(S, S') = π(S')`. -/
theorem lra_col (hrev : ∀ S ∈ X, ∀ S' ∈ X, π S * P S S' = π S' * P S' S)
    (hrow : ∀ S ∈ X, ∑ S' ∈ X, P S S' = 1) (S' : α) (hS' : S' ∈ X) :
    ∑ S ∈ X, π S * P S S' = π S' := by
  rw [sum_congr rfl fun S hS => hrev S hS S' hS', ← mul_sum, hrow S' hS', mul_one]

/-- INTERNAL: stationarity of `π`: `Σ_X π (P g) = Σ_X π g`. -/
theorem lra_stat (hrev : ∀ S ∈ X, ∀ S' ∈ X, π S * P S S' = π S' * P S' S)
    (hrow : ∀ S ∈ X, ∑ S' ∈ X, P S S' = 1) (g : α → ℝ) :
    ∑ S ∈ X, π S * lraOp X P g S = ∑ S ∈ X, π S * g S := by
  unfold lraOp
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun S' hS' => ?_
  rw [← lra_col hrev hrow S' hS', sum_mul]
  exact sum_congr rfl fun _ _ => by ring

/-- INTERNAL: stationarity of `π` under every power `P^t`. -/
theorem lra_stat_iter (hrev : ∀ S ∈ X, ∀ S' ∈ X, π S * P S S' = π S' * P S' S)
    (hrow : ∀ S ∈ X, ∑ S' ∈ X, P S S' = 1) (t : ℕ) (g : α → ℝ) :
    ∑ S ∈ X, π S * (lraOp X P)^[t] g S = ∑ S ∈ X, π S * g S := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', lra_stat hrev hrow, ih]

/-- INTERNAL: laziness makes `P` positive semidefinite: `⟨f, P f⟩_π ≥ 0`.
TEXLINE: sections/transport.tex:616-621 -/
theorem lra_inner_op_nonneg (hπ : ∀ S ∈ X, 0 ≤ π S) (hP0 : ∀ S ∈ X, ∀ S' ∈ X, 0 ≤ P S S')
    (hrow : ∀ S ∈ X, ∑ S' ∈ X, P S S' = 1)
    (hrev : ∀ S ∈ X, ∀ S' ∈ X, π S * P S S' = π S' * P S' S)
    (hlazy : ∀ S ∈ X, 1 / 2 ≤ P S S) [DecidableEq α] (f : α → ℝ) :
    0 ≤ lraInner X π f (lraOp X P f) := by
  have hexp : lraInner X π f (lraOp X P f) =
      ∑ S ∈ X, ∑ S' ∈ X, π S * P S S' * f S * f S' := by
    unfold lraInner lraOp
    refine sum_congr rfl fun S _ => ?_
    rw [mul_sum]; exact sum_congr rfl fun S' _ => by ring
  -- pointwise: the term exceeds `-πP (f S² + f S'²)/2`, by `2 π P f²` on the diagonal
  have hpt : ∀ S ∈ X, ∀ S' ∈ X, π S * P S S' * f S * f S' ≥
      -(π S * P S S' * (f S ^ 2 + f S' ^ 2)) / 2 +
        (if S = S' then 2 * (π S * P S S * f S ^ 2) else 0) := by
    intro S hS S' hS'
    have hπP : 0 ≤ π S * P S S' := mul_nonneg (hπ S hS) (hP0 S hS S' hS')
    split_ifs with h
    · subst h; nlinarith
    · nlinarith [mul_nonneg hπP (sq_nonneg (f S + f S'))]
  have hsum := sum_le_sum fun S hS => sum_le_sum fun S' hS' => hpt S hS S' hS'
  have hA : ∑ S ∈ X, ∑ S' ∈ X, -(π S * P S S' * (f S ^ 2 + f S' ^ 2)) / 2 =
      -(∑ S ∈ X, π S * f S ^ 2) := by
    have h1 : ∑ S ∈ X, ∑ S' ∈ X, π S * P S S' * f S ^ 2 = ∑ S ∈ X, π S * f S ^ 2 := by
      refine sum_congr rfl fun S hS => ?_
      rw [← sum_mul, ← mul_sum, hrow S hS, mul_one]
    have h2 : ∑ S ∈ X, ∑ S' ∈ X, π S * P S S' * f S' ^ 2 = ∑ S ∈ X, π S * f S ^ 2 := by
      rw [sum_comm]
      refine sum_congr rfl fun S' hS' => ?_
      rw [← sum_mul, lra_col hrev hrow S' hS']
    have : ∀ S ∈ X, ∑ S' ∈ X, -(π S * P S S' * (f S ^ 2 + f S' ^ 2)) / 2 =
        -(1 / 2) * (∑ S' ∈ X, π S * P S S' * f S ^ 2) +
          -(1 / 2) * (∑ S' ∈ X, π S * P S S' * f S' ^ 2) := by
      intro S _
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun S' _ => by ring
    rw [sum_congr rfl this, sum_add_distrib, ← mul_sum, ← mul_sum, h1, h2]
    ring
  have hB : ∑ S ∈ X, ∑ S' ∈ X, (if S = S' then 2 * (π S * P S S * f S ^ 2) else 0) =
      ∑ S ∈ X, 2 * (π S * P S S * f S ^ 2) := by
    refine sum_congr rfl fun S hS => ?_
    rw [sum_ite_eq]; simp [hS]
  have hC : ∑ S ∈ X, π S * f S ^ 2 ≤ ∑ S ∈ X, 2 * (π S * P S S * f S ^ 2) := by
    refine sum_le_sum fun S hS => ?_
    have := hlazy S hS
    have h0 : 0 ≤ π S * f S ^ 2 := mul_nonneg (hπ S hS) (sq_nonneg _)
    nlinarith
  rw [hexp]
  simp only [sum_add_distrib] at hsum
  linarith

/-- INTERNAL: every autocovariance `c_t = ⟨f, P^t f⟩_π` of a lazy reversible chain is
nonnegative.
TEXLINE: sections/transport.tex:616-621 -/
theorem lra_autocov_nonneg (hπ : ∀ S ∈ X, 0 ≤ π S) (hP0 : ∀ S ∈ X, ∀ S' ∈ X, 0 ≤ P S S')
    (hrow : ∀ S ∈ X, ∑ S' ∈ X, P S S' = 1)
    (hrev : ∀ S ∈ X, ∀ S' ∈ X, π S * P S S' = π S' * P S' S)
    (hlazy : ∀ S ∈ X, 1 / 2 ≤ P S S) [DecidableEq α] (f : α → ℝ) (t : ℕ) :
    0 ≤ lraInner X π f ((lraOp X P)^[t] f) := by
  obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' t
  · rw [two_mul, Function.iterate_add_apply, lra_inner_iter_symm hrev]
    unfold lraInner
    exact sum_nonneg fun S hS => by
      rw [mul_assoc]; exact mul_nonneg (hπ S hS) (mul_self_nonneg _)
  · rw [show 2 * s + 1 = s + (s + 1) by ring, Function.iterate_add_apply,
      lra_inner_iter_symm hrev, Function.iterate_succ_apply']
    exact lra_inner_op_nonneg hπ hP0 hrow hrev hlazy _

/-- INTERNAL: **the autocovariance series is bounded through the energy**: if
`⟨f, g⟩_π² ≤ A 𝓔(g)` for every `g`, then `Σ_{t<n} ⟨f, P^t f⟩_π ≤ A` for every `n`.
TEXLINE: sections/transport.tex:600-621 -/
theorem lra_autocov_sum_le (hπ : ∀ S ∈ X, 0 ≤ π S) (hP0 : ∀ S ∈ X, ∀ S' ∈ X, 0 ≤ P S S')
    (hrow : ∀ S ∈ X, ∑ S' ∈ X, P S S' = 1)
    (hrev : ∀ S ∈ X, ∀ S' ∈ X, π S * P S S' = π S' * P S' S)
    (hlazy : ∀ S ∈ X, 1 / 2 ≤ P S S) [DecidableEq α] (f : α → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hCS : ∀ g, lraInner X π f g ^ 2 ≤ A * lraEnergy X π P g) (n : ℕ) :
    ∑ t ∈ range n, lraInner X π f ((lraOp X P)^[t] f) ≤ A := by
  set u : ℕ → α → ℝ := fun t => (lraOp X P)^[t] f with hu
  set h : α → ℝ := fun S => ∑ t ∈ range n, u t S with hh
  set a := ∑ t ∈ range n, lraInner X π f (u t) with ha
  have ha0 : 0 ≤ a := sum_nonneg fun t _ => lra_autocov_nonneg hπ hP0 hrow hrev hlazy f t
  -- `⟨g, Σ_t u_t⟩ = Σ_t ⟨g, u_t⟩`
  have hlin : ∀ (g : α → ℝ) (v : ℕ → α → ℝ),
      lraInner X π g (fun S => ∑ t ∈ range n, v t S) = ∑ t ∈ range n, lraInner X π g (v t) := by
    intro g v
    unfold lraInner
    simp_rw [mul_sum]
    exact sum_comm
  have hfh : lraInner X π f h = a := hlin f u
  -- `(I - P) h = f - P^n f`
  have hPh : ∀ S, h S - lraOp X P h S = f S - u n S := by
    intro S
    have : lraOp X P h S = ∑ t ∈ range n, u (t + 1) S := by
      simp only [hh, lraOp, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun t _ => ?_
      simp only [hu, Function.iterate_succ_apply', lraOp]
    rw [this, hh, ← sum_sub_distrib, sum_range_sub' (fun t => u t S)]
    simp [hu]
  have hE : lraEnergy X π P h = lraInner X π h f - lraInner X π h (u n) := by
    unfold lraEnergy lraInner
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun S _ => ?_
    have := hPh S
    simp only [lraOp] at this
    rw [this]; ring
  have htail : 0 ≤ lraInner X π h (u n) := by
    rw [lraInner_comm, hlin]
    refine sum_nonneg fun t _ => ?_
    rw [lraInner_comm]
    simp only [hu]
    rw [← lra_inner_iter_symm hrev, ← Function.iterate_add_apply]
    exact lra_autocov_nonneg hπ hP0 hrow hrev hlazy f _
  have hEa : lraEnergy X π P h ≤ a := by
    rw [hE, lraInner_comm, hfh]; linarith
  have hsq : a ^ 2 ≤ A * a := by
    have := hCS h
    rw [hfh] at this
    exact this.trans (mul_le_mul_of_nonneg_left hEa hA)
  rcases ha0.eq_or_lt with h0 | hpos
  · rw [← h0]; exact hA
  · nlinarith

end Cellcounting.Analysis
