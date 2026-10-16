import Cellcounting.Analysis.Contamination

/-!
# The reference experiment of `prop:annealing`

The capped reference experiment of `algorithm.tex:174-257`: the same phases,
caps, restarts, observations and updates as `Pseudocode.annealRun`, but with
exact weights `f_j` (`eq:lifts`), exact uniform choices and exact acceptance
probabilities `min{1, λ(S')/λ(S)}`.  It is a proof-side probability model; the
algorithm never runs it.  Its output is `Z_ref = C(0) ∏_j R̂_j`, or `0` after
an abort.

Also here: the defect masses `c_il(j)` (`cDef`) and the goodness condition
`eq:good-multipliers` (`goodMult`) that the accuracy induction carries.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: the exact uniform law on `{0, …, k - 1}` (`pure 0` if `k = 0`), the
reference counterpart of `dyadicDraw k ξ`.
TEXLINE: sections/algorithm.tex:446-450 -/
noncomputable def uniformBelow (k : ℕ) : PMF ℕ :=
  if h : 0 < k then PMF.uniformOfFinset (Finset.range k) ⟨0, Finset.mem_range.2 h⟩
  else PMF.pure 0

/-- **`f_j(S)`** (`eq:lifts`): `h_j(x, y) ∏_s x_s! y_s! / b_s!` at the
small-count profile of `S`.
PAPER: sections/signatures.tex:22-31 -/
noncomputable def fWeight (I : Instance) (ε δ : ℚ) (j : ℕ) (S : Finset ℕ) : ℝ :=
  hWeight I ε δ j (profile I ε δ S).1 (profile I ε δ S).2 *
    ∏ s ∈ Finset.range (nSmall I ε δ),
      ((((profile I ε δ S).1 s).factorial : ℝ) * (((profile I ε δ S).2 s).factorial : ℝ) /
        ((smallB I ε δ s).factorial : ℝ))

/-- **`λ(S)`** (`transport.tex:36-44`): `f_j(S)` on transversals, `w_il f_j(S)` on
`A_il`.
PAPER: sections/transport.tex:36-44 -/
noncomputable def refLam (I : Instance) (ε δ : ℚ) (S : Finset ℕ) (a : ℕ)
    (w : ℕ → ℕ → ℚ) : ℝ :=
  match kind I ε δ S with
  | .defect i l => fWeight I ε δ a S * (w i l : ℝ)
  | _ => fWeight I ε δ a S

/-- INTERNAL: the exact acceptance coin with probability `min{1, r}` (clipped at
`0` for the `PMF`; `r ≥ 0` wherever it is used).
TEXLINE: sections/transport.tex:64-69 -/
noncomputable def refAccept (r : ℝ) : PMF Bool :=
  PMF.bernoulli (Real.toNNReal (min 1 r)) (by
    rw [Real.toNNReal_le_one]; exact min_le_left _ _)

/-- **One exact transition of `P_{a, w}`** (`transport.tex:60-69`): hold on a fair
bit; otherwise exchange a uniform element of `S` with a uniform element of its
complement; reject outside `X`; otherwise accept with probability
`min{1, λ(S')/λ(S)}`.
PAPER: sections/transport.tex:60-69 -/
noncomputable def refStep (I : Instance) (ε δ : ℚ) (a : ℕ) (w : ℕ → ℕ → ℚ) (S : Finset ℕ) :
    PMF (Finset ℕ) := do
  let hold ← Arlib.Computation.ProbRAM.fair
  if hold then pure S else do
    let u1 ← uniformBelow (pSmall I ε δ)
    let u2 ← uniformBelow (pSmall I ε δ)
    let S' := insert (nthWith I ε δ S false u2) (S.erase (nthWith I ε δ S true u1))
    match kind I ε δ S' with
    | .outside => pure S
    | _ => do
      let ok ← refAccept (refLam I ε δ S' a w / refLam I ε δ S a w)
      pure (if ok then S' else S)

/-- **The exact `μ₀` sampler** (`lem:initialization`, `algorithm.tex:44-47`): per
small cell, a uniform `k_s ∈ {0..b_s}` and a uniform `k_s`-subset of its pairs
(lexicographic rank, as in `Pseudocode.mu0`) use their row elements.
PAPER: sections/algorithm.tex:44-47 -/
noncomputable def refMu0 (I : Instance) (ε δ : ℚ) : PMF (Finset ℕ) :=
  loop (fun s S => do
    let k ← uniformBelow (smallB I ε δ s + 1)
    let rank ← uniformBelow (Nat.choose (smallB I ε δ s) k)
    pure (S ∪ (Finset.range (smallB I ε δ s)).image fun t =>
      if t ∈ unrank (smallB I ε δ s) k rank then 2 * (cellFirst I ε δ s + t)
      else 2 * (cellFirst I ε δ s + t) + 1))
    (nSmall I ε δ) ∅

/-- INTERNAL: one iteration of the capped reference restart, `restartStep` with
the exact transition.
TEXLINE: sections/algorithm.tex:214-225 -/
noncomputable def refRestartStep (I : Instance) (ε δ : ℚ) (ws : ℕ → ℕ → ℕ → ℚ) (j : ℕ)
    (st : Restart) : PMF Restart :=
  if st.finished then pure st else if st.aborted then pure st else
  if BretParam I ε δ ≤ st.used then pure { st with aborted := true } else do
    let S' ← refStep I ε δ st.stage (ws st.stage) st.S
    match kind I ε δ S' with
    | .transversal =>
      if st.hits + 1 = τParam I ε δ then
        pure ⟨S', st.stage + 1, 0, st.used + 1, decide (st.stage = j), false⟩
      else pure ⟨S', st.stage, st.hits + 1, st.used + 1, false, false⟩
    | _ => pure ⟨S', st.stage, st.hits, st.used + 1, false, false⟩

/-- **The capped reference restart** (`algorithm.tex:214-225`).
PAPER: sections/algorithm.tex:214-225 -/
noncomputable def refRestart (I : Instance) (ε δ : ℚ) (ws : ℕ → ℕ → ℕ → ℚ) (j : ℕ)
    (S0 : Finset ℕ) : PMF Restart :=
  loop (fun _ st => refRestartStep I ε δ ws j st) (BretParam I ε δ + 1)
    ⟨S0, 1, 0, 0, decide (j = 0), false⟩

/-- INTERNAL: the reference observation tallies; `sumG` is real.
TEXLINE: sections/algorithm.tex:226-233 -/
structure RefObs where
  /-- Current state. -/
  S : Finset ℕ
  /-- Transversals observed. -/
  n0 : ℕ
  /-- States of `A_il` observed. -/
  nT : ℕ → ℕ → ℕ
  /-- `Σ G_j` over the observed states. -/
  sumG : ℝ

/-- INTERNAL: observe the current state exactly: count its type, and at a
transversal add `G_j = f_{j+1}/f_j = h_{j+1}/h_j`.
TEXLINE: sections/algorithm.tex:150-156 -/
noncomputable def refObserveState (I : Instance) (ε δ : ℚ) (j : ℕ) (o : RefObs) : RefObs :=
  match kind I ε δ o.S with
  | .transversal =>
    { o with n0 := o.n0 + 1,
             sumG := o.sumG + hWeight I ε δ (j + 1) (profile I ε δ o.S).1 (profile I ε δ o.S).2 /
               hWeight I ε δ j (profile I ε δ o.S).1 (profile I ε δ o.S).2 }
  | .defect i l =>
    { o with nT := fun a b => if a = i ∧ b = l then o.nT i l + 1 else o.nT a b }
  | .outside => o

/-- **Reference observation** (`algorithm.tex:226-233`): `N_av` observed states of
the exact chain `P_{j, w}` from `S0`, the starting state included.
PAPER: sections/algorithm.tex:226-233 -/
noncomputable def refObserve (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ) (S0 : Finset ℕ) :
    PMF RefObs :=
  loop (fun _ o => (refStep I ε δ j w o.S).map fun S' => refObserveState I ε δ j { o with S := S' })
    (NavParam I ε δ - 1) (refObserveState I ε δ j ⟨S0, 0, fun _ _ => 0, 0⟩)

/-- INTERNAL: the multiplier update `eq:alg-multiplier-update` on reference tallies.
TEXLINE: sections/algorithm.tex:242-247 -/
noncomputable def refUpdateW (p : ℕ) (w : ℕ → ℕ → ℚ) (o : RefObs) : ℕ → ℕ → ℚ := fun i l =>
  if i < p ∧ l < p ∧ i ≠ l then w i l * (o.n0 : ℚ) / (o.nT i l : ℚ) else w i l

/-- INTERNAL: the reference run in progress: stored multipliers, `∏ R̂`, abort flag.
TEXLINE: sections/algorithm.tex:251-254 -/
structure RefRunState where
  /-- `w^(a)`, for the stages stored so far. -/
  ws : ℕ → ℕ → ℕ → ℚ
  /-- `∏ R̂_j` so far. -/
  prod : ℝ
  /-- Some phase aborted. -/
  aborted : Bool

/-- **Reference phase `j`** (`algorithm.tex:214-249`), `Pseudocode.phase` with exact
weights and probabilities.
PAPER: sections/algorithm.tex:214-249 -/
noncomputable def refPhase (I : Instance) (ε δ : ℚ) (j : ℕ) (st : RefRunState) :
    PMF RefRunState :=
  if st.aborted then pure st else do
    let S0 ← refMu0 I ε δ
    let rs ← refRestart I ε δ st.ws j S0
    if rs.aborted then pure { st with aborted := true } else do
      let o ← refObserve I ε δ j (st.ws j) rs.S
      if 0 < o.n0 ∧ ∀ i < pSmall I ε δ, ∀ l < pSmall I ε δ, i ≠ l → 0 < o.nT i l then
        let R := (o.sumG / (NavParam I ε δ : ℝ)) / ((o.n0 : ℝ) / (NavParam I ε δ : ℝ))
        if j + 1 < HParam I ε δ then
          pure ⟨Function.update st.ws (j + 1) (refUpdateW (pSmall I ε δ) (st.ws j) o),
            st.prod * R, false⟩
        else pure ⟨st.ws, st.prod * R, false⟩
      else pure { st with aborted := true }

/-- **The reference experiment** (`algorithm.tex:251-257`): phases `j = 0..H-1`
from `w^(0)`; output `Z_ref = C(0) ∏_j R̂_j`, or `0` after an abort.
PAPER: sections/algorithm.tex:251-257 -/
noncomputable def refRun (I : Instance) (ε δ : ℚ) : PMF ℝ :=
  (loop (refPhase I ε δ) (HParam I ε δ)
      ⟨fun a => if a = 0 then w0 I ε δ else fun _ _ => 0, 1, false⟩).map
    fun st => if st.aborted then 0 else (C0 I ε δ : ℝ) * st.prod

/-- INTERNAL: the paired state space: all subsets of the `2p` elements.
TEXLINE: sections/signatures.tex:13-41 -/
noncomputable def refStates (I : Instance) (ε δ : ℚ) : Finset (Finset ℕ) :=
  (Finset.range (2 * pSmall I ε δ)).powerset

open Classical in
/-- **`c_il(j)`**: the unmultiplied `f_j`-mass of the defect class `A_il`.
PAPER: sections/transport.tex:45-58 -/
noncomputable def cDef (I : Instance) (ε δ : ℚ) (j i l : ℕ) : ℝ :=
  ∑ S ∈ (refStates I ε δ).filter (fun S => kind I ε δ S = .defect i l), fWeight I ε δ j S

/-- **Good multipliers** (`eq:good-multipliers`): `C(j)/(4 c_il(j)) ≤ w_il ≤ 4 C(j)/c_il(j)`
for every ordered pair of distinct labels `i ≠ l < p`.
PAPER: sections/transport.tex:50-54 -/
def goodMult (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ) : Prop :=
  ∀ i < pSmall I ε δ, ∀ l < pSmall I ε δ, i ≠ l →
    Cpart I ε δ j / (4 * cDef I ε δ j i l) ≤ (w i l : ℝ) ∧
      (w i l : ℝ) ≤ 4 * Cpart I ε δ j / cDef I ε δ j i l

/-- INTERNAL: a list product read through `getD`. -/
theorem prod_range_getD_eq {α : Type*} (l : List α) (g : α → ℕ) (d : α) :
    ∏ i ∈ Finset.range l.length, g (l.getD i d) = (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih, List.map_cons, List.prod_cons, mul_comm]

/-- INTERNAL: the free box has `M_f` points.
TEXLINE: sections/algorithm.tex:94-133 -/
theorem card_freeBox (I : Instance) (ε δ : ℚ) : (freeBox I ε δ).card = Mf I ε δ := by
  unfold freeBox
  rw [Fintype.card_piFinset]
  simp only [Finset.card_range]
  rw [Fin.prod_univ_eq_prod_range (fun k => (freeAt I ε δ k).2.2 + 1) (nFree I ε δ)]
  unfold nFree freeAt Mf
  exact prod_range_getD_eq _ (fun e => e.2.2 + 1) (0, 0, 0)

/-- INTERNAL: `C(0) = M_f ∏_s (b_s + 1)`: at parameter zero every term of `h_0` is one.
TEXLINE: sections/algorithm.tex:94-133 -/
theorem Cpart_zero (I : Instance) (ε δ : ℚ) : Cpart I ε δ 0 = (C0 I ε δ : ℝ) := by
  have hh : ∀ x y, hWeight I ε δ 0 x y = (Mf I ε δ : ℝ) := by
    intro x y
    simp [hWeight, card_freeBox]
  simp only [Cpart, hh, Finset.sum_const, nsmul_eq_mul, C0]
  have hsmall : (smallBox I ε δ).card =
      ∏ k ∈ Finset.range (nSmall I ε δ), (smallB I ε δ k + 1) := by
    unfold smallBox
    rw [Fintype.card_piFinset]
    simp only [Finset.card_range]
    exact Fin.prod_univ_eq_prod_range (fun k => smallB I ε δ k + 1) (nSmall I ε δ)
  rw [hsmall]
  push_cast
  ring

/-- INTERNAL: every `C(j)` is positive (both boxes are nonempty, every term positive).
TEXLINE: sections/scales.tex:279-282 -/
theorem Cpart_pos (I : Instance) (ε δ : ℚ) (j : ℕ) : 0 < Cpart I ε δ j := by
  have hS : (smallBox I ε δ).Nonempty := ⟨fun _ => 0, by simp [smallBox]⟩
  have hF : (freeBox I ε δ).Nonempty := ⟨fun _ => 0, by simp [freeBox]⟩
  refine Finset.sum_pos (fun x _ => Finset.sum_pos (fun z _ => by positivity) hF) hS

end Cellcounting.Analysis
