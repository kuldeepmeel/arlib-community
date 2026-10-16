import Cellcounting.Analysis.HyperbolicForm
import Cellcounting.Analysis.RefExperiment

/-!
# Sums over pair choices, omission matrices and the second lift

Vocabulary shared by `prop:transversal-variance` (`transport.tex:318-428`), the
one-hole transport lemma `lem:transport` (`transport.tex:99-316`), the binary
signature lemmas (`signatures.tex:79-262`) and the defect inequalities
(`signatures.tex:303-410`).

The paired ground set has the elements `2t` (row) and `2t + 1` (column) of pair `t`.

* `chSum L φ` sums `φ c` over the `2^|L|` choice sets `c` taking exactly one element
  of each pair `t ∈ L` ("summing the pairs of `L` at occupancy one");
* `IsChoice L c` characterizes those sets, and `chSum_mono`, `chSum_congr` only ask
  for pointwise facts on them;
* `omitMat f F D L` is the two-omission matrix `(G(D \ {x, y}))_{x ≠ y ∈ D}` of the
  weight `G(U) = Σ_c f(F ∪ U ∪ c)` obtained from `f` by fixing `F` included and
  summing the pairs of `L` at occupancy one;
* `fTilde` is the second lift `f̃_j` of `eq:lifts`;
* `AsgValid p σ T`: `σ` picks one element in each assigned pair and `T` lists the
  unassigned pairs; `trMass φ σ T` and `defMass φ σ T i l` are the `φ`-masses of the
  transversals and of the defect class `A_il` respecting `σ`.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: the sum of `φ c` over the choice sets `c` with exactly one element of
each pair `{2t, 2t + 1}`, `t ∈ L` (summing those pairs at occupancy one).
TEXLINE: sections/signatures.tex:96-104 -/
noncomputable def chSum : List ℕ → (Finset ℕ → ℝ) → ℝ
  | [], φ => φ ∅
  | t :: L, φ => chSum L (fun c => φ (insert (2 * t) c)) +
      chSum L (fun c => φ (insert (2 * t + 1) c))

/-- INTERNAL: `c` takes exactly one element of each pair of `L` and nothing else.
TEXLINE: sections/signatures.tex:96-104 -/
def IsChoice (L : List ℕ) (c : Finset ℕ) : Prop :=
  (∀ e ∈ c, e / 2 ∈ L) ∧ ∀ t ∈ L, (2 * t ∈ c ↔ 2 * t + 1 ∉ c)

/-- INTERNAL: the two-omission matrix `N_{xy} = G(D \ {x, y})` (zero diagonal) of
`G(U) = Σ_c f(F ∪ U ∪ c)`, the weight obtained from `f` by fixing `F` included and
summing the pairs of `L` at occupancy one.
TEXLINE: sections/signatures.tex:79-90 -/
noncomputable def omitMat (f : Finset ℕ → ℝ) (F D : Finset ℕ) (L : List ℕ) :
    D → D → ℝ :=
  fun x y => if x = y then 0 else chSum L (fun c => f (((F ∪ D ∪ c).erase x).erase y))

/-- **`f̃_j(S)`** (`eq:lifts`, second lift):
`h_j(x, y) ∏_s (b_s - x_s)! (b_s - y_s)! / b_s!` at the small-count profile of `S`.
PAPER: sections/signatures.tex:26-31 -/
noncomputable def fTilde (I : Instance) (ε δ : ℚ) (j : ℕ) (S : Finset ℕ) : ℝ :=
  hWeight I ε δ j (profile I ε δ S).1 (profile I ε δ S).2 *
    ∏ s ∈ Finset.range (nSmall I ε δ),
      (((smallB I ε δ s - (profile I ε δ S).1 s).factorial : ℝ) *
          ((smallB I ε δ s - (profile I ε δ S).2 s).factorial : ℝ) /
        ((smallB I ε δ s).factorial : ℝ))

/-- INTERNAL: `σ` is a partial transversal assignment of the pairs `[0, p)` (one
chosen element in each assigned pair) and `T` lists the unassigned pairs, without
repetition.
TEXLINE: sections/signatures.tex:303-310 -/
def AsgValid (p : ℕ) (σ : Finset ℕ) (T : List ℕ) : Prop :=
  T.Nodup ∧ (∀ t ∈ T, t < p) ∧ (∀ e ∈ σ, e < 2 * p) ∧
    (∀ e ∈ σ, ∀ e' ∈ σ, e / 2 = e' / 2 → e = e') ∧
    ∀ t < p, (t ∈ T ↔ ∀ e ∈ σ, e / 2 ≠ t)

/-- INTERNAL: `z_σ`, the `φ`-mass of the transversals respecting `σ`.
TEXLINE: sections/signatures.tex:303-318 -/
noncomputable def trMass (φ : Finset ℕ → ℝ) (σ : Finset ℕ) (T : List ℕ) : ℝ :=
  chSum T (fun c => φ (σ ∪ c))

/-- INTERNAL: `c^σ_il`, the `φ`-mass of the defect class `A_il` (pair `i` empty,
pair `l` full) respecting `σ`.
TEXLINE: sections/signatures.tex:303-318 -/
noncomputable def defMass (φ : Finset ℕ → ℝ) (σ : Finset ℕ) (T : List ℕ) (i l : ℕ) : ℝ :=
  chSum ((T.erase i).erase l) (fun c => φ (insert (2 * l) (insert (2 * l + 1) (σ ∪ c))))

/-! ### Basic facts about `chSum` -/

theorem chSum_nil (φ : Finset ℕ → ℝ) : chSum [] φ = φ ∅ := rfl

theorem chSum_cons (t : ℕ) (L : List ℕ) (φ : Finset ℕ → ℝ) :
    chSum (t :: L) φ = chSum L (fun c => φ (insert (2 * t) c)) +
      chSum L (fun c => φ (insert (2 * t + 1) c)) := rfl

theorem chSum_add (L : List ℕ) (φ ψ : Finset ℕ → ℝ) :
    chSum L (fun c => φ c + ψ c) = chSum L φ + chSum L ψ := by
  induction L generalizing φ ψ with
  | nil => rfl
  | cons t L ih =>
    simp only [chSum_cons]
    rw [ih (fun c => φ (insert (2 * t) c)) (fun c => ψ (insert (2 * t) c)),
      ih (fun c => φ (insert (2 * t + 1) c)) (fun c => ψ (insert (2 * t + 1) c))]
    ring

theorem chSum_mul_left (L : List ℕ) (a : ℝ) (φ : Finset ℕ → ℝ) :
    chSum L (fun c => a * φ c) = a * chSum L φ := by
  induction L generalizing φ with
  | nil => rfl
  | cons t L ih =>
    simp only [chSum_cons]
    rw [ih (fun c => φ (insert (2 * t) c)), ih (fun c => φ (insert (2 * t + 1) c))]
    ring

theorem chSum_mul_right (L : List ℕ) (a : ℝ) (φ : Finset ℕ → ℝ) :
    chSum L (fun c => φ c * a) = chSum L φ * a := by
  rw [mul_comm (chSum L φ)]
  simp_rw [mul_comm _ a]
  exact chSum_mul_left L a φ

theorem chSum_sub (L : List ℕ) (φ ψ : Finset ℕ → ℝ) :
    chSum L (fun c => φ c - ψ c) = chSum L φ - chSum L ψ := by
  have h := chSum_add L (fun c => φ c - ψ c) ψ
  simp only [sub_add_cancel] at h
  linarith

theorem chSum_zero (L : List ℕ) : chSum L (fun _ => 0) = 0 := by
  have h := chSum_mul_left L 0 (fun _ => 0)
  simpa using h

theorem chSum_finset_sum {ι : Type*} (s : Finset ι) (L : List ℕ) (φ : ι → Finset ℕ → ℝ) :
    chSum L (fun c => ∑ i ∈ s, φ i c) = ∑ i ∈ s, chSum L (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using chSum_zero L
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [chSum_add, ih]

theorem isChoice_nil (c : Finset ℕ) : IsChoice [] c ↔ c = ∅ := by
  constructor
  · rintro ⟨h, -⟩
    exact Finset.eq_empty_of_forall_notMem fun e he => by simpa using h e he
  · rintro rfl
    exact ⟨by simp, by simp⟩

/-- INTERNAL: adding a choice in a new pair `t` to a choice of `L`. -/
theorem isChoice_insert {t : ℕ} {L : List ℕ} (ht : t ∉ L) {c : Finset ℕ}
    (hc : IsChoice L c) (b : ℕ) (hb : b < 2) : IsChoice (t :: L) (insert (2 * t + b) c) := by
  obtain ⟨h1, h2⟩ := hc
  refine ⟨?_, ?_⟩
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · simp; omega
    · exact List.mem_cons_of_mem _ (h1 e he)
  · intro t' ht'
    rcases List.mem_cons.1 ht' with rfl | ht'
    · have hn0 : 2 * t' ∉ c := fun h => ht (by simpa using h1 _ h)
      have hn1 : 2 * t' + 1 ∉ c := fun h => ht (by
        have := h1 _ h; rwa [show (2 * t' + 1) / 2 = t' by omega] at this)
      simp only [Finset.mem_insert]
      interval_cases b <;> simp [hn0, hn1]
    · have hne : t' ≠ t := fun h => ht (h ▸ ht')
      simp only [Finset.mem_insert]
      have e1 : 2 * t' ≠ 2 * t + b := by omega
      have e2 : 2 * t' + 1 ≠ 2 * t + b := by omega
      simp only [e1, e2, false_or]
      exact h2 t' ht'

theorem chSum_congr {L : List ℕ} (hL : L.Nodup) {φ ψ : Finset ℕ → ℝ}
    (h : ∀ c, IsChoice L c → φ c = ψ c) : chSum L φ = chSum L ψ := by
  induction L generalizing φ ψ with
  | nil => exact h ∅ ((isChoice_nil ∅).2 rfl)
  | cons t L ih =>
    obtain ⟨ht, hL'⟩ := List.nodup_cons.1 hL
    simp only [chSum_cons]
    congr 1
    · exact ih hL' fun c hc => h _ (by simpa using isChoice_insert ht hc 0 (by norm_num))
    · exact ih hL' fun c hc => h _ (isChoice_insert ht hc 1 (by norm_num))

theorem chSum_mono {L : List ℕ} (hL : L.Nodup) {φ ψ : Finset ℕ → ℝ}
    (h : ∀ c, IsChoice L c → φ c ≤ ψ c) : chSum L φ ≤ chSum L ψ := by
  induction L generalizing φ ψ with
  | nil => exact h ∅ ((isChoice_nil ∅).2 rfl)
  | cons t L ih =>
    obtain ⟨ht, hL'⟩ := List.nodup_cons.1 hL
    simp only [chSum_cons]
    refine add_le_add ?_ ?_
    · exact ih hL' fun c hc => h _ (by simpa using isChoice_insert ht hc 0 (by norm_num))
    · exact ih hL' fun c hc => h _ (isChoice_insert ht hc 1 (by norm_num))

theorem chSum_nonneg {L : List ℕ} (hL : L.Nodup) {φ : Finset ℕ → ℝ}
    (h : ∀ c, IsChoice L c → 0 ≤ φ c) : 0 ≤ chSum L φ := by
  have := chSum_mono hL (φ := fun _ => 0) (ψ := φ) h
  rwa [chSum_zero] at this

theorem chSum_pos {L : List ℕ} (hL : L.Nodup) {φ : Finset ℕ → ℝ}
    (h : ∀ c, IsChoice L c → 0 < φ c) : 0 < chSum L φ := by
  induction L generalizing φ with
  | nil => exact h ∅ ((isChoice_nil ∅).2 rfl)
  | cons t L ih =>
    obtain ⟨ht, hL'⟩ := List.nodup_cons.1 hL
    simp only [chSum_cons]
    refine add_pos ?_ ?_
    · exact ih hL' fun c hc => h _ (by simpa using isChoice_insert ht hc 0 (by norm_num))
    · exact ih hL' fun c hc => h _ (isChoice_insert ht hc 1 (by norm_num))

/-- INTERNAL: `chSum` does not depend on the order of the pairs. -/
theorem chSum_perm {L L' : List ℕ} (hp : L.Perm L') (φ : Finset ℕ → ℝ) :
    chSum L φ = chSum L' φ := by
  induction hp generalizing φ with
  | nil => rfl
  | cons t _ ih =>
    simp only [chSum_cons]
    rw [ih, ih]
  | swap a b L =>
    simp only [chSum_cons]
    simp_rw [Finset.insert_comm (2 * a) (2 * b), Finset.insert_comm (2 * a) (2 * b + 1),
      Finset.insert_comm (2 * a + 1) (2 * b), Finset.insert_comm (2 * a + 1) (2 * b + 1)]
    ring
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

/-- INTERNAL: splitting off one pair `t ∈ L`. -/
theorem chSum_split {L : List ℕ} {t : ℕ} (ht : t ∈ L) (φ : Finset ℕ → ℝ) :
    chSum L φ = chSum (L.erase t) (fun c => φ (insert (2 * t) c)) +
      chSum (L.erase t) (fun c => φ (insert (2 * t + 1) c)) := by
  rw [chSum_perm (List.perm_cons_erase ht) φ, chSum_cons]

end Cellcounting.Analysis
