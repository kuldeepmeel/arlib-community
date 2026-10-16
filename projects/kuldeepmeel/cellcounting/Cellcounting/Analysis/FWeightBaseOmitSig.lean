import Cellcounting.Analysis.OmitSig
import Cellcounting.Analysis.HWeightRemovalHyp
import Cellcounting.Analysis.RefExperiment
import Cellcounting.Analysis.TransMassEqCpart
import Mathlib.Algebra.Order.Chebyshev

/-!
# The omission property of `f_j` on the full `p`-subset domain

`lem:binary-signatures`, first assertion (`signatures.tex:211-246`): `f_j` is positive
on every subset, and at every display `P ⊆ [0, 2p)` of `p + 2` elements its two-omission
matrix has at most one positive eigenvalue (`OmitSig (fWeight I ε δ j) [0, 2p) p`).

The proof is the paper's group decomposition.  Group the displayed elements by
small-cell coordinate (`(s, false)` for the row element of a pair of cell `s`,
`(s, true)` for its column element); the matrix entry of `x ≠ y` depends only on the
groups of `x` and `y`.  `hyp_of_groups` reduces `Hyp` to the group-level matrix
`n_u (n_v - [u = v]) N_uv` (group-sum-zero vectors have nonpositive square and do not
couple to group-constant ones), and the ordered-copy multiplicities cancel the
factorial reductions, so the group-level matrix is a positive multiple of the
removal matrix of `h_j` at the display `n` (`hWeight_removal_hyp`).
-/

namespace Cellcounting.Analysis

open Finset Pseudocode

/-- INTERNAL: the group reduction of `lem:binary-signatures`.  A zero-diagonal matrix
whose off-diagonal entries depend only on the groups `g x`, `g y` of the indices, with
symmetric group values `N` and `N_uu ≥ 0`, is `Hyp` as soon as the group-level matrix
`n_u (n_v - [u = v]) N_uv` (with `n_u = |g⁻¹(u)|`) is `Hyp`.
TEXLINE: sections/signatures.tex:216-240 -/
theorem hyp_of_groups {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (g : ι → κ) (N : κ → κ → ℝ) (hN : ∀ u v, N u v = N v u) (hdiag : ∀ u, 0 ≤ N u u)
    (hM : Hyp (fun u v => ((univ.filter fun x => g x = u).card : ℝ) *
        (((univ.filter fun x => g x = v).card : ℝ) - if u = v then 1 else 0) * N u v)) :
    Hyp (fun x y : ι => if x = y then 0 else N (g x) (g y)) := by
  set fib : κ → Finset ι := fun u => univ.filter fun x => g x = u with hfib
  set n : κ → ℝ := fun u => ((fib u).card : ℝ) with hn
  set M : κ → κ → ℝ := fun u v => n u * (n v - if u = v then 1 else 0) * N u v with hMdef
  set Q : ι → ι → ℝ := fun x y => if x = y then 0 else N (g x) (g y) with hQ
  set S : (ι → ℝ) → κ → ℝ := fun v u => ∑ x ∈ fib u, v x with hS
  set τ : (ι → ℝ) → κ → ℝ := fun v u => S v u / n u with hτ
  have hS0 : ∀ v u, n u = 0 → S v u = 0 := by
    intro v u hu
    have : fib u = ∅ := by
      have h' : ((fib u).card : ℝ) = 0 := hu
      rw [← card_eq_zero]; exact_mod_cast h'
    simp only [hS, this, sum_empty]
  have hfw : ∀ F : ι → ℝ, ∑ u, ∑ x ∈ fib u, F x = ∑ x, F x := fun F =>
    Finset.sum_fiberwise (s := univ) g F
  have hfw' : ∀ F : κ → ι → ℝ, ∑ x, F (g x) x = ∑ u, ∑ x ∈ fib u, F u x := by
    intro F
    rw [← hfw]
    refine sum_congr rfl fun u _ => sum_congr rfl fun x hx => ?_
    rw [(mem_filter.1 hx).2]
  -- (1) the form of `Q`
  have hQv : ∀ v, qf Q v v = (∑ u, ∑ w, S v u * N u w * S v w) -
      ∑ x, v x ^ 2 * N (g x) (g x) := by
    intro v
    have h1 : ∀ x y, v x * Q x y * v y =
        v x * N (g x) (g y) * v y - if x = y then v x ^ 2 * N (g x) (g x) else 0 := by
      intro x y
      simp only [hQ]
      split_ifs with h
      · subst h; ring
      · ring
    unfold qf
    simp only [h1, sum_sub_distrib, sum_ite_eq, mem_univ, if_true]
    congr 1
    rw [hfw' (fun u x => ∑ y, v x * N u (g y) * v y)]
    refine sum_congr rfl fun u _ => ?_
    have h2 : ∀ x, ∑ y, v x * N u (g y) * v y = ∑ w, ∑ y ∈ fib w, v x * N u w * v y :=
      fun x => hfw' (fun w y => v x * N u w * v y)
    simp only [h2]
    rw [sum_comm]
    refine sum_congr rfl fun w _ => ?_
    simp only [hS, sum_mul, mul_sum]
    rw [sum_comm]
  -- (2) the form of `M` at `τ v`
  have hMv : ∀ v, qf M (τ v) (τ v) = (∑ u, ∑ w, S v u * N u w * S v w) -
      ∑ u, S v u ^ 2 / n u * N u u := by
    intro v
    have h1 : ∀ u w, τ v u * M u w * τ v w =
        S v u * N u w * S v w - if u = w then S v u ^ 2 / n u * N u u else 0 := by
      intro u w
      simp only [hτ, hMdef]
      by_cases hu : n u = 0
      · rw [hS0 v u hu]; split_ifs <;> simp
      by_cases hw : n w = 0
      · rw [hS0 v w hw]; split_ifs with h
        · subst h; exact absurd hw hu
        · simp
      split_ifs with h
      · subst h; field_simp
      · field_simp; ring
    unfold qf
    simp only [h1, sum_sub_distrib, sum_ite_eq, mem_univ, if_true]
  -- (3) Cauchy–Schwarz in each group
  have hcs : ∀ v, ∑ u, S v u ^ 2 / n u * N u u ≤ ∑ x, v x ^ 2 * N (g x) (g x) := by
    intro v
    rw [hfw' (fun u x => v x ^ 2 * N u u)]
    refine sum_le_sum fun u _ => ?_
    rw [← sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (hdiag u)
    by_cases hu : n u = 0
    · rw [hu, div_zero]; exact sum_nonneg fun x _ => sq_nonneg _
    · rw [div_le_iff₀ (lt_of_le_of_ne (by positivity) (Ne.symm hu)), mul_comm]
      exact sq_sum_le_card_mul_sum_sq
  have hle : ∀ v, qf Q v v ≤ qf M (τ v) (τ v) := by
    intro v; rw [hQv, hMv]; linarith [hcs v]
  -- (4) `v ↦ tᵀ M τ(v)` is a linear functional
  have hlin : ∀ t v, qf M t (τ v) = ∑ x, (∑ u, t u * M u (g x) / n (g x)) * v x := by
    intro t v
    unfold qf
    rw [hfw' (fun w x => (∑ u, t u * M u w / n w) * v x), sum_comm]
    refine sum_congr rfl fun w _ => ?_
    rw [← mul_sum, ← sum_mul, ← sum_div]
    simp only [hτ]
    ring
  have hQs : QSymm Q := by
    intro x y
    simp only [hQ]
    by_cases h : x = y
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), hN]
  by_cases hpos : ∃ t, 0 < qf M t t
  · obtain ⟨t, ht⟩ := hpos
    refine hyp_of_kernel hQs (fun x => ∑ u, t u * M u (g x) / n (g x)) fun v hv => ?_
    have h1 := hM t (τ v) ht
    rw [hlin t v, hv, sq, mul_zero] at h1
    have h2 : qf M (τ v) (τ v) ≤ 0 := by
      by_contra h3; push Not at h3
      exact absurd h1 (not_le.2 (mul_pos ht h3))
    exact (hle v).trans h2
  · push Not at hpos
    intro u w hu
    exact absurd ((hle u).trans (hpos _)) (not_le.2 hu)

/-- **`f_j` has the omission property, with positivity, on the `p`-subsets of `[0, 2p)`**
(`lem:binary-signatures`, first assertion).
PAPER: sections/signatures.tex:201-246 -/
theorem fWeight_base_omitSig (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (j : ℕ) (hj : j ≤ HParam I ε δ) :
    OmitSig (fWeight I ε δ j) (range (2 * pSmall I ε δ)) (pSmall I ε δ) := by
  classical
  refine ⟨fun S _ _ => ?_, fun P hP hPc => ?_⟩
  · -- positivity on every subset
    unfold fWeight
    refine mul_pos ?_ (Finset.prod_pos fun s _ => by positivity)
    exact Finset.sum_pos (fun z _ => by positivity) ⟨fun _ => 0, by simp [freeBox]⟩
  set p := pSmall I ε δ with hpdef
  set N := nSmall I ε δ with hNdef
  -- the coordinate group of a displayed element: (cell of its pair, column element?)
  have hcell : ∀ x : P, pairCell I ε δ (x.1 / 2) < N := fun x =>
    pairCell_lt I ε δ (by have := mem_range.1 (hP x.2); omega)
  set g : P → Fin N × Bool := fun x =>
    (⟨pairCell I ε δ (x.1 / 2), hcell x⟩, decide (x.1 % 2 = 1)) with hg
  set n : Fin N × Bool → ℕ := fun u => (univ.filter fun x : P => g x = u).card with hndef
  -- the group value: `h_j(n - e_u - e_v)` times the factorial factor
  set Nm : Fin N × Bool → Fin N × Bool → ℝ := fun u v =>
    hWeight I ε δ j (extendN fun s => remDisp n u v (s, false))
        (extendN fun s => remDisp n u v (s, true)) *
      ∏ s : Fin N, (((remDisp n u v (s, false)).factorial : ℝ) *
        ((remDisp n u v (s, true)).factorial : ℝ) / ((smallB I ε δ s).factorial : ℝ)) with hNm
  -- group membership, read on the raw label
  have hgu : ∀ (x : P) (u : Fin N × Bool),
      g x = u ↔ pairCell I ε δ (x.1 / 2) = u.1.1 ∧ decide (x.1 % 2 = 1) = u.2 := by
    intro x u
    simp only [hg, Prod.ext_iff, Fin.ext_iff]
  have hn_eq : ∀ u : Fin N × Bool, n u =
      (P.filter fun z => pairCell I ε δ (z / 2) = u.1.1 ∧ decide (z % 2 = 1) = u.2).card := by
    intro u
    simp only [hndef]
    refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
    · intro x hx
      exact mem_filter.2 ⟨x.2, (hgu x u).1 (mem_filter.1 hx).2⟩
    · intro x _ y _ h; exact Subtype.ext h
    · intro z hz
      obtain ⟨hzP, hz⟩ := mem_filter.1 hz
      exact ⟨⟨z, hzP⟩, mem_filter.2 ⟨mem_univ _, (hgu ⟨z, hzP⟩ u).2 hz⟩, rfl⟩
  have hPr : ∀ z ∈ P, z < 2 * p := fun z hz => mem_range.1 (hP hz)
  -- (a) an entry depends only on the groups of its indices
  -- the profile of a subset of the display counts its labels group by group
  have hprofF : ∀ S ⊆ P, ∀ k : ℕ,
      ((range p).filter fun i => pairCell I ε δ i = k ∧ 2 * i ∈ S).card =
      (S.filter fun z => pairCell I ε δ (z / 2) = k ∧ decide (z % 2 = 1) = false).card := by
    intro S hS k
    refine card_nbij' (fun i => 2 * i) (fun z => z / 2) ?_ ?_ ?_ ?_
    · intro i hi
      obtain ⟨_, hik, hiS⟩ := mem_filter.1 hi
      refine mem_filter.2 ⟨hiS, ?_, ?_⟩
      · show pairCell I ε δ (2 * i / 2) = k
        rw [show 2 * i / 2 = i by omega]; exact hik
      · simp
    · intro z hz
      obtain ⟨hzS, hzk, hz2⟩ := mem_filter.1 hz
      have := hPr z (hS hzS)
      have hz2' : z % 2 ≠ 1 := by simpa using hz2
      refine mem_filter.2 ⟨mem_range.2 ?_, hzk, ?_⟩
      · show z / 2 < p; omega
      · show 2 * (z / 2) ∈ S; rw [show 2 * (z / 2) = z by omega]; exact hzS
    · intro i _; show 2 * i / 2 = i; omega
    · intro z hz
      have hz2' : z % 2 ≠ 1 := by simpa using (mem_filter.1 hz).2.2
      show 2 * (z / 2) = z; omega
  have hprofT : ∀ S ⊆ P, ∀ k : ℕ,
      ((range p).filter fun i => pairCell I ε δ i = k ∧ 2 * i + 1 ∈ S).card =
      (S.filter fun z => pairCell I ε δ (z / 2) = k ∧ decide (z % 2 = 1) = true).card := by
    intro S hS k
    refine card_nbij' (fun i => 2 * i + 1) (fun z => z / 2) ?_ ?_ ?_ ?_
    · intro i hi
      obtain ⟨_, hik, hiS⟩ := mem_filter.1 hi
      refine mem_filter.2 ⟨hiS, ?_, ?_⟩
      · show pairCell I ε δ ((2 * i + 1) / 2) = k
        rw [show (2 * i + 1) / 2 = i by omega]; exact hik
      · simp only [decide_eq_true_eq]; omega
    · intro z hz
      obtain ⟨hzS, hzk, hz2⟩ := mem_filter.1 hz
      have := hPr z (hS hzS)
      have hz2' : z % 2 = 1 := by simpa using hz2
      refine mem_filter.2 ⟨mem_range.2 ?_, hzk, ?_⟩
      · show z / 2 < p; omega
      · show 2 * (z / 2) + 1 ∈ S; rw [show 2 * (z / 2) + 1 = z by omega]; exact hzS
    · intro i _; show (2 * i + 1) / 2 = i; omega
    · intro z hz
      have hz2' : z % 2 = 1 := by simpa using (mem_filter.1 hz).2.2
      show 2 * (z / 2) + 1 = z; omega
  -- removing two displayed labels removes one from each of their groups
  have hcnt : ∀ x y : P, x ≠ y → ∀ u : Fin N × Bool,
      (((P.erase x).erase y).filter fun z =>
        pairCell I ε δ (z / 2) = u.1.1 ∧ decide (z % 2 = 1) = u.2).card =
      remDisp n (g x) (g y) u := by
    intro x y hxy u
    have hxy' : y.1 ≠ x.1 := fun h => hxy (Subtype.ext h).symm
    rw [filter_erase, filter_erase, card_erase_eq_ite, card_erase_eq_ite, ← hn_eq u]
    simp only [remDisp, mem_erase, mem_filter, ← hgu, ne_eq, hxy', not_false_eq_true,
      true_and, x.2, y.2]
    have ex : ∀ w, (u = w) = (w = u) := fun w => propext eq_comm
    simp only [ex]
    by_cases hx : g x = u <;> by_cases hy : g y = u <;> simp [hx, hy]
  have hentry : ∀ x y : P, x ≠ y → fWeight I ε δ j ((P.erase x).erase y) = Nm (g x) (g y) := by
    intro x y hxy
    have hS : (P.erase x).erase y ⊆ P := (erase_subset _ _).trans (erase_subset _ _)
    have hout : ∀ (k : ℕ) (q : ℕ → Prop) [DecidablePred q], ¬ k < N →
        ((range p).filter fun i => pairCell I ε δ i = k ∧ q i).card = 0 := by
      intro k q _ hk
      rw [card_eq_zero, filter_eq_empty_iff]
      rintro i hi ⟨hik, _⟩
      exact hk (hik ▸ pairCell_lt I ε δ (mem_range.1 hi))
    have h1 : (profile I ε δ ((P.erase x).erase y)).1 =
        extendN fun s => remDisp n (g x) (g y) (s, false) := by
      funext k
      simp only [profile, extendN]
      split_ifs with hk
      · rw [hprofF _ hS k, ← hcnt x y hxy (⟨k, hk⟩, false)]
      · exact hout k _ hk
    have h2 : (profile I ε δ ((P.erase x).erase y)).2 =
        extendN fun s => remDisp n (g x) (g y) (s, true) := by
      funext k
      simp only [profile, extendN]
      split_ifs with hk
      · rw [hprofT _ hS k, ← hcnt x y hxy (⟨k, hk⟩, true)]
      · exact hout k _ hk
    rw [fWeight, h1, h2, hNm, prod_range]
    congr 1
    refine prod_congr rfl fun s _ => ?_
    have hs : (s : ℕ) < N := s.2
    simp [extendN, hs]
  -- (b) the display `n` is box-valid of total `p + 2`
  have hbox : ∀ w, n w ≤ smallB I ε δ w.1 := by
    intro w
    rw [hn_eq w, smallB_eq_card]
    refine card_le_card_of_injOn (fun z => z / 2) ?_ ?_
    · intro z hz
      obtain ⟨hzP, hz1, _⟩ := mem_filter.1 hz
      have := hPr z hzP
      refine mem_filter.2 ⟨mem_range.2 ?_, hz1⟩
      show z / 2 < p
      omega
    · intro z1 hz1 z2 hz2 h
      have h1 := (mem_filter.1 hz1).2.2
      have h2 := (mem_filter.1 hz2).2.2
      simp only at h
      have : z1 % 2 = z2 % 2 := by
        rw [← h2] at h1
        by_cases hz : z1 % 2 = 1
        · have : z2 % 2 = 1 := by simpa [hz] using h1
          omega
        · have : z2 % 2 ≠ 1 := by simpa [hz] using h1
          omega
      omega
  have htot : ∑ w, n w = p + 2 := by
    rw [← hPc, ← Fintype.card_coe, ← Finset.card_univ,
      card_eq_sum_card_fiberwise (f := g) (t := univ) (fun x _ => mem_univ _)]
  -- (c) multiplicities cancel the factorial reductions
  set c : ℝ := (∏ w : Fin N × Bool, ((n w).factorial : ℝ)) /
      ∏ s : Fin N, ((smallB I ε δ s).factorial : ℝ) with hc
  have hcpos : 0 < c := by
    rw [hc]; positivity
  have hfact : ∀ u v, (1 ≤ n u ∧ 1 ≤ n v ∧ (u = v → 2 ≤ n u)) →
      n u * (n v - if u = v then 1 else 0) * ∏ w, (remDisp n u v w).factorial =
        ∏ w, (n w).factorial := by
    rintro u v ⟨hu, hv, huv⟩
    by_cases h : u = v
    · subst h
      have h2 := huv rfl
      rw [if_pos rfl, ← mul_prod_erase univ (fun w => (remDisp n u u w).factorial) (mem_univ u),
        ← mul_prod_erase univ (fun w => (n w).factorial) (mem_univ u)]
      have hrest : ∏ w ∈ univ.erase u, (remDisp n u u w).factorial =
          ∏ w ∈ univ.erase u, (n w).factorial :=
        prod_congr rfl fun w hw => by simp [remDisp, ne_of_mem_erase hw]
      rw [hrest, ← mul_assoc]
      congr 1
      simp only [remDisp, if_true]
      rw [mul_assoc, Nat.mul_factorial_pred (by omega : n u - 1 ≠ 0),
        Nat.mul_factorial_pred (by omega : n u ≠ 0)]
    · have hv' : v ∈ univ.erase u := mem_erase.2 ⟨Ne.symm h, mem_univ v⟩
      rw [if_neg h, Nat.sub_zero,
        ← mul_prod_erase univ (fun w => (remDisp n u v w).factorial) (mem_univ u),
        ← mul_prod_erase (univ.erase u) (fun w => (remDisp n u v w).factorial) hv',
        ← mul_prod_erase univ (fun w => (n w).factorial) (mem_univ u),
        ← mul_prod_erase (univ.erase u) (fun w => (n w).factorial) hv']
      have hrest : ∏ w ∈ (univ.erase u).erase v, (remDisp n u v w).factorial =
          ∏ w ∈ (univ.erase u).erase v, (n w).factorial :=
        prod_congr rfl fun w hw => by
          simp [remDisp, ne_of_mem_erase hw, ne_of_mem_erase (mem_of_mem_erase hw)]
      have hru : remDisp n u v u = n u - 1 := by simp [remDisp, h]
      have hrv : remDisp n u v v = n v - 1 := by simp [remDisp, Ne.symm h]
      rw [hrest, hru, hrv, ← Nat.mul_factorial_pred (by omega : n u ≠ 0),
        ← Nat.mul_factorial_pred (by omega : n v ≠ 0)]
      ring
  have hcancel : ∀ u v, (n u : ℝ) * ((n v : ℝ) - if u = v then 1 else 0) * Nm u v =
      c * (1 * (if 1 ≤ n u ∧ 1 ≤ n v ∧ (u = v → 2 ≤ n u) then
        hWeight I ε δ j (extendN fun s => remDisp n u v (s, false))
          (extendN fun s => remDisp n u v (s, true)) else 0) * 1) := by
    intro u v
    by_cases hcond : 1 ≤ n u ∧ 1 ≤ n v ∧ (u = v → 2 ≤ n u)
    · rw [if_pos hcond]
      have hk := hfact u v hcond
      have hsub : ((n v : ℝ) - if u = v then 1 else 0) =
          ((n v - if u = v then 1 else 0 : ℕ) : ℝ) := by
        split_ifs with h
        · rw [Nat.cast_sub (by omega), Nat.cast_one]
        · simp
      have hprod : ∏ s : Fin N, (((remDisp n u v (s, false)).factorial : ℝ) *
            ((remDisp n u v (s, true)).factorial : ℝ) / ((smallB I ε δ s).factorial : ℝ)) =
          (∏ w, ((remDisp n u v w).factorial : ℝ)) /
            ∏ s : Fin N, ((smallB I ε δ s).factorial : ℝ) := by
        rw [prod_div_distrib, Fintype.prod_prod_type]
        congr 1
        refine prod_congr rfl fun s _ => ?_
        rw [Fintype.prod_bool, mul_comm]
      have hk' : (n u : ℝ) * ((n v - if u = v then 1 else 0 : ℕ) : ℝ) *
          ∏ w, ((remDisp n u v w).factorial : ℝ) = ∏ w, ((n w).factorial : ℝ) := by
        exact_mod_cast hk
      simp only [hNm]
      rw [hprod, hc, hsub, ← hk']
      ring
    · have h0 : (n u : ℝ) * ((n v : ℝ) - if u = v then 1 else 0) = 0 := by
        by_cases hu : n u = 0
        · simp [hu]
        by_cases h : u = v
        · subst h
          have : n u = 1 := by
            by_contra hne
            exact hcond ⟨by omega, by omega, fun _ => by omega⟩
          simp [this]
        · have : n v = 0 := by
            by_contra hne
            exact hcond ⟨by omega, by omega, fun e => absurd e h⟩
          simp [this, h]
      rw [if_neg hcond, h0]; simp
  have hR := hWeight_removal_hyp hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas j hj n hbox htot
  have hM := hyp_congr hR c hcpos (fun _ => 1)
  have hNsymm : ∀ u v, Nm u v = Nm v u := by
    intro u v
    have : remDisp n u v = remDisp n v u := by
      funext w; simp only [remDisp]; omega
    simp only [hNm, this]
  have hNdiag : ∀ u, 0 ≤ Nm u u := by
    intro u
    simp only [hNm]
    refine mul_nonneg ?_ (Finset.prod_nonneg fun s _ => by positivity)
    exact Finset.sum_nonneg fun z _ => by positivity
  have hG := hyp_of_groups g Nm hNsymm hNdiag (by
    convert hM using 1
    funext u v
    exact hcancel u v)
  convert hG using 1
  funext x y
  simp only [omMat]
  split_ifs with hxy
  · rfl
  · exact hentry x y hxy

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · proved · `fWeight_base_omitSig` closed (entry/box/total/cancellation steps); rests only
  on `hWeight_removal_hyp` (open in `HWeightRemovalHyp.lean`); constant `c` corrected to
  `∏ n_w! / ∏ b_s!`
-/
