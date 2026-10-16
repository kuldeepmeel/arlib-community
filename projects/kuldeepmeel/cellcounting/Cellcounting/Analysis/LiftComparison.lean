import Cellcounting.Analysis.ChoiceSum
import Cellcounting.Analysis.TransMassEqCpart
import Cellcounting.Analysis.W0Good
import Cellcounting.Analysis.ImplementationCoupling
import Cellcounting.Model.Prior

/-!
# Comparison of the two lifts (`eq:lift-comparison`, `signatures.tex:62-78`)

`f_j` and `f̃_j` agree on transversals (`lift_trans_eq`: in every cell `x_s + y_s = b_s`,
so both factorial multipliers are `1/binom(b_s, x_s)`), and on a defect class `A_il`
they are within the factor `q = W²` of each other (`lift_defect_le`): if the empty and
the full pair lie in one cell the ratio is one; otherwise one cell contributes
`(x_s + 1)(y_s + 1)` and another `1/(x_s y_s)` to `f̃/f`, both integer products between
one and `W²` because the small bounds are less than `W`.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- **The lifts agree on transversals** (`signatures.tex:36-52`).
PAPER: sections/signatures.tex:41-46 -/
theorem lift_trans_eq (I : Instance) (ε δ : ℚ) (j : ℕ) (S : Finset ℕ)
    (hS : kind I ε δ S = .transversal) : fTilde I ε δ j S = fWeight I ε δ j S := by
  rw [kind_eq_transversal_iff] at hS
  have hbal : ∀ s, (profile I ε δ S).1 s + (profile I ε δ S).2 s = smallB I ε δ s := by
    intro s
    rw [smallB_eq_card]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.range (pSmall I ε δ)).filter fun i => pairCell I ε δ i = s)
      (fun i => 2 * i ∈ S)
    rw [Finset.filter_filter, Finset.filter_filter] at hsplit
    rw [← hsplit]
    unfold profile
    simp only
    congr 2
    apply Finset.filter_congr
    intro i hi
    rw [hS i (Finset.mem_range.1 hi), not_not]
  unfold fTilde fWeight
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  have h := hbal s
  rw [show smallB I ε δ s - (profile I ε δ S).1 s = (profile I ε δ S).2 s by omega,
    show smallB I ε δ s - (profile I ε δ S).2 s = (profile I ε δ S).1 s by omega]
  ring

set_option maxHeartbeats 1000000 in
/-- **Lift comparison on defect states** (`eq:lift-comparison`):
`q⁻¹ f ≤ f̃ ≤ q f` on `A_il`, stated as `f ≤ q f̃` and `f̃ ≤ q f`.
PAPER: sections/signatures.tex:62-78 -/
theorem lift_defect_le (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (j : ℕ) (S : Finset ℕ) (i l : ℕ)
    (hS : kind I ε δ S = .defect i l) :
    fWeight I ε δ j S ≤ (qParam I ε δ : ℝ) * fTilde I ε δ j S ∧
      fTilde I ε δ j S ≤ (qParam I ε δ : ℝ) * fWeight I ε δ j S := by
  classical
  set p := pSmall I ε δ with hp_def
  set n := nSmall I ε δ with hn_def
  set x := (profile I ε δ S).1 with hx_def
  set y := (profile I ε δ S).2 with hy_def
  -- Step 1: extract the defect structure from `kind`.
  rw [w0_kind_eq_defect_iff] at hS
  obtain ⟨hE, hF⟩ := hS
  have hiE : i ∈ (Finset.range p).filter (fun k => 2 * k ∉ S ∧ 2 * k + 1 ∉ S) := by
    rw [hE]; exact Finset.mem_singleton_self i
  have hlF : l ∈ (Finset.range p).filter (fun k => 2 * k ∈ S ∧ 2 * k + 1 ∈ S) := by
    rw [hF]; exact Finset.mem_singleton_self l
  obtain ⟨hip, hiS⟩ := Finset.mem_filter.1 hiE
  obtain ⟨hlp, hlS⟩ := Finset.mem_filter.1 hlF
  have hi : i < p := Finset.mem_range.1 hip
  have hl : l < p := Finset.mem_range.1 hlp
  have hil : i ≠ l := by
    rintro rfl
    exact hiS.1 hlS.1
  -- every other pair occupies exactly one of its two slots.
  have hkey : ∀ k, k < p → k ≠ i → k ≠ l →
      ((2 * k ∈ S ∧ 2 * k + 1 ∉ S) ∨ (2 * k ∉ S ∧ 2 * k + 1 ∈ S)) := by
    intro k hkp hki hkl
    have hkE : ¬ (2 * k ∉ S ∧ 2 * k + 1 ∉ S) := by
      intro h
      apply hki
      have hmem : k ∈ (Finset.range p).filter (fun k => 2 * k ∉ S ∧ 2 * k + 1 ∉ S) :=
        Finset.mem_filter.2 ⟨Finset.mem_range.2 hkp, h⟩
      rw [hE] at hmem
      exact Finset.mem_singleton.1 hmem
    have hkF : ¬ (2 * k ∈ S ∧ 2 * k + 1 ∈ S) := by
      intro h
      apply hkl
      have hmem : k ∈ (Finset.range p).filter (fun k => 2 * k ∈ S ∧ 2 * k + 1 ∈ S) :=
        Finset.mem_filter.2 ⟨Finset.mem_range.2 hkp, h⟩
      rw [hF] at hmem
      exact Finset.mem_singleton.1 hmem
    by_cases h1 : 2 * k ∈ S
    · exact Or.inl ⟨h1, fun h2 => hkF ⟨h1, h2⟩⟩
    · exact Or.inr ⟨h1, by by_contra h2; exact hkE ⟨h1, h2⟩⟩
  -- Step 2: the per-cell count identity `x s + y s + [i's cell = s] = b_s + [l's cell = s]`.
  have hgen : ∀ s : ℕ, x s + y s + (if pairCell I ε δ i = s then 1 else 0) =
      smallB I ε δ s + (if pairCell I ε δ l = s then 1 else 0) := by
    intro s
    set Cs : Finset ℕ := (Finset.range p).filter (fun k => pairCell I ε δ k = s) with hCs_def
    have hxs : x s = ∑ k ∈ Cs, (if 2 * k ∈ S then (1 : ℕ) else 0) := by
      have hshow : x s = ((Finset.range p).filter
          fun k => pairCell I ε δ k = s ∧ 2 * k ∈ S).card := by
        rw [hx_def]; unfold profile; rfl
      rw [hshow, hCs_def]
      simp [Finset.filter_filter]
    have hys : y s = ∑ k ∈ Cs, (if 2 * k + 1 ∈ S then (1 : ℕ) else 0) := by
      have hshow : y s = ((Finset.range p).filter
          fun k => pairCell I ε δ k = s ∧ 2 * k + 1 ∈ S).card := by
        rw [hy_def]; unfold profile; rfl
      rw [hshow, hCs_def]
      simp [Finset.filter_filter]
    have hbs : smallB I ε δ s = Cs.card := by rw [smallB_eq_card, hCs_def]
    have hiCs : i ∈ Cs ↔ pairCell I ε δ i = s := by
      simp [hCs_def, Finset.mem_filter, Finset.mem_range, hi]
    have hlCs : l ∈ Cs ↔ pairCell I ε δ l = s := by
      simp [hCs_def, Finset.mem_filter, Finset.mem_range, hl]
    have hiCs2 : (if pairCell I ε δ i = s then (1 : ℕ) else 0) =
        ∑ k ∈ Cs, (if k = i then (1 : ℕ) else 0) := by
      rw [Finset.sum_ite_eq' Cs i (fun _ => (1 : ℕ))]
      by_cases h : pairCell I ε δ i = s
      · simp [h, hiCs.2 h]
      · have hni : i ∉ Cs := fun hc => h (hiCs.1 hc)
        simp [h, hni]
    have hlCs2 : (if pairCell I ε δ l = s then (1 : ℕ) else 0) =
        ∑ k ∈ Cs, (if k = l then (1 : ℕ) else 0) := by
      rw [Finset.sum_ite_eq' Cs l (fun _ => (1 : ℕ))]
      by_cases h : pairCell I ε δ l = s
      · simp [h, hlCs.2 h]
      · have hnl : l ∉ Cs := fun hc => h (hlCs.1 hc)
        simp [h, hnl]
    have hperk : ∀ k ∈ Cs,
        (if 2 * k ∈ S then (1 : ℕ) else 0) + (if 2 * k + 1 ∈ S then 1 else 0) +
          (if k = i then 1 else 0) = 1 + (if k = l then 1 else 0) := by
      intro k hk
      have hkp : k < p := Finset.mem_range.1 (Finset.mem_filter.1 (hCs_def ▸ hk)).1
      by_cases hki : k = i
      · subst hki; simp [hiS.1, hiS.2, hil]
      · by_cases hkl : k = l
        · subst hkl; simp [hlS.1, hlS.2, Ne.symm hil]
        · rcases hkey k hkp hki hkl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [hki, hkl, h1, h2]
    calc x s + y s + (if pairCell I ε δ i = s then 1 else 0)
        = (∑ k ∈ Cs, (if 2 * k ∈ S then (1 : ℕ) else 0)) +
            (∑ k ∈ Cs, (if 2 * k + 1 ∈ S then (1 : ℕ) else 0)) +
            (∑ k ∈ Cs, (if k = i then (1 : ℕ) else 0)) := by rw [hxs, hys, hiCs2]
      _ = ∑ k ∈ Cs, ((if 2 * k ∈ S then (1 : ℕ) else 0) + (if 2 * k + 1 ∈ S then 1 else 0) +
            (if k = i then 1 else 0)) := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = ∑ k ∈ Cs, (1 + (if k = l then (1 : ℕ) else 0)) := Finset.sum_congr rfl hperk
      _ = Cs.card + (if pairCell I ε δ l = s then 1 else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, hlCs2]
      _ = smallB I ε δ s + (if pairCell I ε δ l = s then 1 else 0) := by rw [hbs]
  -- Step 3: specialize at `s_i = pairCell i`, `s_l = pairCell l`.
  set s_i := pairCell I ε δ i with hsi_def
  set s_l := pairCell I ε δ l with hsl_def
  have hsiN : s_i < n := pairCell_lt I ε δ hi
  have hslN : s_l < n := pairCell_lt I ε δ hl
  have hgen_i := hgen s_i
  have hgen_l := hgen s_l
  rw [if_pos rfl] at hgen_i
  rw [if_pos rfl] at hgen_l
  -- Step 4: the cell-size bound `smallB s < W` for `s < n`.
  have hWbound : ∀ s, s < n → smallB I ε δ s < WParam I ε δ := by
    intro s hs
    rw [hn_def] at hs
    unfold nSmall at hs
    have hmem : smallAt I ε δ s ∈ smallCells I ε δ := by
      rw [smallAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]
      exact List.getElem_mem hs
    have hfil := List.mem_filter.1 hmem
    unfold smallB
    exact of_decide_eq_true hfil.2
  by_cases heq : s_i = s_l
  · -- Same cell: both lifts coincide, so the ratio is exactly `1`.
    have hbal : ∀ s, x s + y s = smallB I ε δ s := by
      intro s
      have h := hgen s
      rw [heq] at h
      omega
    have heqft : fTilde I ε δ j S = fWeight I ε δ j S := by
      unfold fTilde fWeight
      congr 1
      refine Finset.prod_congr rfl fun s _ => ?_
      have h := hbal s
      rw [show smallB I ε δ s - x s = y s by omega,
        show smallB I ε δ s - y s = x s by omega]
      ring
    have hfW : 0 < fWeight I ε δ j S := by
      unfold fWeight
      refine mul_pos ?_ (Finset.prod_pos fun s _ => by positivity)
      refine Finset.sum_pos (fun z _ => by positivity) ?_
      exact ⟨fun _ => 0, by simp [freeBox]⟩
    have hq1 : (1 : ℝ) ≤ (qParam I ε δ : ℝ) := by
      have hW : 0 < WParam I ε δ := lt_of_le_of_lt (Nat.zero_le _) (hWbound s_i hsiN)
      have : (1 : ℕ) ≤ qParam I ε δ := by
        rw [qParam]; nlinarith [Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 hW)]
      exact_mod_cast this
    rw [heqft]
    constructor
    · nlinarith [hfW.le]
    · nlinarith [hfW.le]
  · -- Different cells: the two exceptional factors give the `W²` ratio.
    have hsiN_mem : s_i ∈ Finset.range n := Finset.mem_range.2 hsiN
    have hsl_erase_mem : s_l ∈ (Finset.range n).erase s_i :=
      Finset.mem_erase.2 ⟨Ne.symm heq, Finset.mem_range.2 hslN⟩
    rw [if_neg (Ne.symm heq)] at hgen_i
    rw [if_neg heq] at hgen_l
    simp only [add_zero] at hgen_i hgen_l
    -- `l`'s own pair witnesses `x s_l ≥ 1` and `y s_l ≥ 1`.
    have hxl_pos : 1 ≤ x s_l := by
      have hshow : x s_l = ((Finset.range p).filter
          fun k => pairCell I ε δ k = s_l ∧ 2 * k ∈ S).card := by
        rw [hx_def]; unfold profile; rfl
      rw [hshow]
      refine Finset.card_pos.2 ⟨l, Finset.mem_filter.2 ⟨Finset.mem_range.2 hl, rfl, hlS.1⟩⟩
    have hyl_pos : 1 ≤ y s_l := by
      have hshow : y s_l = ((Finset.range p).filter
          fun k => pairCell I ε δ k = s_l ∧ 2 * k + 1 ∈ S).card := by
        rw [hy_def]; unfold profile; rfl
      rw [hshow]
      refine Finset.card_pos.2 ⟨l, Finset.mem_filter.2 ⟨Finset.mem_range.2 hl, rfl, hlS.2⟩⟩
    have hbal_other : ∀ s, s ≠ s_i → s ≠ s_l → x s + y s = smallB I ε δ s := by
      intro s hsi hsl
      have h := hgen s
      rw [if_neg (Ne.symm hsi), if_neg (Ne.symm hsl)] at h
      omega
    -- the exceptional-factor bounds.
    have hWi : (x s_i + 1) * (y s_i + 1) ≤ qParam I ε δ := by
      have hb : smallB I ε δ s_i < WParam I ε δ := hWbound s_i hsiN
      rw [qParam]
      nlinarith [hgen_i]
    have hWl : x s_l * y s_l ≤ qParam I ε δ := by
      have hb : smallB I ε δ s_l < WParam I ε δ := hWbound s_l hslN
      rw [qParam]
      nlinarith [hgen_l]
    -- the product splitting over the two exceptional cells.
    have hsplit : ∀ h : ℕ → ℝ, ∏ s ∈ Finset.range n, h s =
        h s_i * (h s_l * ∏ s ∈ (Finset.range n).erase s_i |>.erase s_l, h s) := by
      intro h
      rw [Finset.mul_prod_erase _ h hsl_erase_mem, Finset.mul_prod_erase _ h hsiN_mem]
    set Fh : ℕ → ℝ := fun s =>
      ((x s).factorial : ℝ) * ((y s).factorial : ℝ) / ((smallB I ε δ s).factorial : ℝ)
      with hFh_def
    set Gh : ℕ → ℝ := fun s =>
      (((smallB I ε δ s - x s)).factorial : ℝ) * (((smallB I ε δ s - y s)).factorial : ℝ) /
        ((smallB I ε δ s).factorial : ℝ) with hGh_def
    have hFWeight : fWeight I ε δ j S =
        hWeight I ε δ j x y * ∏ s ∈ Finset.range n, Fh s := by
      rw [hx_def, hy_def]; unfold fWeight; rfl
    have hFTilde : fTilde I ε δ j S =
        hWeight I ε δ j x y * ∏ s ∈ Finset.range n, Gh s := by
      rw [hx_def, hy_def]; unfold fTilde; rfl
    have hRest : ∀ s ∈ (Finset.range n).erase s_i |>.erase s_l, Gh s = Fh s := by
      intro s hs
      obtain ⟨hsl', hs'⟩ := Finset.mem_erase.1 hs
      obtain ⟨hsi', -⟩ := Finset.mem_erase.1 hs'
      have h := hbal_other s hsi' hsl'
      rw [hGh_def, hFh_def]
      simp only
      rw [show smallB I ε δ s - x s = y s by omega,
        show smallB I ε δ s - y s = x s by omega]
      ring
    have hGi : Gh s_i = ((x s_i : ℝ) + 1) * ((y s_i : ℝ) + 1) * Fh s_i := by
      rw [hGh_def, hFh_def]
      simp only
      rw [show smallB I ε δ s_i - x s_i = y s_i + 1 by omega,
        show smallB I ε δ s_i - y s_i = x s_i + 1 by omega,
        Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have hFl : Fh s_l = (x s_l : ℝ) * (y s_l : ℝ) * Gh s_l := by
      rw [hGh_def, hFh_def]
      simp only
      have factx : (x s_l).factorial = x s_l * (x s_l - 1).factorial := by
        conv_lhs => rw [show x s_l = (x s_l - 1) + 1 by omega]
        rw [Nat.factorial_succ]
        congr 1
        omega
      have facty : (y s_l).factorial = y s_l * (y s_l - 1).factorial := by
        conv_lhs => rw [show y s_l = (y s_l - 1) + 1 by omega]
        rw [Nat.factorial_succ]
        congr 1
        omega
      rw [factx, facty, show smallB I ε δ s_l - x s_l = y s_l - 1 by omega,
        show smallB I ε δ s_l - y s_l = x s_l - 1 by omega]
      push_cast
      ring
    have hkeyeq : fTilde I ε δ j S * ((x s_l : ℝ) * (y s_l : ℝ)) =
        ((x s_i : ℝ) + 1) * ((y s_i : ℝ) + 1) * fWeight I ε δ j S := by
      rw [hFWeight, hFTilde, hsplit Fh, hsplit Gh,
        Finset.prod_congr rfl hRest, hGi, hFl]
      ring
    have hfW : 0 < fWeight I ε δ j S := by
      unfold fWeight
      refine mul_pos ?_ (Finset.prod_pos fun s _ => by positivity)
      refine Finset.sum_pos (fun z _ => by positivity) ?_
      exact ⟨fun _ => 0, by simp [freeBox]⟩
    have hfT : 0 < fTilde I ε δ j S := by
      unfold fTilde
      refine mul_pos ?_ (Finset.prod_pos fun s _ => by positivity)
      refine Finset.sum_pos (fun z _ => by positivity) ?_
      exact ⟨fun _ => 0, by simp [freeBox]⟩
    have hWi' : ((x s_i : ℝ) + 1) * ((y s_i : ℝ) + 1) ≤ (qParam I ε δ : ℝ) := by
      exact_mod_cast hWi
    have hWl1 : (1 : ℝ) ≤ (x s_l : ℝ) * (y s_l : ℝ) := by
      have : (1 : ℕ) ≤ x s_l * y s_l := Nat.mul_le_mul hxl_pos hyl_pos
      exact_mod_cast this
    have hWl' : (x s_l : ℝ) * (y s_l : ℝ) ≤ (qParam I ε δ : ℝ) := by exact_mod_cast hWl
    have hWi_ge1 : (1 : ℝ) ≤ ((x s_i : ℝ) + 1) * ((y s_i : ℝ) + 1) := by
      have hx0 : (0 : ℝ) ≤ (x s_i : ℝ) := Nat.cast_nonneg _
      have hy0 : (0 : ℝ) ≤ (y s_i : ℝ) := Nat.cast_nonneg _
      nlinarith
    constructor
    · nlinarith [hkeyeq, hfT.le, hfW.le, hWl', hWi_ge1,
        mul_le_mul_of_nonneg_right hWl' hfT.le,
        mul_le_mul_of_nonneg_right hWi_ge1 hfW.le]
    · nlinarith [hkeyeq, hfW.le, hfT.le, hWi', hWl1,
        mul_le_mul_of_nonneg_right hWi' hfW.le,
        mul_le_mul_of_nonneg_left hWl1 hfT.le]

end Cellcounting.Analysis
