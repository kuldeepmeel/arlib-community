import Cellcounting.Analysis.ChoiceSum
import Cellcounting.Model.Prior
import Cellcounting.Analysis.OmitSigPairSum
import Cellcounting.Analysis.FWeightBaseOmitSig

/-!
# The omission signature of `f_j` (`lem:binary-signatures`, `signatures.tex:201-262`)

`f_j` has the omission property on the full `p`-subset domain of the paired ground set
`[0, 2p)`, and keeps it after fixing elements included or excluded and summing any
disjoint labeled pairs at occupancy one (`lem:binary-contraction`).  In the form used
by `lem:transport`: fix `F` included, sum the pairs of `L` at occupancy one, exclude
everything else; the resulting weight on subsets of `D` of size `|D| - 2` has a
two-omission matrix `omitMat (fWeight I ε δ j) F D L` with at most one positive
eigenvalue (`Hyp`).

The proof follows the paper.  `fWeight_base_omitSig` is the omission property with
positivity of `f_j` on the `p`-subsets of `[0, 2p)` (the group decomposition reducing to
the removal signature of `h_j`, `cor:hj-signatures`).  Summing the pairs of `L` one at a
time keeps it (`omitSig_pairSum`, the cubic-tensor argument of `lem:binary-contraction`):
after the pairs of `L` the weight `U ↦ Σ_c f_j(U ∪ c)` has the omission property on the
`(p - |L|)`-subsets of the elements outside those pairs.  At the display `F ∪ D` (of size
`p - |L| + 2`) its two-omission matrix is `Hyp`, and `omitMat (fWeight I ε δ j) F D L` is
its principal submatrix on `D` (`hyp_comp_inj`); fixing `F` included is exactly this
restriction.
-/

namespace Cellcounting.Analysis

open Finset Pseudocode

/-- **Omission signature of `f_j`, after fixing and pair summation**
(`lem:binary-signatures` with `lem:binary-contraction`): for `F`, `D` and the pairs of
`L` disjoint in `[0, 2p)` with `|F| + |D| + |L| = p + 2`, the two-omission matrix of
`U ↦ Σ_c f_j(F ∪ U ∪ c)` at `D` has at most one positive eigenvalue.
PAPER: sections/signatures.tex:201-210 -/
theorem fWeight_omission (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j ≤ HParam I ε δ)
    (F D : Finset ℕ) (L : List ℕ)
    (hF : ∀ e ∈ F, e < 2 * pSmall I ε δ) (hD : ∀ e ∈ D, e < 2 * pSmall I ε δ)
    (hL : ∀ t ∈ L, t < pSmall I ε δ) (hLnd : L.Nodup) (hFD : Disjoint F D)
    (hLF : ∀ t ∈ L, 2 * t ∉ F ∧ 2 * t + 1 ∉ F) (hLD : ∀ t ∈ L, 2 * t ∉ D ∧ 2 * t + 1 ∉ D)
    (hcard : F.card + D.card + L.length = pSmall I ε δ + 2) :
    Hyp (omitMat (fWeight I ε δ j) F D L) := by
  classical
  set p := pSmall I ε δ with hpdef
  set f := fWeight I ε δ j with hfdef
  have hbase : OmitSig f (range (2 * p)) p :=
    fWeight_base_omitSig hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas j hj
  clear_value p f
  -- a nodup list of pair labels below `p` has at most `p` entries
  have hlenle : ∀ L : List ℕ, L.Nodup → (∀ t ∈ L, t < p) → L.length ≤ p := by
    intro L hnd hlt
    rw [← List.toFinset_card_of_nodup hnd]
    calc L.toFinset.card ≤ (range p).card :=
          card_le_card fun t ht => mem_range.2 (hlt t (List.mem_toFinset.1 ht))
      _ = p := card_range p
  -- summing the pairs of `L` one at a time (`lem:binary-contraction`)
  have key : ∀ L : List ℕ, L.Nodup → (∀ t ∈ L, t < p) →
      OmitSig (fun U => chSum L (fun c => f (U ∪ c)))
        ((range (2 * p)).filter (fun e => e / 2 ∉ L)) (p - L.length) := by
    intro L
    induction L with
    | nil =>
      intro _ _
      have h1 : (range (2 * p)).filter (fun e => e / 2 ∉ ([] : List ℕ)) = range (2 * p) := by
        ext e; simp
      simpa [h1, chSum_nil] using hbase
    | cons t L ih =>
      intro hnd hlt
      obtain ⟨htL, hnd'⟩ := List.nodup_cons.1 hnd
      have ih' := ih hnd' fun s hs => hlt s (List.mem_cons_of_mem _ hs)
      have ht := hlt t (List.mem_cons_self ..)
      have hlen := hlenle _ hnd hlt
      simp only [List.length_cons] at hlen
      have h2t : 2 * t ∈ (range (2 * p)).filter (fun e => e / 2 ∉ L) := by
        refine mem_filter.2 ⟨mem_range.2 (by omega), ?_⟩
        rwa [show 2 * t / 2 = t by omega]
      have h2t1 : 2 * t + 1 ∈ (range (2 * p)).filter (fun e => e / 2 ∉ L) := by
        refine mem_filter.2 ⟨mem_range.2 (by omega), ?_⟩
        rwa [show (2 * t + 1) / 2 = t by omega]
      have hstep := omitSig_pairSum ih' h2t h2t1 (by omega) (by omega)
      have hφ : pairSum (fun U => chSum L (fun c => f (U ∪ c))) (2 * t) (2 * t + 1) =
          fun U => chSum (t :: L) (fun c => f (U ∪ c)) := by
        funext U
        simp only [pairSum, chSum_cons]
        congr 1
        · congr 1; funext c; rw [insert_union, union_insert]
        · congr 1; funext c; rw [insert_union, union_insert]
      have hΓ : (((range (2 * p)).filter (fun e => e / 2 ∉ L)).erase (2 * t)).erase
          (2 * t + 1) = (range (2 * p)).filter (fun e => e / 2 ∉ t :: L) := by
        ext e
        simp only [mem_erase, mem_filter, mem_range, List.mem_cons, not_or]
        constructor
        · rintro ⟨h1, h2, h3, h4⟩
          exact ⟨h3, by omega, h4⟩
        · rintro ⟨h3, h5, h4⟩
          exact ⟨by omega, by omega, h3, h4⟩
      have hk : p - L.length - 1 = p - (t :: L).length := by simp only [List.length_cons]; omega
      rw [hφ, hΓ, hk] at hstep
      exact hstep
  -- the display `F ∪ D` of the summed weight, restricted to `D`
  have hLle := hlenle L hLnd hL
  have hsig := (key L hLnd hL).2 (F ∪ D) ?_ ?_
  rotate_left
  · intro e he
    have hlt : e < 2 * p := (mem_union.1 he).elim (hF e) (hD e)
    refine mem_filter.2 ⟨mem_range.2 hlt, fun hmem => ?_⟩
    have h2 : e = 2 * (e / 2) ∨ e = 2 * (e / 2) + 1 := by omega
    rcases mem_union.1 he with heF | heD
    · rcases h2 with h2 | h2
      · exact (hLF _ hmem).1 (h2 ▸ heF)
      · exact (hLF _ hmem).2 (h2 ▸ heF)
    · rcases h2 with h2 | h2
      · exact (hLD _ hmem).1 (h2 ▸ heD)
      · exact (hLD _ hmem).2 (h2 ▸ heD)
  · rw [card_union_of_disjoint hFD]; omega
  set e : D → (F ∪ D : Finset ℕ) := fun x => ⟨x.1, mem_union_right _ x.2⟩ with he
  have heinj : Function.Injective e := fun a b hab => Subtype.ext (Subtype.mk.inj hab)
  have hR := hyp_comp_inj hsig e heinj
  suffices hfun : omitMat f F D L = fun x y => omMat (fun U => chSum L (fun c => f (U ∪ c)))
      (F ∪ D) (e x) (e y) by
    rw [hfun]; exact hR
  funext x y
  simp only [omitMat, omMat]
  by_cases hxy : x = y
  · subst hxy; simp
  · have hexy : e x ≠ e y := fun h' => hxy (heinj h')
    rw [if_neg hxy, if_neg hexy]
    refine chSum_congr hLnd fun c hc => ?_
    -- a choice set avoids the displayed elements
    have hnot : ∀ z ∈ D, z ∉ c := by
      intro z hz hzc
      have hm := hc.1 z hzc
      have h2 : z = 2 * (z / 2) ∨ z = 2 * (z / 2) + 1 := by omega
      rcases h2 with h2 | h2
      · exact (hLD _ hm).1 (h2 ▸ hz)
      · exact (hLD _ hm).2 (h2 ▸ hz)
    have hxc := hnot x x.2
    have hyc := hnot y y.2
    congr 1
    ext w
    simp only [he, mem_erase, mem_union]
    constructor
    · rintro ⟨hwy, hwx, (hw | hw) | hw⟩
      · exact Or.inl ⟨hwy, hwx, Or.inl hw⟩
      · exact Or.inl ⟨hwy, hwx, Or.inr hw⟩
      · exact Or.inr hw
    · rintro (⟨hwy, hwx, hw⟩ | hw)
      · exact ⟨hwy, hwx, Or.inl hw⟩
      · refine ⟨fun h' => hyc (h' ▸ hw), fun h' => hxc (h' ▸ hw), Or.inr hw⟩

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved from children · assembly by induction on `L`; open children `hyp_cubic_contract_pos`, `hWeight_removal_hyp`, and the bookkeeping inside `fWeight_base_omitSig`
-/
