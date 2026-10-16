import Cellcounting.Analysis.TransportDirichlet
import Cellcounting.Model.Prior
import Cellcounting.Analysis.SlotTransport
import Cellcounting.Analysis.FWeightOmission
import Cellcounting.Analysis.DefectInequalities
import Cellcounting.Analysis.LiftComparison

/-!
# Variance on transversals (`prop:transversal-variance`, `transport.tex:318-428`)

For good multipliers and every real `g` on `X`, `C(j) Var_μ(g) ≤ C_p 𝔇(g)`, with
`μ = f_j / C(j)` on transversals and `C_p = p (1 + 8 p q²)` (`CpParam`).

The proof is the paper's conditioning tree, run as an induction on the number of
unassigned pairs.  A node is a partial assignment `σ` with unassigned pairs `T`
(`AsgValid`); `tvVar` is its unnormalized transversal variance
`Σ f g² - (Σ f g)² / z_σ` (sums over transversals respecting `σ`, as `chSum`s) and
`tvDir σ` the edge energy `𝔇_σ` restricted to edges whose endpoints respect `σ`.

* `tv_sink`: a sink `k ∈ T` with `a_kt ≤ 1` for all other `t`, from the pair
  inequalities `defect_two_pair`, `defect_three_pair` (`eq:sink-products`).
* `tv_var_split`: the conditional variance identity at the branching on pair `k`.
* `tv_node_charge` (`eq:conditional-variance-charge`): the between-means term is at
  most `(1 + 8 p q²) 𝔇_σ(g)`, from `slot_transport` (singleton slots `2k`, `2k + 1`,
  ordinary slots the other unassigned pairs, `W_t = w_tk`), the omission signature
  `fWeight_omission`, the good-multiplier bound and the lift comparison
  (`eq:sink-comparison`), and the identification of the one-hole states with states of
  `X` (`tv_clique_le`).
* `tv_dir_split`: the two children's energies are at most the parent's.

The root is `σ = ∅`, `T = [0, p)`: `tv_root_var` (`C Var_μ = tvVar`, via the bridge
`tv_trans_eq` from `transStates` to `chSum`) and `tv_root_dir` (`𝔇_∅ = 𝔇`).  The
unconditional defect masses of `goodMult` enter through the bridge `tv_cDef_eq`.

Everything in this file is proved; the paper inputs it rests on are the separately
owned `slot_transport` (`lem:transport`), `fWeight_omission` (`lem:binary-signatures`
for `f`), `defect_two_pair`/`defect_three_pair` (`lem:defect-inequalities`) and
`lift_trans_eq`/`lift_defect_le` (`eq:lift-comparison`).
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: `S` respects the partial assignment `σ`: it contains each chosen element
and not its mate.
TEXLINE: sections/signatures.tex:303-310 -/
def tvResp (σ S : Finset ℕ) : Prop := ∀ e ∈ σ, e ∈ S ∧ ∀ e' ∈ S, e' / 2 = e / 2 → e' = e

open Classical in
/-- INTERNAL: `𝔇_σ(g)`, the edge energy restricted to exchange edges of `X` whose two
endpoints respect `σ`.
TEXLINE: sections/transport.tex:388-392 -/
noncomputable def tvDir (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (g : Finset ℕ → ℝ) (σ : Finset ℕ) : ℝ :=
  (∑ S ∈ chainStates I ε δ, ∑ S' ∈ chainStates I ε δ,
    if exchNbr S S' ∧ tvResp σ S ∧ tvResp σ S' then
      min (refLam I ε δ S j w) (refLam I ε δ S' j w) * (g S - g S') ^ 2
    else 0) / 2

/-- INTERNAL: `z_σ Var_{μ_σ}(g) = Σ φ g² - (Σ φ g)² / z_σ` over the transversals
respecting `σ`.
TEXLINE: sections/transport.tex:396-404 -/
noncomputable def tvVar (φ g : Finset ℕ → ℝ) (σ : Finset ℕ) (T : List ℕ) : ℝ :=
  chSum T (fun c => φ (σ ∪ c) * g (σ ∪ c) ^ 2) -
    chSum T (fun c => φ (σ ∪ c) * g (σ ∪ c)) ^ 2 / trMass φ σ T

/-- INTERNAL: a node assigns `|σ|` pairs and leaves `|T|` unassigned: `|σ| + |T| = p`. -/
theorem tv_card {p : ℕ} {σ : Finset ℕ} {T : List ℕ} (hv : AsgValid p σ T) :
    σ.card + T.length = p := by
  classical
  obtain ⟨hnd, hlt, hσlt, hinj, hiff⟩ := hv
  have h1 : (σ.image (· / 2)).card = σ.card :=
    Finset.card_image_of_injOn fun e he e' he' h => hinj e he e' he' h
  have h2 : σ.image (· / 2) = (Finset.range p).filter (fun t => t ∉ T) := by
    ext t
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨e, he, rfl⟩
      have := hσlt e he
      refine ⟨by omega, fun ht => (hiff _ (by omega)).1 ht e he rfl⟩
    · rintro ⟨ht, hnT⟩
      by_contra hcon
      push Not at hcon
      exact hnT ((hiff t ht).2 fun e he h => hcon e he h)
  have h3 : (Finset.range p).filter (fun t => t ∈ T) = T.toFinset := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨hlt t h, h⟩⟩
  have h4 := Finset.card_filter_add_card_filter_not
    (s := Finset.range p) (fun t => t ∈ T)
  rw [h3, ← h2, h1, List.toFinset_card_of_nodup hnd, Finset.card_range] at h4
  omega

/-- INTERNAL: the root node `σ = ∅`, `T = [0, p)` is valid. -/
theorem tv_root_valid' (p : ℕ) : AsgValid p ∅ (List.range p) :=
  ⟨List.nodup_range, fun t ht => List.mem_range.1 ht, by simp, by simp,
    fun t ht => by simp [ht]⟩

/-- INTERNAL: `f̃_j(S) > 0`. -/
theorem tv_fTilde_pos (I : Instance) (ε δ : ℚ) (j : ℕ) (S : Finset ℕ) :
    0 < fTilde I ε δ j S := by
  unfold fTilde
  refine mul_pos ?_ (Finset.prod_pos fun s _ => by positivity)
  exact Finset.sum_pos (fun z _ => by positivity) ⟨fun _ => 0, by simp [freeBox]⟩

/-- INTERNAL: defect masses are positive. -/
theorem tv_defMass_pos (φ : Finset ℕ → ℝ) (hφ : ∀ S, 0 < φ S) (σ : Finset ℕ) (T : List ℕ)
    (hT : T.Nodup) (i l : ℕ) : 0 < defMass φ σ T i l :=
  chSum_pos ((hT.erase i).erase l) fun _ _ => hφ _

/-- INTERNAL: transversal masses are positive.
TEXLINE: sections/signatures.tex:311-318 -/
theorem tv_trMass_pos (I : Instance) (ε δ : ℚ) (j : ℕ) (σ : Finset ℕ) (T : List ℕ)
    (hT : T.Nodup) : 0 < trMass (fWeight I ε δ j) σ T :=
  chSum_pos hT fun _ _ => td_fWeight_pos I ε δ j _

/-- INTERNAL: `σ` has no element in an unassigned pair. -/
theorem tv_sigma_none {p : ℕ} {σ : Finset ℕ} {T : List ℕ} (hv : AsgValid p σ T) {t : ℕ}
    (ht : t ∈ T) : 2 * t ∉ σ ∧ 2 * t + 1 ∉ σ := by
  have h := (hv.2.2.2.2 t (hv.2.1 t ht)).1 ht
  exact ⟨fun hm => h _ hm (by omega), fun hm => h _ hm (by omega)⟩

/-- INTERNAL: `σ` has exactly one element in an assigned pair. -/
theorem tv_sigma_pair {p : ℕ} {σ : Finset ℕ} {T : List ℕ} (hv : AsgValid p σ T) {t : ℕ}
    (htp : t < p) (ht : t ∉ T) :
    (2 * t ∈ σ ∧ 2 * t + 1 ∉ σ) ∨ (2 * t ∉ σ ∧ 2 * t + 1 ∈ σ) := by
  obtain ⟨-, -, -, hinj, hiff⟩ := hv
  have : ¬ ∀ e ∈ σ, e / 2 ≠ t := fun h => ht ((hiff t htp).2 h)
  push Not at this
  obtain ⟨e, he, het⟩ := this
  obtain ⟨b, hb, rfl⟩ : ∃ b < 2, e = 2 * t + b := ⟨e % 2, Nat.mod_lt _ (by norm_num), by omega⟩
  interval_cases b
  · left
    refine ⟨by simpa using he, fun h => ?_⟩
    have := hinj _ h _ he (by omega)
    omega
  · right
    refine ⟨fun h => ?_, he⟩
    have := hinj _ h _ he (by omega)
    omega

/-- INTERNAL: elements of `σ` lie in assigned pairs. -/
theorem tv_sigma_notT {p : ℕ} {σ : Finset ℕ} {T : List ℕ} (hv : AsgValid p σ T) {e : ℕ}
    (he : e ∈ σ) : e / 2 ∉ T := fun h =>
  (hv.2.2.2.2 _ (hv.2.1 _ h)).1 h e he rfl

/-- INTERNAL: a state with pair `i` empty, pair `l` full and every other pair of
`[0, p)` singly occupied has type `A_il`. -/
theorem tv_kind_defect_of {I : Instance} {ε δ : ℚ} {S : Finset ℕ} {i l : ℕ}
    (hi : i < pSmall I ε δ) (hl : l < pSmall I ε δ)
    (hE : ∀ t < pSmall I ε δ, (2 * t ∉ S ∧ 2 * t + 1 ∉ S) ↔ t = i)
    (hF : ∀ t < pSmall I ε δ, (2 * t ∈ S ∧ 2 * t + 1 ∈ S) ↔ t = l) :
    kind I ε δ S = .defect i l := by
  have hE' : ((Finset.range (pSmall I ε δ)).filter fun t => 2 * t ∉ S ∧ 2 * t + 1 ∉ S) = {i} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨ht, h⟩; exact (hE t ht).1 h
    · rintro rfl; exact ⟨hi, (hE t hi).2 rfl⟩
  have hF' : ((Finset.range (pSmall I ε δ)).filter fun t => 2 * t ∈ S ∧ 2 * t + 1 ∈ S) = {l} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨ht, h⟩; exact (hF t ht).1 h
    · rintro rfl; exact ⟨hl, (hF t hl).2 rfl⟩
  unfold kind
  simp only [hE', hF', Finset.card_singleton, Finset.sup_singleton, id]
  simp

/-- INTERNAL: a choice of the unassigned pairs completes `σ` to a transversal.
TEXLINE: sections/signatures.tex:303-318 -/
theorem tv_kind_trans {I : Instance} {ε δ : ℚ} {σ : Finset ℕ} {T : List ℕ}
    (hv : AsgValid (pSmall I ε δ) σ T) {c : Finset ℕ} (hc : IsChoice T c) :
    kind I ε δ (σ ∪ c) = .transversal := by
  rw [kind_eq_transversal_iff]
  intro t htp
  by_cases ht : t ∈ T
  · obtain ⟨h0, h1⟩ := tv_sigma_none hv ht
    simp only [Finset.mem_union, h0, h1, false_or]
    exact hc.2 t ht
  · have hc0 : 2 * t ∉ c := fun h => ht (by simpa using hc.1 _ h)
    have hc1 : 2 * t + 1 ∉ c := fun h => ht (by
      have := hc.1 _ h; rwa [show (2 * t + 1) / 2 = t by omega] at this)
    rcases tv_sigma_pair hv htp ht with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
      simp [Finset.mem_union, h0, h1, hc0, hc1]

/-- INTERNAL: emptying pair `i` and filling pair `l` of such a completion gives a state
of `A_il`.
TEXLINE: sections/signatures.tex:303-318 -/
theorem tv_kind_defect {I : Instance} {ε δ : ℚ} {σ : Finset ℕ} {T : List ℕ}
    (hv : AsgValid (pSmall I ε δ) σ T) {i l : ℕ} (hi : i ∈ T) (hl : l ∈ T) (hil : i ≠ l)
    {c : Finset ℕ} (hc : IsChoice ((T.erase i).erase l) c) :
    kind I ε δ (insert (2 * l) (insert (2 * l + 1) (σ ∪ c))) = .defect i l := by
  have hip := hv.2.1 i hi
  have hlp := hv.2.1 l hl
  set T' := (T.erase i).erase l
  -- pairs met by `c`
  have hcT : ∀ e ∈ c, e / 2 ∈ T ∧ e / 2 ≠ i ∧ e / 2 ≠ l := by
    intro e he
    have h := hc.1 e he
    have hne_l : e / 2 ≠ l := fun h' => (hv.1.erase i).not_mem_erase (h' ▸ h)
    have h2 := List.mem_of_mem_erase h
    have hne_i : e / 2 ≠ i := fun h' => hv.1.not_mem_erase (h' ▸ h2)
    exact ⟨List.mem_of_mem_erase h2, hne_i, hne_l⟩
  have hc0 : ∀ t, t ∉ T' → 2 * t ∉ c := fun t ht h => ht (by simpa using hc.1 _ h)
  have hc1 : ∀ t, t ∉ T' → 2 * t + 1 ∉ c := fun t ht h => ht (by
    have := hc.1 _ h; rwa [show (2 * t + 1) / 2 = t by omega] at this)
  have hmemT' : ∀ t, t ∈ T → t ≠ i → t ≠ l → t ∈ T' := fun t ht h1 h2 =>
    (List.mem_erase_of_ne h2).2 ((List.mem_erase_of_ne h1).2 ht)
  have hiT' : i ∉ T' := fun h => hv.1.not_mem_erase (List.mem_of_mem_erase h)
  have hlT' : l ∉ T' := (hv.1.erase i).not_mem_erase
  apply tv_kind_defect_of hip hlp
  · intro t htp
    constructor
    · intro ⟨h0, h1⟩
      by_contra hti
      simp only [Finset.mem_insert, Finset.mem_union, not_or] at h0 h1
      by_cases htT : t ∈ T
      · by_cases htl : t = l
        · exact h0.1 (by rw [htl])
        · have hT' := hmemT' t htT hti htl
          have := hc.2 t hT'
          tauto
      · rcases tv_sigma_pair hv htp htT with ⟨h, -⟩ | ⟨-, h⟩
        · exact h0.2.2.1 h
        · exact h1.2.2.1 h
    · rintro rfl
      obtain ⟨s0, s1⟩ := tv_sigma_none hv hi
      simp only [Finset.mem_insert, Finset.mem_union, not_or]
      refine ⟨⟨by omega, by omega, s0, hc0 _ hiT'⟩, ⟨by omega, by omega, s1, hc1 _ hiT'⟩⟩
  · intro t htp
    constructor
    · intro ⟨h0, h1⟩
      by_contra htl
      simp only [Finset.mem_insert, Finset.mem_union] at h0 h1
      have e0 : 2 * t ∈ σ ∨ 2 * t ∈ c := by
        rcases h0 with h | h | h
        · omega
        · omega
        · exact h
      have e1 : 2 * t + 1 ∈ σ ∨ 2 * t + 1 ∈ c := by
        rcases h1 with h | h | h
        · omega
        · omega
        · exact h
      by_cases htT : t ∈ T
      · obtain ⟨s0, s1⟩ := tv_sigma_none hv htT
        have hc0' : 2 * t ∈ c := e0.resolve_left s0
        have hc1' : 2 * t + 1 ∈ c := e1.resolve_left s1
        have hT' : t ∈ T' := by
          have := hc.1 _ hc0'; simpa using this
        exact ((hc.2 t hT').1 hc0') hc1'
      · have hc0' : 2 * t ∉ c := fun h => htT (by simpa using (hcT _ h).1)
        have hc1' : 2 * t + 1 ∉ c := fun h => htT (by
          have := (hcT _ h).1; rwa [show (2 * t + 1) / 2 = t by omega] at this)
        have s0 := e0.resolve_right hc0'
        have s1 := e1.resolve_right hc1'
        rcases tv_sigma_pair hv htp htT with ⟨-, h⟩ | ⟨h, -⟩
        · exact h s1
        · exact h s0
    · rintro rfl
      simp

/-- INTERNAL: the finset of choice sets of the pairs of `L` (one element of each). -/
noncomputable def tvChFin : List ℕ → Finset (Finset ℕ)
  | [] => {∅}
  | t :: L => (tvChFin L).image (insert (2 * t)) ∪ (tvChFin L).image (insert (2 * t + 1))

/-- INTERNAL: `tvChFin L` is exactly the set of choice sets of `L`. -/
theorem mem_tvChFin {L : List ℕ} (hL : L.Nodup) {c : Finset ℕ} :
    c ∈ tvChFin L ↔ IsChoice L c := by
  induction L generalizing c with
  | nil => simp [tvChFin, isChoice_nil]
  | cons t L ih =>
    obtain ⟨ht, hL'⟩ := List.nodup_cons.1 hL
    simp only [tvChFin, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (⟨c', hc', rfl⟩ | ⟨c', hc', rfl⟩)
      · simpa using isChoice_insert ht ((ih hL').1 hc') 0 (by norm_num)
      · exact isChoice_insert ht ((ih hL').1 hc') 1 (by norm_num)
    · intro hc
      obtain ⟨h1, h2⟩ := hc
      have key : ∀ a, a / 2 = t → a ∈ c → IsChoice L (c.erase a) := by
        intro a ha hac
        refine ⟨fun e he => ?_, fun t' ht' => ?_⟩
        · obtain ⟨hea, hec⟩ := Finset.mem_erase.1 he
          rcases List.mem_cons.1 (h1 e hec) with h | h
          · exfalso
            have hpair := h2 t (List.mem_cons_self)
            have : e = 2 * t ∨ e = 2 * t + 1 := by omega
            have : a = 2 * t ∨ a = 2 * t + 1 := by omega
            rcases this with rfl | rfl <;> rcases ‹e = 2 * t ∨ e = 2 * t + 1› with rfl | rfl
            · exact hea rfl
            · exact (hpair.1 hac) hec
            · exact (hpair.1 hec) hac
            · exact hea rfl
          · exact h
        · have htt : t' ≠ t := fun h => ht (h ▸ ht')
          have e1 : 2 * t' ≠ a := by omega
          have e2 : 2 * t' + 1 ≠ a := by omega
          simp only [Finset.mem_erase, ne_eq, e1, e2, not_false_eq_true, true_and]
          exact h2 t' (List.mem_cons_of_mem _ ht')
      by_cases h0 : 2 * t ∈ c
      · left
        exact ⟨c.erase (2 * t), (ih hL').2 (key _ (by omega) h0), Finset.insert_erase h0⟩
      · right
        have h1' : 2 * t + 1 ∈ c := by
          by_contra h'
          exact h0 ((h2 t List.mem_cons_self).2 h')
        exact ⟨c.erase (2 * t + 1), (ih hL').2 (key _ (by omega) h1'), Finset.insert_erase h1'⟩

/-- INTERNAL: `chSum` is the sum over `tvChFin`. -/
theorem chSum_eq_sum_tvChFin {L : List ℕ} (hL : L.Nodup) (φ : Finset ℕ → ℝ) :
    chSum L φ = ∑ c ∈ tvChFin L, φ c := by
  induction L generalizing φ with
  | nil => simp [chSum_nil, tvChFin]
  | cons t L ih =>
    obtain ⟨ht, hL'⟩ := List.nodup_cons.1 hL
    have hno : ∀ c ∈ tvChFin L, 2 * t ∉ c ∧ 2 * t + 1 ∉ c := by
      intro c hc
      have h := ((mem_tvChFin hL').1 hc).1
      exact ⟨fun h' => ht (by simpa using h _ h'), fun h' => ht (by
        have := h _ h'; rwa [show (2 * t + 1) / 2 = t by omega] at this)⟩
    have hinj : ∀ a, (∀ c ∈ tvChFin L, a ∉ c) → Set.InjOn (insert a) (↑(tvChFin L) : Set (Finset ℕ)) := by
      intro a ha c1 hc1 c2 hc2 h
      have e1 := Finset.erase_insert (ha c1 hc1)
      have e2 := Finset.erase_insert (ha c2 hc2)
      rw [← e1, ← e2]
      exact congrArg (fun x => Finset.erase x a) h
    rw [chSum_cons, ih hL', ih hL', tvChFin, Finset.sum_union, Finset.sum_image, Finset.sum_image]
    · exact hinj _ fun c hc => (hno c hc).2
    · exact hinj _ fun c hc => (hno c hc).1
    · rw [Finset.disjoint_left]
      intro S h1 h2
      obtain ⟨c1, hc1, rfl⟩ := Finset.mem_image.1 h1
      obtain ⟨c2, hc2, h⟩ := Finset.mem_image.1 h2
      have : 2 * t ∈ insert (2 * t + 1) c2 := by rw [h]; exact Finset.mem_insert_self _ _
      rcases Finset.mem_insert.1 this with h' | h'
      · omega
      · exact (hno c2 hc2).1 h'

/-- INTERNAL: the lifts have equal transversal masses (`eq:transversal-mass`).
TEXLINE: sections/signatures.tex:47-52 -/
theorem tv_trMass_lift {I : Instance} {ε δ : ℚ} (j : ℕ) {σ : Finset ℕ} {T : List ℕ}
    (hv : AsgValid (pSmall I ε δ) σ T) :
    trMass (fTilde I ε δ j) σ T = trMass (fWeight I ε δ j) σ T :=
  chSum_congr hv.1 fun _ hc => lift_trans_eq I ε δ j _ (tv_kind_trans hv hc)

/-- INTERNAL: `c^σ_il ≤ q c̃^σ_il` (`eq:lift-comparison` on `A_il`).
TEXLINE: sections/transport.tex:376-385 -/
theorem tv_defMass_lift (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (j : ℕ) {σ : Finset ℕ} {T : List ℕ}
    (hv : AsgValid (pSmall I ε δ) σ T) {i l : ℕ} (hi : i ∈ T) (hl : l ∈ T) (hil : i ≠ l) :
    defMass (fWeight I ε δ j) σ T i l ≤
      (qParam I ε δ : ℝ) * defMass (fTilde I ε δ j) σ T i l := by
  unfold defMass
  rw [← chSum_mul_left]
  exact chSum_mono ((hv.1.erase i).erase l) fun c hc =>
    (lift_defect_le hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas j _ i l
      (tv_kind_defect hv hi hl hil hc)).1

/-- INTERNAL: a state of type `A_il` has pair `i` empty, pair `l` full, the others
singly occupied. -/
theorem tv_of_kind_defect {I : Instance} {ε δ : ℚ} {S : Finset ℕ} {i l : ℕ}
    (h : kind I ε δ S = .defect i l) :
    (∀ t < pSmall I ε δ, (2 * t ∉ S ∧ 2 * t + 1 ∉ S) ↔ t = i) ∧
      (∀ t < pSmall I ε δ, (2 * t ∈ S ∧ 2 * t + 1 ∈ S) ↔ t = l) := by
  unfold kind at h
  simp only at h
  split_ifs at h with hE hF hEF
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := And.intro (Finset.card_eq_one.1 hEF.1)
    (Finset.card_eq_one.1 hEF.2)
  rw [ha, hb] at h
  simp only [Finset.sup_singleton, id, Program.Kind.defect.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  constructor
  · intro t ht
    have := congrArg (fun F => t ∈ F) ha
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, eq_iff_iff] at this
    rw [← this]; simp [ht]
  · intro t ht
    have := congrArg (fun F => t ∈ F) hb
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, eq_iff_iff] at this
    rw [← this]; simp [ht]

open Classical in
/-- INTERNAL: the unconditional defect mass `c_il` as a `chSum`.
TEXLINE: sections/transport.tex:45-58 -/
theorem tv_cDef_eq (I : Instance) (ε δ : ℚ) (φ : Finset ℕ → ℝ) (i l : ℕ)
    (hi : i < pSmall I ε δ) (hl : l < pSmall I ε δ) (hil : i ≠ l) :
    (∑ S ∈ (refStates I ε δ).filter (fun S => kind I ε δ S = .defect i l), φ S) =
      defMass φ ∅ (List.range (pSmall I ε δ)) i l := by
  set p := pSmall I ε δ with hpdef
  set R := List.range p
  set R2 := (R.erase i).erase l
  have hR2 : R2.Nodup := (List.nodup_range.erase i).erase l
  have hiR : i ∈ R := List.mem_range.2 hi
  have hlR : l ∈ R := List.mem_range.2 hl
  have hR2mem : ∀ t, t ∈ R2 ↔ t < p ∧ t ≠ i ∧ t ≠ l := by
    intro t
    constructor
    · intro h
      have hne_l : t ≠ l := fun h' => ((List.nodup_range).erase i).not_mem_erase (h' ▸ h)
      have h2 := List.mem_of_mem_erase h
      have hne_i : t ≠ i := fun h' => List.nodup_range.not_mem_erase (h' ▸ h2)
      exact ⟨List.mem_range.1 (List.mem_of_mem_erase h2), hne_i, hne_l⟩
    · rintro ⟨h1, h2, h3⟩
      exact (List.mem_erase_of_ne h3).2 ((List.mem_erase_of_ne h2).2 (List.mem_range.2 h1))
  have hno : ∀ c ∈ tvChFin R2, 2 * l ∉ c ∧ 2 * l + 1 ∉ c := by
    intro c hc
    have h := ((mem_tvChFin hR2).1 hc).1
    refine ⟨fun h' => ?_, fun h' => ?_⟩
    · have := (hR2mem _).1 (h _ h'); omega
    · have := (hR2mem _).1 (h _ h'); omega
  have hinj : Set.InjOn (fun c => insert (2 * l) (insert (2 * l + 1) c))
      (↑(tvChFin R2) : Set (Finset ℕ)) := by
    intro c1 hc1 c2 hc2 h
    have e1 : ((insert (2 * l) (insert (2 * l + 1) c1)).erase (2 * l)).erase (2 * l + 1) = c1 := by
      rw [Finset.erase_insert (by
        simp only [Finset.mem_insert, not_or]; exact ⟨by omega, (hno c1 hc1).1⟩),
        Finset.erase_insert (hno c1 hc1).2]
    have e2 : ((insert (2 * l) (insert (2 * l + 1) c2)).erase (2 * l)).erase (2 * l + 1) = c2 := by
      rw [Finset.erase_insert (by
        simp only [Finset.mem_insert, not_or]; exact ⟨by omega, (hno c2 hc2).1⟩),
        Finset.erase_insert (hno c2 hc2).2]
    rw [← e1, ← e2]
    exact congrArg (fun x => (Finset.erase x (2 * l)).erase (2 * l + 1)) h
  unfold defMass
  rw [chSum_eq_sum_tvChFin hR2]
  simp only [Finset.empty_union]
  rw [← Finset.sum_image (f := φ) hinj]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext S
  simp only [Finset.mem_filter, Finset.mem_image, refStates, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hk⟩
    obtain ⟨hE, hF⟩ := tv_of_kind_defect hk
    have hl2 := ((hF l hl).2 rfl)
    refine ⟨(S.erase (2 * l)).erase (2 * l + 1), (mem_tvChFin hR2).2 ⟨?_, ?_⟩, ?_⟩
    · intro e he
      simp only [Finset.mem_erase] at he
      obtain ⟨h1, h2, he⟩ := he
      have hep := Finset.mem_range.1 (hsub he)
      rw [hR2mem]
      refine ⟨by omega, fun h => ?_, fun h => ?_⟩
      · have := (hE i hi).2 rfl
        rcases (show e = 2 * i ∨ e = 2 * i + 1 by omega) with rfl | rfl
        · exact this.1 he
        · exact this.2 he
      · omega
    · intro t ht
      obtain ⟨htp, hti, htl⟩ := (hR2mem t).1 ht
      simp only [Finset.mem_erase, ne_eq]
      have a1 : 2 * t + 1 ≠ 2 * l + 1 := by omega
      have a2 : 2 * t ≠ 2 * l + 1 := by omega
      have a3 : 2 * t ≠ 2 * l := by omega
      have a4 : 2 * t + 1 ≠ 2 * l := by omega
      simp only [a1, a2, a3, a4, not_false_eq_true, true_and]
      have nE := fun h => hti ((hE t htp).1 h)
      have nF := fun h => htl ((hF t htp).1 h)
      tauto
    · rw [Finset.erase_right_comm, Finset.insert_comm, Finset.insert_erase
        (Finset.mem_erase.2 ⟨by omega, hl2.1⟩), Finset.insert_erase hl2.2]
  · rintro ⟨c, hc, rfl⟩
    have hc' := (mem_tvChFin hR2).1 hc
    refine ⟨fun e he => ?_, ?_⟩
    · rw [Finset.mem_range]
      simp only [Finset.mem_insert] at he
      rcases he with rfl | rfl | he
      · omega
      · omega
      · have := (hR2mem _).1 (hc'.1 e he); omega
    · have := tv_kind_defect (tv_root_valid' p) hiR hlR hil hc'
      simpa using this

/-- INTERNAL: the transversal sum as a `chSum`.
TEXLINE: sections/signatures.tex:36-52 -/
theorem tv_trans_eq (I : Instance) (ε δ : ℚ) (φ : Finset ℕ → ℝ) :
    (∑ S ∈ transStates I ε δ, φ S) = trMass φ ∅ (List.range (pSmall I ε δ)) := by
  have hR : (List.range (pSmall I ε δ)).Nodup := List.nodup_range
  unfold trMass
  rw [chSum_eq_sum_tvChFin hR]
  simp only [Finset.empty_union]
  have hset : transStates I ε δ = tvChFin (List.range (pSmall I ε δ)) := by
    ext S
    rw [mem_tvChFin hR]
    unfold transStates refStates IsChoice
    simp only [Finset.mem_filter, Finset.mem_powerset, kind_eq_transversal_iff]
    constructor
    · rintro ⟨hsub, h⟩
      refine ⟨fun e he => ?_, fun t ht => h t (List.mem_range.1 ht)⟩
      have := Finset.mem_range.1 (hsub he); rw [List.mem_range]; omega
    · rintro ⟨h1, h2⟩
      refine ⟨fun e he => ?_, fun t ht => h2 t (List.mem_range.2 ht)⟩
      have := List.mem_range.1 (h1 e he); rw [Finset.mem_range]; omega
  rw [hset]

/-- INTERNAL: `C(j) = z_∅` for the second lift.
TEXLINE: sections/signatures.tex:47-52 -/
theorem tv_Cpart_eq (I : Instance) (ε δ : ℚ) (j : ℕ) :
    trMass (fTilde I ε δ j) ∅ (List.range (pSmall I ε δ)) = Cpart I ε δ j := by
  rw [tv_trMass_lift j (tv_root_valid' _), ← tv_trans_eq, ← transMass_eq_Cpart]
  rfl

/-- INTERNAL: a sink of the arc relation `a_il > 1` (`transport.tex:350-361`).
TEXLINE: sections/transport.tex:342-361 -/
theorem tv_sink (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j ≤ HParam I ε δ)
    (σ : Finset ℕ) (T : List ℕ) (hv : AsgValid (pSmall I ε δ) σ T) (hT : T ≠ []) :
    ∃ k ∈ T, ∀ t ∈ T, t ≠ k →
      defMass (fTilde I ε δ j) σ T k t *
          defMass (fTilde I ε δ j) ∅ (List.range (pSmall I ε δ)) t k ≤
        trMass (fTilde I ε δ j) σ T * Cpart I ε δ j := by
  classical
  set R := List.range (pSmall I ε δ)
  set fT := fTilde I ε δ j
  set z := trMass fT σ T
  set C := Cpart I ε δ j
  have hfT : ∀ S, 0 < fT S := tv_fTilde_pos I ε δ j
  have hz : 0 < z := chSum_pos hv.1 fun _ _ => hfT _
  have hC : 0 < C := td_Cpart_pos I ε δ j
  have hR := tv_root_valid' (pSmall I ε δ)
  have hCeq : trMass fT ∅ R = C := tv_Cpart_eq I ε δ j
  set a : ℕ → ℕ → ℝ := fun i l => defMass fT σ T i l * defMass fT ∅ R l i with ha
  have hTR : ∀ t ∈ T, t ∈ R := fun t ht => List.mem_range.2 (hv.2.1 t ht)
  -- the two-cycle bound `a_il a_li ≤ (zC)²/16`
  have h2 : ∀ i ∈ T, ∀ l ∈ T, i ≠ l → a i l * a l i ≤ (z * C) ^ 2 / 16 := by
    intro i hi l hl hil
    have e1 := defect_two_pair hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj σ T hv i l hi hl hil
    have e2 := defect_two_pair hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj ∅ R hR l i
      (hTR l hl) (hTR i hi) (Ne.symm hil)
    rw [hCeq] at e2
    have p1 := tv_defMass_pos fT hfT σ T hv.1 i l
    have p2 := tv_defMass_pos fT hfT σ T hv.1 l i
    have p3 := tv_defMass_pos fT hfT ∅ R hR.1 l i
    have p4 := tv_defMass_pos fT hfT ∅ R hR.1 i l
    simp only [ha]
    have := mul_le_mul e1 e2 (by positivity) (by positivity)
    nlinarith
  -- the three-pair product bound `a_il a_lk ≤ zC a_ik`
  have h3 : ∀ i ∈ T, ∀ l ∈ T, ∀ k ∈ T, i ≠ l → l ≠ k → i ≠ k →
      a i l * a l k ≤ z * C * a i k := by
    intro i hi l hl k hk hil hlk hik
    have e1 := defect_three_pair hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj σ T hv i l k
      hi hl hk hil hlk hik
    have e2 := defect_three_pair hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj ∅ R hR k l i
      (hTR k hk) (hTR l hl) (hTR i hi) (Ne.symm hlk) (Ne.symm hil) (Ne.symm hik)
    rw [hCeq] at e2
    have p1 := tv_defMass_pos fT hfT σ T hv.1 i l
    have p2 := tv_defMass_pos fT hfT σ T hv.1 l k
    have p3 := tv_defMass_pos fT hfT ∅ R hR.1 l i
    have p4 := tv_defMass_pos fT hfT ∅ R hR.1 k l
    simp only [ha]
    have := mul_le_mul e1 e2 (by positivity)
      (mul_pos hz (tv_defMass_pos fT hfT σ T hv.1 i k)).le
    nlinarith
  -- arcs `i → l` when `a_il > zC`; choose `k` with the fewest out-arcs
  set arc : ℕ → ℕ → Prop := fun i l => i ≠ l ∧ z * C < a i l with harc
  have hzC : 0 < z * C := mul_pos hz hC
  have htrans : ∀ i ∈ T, ∀ l ∈ T, ∀ k ∈ T, arc i l → arc l k → arc i k := by
    intro i hi l hl k hk ⟨hil, h1⟩ ⟨hlk, h2'⟩
    have hik : i ≠ k := by
      rintro rfl
      have := h2 i hi l hl hil
      nlinarith
    refine ⟨hik, ?_⟩
    have := h3 i hi l hl k hk hil hlk hik
    by_contra hcon
    push Not at hcon
    nlinarith
  set out : ℕ → Finset ℕ := fun i => T.toFinset.filter (fun l => arc i l) with hout
  have hTne : T.toFinset.Nonempty := by
    obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil T hT
    exact ⟨t, List.mem_toFinset.2 ht⟩
  obtain ⟨k, hkT, hkmin⟩ := Finset.exists_min_image T.toFinset (fun i => (out i).card) hTne
  have hk : k ∈ T := List.mem_toFinset.1 hkT
  refine ⟨k, hk, fun t ht htk => ?_⟩
  by_contra hcon
  push Not at hcon
  have hkt : arc k t := ⟨Ne.symm htk, hcon⟩
  have hsub : out t ⊂ out k := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨t, ?_, ?_⟩
      · simp only [hout, Finset.mem_filter]; exact ⟨List.mem_toFinset.2 ht, hkt⟩
      · simp only [hout, Finset.mem_filter, not_and]; exact fun _ h => h.1 rfl
    · intro m hm
      simp only [hout, Finset.mem_filter] at hm ⊢
      exact ⟨hm.1, htrans k hk t ht m (List.mem_toFinset.1 hm.1) hkt hm.2⟩
  have := hkmin t (List.mem_toFinset.2 ht)
  have := Finset.card_lt_card hsub
  omega

/-- INTERNAL: the children of a node are nodes.
TEXLINE: sections/transport.tex:363-366 -/
theorem tv_child_valid {p : ℕ} {σ : Finset ℕ} {T : List ℕ} (hv : AsgValid p σ T)
    {k : ℕ} (hk : k ∈ T) (b : ℕ) (hb : b < 2) :
    AsgValid p (insert (2 * k + b) σ) (T.erase k) := by
  obtain ⟨hnd, hlt, hσlt, hinj, hiff⟩ := hv
  have hkp : k < p := hlt k hk
  have hkσ : ∀ e ∈ σ, e / 2 ≠ k := (hiff k hkp).1 hk
  refine ⟨hnd.erase k, fun t ht => hlt t (List.mem_of_mem_erase ht), ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · omega
    · exact hσlt e he
  · intro e he e' he' hee
    rcases Finset.mem_insert.1 he with rfl | he <;> rcases Finset.mem_insert.1 he' with rfl | he'
    · rfl
    · exact absurd (by omega) (hkσ e' he')
    · exact absurd (by omega) (hkσ e he)
    · exact hinj e he e' he' hee
  · intro t ht
    constructor
    · intro htT e he
      have htk : t ≠ k := fun h => (List.Nodup.not_mem_erase hnd) (h ▸ htT)
      rcases Finset.mem_insert.1 he with rfl | he
      · omega
      · exact (hiff t ht).1 (List.mem_of_mem_erase htT) e he
    · intro h
      have htk : t ≠ k := fun htk => h (2 * k + b) (Finset.mem_insert_self _ _) (by omega)
      exact (List.mem_erase_of_ne htk).2
        ((hiff t ht).2 fun e he => h e (Finset.mem_insert_of_mem he))

/-- INTERNAL: the conditional variance identity at the branching on pair `k`.
TEXLINE: sections/transport.tex:396-404 -/
theorem tv_var_split (φ g : Finset ℕ → ℝ) (σ : Finset ℕ) (T : List ℕ) (k : ℕ) (hk : k ∈ T)
    (ha : 0 < trMass φ (insert (2 * k) σ) (T.erase k))
    (hb : 0 < trMass φ (insert (2 * k + 1) σ) (T.erase k)) :
    tvVar φ g σ T = tvVar φ g (insert (2 * k) σ) (T.erase k) +
      tvVar φ g (insert (2 * k + 1) σ) (T.erase k) +
      trMass φ (insert (2 * k) σ) (T.erase k) * trMass φ (insert (2 * k + 1) σ) (T.erase k) /
          (trMass φ (insert (2 * k) σ) (T.erase k) +
            trMass φ (insert (2 * k + 1) σ) (T.erase k)) *
        (chSum (T.erase k) (fun c => φ (insert (2 * k) σ ∪ c) * g (insert (2 * k) σ ∪ c)) /
            trMass φ (insert (2 * k) σ) (T.erase k) -
          chSum (T.erase k)
              (fun c => φ (insert (2 * k + 1) σ ∪ c) * g (insert (2 * k + 1) σ ∪ c)) /
            trMass φ (insert (2 * k + 1) σ) (T.erase k)) ^ 2 := by
  unfold tvVar trMass at *
  rw [chSum_split hk (fun c => φ (σ ∪ c) * g (σ ∪ c) ^ 2),
    chSum_split hk (fun c => φ (σ ∪ c) * g (σ ∪ c)), chSum_split hk (fun c => φ (σ ∪ c))]
  simp only [Finset.union_insert, Finset.insert_union] at ha hb ⊢
  set Qa := chSum (T.erase k) fun c => φ (insert (2 * k) (σ ∪ c)) * g (insert (2 * k) (σ ∪ c)) ^ 2
  set Qb := chSum (T.erase k) fun c =>
    φ (insert (2 * k + 1) (σ ∪ c)) * g (insert (2 * k + 1) (σ ∪ c)) ^ 2
  set Ma := chSum (T.erase k) fun c => φ (insert (2 * k) (σ ∪ c)) * g (insert (2 * k) (σ ∪ c))
  set Mb := chSum (T.erase k) fun c =>
    φ (insert (2 * k + 1) (σ ∪ c)) * g (insert (2 * k + 1) (σ ∪ c))
  set sa := chSum (T.erase k) fun c => φ (insert (2 * k) (σ ∪ c))
  set sb := chSum (T.erase k) fun c => φ (insert (2 * k + 1) (σ ∪ c))
  have hab : 0 < sa + sb := add_pos ha hb
  field_simp
  ring

/-- INTERNAL: the restricted energies of the two children add up to at most the
parent's (`transport.tex:405-414`).
TEXLINE: sections/transport.tex:405-414 -/
theorem tv_dir_split (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ j w) (g : Finset ℕ → ℝ) (σ : Finset ℕ) (k : ℕ) :
    tvDir I ε δ j w g (insert (2 * k) σ) + tvDir I ε δ j w g (insert (2 * k + 1) σ) ≤
      tvDir I ε δ j w g σ := by
  classical
  have hmono : ∀ a S, tvResp (insert a σ) S → tvResp σ S :=
    fun a S h e he => h e (Finset.mem_insert_of_mem he)
  have hdisj : ∀ S, tvResp (insert (2 * k) σ) S → tvResp (insert (2 * k + 1) σ) S → False := by
    intro S ha hb
    have h1 := (ha (2 * k) (Finset.mem_insert_self _ _)).2
    have h2 := (hb (2 * k + 1) (Finset.mem_insert_self _ _)).1
    have := h1 (2 * k + 1) h2 (by omega)
    omega
  unfold tvDir
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (by norm_num)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun S _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun S' _ => ?_
  have hnn : 0 ≤ min (refLam I ε δ S j w) (refLam I ε δ S' j w) * (g S - g S') ^ 2 :=
    mul_nonneg (le_min (td_refLam_nonneg I ε δ j w hgood S)
      (td_refLam_nonneg I ε δ j w hgood S')) (sq_nonneg _)
  by_cases ha : exchNbr S S' ∧ tvResp (insert (2 * k) σ) S ∧ tvResp (insert (2 * k) σ) S'
  · have hb : ¬ (exchNbr S S' ∧ tvResp (insert (2 * k + 1) σ) S ∧
        tvResp (insert (2 * k + 1) σ) S') := fun hb => hdisj S ha.2.1 hb.2.1
    rw [if_pos ha, if_neg hb, if_pos ⟨ha.1, hmono _ _ ha.2.1, hmono _ _ ha.2.2⟩, add_zero]
  · rw [if_neg ha, zero_add]
    by_cases hb : exchNbr S S' ∧ tvResp (insert (2 * k + 1) σ) S ∧
        tvResp (insert (2 * k + 1) σ) S'
    · rw [if_pos hb, if_pos ⟨hb.1, hmono _ _ hb.2.1, hmono _ _ hb.2.2⟩]
    · rw [if_neg hb]
      split_ifs
      · exact hnn
      · exact le_refl 0

/-- INTERNAL: the complete display `Y = σ ∪ {2k, 2k+1} ∪ c` at a sink `k`: inside
`[0, 2p)`, full in pair `k`, singly occupied in every other pair; its displayed elements
lie outside `σ` in unassigned pairs. -/
theorem tv_Y_struct {p : ℕ} {σ : Finset ℕ} {T : List ℕ} (hv : AsgValid p σ T) {k : ℕ}
    (hk : k ∈ T) {c : Finset ℕ} (hc : IsChoice (T.erase k) c) :
    (∀ e ∈ σ ∪ insert (2 * k) (insert (2 * k + 1) c), e < 2 * p) ∧
      (∀ t < p, t ≠ k →
        (2 * t ∈ σ ∪ insert (2 * k) (insert (2 * k + 1) c) ↔
          2 * t + 1 ∉ σ ∪ insert (2 * k) (insert (2 * k + 1) c))) ∧
      (∀ e ∈ insert (2 * k) (insert (2 * k + 1) c), e ∉ σ ∧ e / 2 ∈ T) := by
  have hkp := hv.2.1 k hk
  have hcT : ∀ e ∈ c, e / 2 ∈ T ∧ e / 2 ≠ k := by
    intro e he
    have h := hc.1 e he
    exact ⟨List.mem_of_mem_erase h, fun h' => hv.1.not_mem_erase (h' ▸ h)⟩
  have hD : ∀ e ∈ insert (2 * k) (insert (2 * k + 1) c), e ∉ σ ∧ e / 2 ∈ T := by
    intro e he
    have hT : e / 2 ∈ T := by
      simp only [Finset.mem_insert] at he
      rcases he with rfl | rfl | he
      · rwa [show 2 * k / 2 = k by omega]
      · rwa [show (2 * k + 1) / 2 = k by omega]
      · exact (hcT e he).1
    exact ⟨fun h => tv_sigma_notT hv h hT, hT⟩
  refine ⟨?_, ?_, hD⟩
  · intro e he
    rcases Finset.mem_union.1 he with he | he
    · exact hv.2.2.1 e he
    · have := hv.2.1 _ (hD e he).2; omega
  · intro t htp htk
    have a1 : 2 * t ≠ 2 * k := by omega
    have a2 : 2 * t ≠ 2 * k + 1 := by omega
    have a3 : 2 * t + 1 ≠ 2 * k := by omega
    have a4 : 2 * t + 1 ≠ 2 * k + 1 := by omega
    simp only [Finset.mem_union, Finset.mem_insert, a1, a2, a3, a4, false_or]
    by_cases ht : t ∈ T
    · obtain ⟨s0, s1⟩ := tv_sigma_none hv ht
      simp only [s0, s1, false_or]
      exact hc.2 t ((List.mem_erase_of_ne htk).2 ht)
    · have c0 : 2 * t ∉ c := fun h => ht (by simpa using (hcT _ h).1)
      have c1 : 2 * t + 1 ∉ c := fun h => ht (by
        have := (hcT _ h).1; rwa [show (2 * t + 1) / 2 = t by omega] at this)
      rcases tv_sigma_pair hv htp ht with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [h0, h1, c0, c1]

/-- INTERNAL: a one-hole state `Y \ {i}` of the sink-`k` transport application is a state
of `X` respecting `σ`, with `λ = W_i f`.
TEXLINE: sections/transport.tex:363-375 -/
theorem tv_hole_state {I : Instance} {ε δ : ℚ} (j : ℕ) (w : ℕ → ℕ → ℚ) {σ : Finset ℕ}
    {T : List ℕ} (hv : AsgValid (pSmall I ε δ) σ T) {k : ℕ} (hk : k ∈ T) {c : Finset ℕ}
    (hc : IsChoice (T.erase k) c) {i : ℕ} (hi : i ∈ insert (2 * k) (insert (2 * k + 1) c)) :
    (σ ∪ insert (2 * k) (insert (2 * k + 1) c)).erase i ∈ chainStates I ε δ ∧
      refLam I ε δ ((σ ∪ insert (2 * k) (insert (2 * k + 1) c)).erase i) j w =
        (if i / 2 = k then 1 else (w (i / 2) k : ℝ)) *
          fWeight I ε δ j ((σ ∪ insert (2 * k) (insert (2 * k + 1) c)).erase i) ∧
      tvResp σ ((σ ∪ insert (2 * k) (insert (2 * k + 1) c)).erase i) := by
  classical
  set p := pSmall I ε δ
  set D := insert (2 * k) (insert (2 * k + 1) c)
  set Y := σ ∪ D
  obtain ⟨hYlt, hYpair, hDσ⟩ := tv_Y_struct hv hk hc
  have hkp := hv.2.1 k hk
  have hYk0 : 2 * k ∈ Y := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  have hYk1 : 2 * k + 1 ∈ Y :=
    Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hiY : i ∈ Y := Finset.mem_union_right _ hi
  have hsub : Y.erase i ∈ refStates I ε δ := by
    unfold refStates
    rw [Finset.mem_powerset]
    intro e he
    exact Finset.mem_range.2 (hYlt e (Finset.mem_of_mem_erase he))
  have hresp : tvResp σ (Y.erase i) := by
    intro e he
    have hei : e ≠ i := fun h => (hDσ i hi).1 (h ▸ he)
    refine ⟨Finset.mem_erase.2 ⟨hei, Finset.mem_union_left _ he⟩, fun e' he' hee => ?_⟩
    rcases Finset.mem_union.1 (Finset.mem_of_mem_erase he') with h | h
    · exact hv.2.2.2.1 e' h e he hee
    · exact absurd (hee ▸ (hDσ e' h).2) (tv_sigma_notT hv he)
  by_cases hik : i / 2 = k
  · -- the hole is in pair `k`: a transversal
    have hkind : kind I ε δ (Y.erase i) = .transversal := by
      rw [kind_eq_transversal_iff]
      intro t htp
      by_cases htk : t = k
      · subst htk
        rcases (show i = 2 * t ∨ i = 2 * t + 1 by omega) with rfl | rfl
        · simp [Finset.mem_erase, hYk1]
        · simp [Finset.mem_erase, hYk0]
      · have a1 : 2 * t ≠ i := by omega
        have a2 : 2 * t + 1 ≠ i := by omega
        simp only [Finset.mem_erase, ne_eq, a1, a2, not_false_eq_true, true_and]
        exact hYpair t htp htk
    refine ⟨Finset.mem_filter.2 ⟨hsub, by rw [hkind]; simp⟩, ?_, hresp⟩
    rw [td_refLam_eq, hkind, if_pos hik, one_mul]
  · -- the hole is in an ordinary pair `t0 = i / 2`: a state of `A_{t0 k}`
    set t0 := i / 2
    have ht0T := (hDσ i hi).2
    have ht0p := hv.2.1 t0 ht0T
    have hkind : kind I ε δ (Y.erase i) = .defect t0 k := by
      apply tv_kind_defect_of ht0p hkp
      · intro t htp
        constructor
        · rintro ⟨h0, h1⟩
          by_contra htt
          have a0 : 2 * t ≠ i := by omega
          have a1 : 2 * t + 1 ≠ i := by omega
          have n0 : 2 * t ∉ Y := fun h => h0 (Finset.mem_erase.2 ⟨a0, h⟩)
          have n1 : 2 * t + 1 ∉ Y := fun h => h1 (Finset.mem_erase.2 ⟨a1, h⟩)
          by_cases htk : t = k
          · subst htk; exact n0 hYk0
          · exact n0 ((hYpair t htp htk).2 n1)
        · intro htt
          rw [htt]
          have hp0 := hYpair t0 ht0p hik
          rcases (show i = 2 * t0 ∨ i = 2 * t0 + 1 by omega) with h | h
          · refine ⟨fun h' => (Finset.mem_erase.1 h').1 h.symm, fun h' => ?_⟩
            exact hp0.1 (h ▸ hiY) (Finset.mem_of_mem_erase h')
          · refine ⟨fun h' => ?_, fun h' => (Finset.mem_erase.1 h').1 h.symm⟩
            exact (hp0.1 (Finset.mem_of_mem_erase h')) (h ▸ hiY)
      · intro t htp
        constructor
        · rintro ⟨h0, h1⟩
          by_contra htk
          have := hYpair t htp htk
          exact (this.1 (Finset.mem_of_mem_erase h0)) (Finset.mem_of_mem_erase h1)
        · rintro rfl
          exact ⟨Finset.mem_erase.2 ⟨by omega, hYk0⟩, Finset.mem_erase.2 ⟨by omega, hYk1⟩⟩
    refine ⟨Finset.mem_filter.2 ⟨hsub, by rw [hkind]; simp⟩, ?_, hresp⟩
    rw [td_refLam_eq, hkind, if_neg hik]
    simp only
    ring

/-- INTERNAL: the one-hole states of the transport application at a sink `k` are states
of `X` respecting `σ`, with weight `λ`, and distinct displays have disjoint clique
edges, so the slot energy is at most `𝔇_σ(g)` (`transport.tex:388-392`).
TEXLINE: sections/transport.tex:363-392 -/
theorem tv_clique_le (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (hgood : goodMult I ε δ j w) (g : Finset ℕ → ℝ) (σ : Finset ℕ) (T : List ℕ)
    (hv : AsgValid (pSmall I ε δ) σ T) (k : ℕ) (hk : k ∈ T) :
    chSum (T.erase k) (fun c => cliqueEnergy (fWeight I ε δ j) g
        (fun e => if e / 2 = k then 1 else (w (e / 2) k : ℝ)) σ
        (insert (2 * k) (insert (2 * k + 1) c))) ≤ tvDir I ε δ j w g σ := by
  classical
  set f := fWeight I ε δ j
  set W : ℕ → ℝ := fun e => if e / 2 = k then 1 else (w (e / 2) k : ℝ) with hWdef
  set L := T.erase k
  have hLnd : L.Nodup := hv.1.erase k
  set D : Finset ℕ → Finset ℕ := fun c => insert (2 * k) (insert (2 * k + 1) c) with hDdef
  set X := chainStates I ε δ
  -- the summands on both sides
  set H : (Σ _ : Finset ℕ, ℕ × ℕ) → ℝ := fun x =>
    if x.2.1 = x.2.2 then 0 else
      min (W x.2.1 * f ((σ ∪ D x.1).erase x.2.1)) (W x.2.2 * f ((σ ∪ D x.1).erase x.2.2)) *
        (g ((σ ∪ D x.1).erase x.2.1) - g ((σ ∪ D x.1).erase x.2.2)) ^ 2 with hHdef
  set G : Finset ℕ × Finset ℕ → ℝ := fun y =>
    if exchNbr y.1 y.2 ∧ tvResp σ y.1 ∧ tvResp σ y.2 then
      min (refLam I ε δ y.1 j w) (refLam I ε δ y.2 j w) * (g y.1 - g y.2) ^ 2 else 0
    with hGdef
  set dom := (tvChFin L).sigma (fun c => D c ×ˢ D c)
  have hLHS : chSum L (fun c => cliqueEnergy f g W σ (D c)) = (∑ x ∈ dom, H x) / 2 := by
    rw [chSum_eq_sum_tvChFin hLnd, Finset.sum_sigma, Finset.sum_div]
    refine Finset.sum_congr rfl fun c _ => ?_
    unfold cliqueEnergy
    rw [Finset.sum_product]
  have hRHS : tvDir I ε δ j w g σ = (∑ y ∈ X ×ˢ X, G y) / 2 := by
    unfold tvDir
    rw [Finset.sum_product]
  rw [hLHS, hRHS]
  refine div_le_div_of_nonneg_right ?_ (by norm_num)
  rw [← Finset.sum_filter_of_ne (p := fun x => x.2.1 ≠ x.2.2) (fun x _ hx => by
    intro h; exact hx (by simp only [hHdef, if_pos h]))]
  -- the map to ordered edges
  set φ : (Σ _ : Finset ℕ, ℕ × ℕ) → Finset ℕ × Finset ℕ := fun x =>
    ((σ ∪ D x.1).erase x.2.1, (σ ∪ D x.1).erase x.2.2) with hφdef
  have hmem : ∀ x ∈ dom.filter (fun x => x.2.1 ≠ x.2.2),
      IsChoice L x.1 ∧ x.2.1 ∈ D x.1 ∧ x.2.2 ∈ D x.1 ∧ x.2.1 ≠ x.2.2 := by
    intro x hx
    obtain ⟨hx, hne⟩ := Finset.mem_filter.1 hx
    obtain ⟨hc, hik⟩ := Finset.mem_sigma.1 hx
    obtain ⟨hi, hk'⟩ := Finset.mem_product.1 hik
    exact ⟨(mem_tvChFin hLnd).1 hc, hi, hk', hne⟩
  -- recovering the display and the choice set from the union of the two endpoints
  have hrec : ∀ c, IsChoice L c → ∀ e, e ∈ c ↔ e ∈ σ ∪ D c ∧ e ∉ σ ∧ e / 2 ≠ k := by
    intro c hc e
    obtain ⟨-, -, hDσ⟩ := tv_Y_struct hv hk hc
    constructor
    · intro he
      have hD : e ∈ D c := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem he)
      refine ⟨Finset.mem_union_right _ hD, (hDσ e hD).1, fun h => ?_⟩
      have := hc.1 e he
      rw [h] at this
      exact hv.1.not_mem_erase this
    · rintro ⟨he, hσ, hk2⟩
      rcases Finset.mem_union.1 he with h | h
      · exact absurd h hσ
      · simp only [hDdef, Finset.mem_insert] at h
        rcases h with rfl | rfl | h
        · omega
        · omega
        · exact h
  have hunion : ∀ (Y : Finset ℕ) (i i' : ℕ), i ∈ Y → i' ∈ Y → i ≠ i' →
      Y.erase i ∪ Y.erase i' = Y := by
    intro Y i i' hi hi' hne
    ext e
    simp only [Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
    · intro h
      by_cases he : e = i
      · exact Or.inr ⟨by rw [he]; exact hne, h⟩
      · exact Or.inl ⟨he, h⟩
  have herase_inj : ∀ (Y : Finset ℕ) (i i' : ℕ), i ∈ Y → i' ∈ Y → Y.erase i = Y.erase i' →
      i = i' := by
    intro Y i i' hi hi' h
    by_contra hne
    have : i ∈ Y.erase i' := Finset.mem_erase.2 ⟨hne, hi⟩
    rw [← h] at this
    exact Finset.notMem_erase i Y this
  have hinj : Set.InjOn φ ↑(dom.filter (fun x => x.2.1 ≠ x.2.2)) := by
    rintro ⟨c1, i1, k1⟩ h1 ⟨c2, i2, k2⟩ h2 heq
    obtain ⟨hc1, hi1, hk1, hne1⟩ := hmem _ h1
    obtain ⟨hc2, hi2, hk2, hne2⟩ := hmem _ h2
    simp only [hφdef, Prod.mk.injEq] at heq
    obtain ⟨e1, e2⟩ := heq
    have hY1 : σ ∪ D c1 = σ ∪ D c2 := by
      rw [← hunion (σ ∪ D c1) i1 k1 (Finset.mem_union_right _ hi1)
          (Finset.mem_union_right _ hk1) hne1,
        ← hunion (σ ∪ D c2) i2 k2 (Finset.mem_union_right _ hi2)
          (Finset.mem_union_right _ hk2) hne2, e1, e2]
    have hc : c1 = c2 := by
      ext e
      rw [hrec c1 hc1, hrec c2 hc2, hY1]
    subst hc
    have hi : i1 = i2 := herase_inj _ _ _ (Finset.mem_union_right _ hi1)
      (Finset.mem_union_right _ hi2) e1
    have hk : k1 = k2 := herase_inj _ _ _ (Finset.mem_union_right _ hk1)
      (Finset.mem_union_right _ hk2) e2
    subst hi; subst hk
    rfl
  have hstate : ∀ x ∈ dom.filter (fun x => x.2.1 ≠ x.2.2),
      (φ x).1 ∈ X ∧ (φ x).2 ∈ X ∧ exchNbr (φ x).1 (φ x).2 ∧ tvResp σ (φ x).1 ∧
        tvResp σ (φ x).2 ∧ refLam I ε δ (φ x).1 j w = W x.2.1 * f (φ x).1 ∧
        refLam I ε δ (φ x).2 j w = W x.2.2 * f (φ x).2 := by
    intro x hx
    obtain ⟨hc, hi, hk', hne⟩ := hmem x hx
    obtain ⟨s1, l1, r1⟩ := tv_hole_state j w hv hk hc hi
    obtain ⟨s2, l2, r2⟩ := tv_hole_state j w hv hk hc hk'
    refine ⟨s1, s2, ?_, r1, r2, l1, l2⟩
    have hiY : x.2.1 ∈ σ ∪ D x.1 := Finset.mem_union_right _ hi
    have hkY : x.2.2 ∈ σ ∪ D x.1 := Finset.mem_union_right _ hk'
    have hd : ∀ a b, a ∈ σ ∪ D x.1 → b ∈ σ ∪ D x.1 → a ≠ b →
        (σ ∪ D x.1).erase a \ (σ ∪ D x.1).erase b = {b} := by
      intro a b ha hb hab
      ext e
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨-, h1⟩, h2⟩
        by_contra h; exact h2 ⟨h, h1⟩
      · rintro rfl
        exact ⟨⟨fun h => hab h.symm, hb⟩, fun h => h.1 rfl⟩
    refine ⟨?_, ?_⟩
    · simp only [hφdef]; rw [hd _ _ hiY hkY hne, Finset.card_singleton]
    · simp only [hφdef]; rw [hd _ _ hkY hiY (Ne.symm hne), Finset.card_singleton]
  refine Finset.sum_le_sum_of_injOn φ hinj ?_ ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨h1, h2, -⟩ := hstate x hx
    exact Finset.mem_product.2 ⟨h1, h2⟩
  · intro x hx
    obtain ⟨-, -, hex, hr1, hr2, hl1, hl2⟩ := hstate x hx
    obtain ⟨-, -, -, hne⟩ := hmem x hx
    simp only [hHdef, hGdef, if_neg hne]
    rw [if_pos ⟨hex, hr1, hr2⟩, hl1, hl2]
  · intro y _ _
    simp only [hGdef]
    split_ifs
    · exact mul_nonneg (le_min (td_refLam_nonneg I ε δ j w hgood _)
        (td_refLam_nonneg I ε δ j w hgood _)) (sq_nonneg _)
    · exact le_refl 0

/-- INTERNAL: clique energies are nonnegative for nonnegative hole weights. -/
theorem tv_cliqueEnergy_nonneg (f g : Finset ℕ → ℝ) (W : ℕ → ℝ) (F Disp : Finset ℕ)
    (hf : ∀ S, 0 ≤ f S) (hW : ∀ e ∈ Disp, 0 ≤ W e) : 0 ≤ cliqueEnergy f g W F Disp := by
  unfold cliqueEnergy
  refine div_nonneg (Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun k hk => ?_) (by norm_num)
  split_ifs
  · exact le_refl 0
  · exact mul_nonneg (le_min (mul_nonneg (hW i hi) (hf _)) (mul_nonneg (hW k hk) (hf _)))
      (sq_nonneg _)

/-- INTERNAL: the between-means charge `eq:conditional-variance-charge` at a sink `k`.
TEXLINE: sections/transport.tex:363-395 -/
theorem tv_node_charge (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) (g : Finset ℕ → ℝ)
    (σ : Finset ℕ) (T : List ℕ) (hv : AsgValid (pSmall I ε δ) σ T) (k : ℕ) (hk : k ∈ T)
    (hsink : ∀ t ∈ T, t ≠ k →
      defMass (fTilde I ε δ j) σ T k t *
          defMass (fTilde I ε δ j) ∅ (List.range (pSmall I ε δ)) t k ≤
        trMass (fTilde I ε δ j) σ T * Cpart I ε δ j) :
    trMass (fWeight I ε δ j) (insert (2 * k) σ) (T.erase k) *
        trMass (fWeight I ε δ j) (insert (2 * k + 1) σ) (T.erase k) /
          (trMass (fWeight I ε δ j) (insert (2 * k) σ) (T.erase k) +
            trMass (fWeight I ε δ j) (insert (2 * k + 1) σ) (T.erase k)) *
        (chSum (T.erase k) (fun c => fWeight I ε δ j (insert (2 * k) σ ∪ c) *
              g (insert (2 * k) σ ∪ c)) /
            trMass (fWeight I ε δ j) (insert (2 * k) σ) (T.erase k) -
          chSum (T.erase k) (fun c => fWeight I ε δ j (insert (2 * k + 1) σ ∪ c) *
              g (insert (2 * k + 1) σ ∪ c)) /
            trMass (fWeight I ε δ j) (insert (2 * k + 1) σ) (T.erase k)) ^ 2 ≤
      (1 + 8 * (pSmall I ε δ : ℝ) * (qParam I ε δ : ℝ) ^ 2) * tvDir I ε δ j w g σ := by
  classical
  set p := pSmall I ε δ with hpdef
  set R := List.range p
  set f := fWeight I ε δ j
  set fT := fTilde I ε δ j
  set L := T.erase k with hLdef
  set q : ℝ := (qParam I ε δ : ℝ)
  set C := Cpart I ε δ j
  set W : ℕ → ℝ := fun e => if e / 2 = k then 1 else (w (e / 2) k : ℝ) with hWdef
  have hf : ∀ S, 0 < f S := td_fWeight_pos I ε δ j
  have hC : 0 < C := td_Cpart_pos I ε δ j
  have hR := tv_root_valid' p
  have hLnd : L.Nodup := hv.1.erase k
  have hkp : k < p := hv.2.1 k hk
  have hTR : ∀ t ∈ T, t < p := hv.2.1
  have hLT : ∀ t ∈ L, t ∈ T ∧ t ≠ k := fun t ht =>
    ⟨List.mem_of_mem_erase ht, fun h => (List.Nodup.not_mem_erase hv.1) (h ▸ ht)⟩
  have hσT : ∀ t ∈ T, ∀ e ∈ σ, e / 2 ≠ t := fun t ht => (hv.2.2.2.2 t (hTR t ht)).1 ht
  -- multipliers `w_tk` are positive
  have hcpos : ∀ t ∈ T, t ≠ k → 0 < cDef I ε δ j t k := by
    intro t ht htk
    unfold cDef
    rw [tv_cDef_eq I ε δ f t k (hTR t ht) hkp htk]
    exact tv_defMass_pos f hf ∅ R hR.1 t k
  have hwpos : ∀ t ∈ T, t ≠ k → 0 < (w t k : ℝ) := by
    intro t ht htk
    exact lt_of_lt_of_le (div_pos hC (by linarith [hcpos t ht htk]))
      (hgood t (hTR t ht) k hkp htk).1
  have hW2 : ∀ t, W (2 * t) = if t = k then 1 else (w t k : ℝ) := by
    intro t; simp only [hWdef, show 2 * t / 2 = t by omega]
  have hW3 : ∀ t, W (2 * t + 1) = if t = k then 1 else (w t k : ℝ) := by
    intro t; simp only [hWdef, show (2 * t + 1) / 2 = t by omega]
  -- the omission signature at every node of the transport recursion
  have hsig : ∀ (D : Finset ℕ) (L' : List ℕ), L'.Nodup → (∀ t ∈ L', t ∈ L) →
      (∀ e ∈ D, e = 2 * k ∨ e = 2 * k + 1 ∨ ∃ t ∈ L, e = 2 * t ∨ e = 2 * t + 1) →
      (∀ t ∈ L', 2 * t ∉ D ∧ 2 * t + 1 ∉ D) →
      D.card + L'.length = L.length + 3 → Hyp (omitMat f σ D L') := by
    intro D L' hL'nd hL'L hD hL'D hcard
    have hDT : ∀ e ∈ D, e / 2 ∈ T := by
      intro e he
      rcases hD e he with rfl | rfl | ⟨t, ht, rfl | rfl⟩
      · rwa [show 2 * k / 2 = k by omega]
      · rwa [show (2 * k + 1) / 2 = k by omega]
      · rw [show 2 * t / 2 = t by omega]; exact (hLT t ht).1
      · rw [show (2 * t + 1) / 2 = t by omega]; exact (hLT t ht).1
    have hσcard : σ.card + T.length = p := tv_card hv
    refine fWeight_omission hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj.le σ D L'
      hv.2.2.1 (fun e he => by have := hTR _ (hDT e he); omega)
      (fun t ht => hTR t (hLT t (hL'L t ht)).1) hL'nd ?_ ?_ hL'D ?_
    · rw [Finset.disjoint_left]
      intro e heσ heD
      exact hσT _ (hDT e heD) e heσ rfl
    · intro t ht
      have htT := (hLT t (hL'L t ht)).1
      refine ⟨fun h => hσT t htT _ h (by omega), fun h => hσT t htT _ h (by omega)⟩
    · have hL := List.length_erase_of_mem hk
      have hTpos : 0 < T.length := List.length_pos_of_mem hk
      rw [← hLdef] at hL
      omega
  have htr := slot_transport f g W σ (2 * k) (2 * k + 1) L hf (by omega)
    (fun h => hσT k hk _ h (by omega)) (fun h => hσT k hk _ h (by omega)) hLnd
    (fun t ht => ⟨fun h => hσT t (hLT t ht).1 _ h (by omega),
      fun h => hσT t (hLT t ht).1 _ h (by omega)⟩)
    (fun t ht => by have := (hLT t ht).2; omega)
    (by rw [hW2]; simp) (by rw [hW3]; simp)
    (fun t ht => by
      rw [hW2, hW3, if_neg (hLT t ht).2]
      exact ⟨hwpos t (hLT t ht).1 (hLT t ht).2, rfl⟩)
    hsig
  -- rewrite the transport bound in terms of the two children
  have hsa : chSum L (fun c => f (insert (2 * k) (σ ∪ c))) =
      trMass f (insert (2 * k) σ) L := by
    unfold trMass; simp only [Finset.insert_union]
  have hsb : chSum L (fun c => f (insert (2 * k + 1) (σ ∪ c))) =
      trMass f (insert (2 * k + 1) σ) L := by
    unfold trMass; simp only [Finset.insert_union]
  have hma : chSum L (fun c => f (insert (2 * k) (σ ∪ c)) * g (insert (2 * k) (σ ∪ c))) =
      chSum L (fun c => f (insert (2 * k) σ ∪ c) * g (insert (2 * k) σ ∪ c)) := by
    simp only [Finset.insert_union]
  have hmb : chSum L (fun c => f (insert (2 * k + 1) (σ ∪ c)) *
        g (insert (2 * k + 1) (σ ∪ c))) =
      chSum L (fun c => f (insert (2 * k + 1) σ ∪ c) * g (insert (2 * k + 1) σ ∪ c)) := by
    simp only [Finset.insert_union]
  rw [hsa, hsb, hma, hmb, hW2 k, hW3 k, if_pos rfl, mul_one, mul_one] at htr
  have hz : trMass f σ T = trMass f (insert (2 * k) σ) L + trMass f (insert (2 * k + 1) σ) L := by
    unfold trMass
    rw [chSum_split hk]
    simp only [Finset.union_insert, Finset.insert_union]
    rfl
  set sa := trMass f (insert (2 * k) σ) L
  set sb := trMass f (insert (2 * k + 1) σ) L
  set ma := chSum L (fun c => f (insert (2 * k) σ ∪ c) * g (insert (2 * k) σ ∪ c))
  set mb := chSum L (fun c => f (insert (2 * k + 1) σ ∪ c) * g (insert (2 * k + 1) σ ∪ c))
  set Dsl := chSum L (fun c => cliqueEnergy f g W σ (insert (2 * k) (insert (2 * k + 1) c)))
  set Sg := ∑ t ∈ L.toFinset,
    chSum (L.erase t) (fun c => f (insert (2 * t) (insert (2 * t + 1) (σ ∪ c)))) / W (2 * t)
  have hsapos : 0 < sa := tv_trMass_pos I ε δ j _ _ hLnd
  have hsbpos : 0 < sb := tv_trMass_pos I ε δ j _ _ hLnd
  -- each ordinary slot costs at most `4 q² z` (`eq:sink-comparison`)
  have hslot : ∀ t ∈ L.toFinset,
      chSum (L.erase t) (fun c => f (insert (2 * t) (insert (2 * t + 1) (σ ∪ c)))) / W (2 * t) ≤
        4 * q ^ 2 * (sa + sb) := by
    intro t htL
    obtain ⟨ht, htk⟩ := hLT t (List.mem_toFinset.1 htL)
    have hD : chSum (L.erase t) (fun c => f (insert (2 * t) (insert (2 * t + 1) (σ ∪ c)))) =
        defMass f σ T k t := rfl
    rw [hD, hW2 t, if_neg htk]
    have hw := hwpos t ht htk
    have hc := hcpos t ht htk
    have hD1 := tv_defMass_lift hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas j hv hk ht (Ne.symm htk)
    have hD2 := tv_defMass_lift hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas j hR
      (List.mem_range.2 (hTR t ht)) (List.mem_range.2 hkp) htk
    have hcD : cDef I ε δ j t k = defMass f ∅ R t k := by
      unfold cDef; exact tv_cDef_eq I ε δ f t k (hTR t ht) hkp htk
    rw [← hcD] at hD2
    have hsk := hsink t ht htk
    rw [tv_trMass_lift j hv, hz] at hsk
    have hgw := (hgood t (hTR t ht) k hkp htk).1
    have p1 := tv_defMass_pos f hf σ T hv.1 k t
    have p2 := tv_defMass_pos fT (tv_fTilde_pos I ε δ j) σ T hv.1 k t
    have p3 := tv_defMass_pos fT (tv_fTilde_pos I ε δ j) ∅ R hR.1 t k
    have hq : 0 ≤ q := Nat.cast_nonneg _
    -- `c^σ_kt c_tk ≤ q² z C`
    have hprod : defMass f σ T k t * cDef I ε δ j t k ≤ q ^ 2 * ((sa + sb) * C) := by
      have := mul_le_mul hD1 hD2 hc.le (mul_nonneg hq p2.le)
      calc defMass f σ T k t * cDef I ε δ j t k
          ≤ q * defMass fT σ T k t * (q * defMass fT ∅ R t k) := this
        _ = q ^ 2 * (defMass fT σ T k t * defMass fT ∅ R t k) := by ring
        _ ≤ q ^ 2 * ((sa + sb) * C) := mul_le_mul_of_nonneg_left hsk (pow_nonneg hq 2)
    rw [div_le_iff₀ hw]
    have h4 : C / (4 * cDef I ε δ j t k) * (4 * cDef I ε δ j t k) = C := by
      field_simp
    have hzpos : 0 < sa + sb := add_pos hsapos hsbpos
    have : defMass f σ T k t * (4 * cDef I ε δ j t k) ≤
        4 * q ^ 2 * (sa + sb) * (C / (4 * cDef I ε δ j t k)) * (4 * cDef I ε δ j t k) := by
      rw [mul_assoc (4 * q ^ 2 * (sa + sb)), h4]; nlinarith
    have hle := le_of_mul_le_mul_right this (by linarith)
    calc defMass f σ T k t ≤ 4 * q ^ 2 * (sa + sb) * (C / (4 * cDef I ε δ j t k)) := hle
      _ ≤ 4 * q ^ 2 * (sa + sb) * (w t k : ℝ) :=
        mul_le_mul_of_nonneg_left hgw
          (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hq 2)) hzpos.le)
  have hcardL : (L.toFinset.card : ℝ) ≤ p := by
    have h1 := List.toFinset_card_le L
    have h2 : L.length ≤ T.length := by rw [hLdef, List.length_erase_of_mem hk]; omega
    have h3 := tv_card hv
    exact_mod_cast (show L.toFinset.card ≤ p by omega)
  have hSg : Sg ≤ p * (4 * q ^ 2 * (sa + sb)) := by
    calc Sg ≤ ∑ _t ∈ L.toFinset, 4 * q ^ 2 * (sa + sb) := Finset.sum_le_sum hslot
      _ = L.toFinset.card * (4 * q ^ 2 * (sa + sb)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ p * (4 * q ^ 2 * (sa + sb)) :=
        mul_le_mul_of_nonneg_right hcardL
          (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) 2))
            (add_pos hsapos hsbpos).le)
  have hSg0 : 0 ≤ Sg := Finset.sum_nonneg fun t htL => by
    obtain ⟨ht, htk⟩ := hLT t (List.mem_toFinset.1 htL)
    rw [hW2 t, if_neg htk]
    exact div_nonneg (chSum_nonneg (hLnd.erase t) fun _ _ => (hf _).le) (hwpos t ht htk).le
  have hD0 : 0 ≤ Dsl := chSum_nonneg hLnd fun c hc =>
    tv_cliqueEnergy_nonneg _ _ _ _ _ (fun S => (hf S).le) fun e he => by
      simp only [hWdef]
      split_ifs with he'
      · norm_num
      · rcases Finset.mem_insert.1 he with rfl | he
        · omega
        rcases Finset.mem_insert.1 he with rfl | he
        · omega
        exact (hwpos _ (hLT _ (hc.1 e he)).1 he').le
  have hDle : Dsl ≤ tvDir I ε δ j w g σ := tv_clique_le I ε δ j w hgood g σ T hv k hk
  -- assemble
  have hzpos : 0 < sa + sb := add_pos hsapos hsbpos
  have hsq : (ma / sa - mb / sb) ^ 2 = (mb / sb - ma / sa) ^ 2 := by ring
  rw [hsq]
  have hcoef : sa * sb / (sa + sb) * (1 / sb + 1 / sa + 2 / (sb * sa) * Sg) =
      1 + 2 * Sg / (sa + sb) := by
    field_simp
  have hcoef2 : 1 + 2 * Sg / (sa + sb) ≤ 1 + 8 * (p : ℝ) * q ^ 2 := by
    have : 2 * Sg / (sa + sb) ≤ 8 * (p : ℝ) * q ^ 2 := by
      rw [div_le_iff₀ hzpos]; linarith [hSg]
    linarith
  have hfac : 0 ≤ sa * sb / (sa + sb) := div_nonneg (mul_nonneg hsapos.le hsbpos.le) hzpos.le
  calc sa * sb / (sa + sb) * (mb / sb - ma / sa) ^ 2
      ≤ sa * sb / (sa + sb) * ((1 / sb + 1 / sa + 2 / (sb * sa) * Sg) * Dsl) :=
        mul_le_mul_of_nonneg_left htr hfac
    _ = (1 + 2 * Sg / (sa + sb)) * Dsl := by rw [← mul_assoc, hcoef]
    _ ≤ (1 + 8 * (p : ℝ) * q ^ 2) * Dsl := mul_le_mul_of_nonneg_right hcoef2 hD0
    _ ≤ (1 + 8 * (p : ℝ) * q ^ 2) * tvDir I ε δ j w g σ :=
        mul_le_mul_of_nonneg_left hDle (by positivity)

/-- INTERNAL: the conditioning-tree induction: `z_σ Var_{μ_σ}(g) ≤ |T| (1 + 8pq²) 𝔇_σ(g)`.
TEXLINE: sections/transport.tex:396-420 -/
theorem tv_tree (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) (g : Finset ℕ → ℝ) :
    ∀ (n : ℕ) (σ : Finset ℕ) (T : List ℕ), T.length = n → AsgValid (pSmall I ε δ) σ T →
      tvVar (fWeight I ε δ j) g σ T ≤
        n * (1 + 8 * (pSmall I ε δ : ℝ) * (qParam I ε δ : ℝ) ^ 2) * tvDir I ε δ j w g σ := by
  intro n
  induction n with
  | zero =>
    intro σ T hT _
    rw [List.length_eq_zero_iff] at hT
    subst hT
    have hpos := td_fWeight_pos I ε δ j (σ ∪ ∅)
    simp only [tvVar, trMass, chSum_nil, Nat.cast_zero, zero_mul]
    rw [le_iff_eq_or_lt]; left
    field_simp
    ring
  | succ n ih =>
    intro σ T hT hv
    have hTne : T ≠ [] := by rintro rfl; simp at hT
    obtain ⟨k, hk, hsink⟩ := tv_sink hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj.le σ T hv
      hTne
    have hlen : (T.erase k).length = n := by rw [List.length_erase_of_mem hk]; omega
    have hnd : (T.erase k).Nodup := hv.1.erase k
    have hva := tv_child_valid hv hk 0 (by norm_num)
    have hvb := tv_child_valid hv hk 1 (by norm_num)
    simp only [add_zero] at hva
    have iha := ih _ _ hlen hva
    have ihb := ih _ _ hlen hvb
    rw [tv_var_split (fWeight I ε δ j) g σ T k hk (tv_trMass_pos I ε δ j _ _ hnd)
      (tv_trMass_pos I ε δ j _ _ hnd)]
    have hcharge := tv_node_charge hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj w hgood g σ T
      hv k hk hsink
    have hsplit := tv_dir_split I ε δ j w hgood g σ k
    have hK : 0 ≤ (n : ℝ) * (1 + 8 * (pSmall I ε δ : ℝ) * (qParam I ε δ : ℝ) ^ 2) := by
      positivity
    have := mul_le_mul_of_nonneg_left hsplit hK
    push_cast
    nlinarith

/-- INTERNAL: at the root, `C Var_μ(g) = Σ_A f g² - (Σ_A f g)² / C`.
TEXLINE: sections/transport.tex:318-329 -/
theorem tv_root_var (I : Instance) (ε δ : ℚ) (j : ℕ) (g : Finset ℕ → ℝ) :
    Cpart I ε δ j * refMuVar I ε δ j g =
      tvVar (fWeight I ε δ j) g ∅ (List.range (pSmall I ε δ)) := by
  set f := fWeight I ε δ j
  set A := transStates I ε δ
  have hC : 0 < Cpart I ε δ j := td_Cpart_pos I ε δ j
  have hM : transMass I ε δ j = Cpart I ε δ j := transMass_eq_Cpart I ε δ j
  set C := Cpart I ε δ j
  have e1 := tv_trans_eq I ε δ (fun S => f S * g S ^ 2)
  have e2 := tv_trans_eq I ε δ (fun S => f S * g S)
  have e3 := tv_trans_eq I ε δ f
  have hSf : ∑ S ∈ A, f S = C := by rw [← hM]; rfl
  unfold tvVar
  unfold trMass at e1 e2
  rw [← e1, ← e2, ← e3, hSf]
  have hmu : ∀ S ∈ A, refMu I ε δ j S = f S / C := by
    intro S hS; unfold refMu; rw [if_pos hS, hM]
  set m := refMuMean I ε δ j g
  have hm : m = (∑ S ∈ A, f S * g S) / C := by
    simp only [m, refMuMean]
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun S hS => by rw [hmu S hS]; ring
  unfold refMuVar
  have hexp : ∀ S ∈ A, refMu I ε δ j S * (g S - m) ^ 2 =
      (1 / C) * (f S * g S ^ 2) - (2 * m / C) * (f S * g S) + (m ^ 2 / C) * f S := by
    intro S hS; rw [hmu S hS]; ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hSf, hm]
  field_simp
  ring

/-- INTERNAL: at the root, `𝔇_∅ = 𝔇`. -/
theorem tv_root_dir (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ) (g : Finset ℕ → ℝ) :
    tvDir I ε δ j w g ∅ = refDir I ε δ j w g := by
  have h : ∀ S, tvResp ∅ S := fun S e he => absurd he (Finset.notMem_empty e)
  unfold tvDir refDir
  congr 1
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun S' _ => ?_
  by_cases hx : exchNbr S S'
  · rw [if_pos ⟨hx, h S, h S'⟩, if_pos hx]
  · rw [if_neg (fun h' => hx h'.1), if_neg hx]

/-- **Transversal variance** (`prop:transversal-variance`): for good multipliers,
`C Var_μ(g) ≤ C_p 𝔇(g)` for every real `g` on `X`.
PAPER: sections/transport.tex:330-337 -/
theorem transversal_variance (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) (g : Finset ℕ → ℝ) :
    Cpart I ε δ j * refMuVar I ε δ j g ≤ (CpParam I ε δ : ℝ) * refDir I ε δ j w g := by
  rw [tv_root_var, ← tv_root_dir]
  have h := tv_tree hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj w hgood g
    (pSmall I ε δ) ∅ (List.range (pSmall I ε δ)) List.length_range (tv_root_valid' _)
  refine h.trans (le_of_eq ?_)
  unfold CpParam
  push_cast
  ring

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · closed on children · tree induction, sink, variance split, node charge, bridges and clique-edge injection proved; `slot_transport`, `fWeight_omission`, `defect_two_pair`, `defect_three_pair`, `lift_defect_le` handed off
-/
