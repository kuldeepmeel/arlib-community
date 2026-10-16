import Cellcounting.Analysis.ChoiceSum
import Cellcounting.Analysis.FTildeAddition
import Cellcounting.Model.Prior

/-!
# Pair inequalities for defect masses (`lem:defect-inequalities`, `signatures.tex:303-410`)

For a partial transversal assignment `σ` with unassigned pairs `T` and the second
lift `f̃_j`:

* `defect_two_pair` (`eq:defect-two-pair`): `4 c̃^σ_il c̃^σ_li ≤ z_σ²`;
* `defect_three_pair` (`eq:defect-three-pair`): `c̃^σ_il c̃^σ_lk ≤ z_σ c̃^σ_ik`.

Here `z_σ = trMass f̃ σ T` and `c̃^σ_il = defMass f̃ σ T i l`.  Both follow the paper's
proof (`signatures.tex:344-400`) from the addition property of `f̃_j` after fixing `σ` and
summing every other unassigned pair at occupancy one (`fTilde_addition`,
`lem:binary-signatures`):

* two pairs: restricting the `4 × 4` addition matrix on pairs `i, l` to pair-constant
  vectors gives `[[2c̃_li, z], [z, 2c̃_il]]`, whose determinant is nonpositive;
* three pairs: the six-element cubic tensor `T a x y = Σ_c f̃(σ ∪ {a, x, y} ∪ c)` has
  `Hyp` slices (`fTilde_addition` with `a` fixed, padded by `di_hyp_map`); its
  contraction along the indicator of pair `k` satisfies `Hyp` on all six indices
  (`cubic_contraction`, the full-matrix assertion of `lem:binary-contraction`), and
  the Schur-complement step against the `l, l` entry is `di_three_pair_algebra`.

Instead of the paper's explicit square-root bound, `di_three_pair_algebra` applies the
reverse Cauchy–Schwarz form of `Hyp` to `u = 𝟙_l`, `w = 2c̃_ik 𝟙_i + z 𝟙_k`, which gives
`N_ll · N_ik ≤ 2 N_il N_lk` directly.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: congruence by an arbitrary linear map `P` preserves `Hyp`:
`(P Q Pᵀ)` has at most one positive eigenvalue when `Q` does. -/
theorem di_hyp_map {ι κ : Type*} [Fintype ι] [Fintype κ] {Q : ι → ι → ℝ} (hQ : Hyp Q)
    (P : κ → ι → ℝ) : Hyp (fun x y => ∑ d, ∑ d', P x d * Q d d' * P y d') := by
  have hrw : ∀ u w : κ → ℝ, qf (fun x y => ∑ d, ∑ d', P x d * Q d d' * P y d') u w =
      qf Q (fun d => ∑ x, u x * P x d) (fun d => ∑ x, w x * P x d) := by
    intro u w
    simp only [qf, Finset.mul_sum, Finset.sum_mul]
    symm
    calc _ = ∑ d, ∑ d', ∑ x, ∑ y, u x * P x d * Q d d' * (w y * P y d') :=
          Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun d' _ => Finset.sum_comm
      _ = ∑ d, ∑ x, ∑ d', ∑ y, u x * P x d * Q d d' * (w y * P y d') :=
          Finset.sum_congr rfl fun d _ => Finset.sum_comm
      _ = ∑ x, ∑ d, ∑ d', ∑ y, u x * P x d * Q d d' * (w y * P y d') := Finset.sum_comm
      _ = ∑ x, ∑ d, ∑ y, ∑ d', u x * P x d * Q d d' * (w y * P y d') :=
          Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => Finset.sum_comm
      _ = ∑ x, ∑ y, ∑ d, ∑ d', u x * P x d * Q d d' * (w y * P y d') :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
          Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun d' _ => by ring
  intro u w hu
  simp only [hrw] at hu ⊢
  exact hQ _ _ hu

/-- INTERNAL: a node assigns `|σ|` pairs and leaves `|T|` unassigned: `|σ| + |T| = p`. -/
theorem di_card {p : ℕ} {σ : Finset ℕ} {T : List ℕ} (hv : AsgValid p σ T) :
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

/-- INTERNAL: `f̃_j(S) > 0`. -/
theorem di_fTilde_pos (I : Instance) (ε δ : ℚ) (j : ℕ) (S : Finset ℕ) :
    0 < fTilde I ε δ j S := by
  unfold fTilde
  refine mul_pos ?_ (Finset.prod_pos fun s _ => by positivity)
  exact Finset.sum_pos (fun z _ => by positivity) ⟨fun _ => 0, by simp [freeBox]⟩

/-- INTERNAL: the Schur-complement step of `eq:defect-three-pair`.  For the contracted
matrix `M` on the six elements of pairs `i, l, k`, evaluate `Hyp M` on the indicator `u` of
pair `l` and on `w = 2V·𝟙_i + z·𝟙_k`; the entries are `N_ll = 2X`, `N_ik = 2Z`, `N_il = z`,
`N_lk = 2V`, `N_kk = 0`, `N_ii ≥ 0` (`eq:contracted-defect-entries`).
TEXLINE: sections/signatures.tex:370-400 -/
theorem di_three_pair_algebra (g : Finset ℕ → ℝ) (hg : ∀ A, 0 ≤ g A) (i l k : ℕ)
    (X Z V z : ℝ) (hV : 0 < V) (hz : 0 < z) (hX : 0 < X)
    (m1 : X = g {2*k, 2*l, 2*l+1} + g {2*k+1, 2*l, 2*l+1})
    (m2 : Z = g {2*k, 2*i, 2*k+1} + g {2*k, 2*i+1, 2*k+1})
    (m3 : V = g {2*k, 2*l, 2*k+1} + g {2*k, 2*l+1, 2*k+1})
    (m4 : z = g {2*k, 2*l, 2*i} + g {2*k+1, 2*l, 2*i} + g {2*k, 2*l, 2*i+1}
      + g {2*k+1, 2*l, 2*i+1} + g {2*k, 2*l+1, 2*i} + g {2*k+1, 2*l+1, 2*i}
      + g {2*k, 2*l+1, 2*i+1} + g {2*k+1, 2*l+1, 2*i+1})
    (E : Fin 6 → ℕ) (hE : E = ![2*i, 2*i+1, 2*l, 2*l+1, 2*k, 2*k+1])
    (Tt : Fin 6 → Fin 6 → Fin 6 → ℝ)
    (hTt : Tt = fun a u h => if a ≠ u ∧ a ≠ h ∧ u ≠ h then g {E a, E u, E h} else 0)
    (hM : Hyp (fun u h => ∑ a, (![0,0,0,0,1,1] : Fin 6 → ℝ) a * Tt a u h)) :
    X * Z ≤ z * V := by
  have key := hM ![0,0,1,1,0,0] ![2*V, 2*V, 0, 0, z, z]
  subst hTt hE
  simp [qf, Fin.sum_univ_six] at key
  have e : ∀ a b c d e f : ℕ, ({a, b, c} : Finset ℕ) = {d, e, f} → g {a, b, c} = g {d, e, f} :=
    fun _ _ _ _ _ _ h => by rw [h]
  rw [e (2*k) (2*l+1) (2*l) (2*k) (2*l) (2*l+1) (by ext; simp; tauto),
    e (2*k+1) (2*l+1) (2*l) (2*k+1) (2*l) (2*l+1) (by ext; simp; tauto),
    e (2*k+1) (2*i) (2*k) (2*k) (2*i) (2*k+1) (by ext; simp; tauto),
    e (2*k+1) (2*k) (2*i) (2*k) (2*i) (2*k+1) (by ext; simp; tauto),
    e (2*k) (2*k+1) (2*i) (2*k) (2*i) (2*k+1) (by ext; simp; tauto),
    e (2*k+1) (2*i+1) (2*k) (2*k) (2*i+1) (2*k+1) (by ext; simp; tauto),
    e (2*k+1) (2*k) (2*i+1) (2*k) (2*i+1) (2*k+1) (by ext; simp; tauto),
    e (2*k) (2*k+1) (2*i+1) (2*k) (2*i+1) (2*k+1) (by ext; simp; tauto),
    e (2*k+1) (2*l) (2*k) (2*k) (2*l) (2*k+1) (by ext; simp; tauto),
    e (2*k+1) (2*l+1) (2*k) (2*k) (2*l+1) (2*k+1) (by ext; simp; tauto),
    e (2*k) (2*i+1) (2*i) (2*k) (2*i) (2*i+1) (by ext; simp; tauto),
    e (2*k+1) (2*i+1) (2*i) (2*k+1) (2*i) (2*i+1) (by ext; simp; tauto)] at key
  have key2 := key (by rw [m1] at hX; linarith)
  have hY := hg {2*k, 2*i, 2*i+1}
  have hY' := hg {2*k+1, 2*i, 2*i+1}
  have hVz := mul_pos hV hz
  have hXY : 0 ≤ X * (V * V) * (g {2*k, 2*i, 2*i+1} + g {2*k+1, 2*i, 2*i+1}) := by positivity
  have h : X * Z * (V * z) ≤ z * V * (V * z) := by
    subst m1 m2 m3 m4
    linarith
  exact le_of_mul_le_mul_right h hVz

/-- **Two-pair defect inequality** (`eq:defect-two-pair`): `4 c̃^σ_il c̃^σ_li ≤ z_σ²`.
PAPER: sections/signatures.tex:328-336 -/
theorem defect_two_pair (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j ≤ HParam I ε δ)
    (σ : Finset ℕ) (T : List ℕ) (hv : AsgValid (pSmall I ε δ) σ T)
    (i l : ℕ) (hi : i ∈ T) (hl : l ∈ T) (hil : i ≠ l) :
    4 * defMass (fTilde I ε δ j) σ T i l * defMass (fTilde I ε δ j) σ T l i ≤
      trMass (fTilde I ε δ j) σ T ^ 2 := by
  classical
  set p := pSmall I ε δ with hpdef
  set fT := fTilde I ε δ j with hfTdef
  set L := (T.erase i).erase l with hL
  set E : Fin 4 → ℕ := ![2*i, 2*i+1, 2*l, 2*l+1] with hE
  have hEinj : ∀ x y : Fin 4, E x = E y → x = y := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp [hE] at h ⊢ <;> omega
  have hLnd : L.Nodup := (hv.1.erase i).erase l
  have hLmem : ∀ t ∈ L, t ∈ T ∧ t ≠ i ∧ t ≠ l := by
    intro t ht
    have h2 := (hv.1.erase i).mem_erase_iff.1 ht
    have h1 := hv.1.mem_erase_iff.1 h2.2
    exact ⟨h1.2, h1.1, h2.1⟩
  have hσT : ∀ e ∈ σ, ∀ t ∈ T, e / 2 ≠ t := fun e he t ht =>
    (hv.2.2.2.2 t (hv.2.1 t ht)).1 ht e he
  have hEhalf : ∀ x : Fin 4, E x / 2 = i ∨ E x / 2 = l := by
    intro x; fin_cases x <;> simp [hE] <;> omega
  have hEσ : ∀ x : Fin 4, E x ∉ σ := by
    intro x hx
    rcases hEhalf x with h | h
    · exact hσT _ hx i hi h
    · exact hσT _ hx l hl h
  have hElt : ∀ x : Fin 4, E x < 2 * p := by
    have := hv.2.1 i hi; have := hv.2.1 l hl
    intro x; fin_cases x <;> simp [hE] <;> omega
  set D := Finset.univ.image E with hD
  have hDmem : ∀ x : Fin 4, E x ∈ D := fun x => Finset.mem_image.2 ⟨x, Finset.mem_univ _, rfl⟩
  have hDmem' : ∀ e ∈ D, ∃ x : Fin 4, E x = e := by
    intro e he
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 he
    exact ⟨x, rfl⟩
  have hadd := fTilde_addition hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj σ D L
    hv.2.2.1
    (by
      intro e he
      obtain ⟨x, rfl⟩ := hDmem' e he
      exact hElt x)
    (fun t ht => hv.2.1 t (hLmem t ht).1) hLnd
    (by
      rw [Finset.disjoint_left]
      intro e heF heD
      obtain ⟨x, rfl⟩ := hDmem' e heD
      exact hEσ x heF)
    (by
      intro t ht
      obtain ⟨htT, -, -⟩ := hLmem t ht
      exact ⟨fun h => hσT _ h t htT (by omega), fun h => hσT _ h t htT (by omega)⟩)
    (by
      intro t ht
      obtain ⟨htT, hti, htl⟩ := hLmem t ht
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨x, hx⟩ := hDmem' _ h
        rcases hEhalf x with h' | h' <;> rw [hx] at h' <;> omega
      · obtain ⟨x, hx⟩ := hDmem' _ h
        rcases hEhalf x with h' | h' <;> rw [hx] at h' <;> omega)
    (by
      have h1 := di_card hv
      have m1 : l ∈ T.erase i := List.mem_erase_of_ne (Ne.symm hil) |>.2 hl
      have e1 := List.length_erase_of_mem hi
      have e2 := List.length_erase_of_mem m1
      have p1 := List.length_pos_of_mem hi
      have p2 := List.length_pos_of_mem m1
      rw [hL, e2, e1]
      omega)
  set M : Fin 4 → Fin 4 → ℝ := fun x y =>
    if x = y then 0 else chSum L (fun c => fT (insert (E x) (insert (E y) (σ ∪ c)))) with hM
  set P : Fin 4 → D → ℝ := fun x d => if E x = d.1 then 1 else 0 with hP
  have hent : M = fun x y => ∑ d, ∑ d', P x d * addMat fT σ D L d d' * P y d' := by
    funext x y
    rw [Finset.sum_eq_single ⟨E x, hDmem x⟩]
    · rw [Finset.sum_eq_single ⟨E y, hDmem y⟩]
      · simp only [hP, hM, addMat, Subtype.mk.injEq, if_true, one_mul, mul_one]
        by_cases hxy : x = y
        · subst hxy; simp
        · have hExy : E x ≠ E y := fun h => hxy (hEinj _ _ h)
          rw [if_neg hxy, if_neg hExy]
      · intro d _ hd
        have : P y d = 0 := by
          simp only [hP]; rw [if_neg]; intro h; exact hd (Subtype.ext h.symm)
        rw [this, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro d _ hd
      have : P x d = 0 := by
        simp only [hP]; rw [if_neg]; intro h; exact hd (Subtype.ext h.symm)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hHM : Hyp M := by rw [hent]; exact di_hyp_map hadd P
  have key := hHM ![1, 1, 0, 0] ![0, 0, 1, 1]
  simp [qf, Fin.sum_univ_four, hM, hE] at key
  simp only [Finset.insert_comm (2 * i + 1) (2 * i), Finset.insert_comm (2 * l + 1) (2 * l)] at key
  have m1 : defMass fT σ T l i = chSum L (fun c => fT (insert (2 * i) (insert (2 * i + 1) (σ ∪ c)))) := by
    unfold defMass; rw [hL, List.erase_comm l i]
  have m2 : trMass fT σ T =
      ((chSum L fun c => fT (insert (2 * i) (insert (2 * l) (σ ∪ c)))) +
          chSum L fun c => fT (insert (2 * i) (insert (2 * l + 1) (σ ∪ c)))) +
        ((chSum L fun c => fT (insert (2 * i + 1) (insert (2 * l) (σ ∪ c)))) +
          chSum L fun c => fT (insert (2 * i + 1) (insert (2 * l + 1) (σ ∪ c)))) := by
    unfold trMass
    rw [chSum_split hi]
    rw [chSum_split (t := l) (List.mem_erase_of_ne (Ne.symm hil) |>.2 hl)]
    rw [chSum_split (t := l) (List.mem_erase_of_ne (Ne.symm hil) |>.2 hl)]
    have e : ∀ a b : ℕ, (fun c => fT (σ ∪ insert a (insert b c))) =
        (fun c => fT (insert a (insert b (σ ∪ c)))) := by
      intro a b; funext c; refine congrArg fT ?_
      ext x; simp only [Finset.mem_union, Finset.mem_insert, or_left_comm]
    simp only [e]
    rfl
  have hA : 0 < defMass fT σ T l i := chSum_pos ((hv.1.erase l).erase i) fun _ _ => di_fTilde_pos I ε δ j _
  rw [m1] at hA
  have key2 := key (by linarith)
  rw [m2, m1]
  show 4 * chSum L (fun c => fT (insert (2 * l) (insert (2 * l + 1) (σ ∪ c)))) * _ ≤ _
  nlinarith [key2]

/-- **Three-pair defect inequality** (`eq:defect-three-pair`):
`c̃^σ_il c̃^σ_lk ≤ z_σ c̃^σ_ik` for distinct unassigned `i, l, k`.
PAPER: sections/signatures.tex:337-342 -/
theorem defect_three_pair (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j ≤ HParam I ε δ)
    (σ : Finset ℕ) (T : List ℕ) (hv : AsgValid (pSmall I ε δ) σ T)
    (i l k : ℕ) (hi : i ∈ T) (hl : l ∈ T) (hk : k ∈ T) (hil : i ≠ l) (hlk : l ≠ k)
    (hik : i ≠ k) :
    defMass (fTilde I ε δ j) σ T i l * defMass (fTilde I ε δ j) σ T l k ≤
      trMass (fTilde I ε δ j) σ T * defMass (fTilde I ε δ j) σ T i k := by
  classical
  set p := pSmall I ε δ with hpdef
  set fT := fTilde I ε δ j with hfTdef
  set T0 := ((T.erase i).erase l).erase k with hT0
  set g : Finset ℕ → ℝ := fun A => chSum T0 (fun c => fT (A ∪ (σ ∪ c))) with hg
  set E : Fin 6 → ℕ := ![2*i, 2*i+1, 2*l, 2*l+1, 2*k, 2*k+1] with hE
  have hEinj : ∀ x y : Fin 6, E x = E y → x = y := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp [hE] at h ⊢ <;> omega
  have hT0nd : T0.Nodup := ((hv.1.erase i).erase l).erase k
  have hT0mem : ∀ t ∈ T0, t ∈ T ∧ t ≠ i ∧ t ≠ l ∧ t ≠ k := by
    intro t ht
    have h3 := ((hv.1.erase i).erase l).mem_erase_iff.1 ht
    have h2 := (hv.1.erase i).mem_erase_iff.1 h3.2
    have h1 := hv.1.mem_erase_iff.1 h2.2
    exact ⟨h1.2, h1.1, h2.1, h3.1⟩
  have hσT : ∀ e ∈ σ, ∀ t ∈ T, e / 2 ≠ t := fun e he t ht =>
    (hv.2.2.2.2 t (hv.2.1 t ht)).1 ht e he
  have hEhalf : ∀ x : Fin 6, E x / 2 = i ∨ E x / 2 = l ∨ E x / 2 = k := by
    intro x; fin_cases x <;> simp [hE] <;> omega
  have hEσ : ∀ x : Fin 6, E x ∉ σ := by
    intro x hx
    rcases hEhalf x with h | h | h
    · exact hσT _ hx i hi h
    · exact hσT _ hx l hl h
    · exact hσT _ hx k hk h
  have hElt : ∀ x : Fin 6, E x < 2 * p := by
    have := hv.2.1 i hi; have := hv.2.1 l hl; have := hv.2.1 k hk
    intro x; fin_cases x <;> simp [hE] <;> omega
  have hgpos : ∀ A, 0 < g A := fun A => chSum_pos hT0nd fun c _ => di_fTilde_pos I ε δ j _
  set Tt : Fin 6 → Fin 6 → Fin 6 → ℝ :=
    fun a u h => if a ≠ u ∧ a ≠ h ∧ u ≠ h then g {E a, E u, E h} else 0 with hTt
  -- the slices satisfy `Hyp`, by `fTilde_addition`
  have hslice : ∀ a, Hyp (Tt a) := by
    intro a
    set F := insert (E a) σ with hF
    set D := (Finset.univ.erase a).image E with hD
    have hDmem : ∀ x : Fin 6, x ≠ a → E x ∈ D := fun x hx =>
      Finset.mem_image.2 ⟨x, Finset.mem_erase.2 ⟨hx, Finset.mem_univ _⟩, rfl⟩
    have hDmem' : ∀ e ∈ D, ∃ x : Fin 6, x ≠ a ∧ E x = e := by
      intro e he
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 he
      exact ⟨x, (Finset.mem_erase.1 hx).1, rfl⟩
    have hadd := fTilde_addition hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp j hj F D T0
      (by
        intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact hElt a
        · exact hv.2.2.1 e he)
      (by
        intro e he
        obtain ⟨x, -, rfl⟩ := hDmem' e he
        exact hElt x)
      (fun t ht => hv.2.1 t (hT0mem t ht).1) hT0nd
      (by
        rw [Finset.disjoint_left]
        intro e heF heD
        obtain ⟨x, hxa, rfl⟩ := hDmem' e heD
        rcases Finset.mem_insert.1 heF with h | h
        · exact hxa (hEinj _ _ h)
        · exact hEσ x h)
      (by
        intro t ht
        obtain ⟨htT, hti, htl, htk⟩ := hT0mem t ht
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rcases Finset.mem_insert.1 h with h | h
          · rcases hEhalf a with h' | h' | h' <;> rw [← h] at h' <;> omega
          · exact hσT _ h t htT (by omega)
        · rcases Finset.mem_insert.1 h with h | h
          · rcases hEhalf a with h' | h' | h' <;> rw [← h] at h' <;> omega
          · exact hσT _ h t htT (by omega))
      (by
        intro t ht
        obtain ⟨htT, hti, htl, htk⟩ := hT0mem t ht
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨x, -, hx⟩ := hDmem' _ h
          rcases hEhalf x with h' | h' | h' <;> rw [hx] at h' <;> omega
        · obtain ⟨x, -, hx⟩ := hDmem' _ h
          rcases hEhalf x with h' | h' | h' <;> rw [hx] at h' <;> omega)
      (by
        have h1 := di_card hv
        have m1 : l ∈ T.erase i := List.mem_erase_of_ne (Ne.symm hil) |>.2 hl
        have m2 : k ∈ (T.erase i).erase l :=
          List.mem_erase_of_ne (Ne.symm hlk) |>.2 (List.mem_erase_of_ne (Ne.symm hik) |>.2 hk)
        have e1 := List.length_erase_of_mem hi
        have e2 := List.length_erase_of_mem m1
        have e3 := List.length_erase_of_mem m2
        have p1 := List.length_pos_of_mem hi
        have p2 := List.length_pos_of_mem m1
        have p3 := List.length_pos_of_mem m2
        rw [hF, Finset.card_insert_of_notMem (hEσ a), hT0, e3, e2, e1]
        omega)
    set P : Fin 6 → D → ℝ := fun x d => if x ≠ a ∧ E x = d.1 then 1 else 0 with hP
    have hent : Tt a = fun x y => ∑ d, ∑ d', P x d * addMat fT F D T0 d d' * P y d' := by
      funext x y
      by_cases hxa : x = a
      · subst hxa; simp [hP, hTt]
      by_cases hya : y = a
      · subst hya; simp [hP, hTt]
      rw [Finset.sum_eq_single ⟨E x, hDmem x hxa⟩]
      · rw [Finset.sum_eq_single ⟨E y, hDmem y hya⟩]
        · simp only [hP, hTt, addMat, Subtype.mk.injEq]
          by_cases hxy : x = y
          · subst hxy; simp
          · have hExy : E x ≠ E y := fun h => hxy (hEinj _ _ h)
            simp only [ne_eq, Ne.symm hxa, not_false_eq_true, Ne.symm hya, hxy, and_self,
              if_true, hExy, if_false, hxa, hya, mul_one, one_mul]
            simp only [hg]
            refine congrArg _ (funext fun c => congrArg fT ?_)
            ext e
            simp only [hF, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
            tauto
        · intro d _ hd
          have : P y d = 0 := by
            simp only [hP]; rw [if_neg]; rintro ⟨-, h⟩; exact hd (Subtype.ext h.symm)
          rw [this, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro d _ hd
        have : P x d = 0 := by
          simp only [hP]; rw [if_neg]; rintro ⟨-, h⟩; exact hd (Subtype.ext h.symm)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hent]
    exact di_hyp_map hadd P
  have hs1 : ∀ a u h, Tt a u h = Tt u a h := by
    intro a u h
    simp only [hTt]
    rw [Finset.insert_comm (E a) (E u)]
    by_cases h1 : a ≠ u ∧ a ≠ h ∧ u ≠ h
    · rw [if_pos h1, if_pos ⟨Ne.symm h1.1, h1.2.2, h1.2.1⟩]
    · rw [if_neg h1, if_neg]
      rintro ⟨h2, h3, h4⟩
      exact h1 ⟨Ne.symm h2, h4, h3⟩
  have hs2 : ∀ a u h, Tt a u h = Tt a h u := by
    intro a u h
    simp only [hTt]
    rw [Finset.pair_comm (E u) (E h)]
    by_cases h1 : a ≠ u ∧ a ≠ h ∧ u ≠ h
    · rw [if_pos h1, if_pos ⟨h1.2.1, h1.1, Ne.symm h1.2.2⟩]
    · rw [if_neg h1, if_neg]
      rintro ⟨h2, h3, h4⟩
      exact h1 ⟨h3, h2, Ne.symm h4⟩
  have hTpos : ∀ a u h, a ≠ u → a ≠ h → u ≠ h → 0 < Tt a u h := by
    intro a u h h1 h2 h3
    simp only [hTt]; rw [if_pos ⟨h1, h2, h3⟩]; exact hgpos _
  have hTzero : ∀ a u h, (a = u ∨ a = h ∨ u = h) → Tt a u h = 0 := by
    intro a u h h1
    simp only [hTt]; rw [if_neg]; tauto
  have hM := cubic_contraction Tt hs1 hs2 hTpos hTzero hslice ![0, 0, 0, 0, 1, 1]
    (by intro a; fin_cases a <;> simp)
  -- the masses as sums of `g` over the six elements
  have mk2 : k ∈ (T.erase i).erase l :=
    List.mem_erase_of_ne (Ne.symm hlk) |>.2 (List.mem_erase_of_ne (Ne.symm hik) |>.2 hk)
  have m1 : defMass fT σ T i l = g {2*k, 2*l, 2*l+1} + g {2*k+1, 2*l, 2*l+1} := by
    unfold defMass
    rw [chSum_split mk2]
    simp only [hg]
    refine congrArg₂ (· + ·) ?_ ?_ <;> refine congrArg _ (funext fun c => congrArg fT ?_) <;>
      (ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        or_assoc, or_comm, or_left_comm])
  have m2 : defMass fT σ T l k = g {2*k, 2*i, 2*k+1} + g {2*k, 2*i+1, 2*k+1} := by
    unfold defMass
    rw [chSum_split (t := i) (List.mem_erase_of_ne hik |>.2 (List.mem_erase_of_ne hil |>.2 hi))]
    have hp' : ((T.erase l).erase k).erase i = T0 := by
      rw [hT0, List.erase_comm k i, List.erase_comm l i]
    rw [hp']
    simp only [hg]
    refine congrArg₂ (· + ·) ?_ ?_ <;> refine congrArg _ (funext fun c => congrArg fT ?_) <;>
      (ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        or_assoc, or_comm, or_left_comm])
  have m3 : defMass fT σ T i k = g {2*k, 2*l, 2*k+1} + g {2*k, 2*l+1, 2*k+1} := by
    unfold defMass
    rw [chSum_split (t := l) (List.mem_erase_of_ne hlk |>.2 (List.mem_erase_of_ne (Ne.symm hil) |>.2 hl))]
    have hp' : ((T.erase i).erase k).erase l = T0 := by
      rw [hT0, List.erase_comm k l]
    rw [hp']
    simp only [hg]
    refine congrArg₂ (· + ·) ?_ ?_ <;> refine congrArg _ (funext fun c => congrArg fT ?_) <;>
      (ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        or_assoc, or_comm, or_left_comm])
  have m4 : trMass fT σ T = g {2*k, 2*l, 2*i} + g {2*k+1, 2*l, 2*i} + g {2*k, 2*l, 2*i+1}
      + g {2*k+1, 2*l, 2*i+1} + g {2*k, 2*l+1, 2*i} + g {2*k+1, 2*l+1, 2*i}
      + g {2*k, 2*l+1, 2*i+1} + g {2*k+1, 2*l+1, 2*i+1} := by
    unfold trMass
    rw [chSum_split hi]
    rw [chSum_split (t := l) (List.mem_erase_of_ne (Ne.symm hil) |>.2 hl)]
    rw [chSum_split (t := l) (List.mem_erase_of_ne (Ne.symm hil) |>.2 hl)]
    rw [chSum_split mk2, chSum_split mk2, chSum_split mk2, chSum_split mk2]
    have e : ∀ a b d : ℕ, (fun c => fT (σ ∪ insert a (insert b (insert d c)))) =
        (fun c => fT ({d, b, a} ∪ (σ ∪ c))) := by
      intro a b d; funext c; refine congrArg fT ?_
      ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    simp only [e, hg]
    ring
  have hX : 0 < defMass fT σ T i l := chSum_pos ((hv.1.erase i).erase l) fun _ _ => di_fTilde_pos I ε δ j _
  have hV : 0 < defMass fT σ T i k := chSum_pos ((hv.1.erase i).erase k) fun _ _ => di_fTilde_pos I ε δ j _
  have hz : 0 < trMass fT σ T := chSum_pos hv.1 fun _ _ => di_fTilde_pos I ε δ j _
  exact di_three_pair_algebra g (fun A => (hgpos A).le) i l k _ _ _ _ hV hz hX m1 m2 m3 m4 E rfl Tt rfl hM

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-15 · closed on children · `defect_three_pair`, `defect_two_pair` proved from `fTilde_addition` and `cubic_contraction` (both handed off)
-/
