import Cellcounting.Analysis.ChoiceSum

/-!
# The one-hole transport inequality (`lem:transport`, `transport.tex:99-316`)

An abstract form of `lem:transport`, for a positive weight `f` on subsets of `ℕ` whose
contracted two-omission matrices have at most one positive eigenvalue.

Fixed inclusions `F`; two singleton slots `{x0}`, `{x1}`; ordinary slots the pairs
`{2t, 2t + 1}`, `t ∈ L`.  A one-hole state is `F ∪ (Y \ {i})` for a complete display
`Y = {x0, x1} ∪ c` (`c` a choice set of `L`) and a hole `i ∈ Y`; its weight is
`W i · f`.  Its hole-`x0` states have `f`-mass `s0` and `f`-weighted mean `m0 / s0`,
similarly for `x1`; `v_t` is the `f`-mass of the sets omitting both singletons, full in
pair `t`, and singly occupied elsewhere.

`slot_transport` is `eq:slot-transport`:
`(ḡ0 - ḡ1)² ≤ (1/(s0 W_{x0}) + 1/(s1 W_{x1}) + 2/(s0 s1) Σ_t v_t / W_t) · D`,
where `D` sums, over complete displays, the clique energy `cliqueEnergy` of the
one-hole states of the display (conductance the minimum of the two endpoint weights).
Distinct displays have disjoint clique edges, so `D` is at most the energy of any
graph containing all those edges with those conductances; that comparison is left
to the application.

The hypothesis `hsig` is the omission signature at every node of the paper's
conditioning tree: for every display `D` drawn from the slots and every set `L'` of
still-unprocessed pairs, with `|D| + |L'| = |L| + 3`, the two-omission matrix
`omitMat f F D L'` has at most one positive eigenvalue (`Hyp`).

Proof (the paper's conditioning-tree argument, without explicit currents).  A node is a
display `R` (the singletons and the chosen elements of the processed pairs) and the list
`L` of unprocessed pairs, with masses `slotM`, functional `slotPhi`, energy `slotD`,
matrices `slotV`, and budget `slotB = Σ_i m_i h_i² / W_i + Σ_{t ∈ L} (-hᵀ V_t h) / W_t`.
`st_node` proves, by induction on `L`, that a balanced (`Σ_i m_i h_i = 0`) node satisfies
`0 ≤ B` and `Φ² ≤ B · D`:
* leaf: route through a hub maximizing `W_i m_i` and apply Cauchy–Schwarz (`st_hub`);
* step: split `Φ`, `D`, `m` over the two children (`st_split_Phi`, `st_split_D`,
  `st_split_M`, new coefficients `∓X/u`), split `hᵀ V_s h` for later pairs
  (`st_split_Q`), bound the increment `2X²/(u W_t)` by `-hᵀ V_t h / W_t` with the
  omission signature of the matrix on `R ∪ {2t, 2t+1}` (`st_schur_node`), and combine the
  children by two-term Cauchy–Schwarz (`st_two_cs`).
`slot_transport` is the root instance `R = {x0, x1}`, `h = (1/s0, -1/s1)`; the root
values of `V_t` are `v_t`.  The flow-criterion step `eq:transport-flow-criterion` of the
paper is absorbed: Cauchy–Schwarz is applied leaf by leaf and the leaf bounds are summed
with the two-term inequality, so no assembled current or divergence check is needed.
-/

namespace Cellcounting.Analysis

/-- INTERNAL: the clique energy of the one-hole states `(F ∪ Disp) \ {i}`, `i ∈ Disp`,
with hole weights `W i · f` and conductance the minimum of the two endpoint weights,
as half the ordered-pair sum.
TEXLINE: sections/transport.tex:152-171 -/
noncomputable def cliqueEnergy (f g : Finset ℕ → ℝ) (W : ℕ → ℝ) (F Disp : Finset ℕ) : ℝ :=
  (∑ i ∈ Disp, ∑ k ∈ Disp,
    if i = k then 0 else
      min (W i * f ((F ∪ Disp).erase i)) (W k * f ((F ∪ Disp).erase k)) *
        (g ((F ∪ Disp).erase i) - g ((F ∪ Disp).erase k)) ^ 2) / 2

/-- INTERNAL: the node mass `m_i`: `f` summed over the sets containing `F ∪ (R \ {i})`
with single occupancy in the unprocessed pairs `L`.
TEXLINE: sections/transport.tex:186-193 -/
noncomputable def slotM (f : Finset ℕ → ℝ) (F R : Finset ℕ) (L : List ℕ) (i : ℕ) : ℝ :=
  chSum L (fun c => f ((F ∪ R ∪ c).erase i))

/-- INTERNAL: the node functional `Σ_i h_i Σ_c (f g)(F ∪ R ∪ c \ {i})`, whose square the
recursion bounds; at the root it is `ḡ0 - ḡ1`.
TEXLINE: sections/transport.tex:142-157 -/
noncomputable def slotPhi (f g : Finset ℕ → ℝ) (F R : Finset ℕ) (L : List ℕ) (h : ℕ → ℝ) : ℝ :=
  ∑ i ∈ R, h i * chSum L (fun c => f ((F ∪ R ∪ c).erase i) * g ((F ∪ R ∪ c).erase i))

/-- INTERNAL: the clique energies of all complete displays below a node.
TEXLINE: sections/transport.tex:152-171 -/
noncomputable def slotD (f g : Finset ℕ → ℝ) (W : ℕ → ℝ) (F R : Finset ℕ) (L : List ℕ) : ℝ :=
  chSum L (fun c => cliqueEnergy f g W F (R ∪ c))

/-- INTERNAL: the matrix `V_t(R)` of a node, zero on the diagonal: holes at `i, k`, pair `t`
full, the other unprocessed pairs singly occupied.
TEXLINE: sections/transport.tex:224-232 -/
noncomputable def slotV (f : Finset ℕ → ℝ) (F R : Finset ℕ) (L : List ℕ) (t i k : ℕ) : ℝ :=
  if i = k then 0 else
    chSum (L.erase t) (fun c =>
      f (((F ∪ insert (2 * t) (insert (2 * t + 1) R) ∪ c).erase i).erase k))

/-- INTERNAL: the quadratic quantity `hᵀ V_t(R) h`.
TEXLINE: sections/transport.tex:272-284 -/
noncomputable def slotQ (f : Finset ℕ → ℝ) (F R : Finset ℕ) (L : List ℕ) (t : ℕ)
    (h : ℕ → ℝ) : ℝ :=
  ∑ i ∈ R, ∑ k ∈ R, h i * h k * slotV f F R L t i k

/-- INTERNAL: the node budget `Ψ(R, h) + Σ_{t unprocessed} (-hᵀ V_t(R) h) / W_t`.
TEXLINE: sections/transport.tex:198-205, 272-290 -/
noncomputable def slotB (f : Finset ℕ → ℝ) (W : ℕ → ℝ) (F R : Finset ℕ) (L : List ℕ)
    (h : ℕ → ℝ) : ℝ :=
  ∑ i ∈ R, slotM f F R L i * h i ^ 2 / W i + ∑ t ∈ L.toFinset, -slotQ f F R L t h / W (2 * t)

/-- INTERNAL: the omission signature for every display drawn from the node's display `R`
and its unprocessed pairs `L`; inherited by both children.
TEXLINE: sections/transport.tex:233-249 -/
def SlotSig (f : Finset ℕ → ℝ) (F R : Finset ℕ) (L : List ℕ) : Prop :=
  ∀ (D : Finset ℕ) (L₀ : List ℕ), L₀.Nodup → (∀ t ∈ L₀, t ∈ L) →
    (∀ e ∈ D, e ∈ R ∨ ∃ t ∈ L, e = 2 * t ∨ e = 2 * t + 1) →
    (∀ t ∈ L₀, 2 * t ∉ D ∧ 2 * t + 1 ∉ D) →
    D.card + L₀.length = R.card + L.length + 1 → Hyp (omitMat f F D L₀)

/-- INTERNAL: a choice set of `L` misses both elements of a pair outside `L`. -/
theorem st_notMem_choice {L : List ℕ} {c : Finset ℕ} (hc : IsChoice L c) {t : ℕ}
    (ht : t ∉ L) : 2 * t ∉ c ∧ 2 * t + 1 ∉ c := by
  refine ⟨fun h => ht ?_, fun h => ht ?_⟩
  · have := hc.1 _ h; rwa [show 2 * t / 2 = t by omega] at this
  · have := hc.1 _ h; rwa [show (2 * t + 1) / 2 = t by omega] at this

/-- INTERNAL: positivity of the pair multipliers on a choice set. -/
theorem st_W_choice {L : List ℕ} {W : ℕ → ℝ}
    (hW : ∀ t ∈ L, 0 < W (2 * t) ∧ W (2 * t + 1) = W (2 * t)) {c : Finset ℕ}
    (hc : IsChoice L c) : ∀ e ∈ c, 0 < W e := by
  intro e he
  have hm := hc.1 e he
  obtain ⟨h1, h2⟩ := hW _ hm
  rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
  · rwa [show 2 * k / 2 = k by omega] at h1
  · rw [show (2 * k + 1) / 2 = k by omega] at h1 h2; rw [h2]; exact h1

/-- INTERNAL: the clique energy is nonnegative. -/
theorem st_cliqueEnergy_nonneg (f g : Finset ℕ → ℝ) (W : ℕ → ℝ) (F Disp : Finset ℕ)
    (hf : ∀ S, 0 < f S) (hW : ∀ e ∈ Disp, 0 < W e) : 0 ≤ cliqueEnergy f g W F Disp := by
  unfold cliqueEnergy
  refine div_nonneg (Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun k hk => ?_)
    (by norm_num)
  split_ifs
  · exact le_rfl
  · have := hW i hi; have := hW k hk; have := hf ((F ∪ Disp).erase i)
    have := hf ((F ∪ Disp).erase k)
    exact mul_nonneg (le_min (by positivity) (by positivity)) (sq_nonneg _)

/-- INTERNAL: the energy below a node is nonnegative. -/
theorem st_slotD_nonneg (f g : Finset ℕ → ℝ) (W : ℕ → ℝ) (F R : Finset ℕ) (L : List ℕ)
    (hf : ∀ S, 0 < f S) (hL : L.Nodup) (hRW : ∀ i ∈ R, 0 < W i)
    (hW : ∀ t ∈ L, 0 < W (2 * t) ∧ W (2 * t + 1) = W (2 * t)) : 0 ≤ slotD f g W F R L := by
  refine chSum_nonneg hL fun c hc => st_cliqueEnergy_nonneg f g W F _ hf fun e he => ?_
  rcases Finset.mem_union.1 he with he | he
  · exact hRW e he
  · exact st_W_choice hW hc e he

/-- INTERNAL: set bookkeeping. -/
theorem st_union_insert (F R c : Finset ℕ) (x : ℕ) :
    F ∪ R ∪ insert x c = F ∪ insert x R ∪ c := by
  ext y; simp only [Finset.mem_union, Finset.mem_insert]; tauto

/-- INTERNAL: `m_i = m_i^a + m_i^b` when the next pair is split.
TEXLINE: sections/transport.tex:207-210 -/
theorem st_split_M (f : Finset ℕ → ℝ) (F R : Finset ℕ) (t : ℕ) (L : List ℕ) (i : ℕ) :
    slotM f F R (t :: L) i = slotM f F (insert (2 * t) R) L i +
      slotM f F (insert (2 * t + 1) R) L i := by
  simp only [slotM, chSum_cons, st_union_insert]

/-- INTERNAL: the energy below a node is the sum of the energies below its children. -/
theorem st_split_D (f g : Finset ℕ → ℝ) (W : ℕ → ℝ) (F R : Finset ℕ) (t : ℕ) (L : List ℕ) :
    slotD f g W F R (t :: L) = slotD f g W F (insert (2 * t) R) L +
      slotD f g W F (insert (2 * t + 1) R) L := by
  have e : ∀ x c, R ∪ insert x c = insert x R ∪ c := fun x c => by
    ext y; simp only [Finset.mem_union, Finset.mem_insert]; tauto
  simp only [slotD, chSum_cons, e]

/-- INTERNAL: set bookkeeping for a newly displayed element. -/
theorem st_erase_new {F R c : Finset ℕ} {x : ℕ} (hF : x ∉ F) (hR : x ∉ R) (hc : x ∉ c) :
    (F ∪ insert x R ∪ c).erase x = F ∪ R ∪ c := by
  rw [← st_union_insert, Finset.union_insert, Finset.erase_insert]
  simp [hF, hR, hc]

/-- INTERNAL: the new hole has the same mass `u` in either child.
TEXLINE: sections/transport.tex:210-213 -/
theorem st_newhole (φ : Finset ℕ → ℝ) (F R : Finset ℕ) (L : List ℕ) (hL : L.Nodup) (x : ℕ)
    (hF : x ∉ F) (hR : x ∉ R) (hc : ∀ c, IsChoice L c → x ∉ c) :
    chSum L (fun c => φ ((F ∪ insert x R ∪ c).erase x)) = chSum L (fun c => φ (F ∪ R ∪ c)) :=
  chSum_congr hL fun c hcc => by rw [st_erase_new hF hR (hc c hcc)]

/-- INTERNAL: the node functional splits over the children with new coefficients `∓ z`.
TEXLINE: sections/transport.tex:213-217 -/
theorem st_split_Phi (f g : Finset ℕ → ℝ) (F R : Finset ℕ) (t : ℕ) (L : List ℕ)
    (hL : L.Nodup) (htL : t ∉ L) (haF : 2 * t ∉ F) (hbF : 2 * t + 1 ∉ F)
    (haR : 2 * t ∉ R) (hbR : 2 * t + 1 ∉ R) (h : ℕ → ℝ) (z : ℝ) :
    slotPhi f g F R (t :: L) h =
      slotPhi f g F (insert (2 * t) R) L (fun i => if i = 2 * t then -z else h i) +
      slotPhi f g F (insert (2 * t + 1) R) L (fun i => if i = 2 * t + 1 then z else h i) := by
  have hc : ∀ c, IsChoice L c → 2 * t ∉ c ∧ 2 * t + 1 ∉ c := fun c hc =>
    st_notMem_choice hc htL
  have n1 : chSum L (fun c => f ((F ∪ insert (2 * t) R ∪ c).erase (2 * t)) *
      g ((F ∪ insert (2 * t) R ∪ c).erase (2 * t))) =
      chSum L (fun c => f (F ∪ R ∪ c) * g (F ∪ R ∪ c)) :=
    st_newhole (fun S => f S * g S) F R L hL _ haF haR fun c h => (hc c h).1
  have n2 : chSum L (fun c => f ((F ∪ insert (2 * t + 1) R ∪ c).erase (2 * t + 1)) *
      g ((F ∪ insert (2 * t + 1) R ∪ c).erase (2 * t + 1))) =
      chSum L (fun c => f (F ∪ R ∪ c) * g (F ∪ R ∪ c)) :=
    st_newhole (fun S => f S * g S) F R L hL _ hbF hbR fun c h => (hc c h).2
  unfold slotPhi
  rw [Finset.sum_insert haR, Finset.sum_insert hbR]
  beta_reduce
  rw [if_pos rfl, if_pos rfl, n1, n2]
  have e1 : ∑ i ∈ R, (if i = 2 * t then -z else h i) *
      chSum L (fun c => f ((F ∪ insert (2 * t) R ∪ c).erase i) *
        g ((F ∪ insert (2 * t) R ∪ c).erase i)) =
      ∑ i ∈ R, h i * chSum L (fun c => f ((F ∪ R ∪ insert (2 * t) c).erase i) *
        g ((F ∪ R ∪ insert (2 * t) c).erase i)) :=
    Finset.sum_congr rfl fun i hi => by
      rw [if_neg (show i ≠ 2 * t from fun he => haR (he ▸ hi))]; simp only [st_union_insert]
  have e2 : ∑ i ∈ R, (if i = 2 * t + 1 then z else h i) *
      chSum L (fun c => f ((F ∪ insert (2 * t + 1) R ∪ c).erase i) *
        g ((F ∪ insert (2 * t + 1) R ∪ c).erase i)) =
      ∑ i ∈ R, h i * chSum L (fun c => f ((F ∪ R ∪ insert (2 * t + 1) c).erase i) *
        g ((F ∪ R ∪ insert (2 * t + 1) c).erase i)) :=
    Finset.sum_congr rfl fun i hi => by
      rw [if_neg (show i ≠ 2 * t + 1 from fun he => hbR (he ▸ hi))]; simp only [st_union_insert]
  rw [e1, e2]
  simp only [chSum_cons, mul_add, Finset.sum_add_distrib]
  ring

/-- INTERNAL: a double sum over `insert x R`. -/
theorem st_dsum_insert {x : ℕ} {R : Finset ℕ} (hx : x ∉ R) (φ : ℕ → ℕ → ℝ) :
    ∑ i ∈ insert x R, ∑ k ∈ insert x R, φ i k =
      φ x x + ∑ k ∈ R, φ x k + ∑ i ∈ R, φ i x + ∑ i ∈ R, ∑ k ∈ R, φ i k := by
  rw [Finset.sum_insert hx, Finset.sum_insert hx]
  simp only [Finset.sum_insert hx, Finset.sum_add_distrib]
  ring

/-- INTERNAL: a child's `V` entry against the new hole does not depend on the child.
TEXLINE: sections/transport.tex:272-280 -/
theorem st_V_cross (f : Finset ℕ → ℝ) (F R : Finset ℕ) (L : List ℕ) (hL : L.Nodup)
    (s x : ℕ) (hxF : x ∉ F) (hxR : x ∉ R) (hxs : x ≠ 2 * s ∧ x ≠ 2 * s + 1)
    (hxc : ∀ c, IsChoice (L.erase s) c → x ∉ c) (k : ℕ) (hk : k ∈ R) :
    slotV f F (insert x R) L s x k =
        chSum (L.erase s) (fun c => f ((F ∪ insert (2 * s) (insert (2 * s + 1) R) ∪ c).erase k)) ∧
      slotV f F (insert x R) L s k x =
        chSum (L.erase s) (fun c => f ((F ∪ insert (2 * s) (insert (2 * s + 1) R) ∪ c).erase k)) := by
  have hkx : k ≠ x := fun he => hxR (he ▸ hk)
  have hset : ∀ c, IsChoice (L.erase s) c →
      (F ∪ insert (2 * s) (insert (2 * s + 1) (insert x R)) ∪ c).erase x =
        F ∪ insert (2 * s) (insert (2 * s + 1) R) ∪ c := by
    intro c hc
    rw [Finset.insert_comm (2 * s + 1) x, Finset.insert_comm (2 * s) x]
    exact st_erase_new hxF (by simp [hxs.1, hxs.2, hxR]) (hxc c hc)
  have hL' : (L.erase s).Nodup := hL.erase s
  refine ⟨?_, ?_⟩
  · unfold slotV
    rw [if_neg (Ne.symm hkx)]
    exact chSum_congr hL' fun c hc => by rw [hset c hc]
  · unfold slotV
    rw [if_neg hkx]
    exact chSum_congr hL' fun c hc => by rw [Finset.erase_right_comm, hset c hc]

/-- INTERNAL: the old `V` entries split additively over the children.
TEXLINE: sections/transport.tex:272-280 -/
theorem st_V_old (f : Finset ℕ → ℝ) (F R : Finset ℕ) (t : ℕ) (L : List ℕ) (s : ℕ)
    (hst : s ≠ t) (i k : ℕ) :
    slotV f F (insert (2 * t) R) L s i k + slotV f F (insert (2 * t + 1) R) L s i k =
      slotV f F R (t :: L) s i k := by
  unfold slotV
  by_cases hik : i = k
  · simp [hik]
  · rw [if_neg hik, if_neg hik, if_neg hik,
      List.erase_cons_tail (by simpa using Ne.symm hst), chSum_cons]
    have e : ∀ x c, F ∪ insert (2 * s) (insert (2 * s + 1) R) ∪ insert x c =
        F ∪ insert (2 * s) (insert (2 * s + 1) (insert x R)) ∪ c := fun x c => by
      ext y; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    simp only [e]

/-- INTERNAL: `hᵀ V_s h` at a node is the sum of the children's quantities, for a pair `s`
processed later.
TEXLINE: sections/transport.tex:272-284 -/
theorem st_split_Q (f : Finset ℕ → ℝ) (F R : Finset ℕ) (t : ℕ) (L : List ℕ)
    (hL : L.Nodup) (htL : t ∉ L) (haF : 2 * t ∉ F) (hbF : 2 * t + 1 ∉ F)
    (haR : 2 * t ∉ R) (hbR : 2 * t + 1 ∉ R) (h : ℕ → ℝ) (z : ℝ) (s : ℕ) (hs : s ∈ L) :
    slotQ f F (insert (2 * t) R) L s (fun i => if i = 2 * t then -z else h i) +
      slotQ f F (insert (2 * t + 1) R) L s (fun i => if i = 2 * t + 1 then z else h i) =
      slotQ f F R (t :: L) s h := by
  have hst : s ≠ t := fun he => htL (he ▸ hs)
  have hc : ∀ c, IsChoice (L.erase s) c → 2 * t ∉ c ∧ 2 * t + 1 ∉ c := fun c hc =>
    st_notMem_choice hc fun h' => htL (List.mem_of_mem_erase h')
  set P : ℕ → ℝ := fun k =>
    chSum (L.erase s) (fun c => f ((F ∪ insert (2 * s) (insert (2 * s + 1) R) ∪ c).erase k))
  have ca := st_V_cross f F R L hL s (2 * t) haF haR (by omega) (fun c h' => (hc c h').1)
  have cb := st_V_cross f F R L hL s (2 * t + 1) hbF hbR (by omega) (fun c h' => (hc c h').2)
  unfold slotQ
  rw [st_dsum_insert haR, st_dsum_insert hbR]
  have hRa : ∀ i ∈ R, i ≠ 2 * t := fun i hi he => haR (he ▸ hi)
  have hRb : ∀ i ∈ R, i ≠ 2 * t + 1 := fun i hi he => hbR (he ▸ hi)
  have a1 : ∑ k ∈ R, (if 2 * t = 2 * t then -z else h (2 * t)) *
      (if k = 2 * t then -z else h k) * slotV f F (insert (2 * t) R) L s (2 * t) k =
      ∑ k ∈ R, -z * h k * P k :=
    Finset.sum_congr rfl fun k hk => by rw [if_pos rfl, if_neg (hRa k hk), (ca k hk).1]
  have a2 : ∑ i ∈ R, (if i = 2 * t then -z else h i) *
      (if 2 * t = 2 * t then -z else h (2 * t)) * slotV f F (insert (2 * t) R) L s i (2 * t) =
      ∑ k ∈ R, -z * h k * P k :=
    Finset.sum_congr rfl fun k hk => by rw [if_pos rfl, if_neg (hRa k hk), (ca k hk).2]; ring
  have a3 : ∑ i ∈ R, ∑ k ∈ R, (if i = 2 * t then -z else h i) *
      (if k = 2 * t then -z else h k) * slotV f F (insert (2 * t) R) L s i k =
      ∑ i ∈ R, ∑ k ∈ R, h i * h k * slotV f F (insert (2 * t) R) L s i k :=
    Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun k hk => by
      rw [if_neg (hRa i hi), if_neg (hRa k hk)]
  have b1 : ∑ k ∈ R, (if 2 * t + 1 = 2 * t + 1 then z else h (2 * t + 1)) *
      (if k = 2 * t + 1 then z else h k) * slotV f F (insert (2 * t + 1) R) L s (2 * t + 1) k =
      ∑ k ∈ R, z * h k * P k :=
    Finset.sum_congr rfl fun k hk => by rw [if_pos rfl, if_neg (hRb k hk), (cb k hk).1]
  have b2 : ∑ i ∈ R, (if i = 2 * t + 1 then z else h i) *
      (if 2 * t + 1 = 2 * t + 1 then z else h (2 * t + 1)) *
        slotV f F (insert (2 * t + 1) R) L s i (2 * t + 1) =
      ∑ k ∈ R, z * h k * P k :=
    Finset.sum_congr rfl fun k hk => by rw [if_pos rfl, if_neg (hRb k hk), (cb k hk).2]; ring
  have b3 : ∑ i ∈ R, ∑ k ∈ R, (if i = 2 * t + 1 then z else h i) *
      (if k = 2 * t + 1 then z else h k) * slotV f F (insert (2 * t + 1) R) L s i k =
      ∑ i ∈ R, ∑ k ∈ R, h i * h k * slotV f F (insert (2 * t + 1) R) L s i k :=
    Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun k hk => by
      rw [if_neg (hRb i hi), if_neg (hRb k hk)]
  have d0 : ∀ x (R' : Finset ℕ), slotV f F R' L s x x = 0 := fun x R' => by simp [slotV]
  beta_reduce
  rw [a1, a2, a3, b1, b2, b3, d0, d0]
  have hsplit : ∑ i ∈ R, ∑ k ∈ R, h i * h k * slotV f F R (t :: L) s i k =
      ∑ i ∈ R, ∑ k ∈ R, h i * h k * slotV f F (insert (2 * t) R) L s i k +
        ∑ i ∈ R, ∑ k ∈ R, h i * h k * slotV f F (insert (2 * t + 1) R) L s i k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← st_V_old f F R t L s hst i k]; ring
  rw [hsplit]
  have hz : ∑ k ∈ R, -z * h k * P k = -∑ k ∈ R, z * h k * P k := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [hz]; ring

/-- INTERNAL: the bilinear form `uᵀ N w` on the finset `D`, with `ℕ`-indexed data. -/
def stForm (D : Finset ℕ) (N : ℕ → ℕ → ℝ) (u w : ℕ → ℝ) : ℝ :=
  ∑ x ∈ D, ∑ y ∈ D, u x * N x y * w y

/-- INTERNAL: expansion of `stForm` on `insert a (insert b R)`. -/
theorem stForm_expand (R : Finset ℕ) (a b : ℕ) (hab : a ≠ b) (haR : a ∉ R) (hbR : b ∉ R)
    (N : ℕ → ℕ → ℝ) (u w : ℕ → ℝ) :
    stForm (insert a (insert b R)) N u w =
      u a * N a a * w a + u a * N a b * w b + u b * N b a * w a + u b * N b b * w b +
      ∑ y ∈ R, u a * N a y * w y + ∑ y ∈ R, u b * N b y * w y +
      ∑ x ∈ R, u x * N x a * w a + ∑ x ∈ R, u x * N x b * w b +
      ∑ x ∈ R, ∑ y ∈ R, u x * N x y * w y := by
  have hsum : ∀ φ : ℕ → ℝ, ∑ x ∈ insert a (insert b R), φ x = φ a + φ b + ∑ x ∈ R, φ x := by
    intro φ
    rw [Finset.sum_insert (by simp [hab, haR]), Finset.sum_insert hbR]; ring
  simp only [stForm, hsum, Finset.sum_add_distrib]
  ring

/-- INTERNAL: `eq:transport-schur` for an abstract form with at most one positive
eigenvalue: `2X²/u ≤ -hᵀ V h`.
TEXLINE: sections/transport.tex:250-269 -/
theorem st_schur_core (R : Finset ℕ) (a b : ℕ) (hab : a ≠ b) (haR : a ∉ R) (hbR : b ∉ R)
    (N : ℕ → ℕ → ℝ)
    (hHyp : ∀ u w : ℕ → ℝ, 0 < stForm (insert a (insert b R)) N u u →
      stForm (insert a (insert b R)) N u u * stForm (insert a (insert b R)) N w w ≤
        stForm (insert a (insert b R)) N u w ^ 2)
    (u0 : ℝ) (hu0 : 0 < u0) (ma mb h : ℕ → ℝ) (hNaa : N a a = 0) (hNbb : N b b = 0)
    (hNab : N a b = u0) (hNba : N b a = u0) (hNa : ∀ i ∈ R, N a i = mb i ∧ N i a = mb i)
    (hNb : ∀ i ∈ R, N b i = ma i ∧ N i b = ma i)
    (hbal : ∑ i ∈ R, (ma i + mb i) * h i = 0) :
    2 * (∑ i ∈ R, h i * ma i) ^ 2 / u0 ≤ -∑ i ∈ R, ∑ k ∈ R, h i * h k * N i k := by
  set X := ∑ i ∈ R, h i * ma i with hX
  set Y := ∑ i ∈ R, h i * mb i with hY
  set Q := ∑ i ∈ R, ∑ k ∈ R, h i * h k * N i k with hQ
  have hXY : X + Y = 0 := by
    rw [hX, hY, ← Finset.sum_add_distrib, ← hbal]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hba : b ≠ a := Ne.symm hab
  have hxa : ∀ x ∈ R, x ≠ a := fun x hx h => haR (h ▸ hx)
  have hxb : ∀ x ∈ R, x ≠ b := fun x hx h => hbR (h ▸ hx)
  set lam := -X / u0 with hlam
  let e : ℕ → ℝ := fun x => if x = a ∨ x = b then 1 else 0
  let w : ℕ → ℝ := fun x => if x = a then lam else if x = b then -lam else h x
  have hea : e a = 1 := by simp [e]
  have heb : e b = 1 := by simp [e]
  have heR : ∀ x ∈ R, e x = 0 := fun x hx => by simp [e, hxa x hx, hxb x hx]
  have hwa : w a = lam := by simp [w]
  have hwb : w b = -lam := by simp [w, hba]
  have hwR : ∀ x ∈ R, w x = h x := fun x hx => by simp [w, hxa x hx, hxb x hx]
  have hexp := stForm_expand R a b hab haR hbR N
  have hee : stForm (insert a (insert b R)) N e e = 2 * u0 := by
    rw [hexp]
    have s1 : ∑ y ∈ R, e a * N a y * e y = 0 :=
      Finset.sum_eq_zero fun y hy => by rw [heR y hy]; ring
    have s2 : ∑ y ∈ R, e b * N b y * e y = 0 :=
      Finset.sum_eq_zero fun y hy => by rw [heR y hy]; ring
    have s3 : ∑ x ∈ R, e x * N x a * e a = 0 :=
      Finset.sum_eq_zero fun y hy => by rw [heR y hy]; ring
    have s4 : ∑ x ∈ R, e x * N x b * e b = 0 :=
      Finset.sum_eq_zero fun y hy => by rw [heR y hy]; ring
    have s5 : ∑ x ∈ R, ∑ y ∈ R, e x * N x y * e y = 0 :=
      Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => by rw [heR y hy]; ring
    rw [s1, s2, s3, s4, s5, hea, heb, hNaa, hNbb, hNab, hNba]; ring
  have hew : stForm (insert a (insert b R)) N e w = 0 := by
    rw [hexp]
    have s1 : ∑ y ∈ R, e a * N a y * w y = Y :=
      Finset.sum_congr rfl fun y hy => by rw [hea, (hNa y hy).1, hwR y hy]; ring
    have s2 : ∑ y ∈ R, e b * N b y * w y = X :=
      Finset.sum_congr rfl fun y hy => by rw [heb, (hNb y hy).1, hwR y hy]; ring
    have s3 : ∑ x ∈ R, e x * N x a * w a = 0 :=
      Finset.sum_eq_zero fun y hy => by rw [heR y hy]; ring
    have s4 : ∑ x ∈ R, e x * N x b * w b = 0 :=
      Finset.sum_eq_zero fun y hy => by rw [heR y hy]; ring
    have s5 : ∑ x ∈ R, ∑ y ∈ R, e x * N x y * w y = 0 :=
      Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => by rw [heR x hx]; ring
    rw [s1, s2, s3, s4, s5, hea, heb, hwa, hwb, hNaa, hNbb, hNab, hNba]; linarith
  have hww : stForm (insert a (insert b R)) N w w = -2 * u0 * lam ^ 2 + 2 * lam * Y -
      2 * lam * X + Q := by
    rw [hexp]
    have s1 : ∑ y ∈ R, w a * N a y * w y = lam * Y := by
      rw [hY, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y hy => by rw [hwa, (hNa y hy).1, hwR y hy]; ring
    have s2 : ∑ y ∈ R, w b * N b y * w y = -lam * X := by
      rw [hX, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y hy => by rw [hwb, (hNb y hy).1, hwR y hy]; ring
    have s3 : ∑ x ∈ R, w x * N x a * w a = lam * Y := by
      rw [hY, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y hy => by rw [hwa, (hNa y hy).2, hwR y hy]; ring
    have s4 : ∑ x ∈ R, w x * N x b * w b = -lam * X := by
      rw [hX, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y hy => by rw [hwb, (hNb y hy).2, hwR y hy]; ring
    have s5 : ∑ x ∈ R, ∑ y ∈ R, w x * N x y * w y = Q :=
      Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by
        rw [hwR x hx, hwR y hy]; ring
    rw [s1, s2, s3, s4, s5, hwa, hwb, hNaa, hNbb, hNab, hNba]; ring
  have hpos : 0 < stForm (insert a (insert b R)) N e e := by rw [hee]; positivity
  have key := hHyp e w hpos
  rw [hee, hew, hww] at key
  have hle : -2 * u0 * lam ^ 2 + 2 * lam * Y - 2 * lam * X + Q ≤ 0 := by nlinarith
  have hYX : Y = -X := by linarith
  rw [hYX, hlam] at hle
  have : -2 * u0 * (-X / u0) ^ 2 + 2 * (-X / u0) * -X - 2 * (-X / u0) * X =
      2 * X ^ 2 / u0 := by field_simp; ring
  linarith



/-- INTERNAL: `Hyp` of an omission matrix, read through `stForm`. -/
theorem hyp_omitMat_stForm {f : Finset ℕ → ℝ} {F D : Finset ℕ} {L : List ℕ}
    (hH : Hyp (omitMat f F D L)) (u w : ℕ → ℝ)
    (hu : 0 < stForm D (fun x y => if x = y then 0 else
        chSum L (fun c => f (((F ∪ D ∪ c).erase x).erase y))) u u) :
    stForm D (fun x y => if x = y then 0 else
        chSum L (fun c => f (((F ∪ D ∪ c).erase x).erase y))) u u *
      stForm D (fun x y => if x = y then 0 else
        chSum L (fun c => f (((F ∪ D ∪ c).erase x).erase y))) w w ≤
      stForm D (fun x y => if x = y then 0 else
        chSum L (fun c => f (((F ∪ D ∪ c).erase x).erase y))) u w ^ 2 := by
  have hrw : ∀ u w : ℕ → ℝ, qf (omitMat f F D L) (fun x => u x) (fun x => w x) =
      stForm D (fun x y => if x = y then 0 else
        chSum L (fun c => f (((F ∪ D ∪ c).erase x).erase y))) u w := by
    intro u w
    unfold qf stForm omitMat
    rw [← Finset.sum_coe_sort D]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_coe_sort D]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Subtype.ext_iff]
  have := hH (fun x => u x) (fun x => w x) (by rw [hrw]; exact hu)
  simpa only [hrw] using this


/-- INTERNAL: `eq:transport-schur` at a node, from the omission signature of the matrix `N`
on the display plus the next pair.
TEXLINE: sections/transport.tex:224-269 -/
theorem st_schur_node (f : Finset ℕ → ℝ) (F R : Finset ℕ) (t : ℕ) (L : List ℕ)
    (hf : ∀ S, 0 < f S) (hL : (t :: L).Nodup)
    (hRL : ∀ s ∈ t :: L, 2 * s ∉ R ∧ 2 * s + 1 ∉ R)
    (hFL : ∀ s ∈ t :: L, 2 * s ∉ F ∧ 2 * s + 1 ∉ F)
    (hsig : SlotSig f F R (t :: L)) (h : ℕ → ℝ)
    (hbal : ∑ i ∈ R, slotM f F R (t :: L) i * h i = 0) :
    2 * (∑ i ∈ R, h i * slotM f F (insert (2 * t) R) L i) ^ 2 /
        chSum L (fun c => f (F ∪ R ∪ c)) ≤ -slotQ f F R (t :: L) t h := by
  obtain ⟨htL, hL'⟩ := List.nodup_cons.1 hL
  obtain ⟨haR, hbR⟩ := hRL t (List.mem_cons_self ..)
  obtain ⟨haF, hbF⟩ := hFL t (List.mem_cons_self ..)
  have hab : 2 * t ≠ 2 * t + 1 := by omega
  have hc : ∀ c, IsChoice L c → 2 * t ∉ c ∧ 2 * t + 1 ∉ c := fun c hc =>
    st_notMem_choice hc htL
  have hbaR : 2 * t ∉ insert (2 * t + 1) R := by simp [haR]
  have hbaR' : 2 * t + 1 ∉ insert (2 * t) R := by simp [hbR]
  have hH : Hyp (omitMat f F (insert (2 * t) (insert (2 * t + 1) R)) L) := by
    refine hsig _ L hL' (fun s hs => List.mem_cons_of_mem _ hs) ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_insert] at he
      rcases he with rfl | rfl | he
      · exact Or.inr ⟨t, List.mem_cons_self .., Or.inl rfl⟩
      · exact Or.inr ⟨t, List.mem_cons_self .., Or.inr rfl⟩
      · exact Or.inl he
    · intro s hs
      have hst : s ≠ t := fun he => htL (he ▸ hs)
      obtain ⟨h1, h2⟩ := hRL s (List.mem_cons_of_mem _ hs)
      simp only [Finset.mem_insert, not_or]
      refine ⟨⟨?_, ?_, h1⟩, ?_, ?_, h2⟩ <;> omega
    · rw [Finset.card_insert_of_notMem hbaR, Finset.card_insert_of_notMem hbR]
      simp; omega
  have hN : ∀ x y, slotV f F R (t :: L) t x y = (fun x y => if x = y then 0 else
      chSum L (fun c => f (((F ∪ insert (2 * t) (insert (2 * t + 1) R) ∪ c).erase x).erase y)))
      x y := by
    intro x y; simp [slotV]
  have hA : ∀ c, IsChoice L c →
      (F ∪ insert (2 * t) (insert (2 * t + 1) R) ∪ c).erase (2 * t) =
        F ∪ insert (2 * t + 1) R ∪ c := fun c hc' => st_erase_new haF hbaR (hc c hc').1
  have hB : ∀ c, IsChoice L c →
      (F ∪ insert (2 * t) (insert (2 * t + 1) R) ∪ c).erase (2 * t + 1) =
        F ∪ insert (2 * t) R ∪ c := fun c hc' => by
    rw [Finset.insert_comm]; exact st_erase_new hbF hbaR' (hc c hc').2
  have hAB : ∀ c, IsChoice L c →
      ((F ∪ insert (2 * t) (insert (2 * t + 1) R) ∪ c).erase (2 * t)).erase (2 * t + 1) =
        F ∪ R ∪ c := fun c hc' => by
    rw [hA c hc']; exact st_erase_new hbF hbR (hc c hc').2
  have key := st_schur_core R (2 * t) (2 * t + 1) hab haR hbR _
    (hyp_omitMat_stForm hH) (chSum L (fun c => f (F ∪ R ∪ c)))
    (chSum_pos hL' fun c _ => hf _)
    (slotM f F (insert (2 * t) R) L) (slotM f F (insert (2 * t + 1) R) L) h
    (by simp) (by simp)
    (by
      rw [if_neg hab]
      exact chSum_congr hL' fun c hc' => by rw [hAB c hc'])
    (by
      rw [if_neg (Ne.symm hab)]
      exact chSum_congr hL' fun c hc' => by rw [Finset.erase_right_comm, hAB c hc'])
    (fun i hi => by
      have hia : i ≠ 2 * t := fun he => haR (he ▸ hi)
      refine ⟨?_, ?_⟩
      · rw [if_neg (Ne.symm hia)]
        exact chSum_congr hL' fun c hc' => by rw [hA c hc']
      · rw [if_neg hia]
        exact chSum_congr hL' fun c hc' => by rw [Finset.erase_right_comm, hA c hc'])
    (fun i hi => by
      have hib : i ≠ 2 * t + 1 := fun he => hbR (he ▸ hi)
      refine ⟨?_, ?_⟩
      · rw [if_neg (Ne.symm hib)]
        exact chSum_congr hL' fun c hc' => by rw [hB c hc']
      · rw [if_neg hib]
        exact chSum_congr hL' fun c hc' => by rw [Finset.erase_right_comm, hB c hc'])
    (by
      rw [← hbal]
      exact Finset.sum_congr rfl fun i _ => by rw [st_split_M])
  refine key.trans (le_of_eq ?_)
  unfold slotQ
  simp only [hN]


/-- INTERNAL: two-term Cauchy–Schwarz `(x + y)² ≤ (B₁ + B₂)(D₁ + D₂)`. -/
theorem st_two_cs {x y B1 B2 D1 D2 : ℝ} (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (hD1 : 0 ≤ D1)
    (hD2 : 0 ≤ D2) (h1 : x ^ 2 ≤ B1 * D1) (h2 : y ^ 2 ≤ B2 * D2) :
    (x + y) ^ 2 ≤ (B1 + B2) * (D1 + D2) := by
  have hP : 0 ≤ B1 * D2 := mul_nonneg hB1 hD2
  have hQ : 0 ≤ B2 * D1 := mul_nonneg hB2 hD1
  have hxy : (x * y) ^ 2 ≤ (B1 * D2) * (B2 * D1) := by
    calc (x * y) ^ 2 = x ^ 2 * y ^ 2 := by ring
      _ ≤ (B1 * D1) * (B2 * D2) := mul_le_mul h1 h2 (sq_nonneg _) (mul_nonneg hB1 hD1)
      _ = _ := by ring
  have hsq : (2 * x * y) ^ 2 ≤ (B1 * D2 + B2 * D1) ^ 2 := by
    nlinarith [sq_nonneg (B1 * D2 - B2 * D1)]
  have := (abs_le_of_sq_le_sq' hsq (add_nonneg hP hQ)).2
  nlinarith

/-- INTERNAL: the leaf (clique) routing bound through a hub maximizing `W_i m_i`.
TEXLINE: sections/transport.tex:159-178 -/
theorem st_hub (R : Finset ℕ) (m W h g : ℕ → ℝ) (hm : ∀ i ∈ R, 0 < m i)
    (hW : ∀ i ∈ R, 0 < W i) (hbal : ∑ i ∈ R, m i * h i = 0) :
    (∑ i ∈ R, h i * (m i * g i)) ^ 2 ≤ (∑ i ∈ R, m i * h i ^ 2 / W i) *
      ((∑ i ∈ R, ∑ k ∈ R, if i = k then 0 else
          min (W i * m i) (W k * m k) * (g i - g k) ^ 2) / 2) := by
  rcases R.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨j, hj, hjmax⟩ := R.exists_max_image (fun i => W i * m i) hne
  set T : ℕ → ℕ → ℝ := fun i k =>
    if i = k then 0 else min (W i * m i) (W k * m k) * (g i - g k) ^ 2 with hTdef
  have hT0 : ∀ i ∈ R, ∀ k ∈ R, 0 ≤ T i k := by
    intro i hi k hk
    simp only [hTdef]
    split_ifs
    · exact le_rfl
    · have := hm i hi; have := hW i hi; have := hm k hk; have := hW k hk
      exact mul_nonneg (le_min (by positivity) (by positivity)) (sq_nonneg _)
  have hTsym : ∀ i k, T i k = T k i := by
    intro i k
    simp only [hTdef]
    by_cases hik : i = k
    · subst hik; rfl
    · rw [if_neg hik, if_neg (Ne.symm hik), min_comm]; ring
  have hΦ : ∑ i ∈ R, h i * (m i * g i) = ∑ i ∈ R, (m i * h i) * (g i - g j) := by
    have : ∑ i ∈ R, (m i * h i) * (g i - g j) =
        ∑ i ∈ R, h i * (m i * g i) - (∑ i ∈ R, m i * h i) * g j := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hbal]; ring
  have hcs : (∑ i ∈ R, (m i * h i) * (g i - g j)) ^ 2 ≤
      (∑ i ∈ R, m i * h i ^ 2 / W i) * ∑ i ∈ R, W i * m i * (g i - g j) ^ 2 := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul R (fun i hi => ?_) (fun i hi => ?_)
      (fun i hi => le_of_eq ?_)
    · have := hm i hi; have := hW i hi; positivity
    · have := hm i hi; have := hW i hi; positivity
    · have := hm i hi; have := hW i hi; field_simp
  have hle1 : ∑ i ∈ R, W i * m i * (g i - g j) ^ 2 ≤ ∑ i ∈ R, T i j := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases hij : i = j
    · subst hij; simp [hTdef]
    · simp only [hTdef, if_neg hij]
      rw [min_eq_left (hjmax i hi)]
  have hle2 : ∑ i ∈ R, T i j ≤ (∑ i ∈ R, ∑ k ∈ R, T i k) / 2 := by
    have hTjj : T j j = 0 := by simp [hTdef]
    have e1 : ∑ i ∈ R, T i j = ∑ i ∈ R.erase j, T i j := by
      rw [← Finset.add_sum_erase R _ hj, hTjj, zero_add]
    have e2 : ∑ i ∈ R, ∑ k ∈ R, T i k = ∑ k ∈ R, T j k + ∑ i ∈ R.erase j, ∑ k ∈ R, T i k := by
      rw [← Finset.add_sum_erase R _ hj]
    have e3 : ∑ k ∈ R, T j k = ∑ i ∈ R, T i j := Finset.sum_congr rfl fun k _ => hTsym j k
    have e4 : ∑ i ∈ R.erase j, T i j ≤ ∑ i ∈ R.erase j, ∑ k ∈ R, T i k :=
      Finset.sum_le_sum fun i hi => Finset.single_le_sum
        (fun k hk => hT0 i (Finset.mem_of_mem_erase hi) k hk) hj
    rw [e2, e3]; linarith
  have hB0 : 0 ≤ ∑ i ∈ R, m i * h i ^ 2 / W i :=
    Finset.sum_nonneg fun i hi => by have := hm i hi; have := hW i hi; positivity
  rw [hΦ]
  calc _ ≤ _ := hcs
    _ ≤ _ := mul_le_mul_of_nonneg_left (hle1.trans hle2) hB0


/-- INTERNAL: the recursion over the conditioning tree: at every node with a balanced
coefficient vector, `Φ² ≤ B · D` and `0 ≤ B`.
TEXLINE: sections/transport.tex:180-307 -/
theorem st_node (f g : Finset ℕ → ℝ) (W : ℕ → ℝ) (F : Finset ℕ) (hf : ∀ S, 0 < f S) :
    ∀ (L : List ℕ) (R : Finset ℕ) (h : ℕ → ℝ), L.Nodup →
      (∀ t ∈ L, 2 * t ∉ R ∧ 2 * t + 1 ∉ R) → (∀ t ∈ L, 2 * t ∉ F ∧ 2 * t + 1 ∉ F) →
      (∀ i ∈ R, 0 < W i) → (∀ t ∈ L, 0 < W (2 * t) ∧ W (2 * t + 1) = W (2 * t)) →
      SlotSig f F R L → ∑ i ∈ R, slotM f F R L i * h i = 0 →
      0 ≤ slotB f W F R L h ∧ slotPhi f g F R L h ^ 2 ≤ slotB f W F R L h * slotD f g W F R L := by
  intro L
  induction L with
  | nil =>
    intro R h _ _ _ hRW _ _ hbal
    have hM : ∀ i, slotM f F R [] i = f ((F ∪ R).erase i) := fun i => by simp [slotM, chSum_nil]
    have hB : slotB f W F R [] h = ∑ i ∈ R, f ((F ∪ R).erase i) * h i ^ 2 / W i := by
      simp [slotB, hM]
    have hP : slotPhi f g F R [] h =
        ∑ i ∈ R, h i * (f ((F ∪ R).erase i) * g ((F ∪ R).erase i)) := by
      simp [slotPhi, chSum_nil]
    have hD : slotD f g W F R [] = cliqueEnergy f g W F R := by simp [slotD, chSum_nil]
    rw [hB, hP, hD]
    refine ⟨Finset.sum_nonneg fun i hi => ?_, ?_⟩
    · have := hRW i hi; have := hf ((F ∪ R).erase i); positivity
    · simp only [hM] at hbal
      exact st_hub R (fun i => f ((F ∪ R).erase i)) W h (fun i => g ((F ∪ R).erase i))
        (fun i _ => hf _) hRW hbal
  | cons t L ih =>
    intro R h hL hRL hFL hRW hWL hsig hbal
    obtain ⟨htL, hL'⟩ := List.nodup_cons.1 hL
    obtain ⟨haR, hbR⟩ := hRL t (List.mem_cons_self ..)
    obtain ⟨haF, hbF⟩ := hFL t (List.mem_cons_self ..)
    obtain ⟨hWa, hWb⟩ := hWL t (List.mem_cons_self ..)
    have hc : ∀ c, IsChoice L c → 2 * t ∉ c ∧ 2 * t + 1 ∉ c := fun c hc =>
      st_notMem_choice hc htL
    set u := chSum L (fun c => f (F ∪ R ∪ c)) with hu
    have hupos : 0 < u := chSum_pos hL' fun c _ => hf _
    set X := ∑ i ∈ R, h i * slotM f F (insert (2 * t) R) L i with hX
    have hMa : slotM f F (insert (2 * t) R) L (2 * t) = u :=
      st_newhole f F R L hL' _ haF haR fun c h' => (hc c h').1
    have hMb : slotM f F (insert (2 * t + 1) R) L (2 * t + 1) = u :=
      st_newhole f F R L hL' _ hbF hbR fun c h' => (hc c h').2
    have hRa : ∀ i ∈ R, i ≠ 2 * t := fun i hi he => haR (he ▸ hi)
    have hRb : ∀ i ∈ R, i ≠ 2 * t + 1 := fun i hi he => hbR (he ▸ hi)
    -- hypotheses at the two children
    have hRLx : ∀ x, x = 2 * t ∨ x = 2 * t + 1 →
        ∀ s ∈ L, 2 * s ∉ insert x R ∧ 2 * s + 1 ∉ insert x R := by
      intro x hx s hs
      have hst : s ≠ t := fun he => htL (he ▸ hs)
      obtain ⟨h1, h2⟩ := hRL s (List.mem_cons_of_mem _ hs)
      simp only [Finset.mem_insert, not_or]
      refine ⟨⟨?_, h1⟩, ?_, h2⟩ <;> omega
    have hFL' : ∀ s ∈ L, 2 * s ∉ F ∧ 2 * s + 1 ∉ F := fun s hs =>
      hFL s (List.mem_cons_of_mem _ hs)
    have hWL' : ∀ s ∈ L, 0 < W (2 * s) ∧ W (2 * s + 1) = W (2 * s) := fun s hs =>
      hWL s (List.mem_cons_of_mem _ hs)
    have hRWx : ∀ x, x = 2 * t ∨ x = 2 * t + 1 → ∀ i ∈ insert x R, 0 < W i := by
      intro x hx i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rcases hx with rfl | rfl
        · exact hWa
        · rw [hWb]; exact hWa
      · exact hRW i hi
    have hsigx : ∀ x, x = 2 * t ∨ x = 2 * t + 1 → SlotSig f F (insert x R) L := by
      intro x hx D L₀ hL₀ hL₀L hD hL₀D hcard
      refine hsig D L₀ hL₀ (fun s hs => List.mem_cons_of_mem _ (hL₀L s hs)) ?_ hL₀D ?_
      · intro e he
        rcases hD e he with he | ⟨s, hs, hes⟩
        · rcases Finset.mem_insert.1 he with rfl | he
          · exact Or.inr ⟨t, List.mem_cons_self .., hx⟩
          · exact Or.inl he
        · exact Or.inr ⟨s, List.mem_cons_of_mem _ hs, hes⟩
      · have hxR : x ∉ R := by rcases hx with rfl | rfl <;> assumption
        rw [Finset.card_insert_of_notMem hxR] at hcard
        simp only [List.length_cons]; omega
    have hsplitM : ∀ i, slotM f F R (t :: L) i =
        slotM f F (insert (2 * t) R) L i + slotM f F (insert (2 * t + 1) R) L i :=
      st_split_M f F R t L
    have hbala : ∑ i ∈ insert (2 * t) R, slotM f F (insert (2 * t) R) L i *
        (fun i => if i = 2 * t then -(X / u) else h i) i = 0 := by
      rw [Finset.sum_insert haR]
      beta_reduce
      rw [if_pos rfl, hMa]
      have : ∑ i ∈ R, slotM f F (insert (2 * t) R) L i * (if i = 2 * t then -(X / u) else h i) =
          X := by
        rw [hX]; exact Finset.sum_congr rfl fun i hi => by rw [if_neg (hRa i hi)]; ring
      rw [this]; field_simp; ring
    have hbalb : ∑ i ∈ insert (2 * t + 1) R, slotM f F (insert (2 * t + 1) R) L i *
        (fun i => if i = 2 * t + 1 then X / u else h i) i = 0 := by
      rw [Finset.sum_insert hbR]
      beta_reduce
      rw [if_pos rfl, hMb]
      have : ∑ i ∈ R, slotM f F (insert (2 * t + 1) R) L i *
          (if i = 2 * t + 1 then X / u else h i) = -X := by
        have e1 : ∑ i ∈ R, slotM f F (insert (2 * t + 1) R) L i *
            (if i = 2 * t + 1 then X / u else h i) =
            ∑ i ∈ R, slotM f F R (t :: L) i * h i - X := by
          rw [hX, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i hi => by rw [if_neg (hRb i hi), hsplitM]; ring
        rw [e1, hbal]; ring
      rw [this]; field_simp; ring
    obtain ⟨hBa, hca⟩ := ih (insert (2 * t) R) _ hL' (hRLx _ (Or.inl rfl)) hFL'
      (hRWx _ (Or.inl rfl)) hWL' (hsigx _ (Or.inl rfl)) hbala
    obtain ⟨hBb, hcb⟩ := ih (insert (2 * t + 1) R) _ hL' (hRLx _ (Or.inr rfl)) hFL'
      (hRWx _ (Or.inr rfl)) hWL' (hsigx _ (Or.inr rfl)) hbalb
    have hDa := st_slotD_nonneg f g W F (insert (2 * t) R) L hf hL' (hRWx _ (Or.inl rfl)) hWL'
    have hDb := st_slotD_nonneg f g W F (insert (2 * t + 1) R) L hf hL'
      (hRWx _ (Or.inr rfl)) hWL'
    have hsch := st_schur_node f F R t L hf hL hRL hFL hsig h hbal
    rw [← hu, ← hX] at hsch
    -- the potential bound
    have hBle : slotB f W F (insert (2 * t) R) L (fun i => if i = 2 * t then -(X / u) else h i) +
        slotB f W F (insert (2 * t + 1) R) L (fun i => if i = 2 * t + 1 then X / u else h i) ≤
        slotB f W F R (t :: L) h := by
      unfold slotB
      rw [Finset.sum_insert haR, Finset.sum_insert hbR, List.toFinset_cons,
        Finset.sum_insert (by simpa using htL)]
      beta_reduce
      rw [if_pos rfl, if_pos rfl, hMa, hMb, hWb]
      have s1 : ∑ i ∈ R, slotM f F (insert (2 * t) R) L i *
          (if i = 2 * t then -(X / u) else h i) ^ 2 / W i =
          ∑ i ∈ R, slotM f F (insert (2 * t) R) L i * h i ^ 2 / W i :=
        Finset.sum_congr rfl fun i hi => by rw [if_neg (hRa i hi)]
      have s2 : ∑ i ∈ R, slotM f F (insert (2 * t + 1) R) L i *
          (if i = 2 * t + 1 then X / u else h i) ^ 2 / W i =
          ∑ i ∈ R, slotM f F (insert (2 * t + 1) R) L i * h i ^ 2 / W i :=
        Finset.sum_congr rfl fun i hi => by rw [if_neg (hRb i hi)]
      have s3 : ∑ i ∈ R, slotM f F R (t :: L) i * h i ^ 2 / W i =
          ∑ i ∈ R, slotM f F (insert (2 * t) R) L i * h i ^ 2 / W i +
            ∑ i ∈ R, slotM f F (insert (2 * t + 1) R) L i * h i ^ 2 / W i := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [hsplitM]; ring
      have s4 : ∑ s ∈ L.toFinset, -slotQ f F (insert (2 * t) R) L s
            (fun i => if i = 2 * t then -(X / u) else h i) / W (2 * s) +
          ∑ s ∈ L.toFinset, -slotQ f F (insert (2 * t + 1) R) L s
            (fun i => if i = 2 * t + 1 then X / u else h i) / W (2 * s) =
          ∑ s ∈ L.toFinset, -slotQ f F R (t :: L) s h / W (2 * s) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [← st_split_Q f F R t L hL' htL haF hbF haR hbR h (X / u) s
          (List.mem_toFinset.1 hs)]
        ring
      rw [s1, s2, s3]
      have hq : 2 * (u * (X / u) ^ 2 / W (2 * t)) ≤ -slotQ f F R (t :: L) t h / W (2 * t) := by
        have : 2 * (u * (X / u) ^ 2 / W (2 * t)) = 2 * X ^ 2 / u / W (2 * t) := by
          field_simp
        rw [this]
        exact div_le_div_of_nonneg_right hsch hWa.le
      have hneg : (-(X / u)) ^ 2 = (X / u) ^ 2 := by ring
      rw [hneg]
      linarith [s4]
    refine ⟨by linarith, ?_⟩
    rw [st_split_Phi f g F R t L hL' htL haF hbF haR hbR h (X / u), st_split_D]
    calc _ ≤ _ := st_two_cs hBa hBb hDa hDb hca hcb
      _ ≤ _ := mul_le_mul_of_nonneg_right hBle (add_nonneg hDa hDb)

/-- **One-hole transport** (`lem:transport`, `eq:slot-transport`): with singleton slots
`{x0}`, `{x1}` and ordinary slots the pairs of `L`,
`(ḡ0 - ḡ1)² ≤ (1/(s0 W_{x0}) + 1/(s1 W_{x1}) + 2/(s0 s1) Σ_t v_t / W_t) · D_sl(g)`.
PAPER: sections/transport.tex:99-129 -/
theorem slot_transport (f g : Finset ℕ → ℝ) (W : ℕ → ℝ) (F : Finset ℕ) (x0 x1 : ℕ)
    (L : List ℕ) (hf : ∀ S, 0 < f S) (hx : x0 ≠ x1) (hx0F : x0 ∉ F) (hx1F : x1 ∉ F)
    (hL : L.Nodup) (hLF : ∀ t ∈ L, 2 * t ∉ F ∧ 2 * t + 1 ∉ F)
    (hLx : ∀ t ∈ L, 2 * t ≠ x0 ∧ 2 * t ≠ x1 ∧ 2 * t + 1 ≠ x0 ∧ 2 * t + 1 ≠ x1)
    (hW0 : 0 < W x0) (hW1 : 0 < W x1)
    (hWL : ∀ t ∈ L, 0 < W (2 * t) ∧ W (2 * t + 1) = W (2 * t))
    (hsig : ∀ (D : Finset ℕ) (L' : List ℕ), L'.Nodup → (∀ t ∈ L', t ∈ L) →
      (∀ e ∈ D, e = x0 ∨ e = x1 ∨ ∃ t ∈ L, e = 2 * t ∨ e = 2 * t + 1) →
      (∀ t ∈ L', 2 * t ∉ D ∧ 2 * t + 1 ∉ D) →
      D.card + L'.length = L.length + 3 → Hyp (omitMat f F D L')) :
    (chSum L (fun c => f (insert x1 (F ∪ c)) * g (insert x1 (F ∪ c))) /
          chSum L (fun c => f (insert x1 (F ∪ c))) -
        chSum L (fun c => f (insert x0 (F ∪ c)) * g (insert x0 (F ∪ c))) /
          chSum L (fun c => f (insert x0 (F ∪ c)))) ^ 2 ≤
      (1 / (chSum L (fun c => f (insert x1 (F ∪ c))) * W x0) +
          1 / (chSum L (fun c => f (insert x0 (F ∪ c))) * W x1) +
          2 / (chSum L (fun c => f (insert x1 (F ∪ c))) *
              chSum L (fun c => f (insert x0 (F ∪ c)))) *
            ∑ t ∈ L.toFinset,
              chSum (L.erase t) (fun c => f (insert (2 * t) (insert (2 * t + 1) (F ∪ c)))) /
                W (2 * t)) *
        chSum L (fun c => cliqueEnergy f g W F (insert x0 (insert x1 c))) := by
  set A := chSum L (fun c => f (insert x1 (F ∪ c))) with hA
  set B := chSum L (fun c => f (insert x0 (F ∪ c))) with hB
  have hApos : 0 < A := chSum_pos hL fun c _ => hf _
  have hBpos : 0 < B := chSum_pos hL fun c _ => hf _
  set R0 : Finset ℕ := insert x0 {x1} with hR0
  have hx0R : x0 ∉ ({x1} : Finset ℕ) := by simpa using hx
  -- choice sets of sublists of `L` avoid the singleton slots
  have hcx : ∀ L₀ : List ℕ, (∀ t ∈ L₀, t ∈ L) → ∀ c, IsChoice L₀ c → x0 ∉ c ∧ x1 ∉ c := by
    intro L₀ hL₀ c hc
    have key : ∀ e ∈ c, e ≠ x0 ∧ e ≠ x1 := by
      intro e he
      have ht := hL₀ _ (hc.1 e he)
      obtain ⟨h1, h2, h3, h4⟩ := hLx _ ht
      rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
      · rw [show 2 * k / 2 = k by omega] at h1 h2; exact ⟨h1, h2⟩
      · rw [show (2 * k + 1) / 2 = k by omega] at h3 h4; exact ⟨h3, h4⟩
    exact ⟨fun h => (key _ h).1 rfl, fun h => (key _ h).2 rfl⟩
  have hcxL := hcx L fun t ht => ht
  have hset0 : ∀ c, x0 ∉ c → x1 ∉ c → (F ∪ R0 ∪ c).erase x0 = insert x1 (F ∪ c) := by
    intro c h0 h1
    rw [show F ∪ R0 ∪ c = insert x0 (insert x1 (F ∪ c)) by
      ext y; simp only [hR0, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto]
    exact Finset.erase_insert (by simp [hx, hx0F, h0])
  have hset1 : ∀ c, x0 ∉ c → x1 ∉ c → (F ∪ R0 ∪ c).erase x1 = insert x0 (F ∪ c) := by
    intro c h0 h1
    rw [show F ∪ R0 ∪ c = insert x1 (insert x0 (F ∪ c)) by
      ext y; simp only [hR0, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto]
    exact Finset.erase_insert (by simp [Ne.symm hx, hx1F, h1])
  have hM0 : slotM f F R0 L x0 = A :=
    chSum_congr hL fun c hc => by rw [hset0 c (hcxL c hc).1 (hcxL c hc).2]
  have hM1 : slotM f F R0 L x1 = B :=
    chSum_congr hL fun c hc => by rw [hset1 c (hcxL c hc).1 (hcxL c hc).2]
  set h0 : ℕ → ℝ := fun i => if i = x0 then 1 / A else if i = x1 then -(1 / B) else 0
    with hh0
  have hh00 : h0 x0 = 1 / A := by simp [hh0]
  have hh01 : h0 x1 = -(1 / B) := by simp [hh0, Ne.symm hx]
  have hsumR0 : ∀ φ : ℕ → ℝ, ∑ i ∈ R0, φ i = φ x0 + φ x1 := fun φ => by
    rw [hR0, Finset.sum_insert hx0R, Finset.sum_singleton]
  have hbal : ∑ i ∈ R0, slotM f F R0 L i * h0 i = 0 := by
    rw [hsumR0, hM0, hM1, hh00, hh01]; field_simp; ring
  have hRL : ∀ t ∈ L, 2 * t ∉ R0 ∧ 2 * t + 1 ∉ R0 := by
    intro t ht
    obtain ⟨h1, h2, h3, h4⟩ := hLx t ht
    simp [hR0, h1, h2, h3, h4]
  have hRW : ∀ i ∈ R0, 0 < W i := by
    intro i hi
    simp only [hR0, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hW0
    · exact hW1
  have hsig0 : SlotSig f F R0 L := by
    intro D L₀ hL₀ hL₀L hD hL₀D hcard
    refine hsig D L₀ hL₀ hL₀L (fun e he => ?_) hL₀D ?_
    · rcases hD e he with he | he
      · simp only [hR0, Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr he)
    · rw [hR0, Finset.card_insert_of_notMem hx0R, Finset.card_singleton] at hcard
      omega
  obtain ⟨-, hmain⟩ := st_node f g W F hf L R0 h0 hL hRL hLF hRW hWL hsig0 hbal
  -- identify the three node quantities at the root
  have hΦ : slotPhi f g F R0 L h0 =
      chSum L (fun c => f (insert x1 (F ∪ c)) * g (insert x1 (F ∪ c))) / A -
        chSum L (fun c => f (insert x0 (F ∪ c)) * g (insert x0 (F ∪ c))) / B := by
    unfold slotPhi
    rw [hsumR0, hh00, hh01]
    have e0 : chSum L (fun c => f ((F ∪ R0 ∪ c).erase x0) * g ((F ∪ R0 ∪ c).erase x0)) =
        chSum L (fun c => f (insert x1 (F ∪ c)) * g (insert x1 (F ∪ c))) :=
      chSum_congr hL fun c hc => by rw [hset0 c (hcxL c hc).1 (hcxL c hc).2]
    have e1 : chSum L (fun c => f ((F ∪ R0 ∪ c).erase x1) * g ((F ∪ R0 ∪ c).erase x1)) =
        chSum L (fun c => f (insert x0 (F ∪ c)) * g (insert x0 (F ∪ c))) :=
      chSum_congr hL fun c hc => by rw [hset1 c (hcxL c hc).1 (hcxL c hc).2]
    rw [e0, e1]; ring
  have hD : slotD f g W F R0 L = chSum L (fun c => cliqueEnergy f g W F (insert x0 (insert x1 c))) := by
    unfold slotD
    have e : ∀ c, R0 ∪ c = insert x0 (insert x1 c) := fun c => by
      ext y; simp only [hR0, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    simp only [e]
  have hV : ∀ t ∈ L, slotV f F R0 L t x0 x1 =
      chSum (L.erase t) (fun c => f (insert (2 * t) (insert (2 * t + 1) (F ∪ c)))) ∧
      slotV f F R0 L t x1 x0 =
      chSum (L.erase t) (fun c => f (insert (2 * t) (insert (2 * t + 1) (F ∪ c)))) := by
    intro t ht
    obtain ⟨h1, h2, h3, h4⟩ := hLx t ht
    have hc := hcx (L.erase t) fun s hs => List.mem_of_mem_erase hs
    have hset : ∀ c, IsChoice (L.erase t) c →
        ((F ∪ insert (2 * t) (insert (2 * t + 1) R0) ∪ c).erase x0).erase x1 =
          insert (2 * t) (insert (2 * t + 1) (F ∪ c)) := by
      intro c hcc
      obtain ⟨hc0, hc1⟩ := hc c hcc
      rw [show F ∪ insert (2 * t) (insert (2 * t + 1) R0) ∪ c =
          insert x0 (insert x1 (insert (2 * t) (insert (2 * t + 1) (F ∪ c)))) by
        ext y; simp only [hR0, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto]
      rw [Finset.erase_insert (by simp [hx, Ne.symm h1, Ne.symm h3, hx0F, hc0]),
        Finset.erase_insert (by simp [Ne.symm h2, Ne.symm h4, hx1F, hc1])]
    have hL' := hL.erase t
    refine ⟨?_, ?_⟩
    · unfold slotV; rw [if_neg hx]
      exact chSum_congr hL' fun c hcc => by rw [hset c hcc]
    · unfold slotV; rw [if_neg (Ne.symm hx)]
      exact chSum_congr hL' fun c hcc => by rw [Finset.erase_right_comm, hset c hcc]
  have hBB : slotB f W F R0 L h0 =
      1 / (A * W x0) + 1 / (B * W x1) +
        2 / (A * B) * ∑ t ∈ L.toFinset,
          chSum (L.erase t) (fun c => f (insert (2 * t) (insert (2 * t + 1) (F ∪ c)))) /
            W (2 * t) := by
    unfold slotB
    rw [hsumR0, hM0, hM1, hh00, hh01, Finset.mul_sum]
    have hs : ∑ t ∈ L.toFinset, -slotQ f F R0 L t h0 / W (2 * t) =
        ∑ t ∈ L.toFinset, 2 / (A * B) *
          (chSum (L.erase t) (fun c => f (insert (2 * t) (insert (2 * t + 1) (F ∪ c)))) /
            W (2 * t)) := by
      refine Finset.sum_congr rfl fun t ht => ?_
      have ht' := List.mem_toFinset.1 ht
      obtain ⟨v1, v2⟩ := hV t ht'
      have hQ : slotQ f F R0 L t h0 = -2 / (A * B) *
          chSum (L.erase t) (fun c => f (insert (2 * t) (insert (2 * t + 1) (F ∪ c)))) := by
        unfold slotQ
        have d0 : ∀ x, slotV f F R0 L t x x = 0 := fun x => by simp [slotV]
        rw [hsumR0, hsumR0, hsumR0, hh00, hh01, v1, v2, d0, d0]
        field_simp; ring
      rw [hQ]; ring
    rw [hs]
    field_simp
  rw [← hΦ, ← hBB, ← hD]
  exact hmain

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-15 · closed · `slot_transport` proved outright by the node recursion `st_node`
-/
