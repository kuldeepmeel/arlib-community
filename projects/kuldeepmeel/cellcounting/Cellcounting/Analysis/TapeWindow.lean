import Cellcounting.Model.Run

/-!
# Fair-tape windows: composing tape laws

INTERNAL infrastructure for `Interface/ProgramModel.lean`. No paper claim is stated here.

The `_tape` lemmas of `ProgramModel.lean` state, for one program piece `f`
started at cursor `c₀`, the joint law of its (viewed) result and the next `n`
unread tape bits (`TapeLaw`).  That form does **not** compose: a piece that
re-read a bit just before its own start cursor would satisfy it, and two such
pieces in sequence would be correlated.  What makes sequencing sound is that a
piece reads only the bits in `[c₀, c₁)` between its start and end cursors
(`Window`).  This file proves:

* `tapeHeads_apply`: `T` fair bits are uniform on subsets of `range T`;
* `tapeHeads_split`: a stopping-time split of a fair tape;
* `window_bind`, `tapeLaw_bind`: windows and tape laws compose along a
  sequential bind; `window_map`, `tapeLaw_map`: deterministic post-processing;
* `window_foldl`: a loop of windowed steps is windowed.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Cellcounting Arlib.Computation

/-- INTERNAL: the mass function of `T` fair bits: uniform on subsets of `range T`. -/
theorem tapeHeads_apply (T : ℕ) (s : Finset ℕ) :
    tapeHeads T s = if s ⊆ Finset.range T then ((2 : ENNReal) ^ T)⁻¹ else 0 := by
  induction T generalizing s with
  | zero =>
    by_cases h : s = ∅ <;> simp [tapeHeads, h]
  | succ T ih =>
    have hfair : ∀ t : Finset ℕ, (ProbRAM.fair.bind fun b => PMF.pure (if b then insert T t else t)) s
        = (if s = insert T t then (2 : ENNReal)⁻¹ else 0) + (if s = t then (2 : ENNReal)⁻¹ else 0) := by
      intro t
      rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
      simp [ProbRAM.fair, PMF.bernoulli_apply, PMF.pure_apply, ENNReal.one_sub_inv_two]
    show (tapeHeads T).bind _ s = _
    rw [PMF.bind_apply]
    simp only [hfair, ih]
    have hpow : ((2 : ENNReal) ^ (T + 1))⁻¹ = ((2 : ENNReal) ^ T)⁻¹ * 2⁻¹ := by
      rw [pow_succ, ENNReal.mul_inv (by simp) (by simp)]
    by_cases hT : T ∈ s
    · rw [tsum_eq_single (s.erase T)]
      · have h1 : s = insert T (s.erase T) := (Finset.insert_erase hT).symm
        have h2 : s ≠ s.erase T := fun h => by
          have := Finset.notMem_erase T s; rw [← h] at this; exact this hT
        have h3 : s.erase T ⊆ Finset.range T ↔ s ⊆ Finset.range (T + 1) := by
          constructor
          · intro h x hx
            by_cases hxT : x = T
            · simp [hxT]
            · have := h (Finset.mem_erase.2 ⟨hxT, hx⟩)
              simp at this ⊢; omega
          · intro h x hx
            have hx' := Finset.mem_erase.1 hx
            have := h hx'.2
            simp at this ⊢; omega
        rw [if_pos h1, if_neg h2, add_zero, hpow]
        by_cases hs : s ⊆ Finset.range (T + 1)
        · rw [if_pos (h3.2 hs), if_pos hs]
        · rw [if_neg (mt h3.1 hs), if_neg hs, zero_mul]
      · intro t ht
        by_cases htT : t ⊆ Finset.range T
        · have hTt : T ∉ t := fun h => by simpa using htT h
          have hne1 : s ≠ insert T t := by
            intro h; apply ht; rw [h, Finset.erase_insert hTt]
          have hne2 : s ≠ t := by intro h; exact hTt (h ▸ hT)
          simp [hne1, hne2]
        · rw [if_neg htT, zero_mul]
    · rw [tsum_eq_single s]
      · have h1 : s ≠ insert T s := fun h => hT (h ▸ Finset.mem_insert_self T s)
        have h3 : s ⊆ Finset.range T ↔ s ⊆ Finset.range (T + 1) := by
          constructor
          · intro h x hx; have := h hx; simp at this ⊢; omega
          · intro h x hx
            have := h hx
            have hxT : x ≠ T := fun e => hT (e ▸ hx)
            simp at this ⊢; omega
        rw [if_neg h1, if_pos rfl, zero_add, hpow]
        by_cases hs : s ⊆ Finset.range (T + 1)
        · rw [if_pos (h3.2 hs), if_pos hs]
        · rw [if_neg (mt h3.1 hs), if_neg hs, zero_mul]
      · intro t ht
        rw [if_neg (Ne.symm ht), add_zero]
        by_cases hst : s = insert T t
        · exact absurd (hst ▸ Finset.mem_insert_self T t) hT
        · rw [if_neg hst, mul_zero]


/-- INTERNAL: two independent fair tapes of length `T`, the product law used by
`tapeHeads_split`. -/
noncomputable def tapeHeads2 (T : ℕ) : PMF (Finset ℕ × Finset ℕ) :=
  (tapeHeads T).bind fun s => (tapeHeads T).map fun t => (s, t)

/-- INTERNAL: the product law is the product of the masses. -/
theorem tapeHeads2_apply (T : ℕ) (p : Finset ℕ × Finset ℕ) :
    tapeHeads2 T p = tapeHeads T p.1 * tapeHeads T p.2 := by
  obtain ⟨s, t⟩ := p
  rw [tapeHeads2, PMF.bind_apply, tsum_eq_single s]
  · congr 1
    rw [PMF.map_apply, tsum_eq_single t]
    · simp
    · intro b hb; simp [Ne.symm hb]
  · intro a ha
    refine mul_eq_zero_of_right _ ?_
    rw [PMF.map_apply]
    simp [Ne.symm ha]

/-- INTERNAL: the first marginal of the product law. -/
theorem tapeHeads2_map_fst (T : ℕ) : (tapeHeads2 T).map Prod.fst = tapeHeads T := by
  rw [tapeHeads2, PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure (tapeHeads T)]
  congr 1; funext s
  rw [PMF.map_comp]
  exact PMF.map_const _ s

/-- INTERNAL: a pushforward of the product law, as an iterated bind. -/
theorem tapeHeads2_map (T : ℕ) {β : Type} (h : Finset ℕ × Finset ℕ → β) :
    (tapeHeads2 T).map h = (tapeHeads T).bind fun s => (tapeHeads T).map fun t => h (s, t) := by
  rw [tapeHeads2, PMF.map_bind]
  congr 1; funext s
  rw [PMF.map_comp]; rfl

/-- INTERNAL: **stopping-time split of a fair tape.**  If `g` reads only the bits
below `c (g s)`, and `F x` reads only the bits at or above `c x`, then running
`F (g s)` on the same tape is the same as running it on an independent tape.
Proved by the involution swapping the two tapes above the stopping position. -/
theorem tapeHeads_split {α β : Type} (T : ℕ) (g : Finset ℕ → α) (c : α → ℕ)
    (hg : ∀ s s', (∀ i, i < c (g s) → (i ∈ s ↔ i ∈ s')) → g s' = g s)
    (F : α → Finset ℕ → β)
    (hF : ∀ s₀ s s', (∀ i, c (g s₀) ≤ i → (i ∈ s ↔ i ∈ s')) → F (g s₀) s = F (g s₀) s') :
    (tapeHeads T).map (fun s => F (g s) s) =
      ((tapeHeads T).map g).bind fun x => (tapeHeads T).map (F x) := by
  let σ : Finset ℕ × Finset ℕ → Finset ℕ × Finset ℕ := fun p =>
    (p.1.filter (· < c (g p.1)) ∪ p.2.filter (c (g p.1) ≤ ·),
     p.2.filter (· < c (g p.1)) ∪ p.1.filter (c (g p.1) ≤ ·))
  have hgσ : ∀ p, g (σ p).1 = g p.1 := by
    intro p
    apply hg
    intro i hi
    simp only [σ, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h; exact Or.inl ⟨h, hi⟩
    · rintro (⟨h, _⟩ | ⟨_, h'⟩)
      · exact h
      · omega
  have hσσ : ∀ p, σ (σ p) = p := by
    intro p
    have hc : c (g (σ p).1) = c (g p.1) := by rw [hgσ]
    obtain ⟨s, t⟩ := p
    simp only [σ] at hc ⊢
    rw [hc]
    ext i <;> rcases lt_or_ge i (c (g s)) with hic | hic <;>
      simp [hic, not_le_of_gt, not_lt_of_ge]
  have hinv : (tapeHeads2 T).map σ = tapeHeads2 T := by
    ext p
    rw [PMF.map_apply, tsum_eq_single (σ p)]
    · rw [if_pos (hσσ p).symm, tapeHeads2_apply, tapeHeads2_apply, tapeHeads_apply,
        tapeHeads_apply, tapeHeads_apply, tapeHeads_apply]
      have hiff : ((σ p).1 ⊆ Finset.range T ∧ (σ p).2 ⊆ Finset.range T) ↔
          (p.1 ⊆ Finset.range T ∧ p.2 ⊆ Finset.range T) := by
        obtain ⟨s, t⟩ := p
        simp only [σ, Finset.union_subset_iff]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3, h4⟩
          refine ⟨fun i hi => ?_, fun i hi => ?_⟩
          · by_cases hic : i < c (g s)
            · exact h1 (Finset.mem_filter.2 ⟨hi, hic⟩)
            · exact h4 (Finset.mem_filter.2 ⟨hi, by omega⟩)
          · by_cases hic : i < c (g s)
            · exact h3 (Finset.mem_filter.2 ⟨hi, hic⟩)
            · exact h2 (Finset.mem_filter.2 ⟨hi, by omega⟩)
        · rintro ⟨h1, h2⟩
          exact ⟨⟨(Finset.filter_subset _ _).trans h1, (Finset.filter_subset _ _).trans h2⟩,
            (Finset.filter_subset _ _).trans h2, (Finset.filter_subset _ _).trans h1⟩
      by_cases h1 : (σ p).1 ⊆ Finset.range T <;> by_cases h2 : (σ p).2 ⊆ Finset.range T <;>
        by_cases h3 : p.1 ⊆ Finset.range T <;> by_cases h4 : p.2 ⊆ Finset.range T <;>
        simp_all
    · intro q hq
      rw [if_neg]
      intro h; apply hq; rw [h, hσσ]
  have hL : (tapeHeads T).map (fun s => F (g s) s) =
      (tapeHeads2 T).map (fun p => F (g p.1) p.1) := by
    rw [← tapeHeads2_map_fst, PMF.map_comp]; rfl
  have hR : ((tapeHeads T).map g).bind (fun x => (tapeHeads T).map (F x)) =
      (tapeHeads2 T).map (fun p => F (g p.1) p.2) := by
    rw [PMF.bind_map, tapeHeads2_map]; rfl
  rw [hL, hR]
  conv_lhs => rw [← hinv]
  rw [PMF.map_comp]
  congr 1
  funext p
  simp only [Function.comp, hgσ]
  apply hF
  intro i hi
  obtain ⟨s, t⟩ := p
  dsimp only at hi
  simp only [σ, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · omega
    · exact h
  · intro h; exact Or.inr ⟨h, hi⟩


/-- INTERNAL: the next `n` tape bits after position `c`, shifted to `0..n-1`. This is the
expression the `_tape` lemmas of `ProgramModel.lean` write out. -/
def tapeRest (s : Finset ℕ) (c n : ℕ) : Finset ℕ :=
  ((s.filter (fun i => c ≤ i)).image (fun i => i - c)).filter (fun i => i < n)

/-- INTERNAL: `f` started at cursor `c₀` ends at cursor `π (f s) ≥ c₀`, and its whole result
is determined by the tape bits in `[c₀, π (f s))`. -/
def Window {α : Type} (c₀ : ℕ) (π : α → ℕ) (f : Finset ℕ → α) : Prop :=
  ∀ s, c₀ ≤ π (f s) ∧ ∀ s', (∀ i, c₀ ≤ i → i < π (f s) → (i ∈ s ↔ i ∈ s')) → f s' = f s

/-- INTERNAL: the shape of every `_tape` lemma: on any tape long enough, the viewed result
and the next `n` unread bits are distributed as `G` times `n` fresh fair bits. -/
def TapeLaw {α γ : Type} (π : α → ℕ) (v : α → γ) (f : Finset ℕ → α) (G : PMF γ) : Prop :=
  ∀ n T : ℕ, (∀ s, π (f s) + n ≤ T) →
    (tapeHeads T).map (fun s => (v (f s), tapeRest s (π (f s)) n)) =
      G.bind fun z => (tapeHeads n).map fun s' => (z, s')

/-- INTERNAL: no bits after `0`. -/
@[simp] theorem tapeRest_zero (s : Finset ℕ) (c : ℕ) : tapeRest s c 0 = ∅ := by
  simp [tapeRest]

/-- INTERNAL: `tapeRest s c n` reads only the bits of `s` at or above `c`. -/
theorem tapeRest_congr (s s' : Finset ℕ) (c n : ℕ)
    (h : ∀ i, c ≤ i → (i ∈ s ↔ i ∈ s')) : tapeRest s c n = tapeRest s' c n := by
  unfold tapeRest
  congr 2
  ext i
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨(h i h2).1 h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨(h i h2).2 h1, h2⟩

/-- INTERNAL: binds agree when the continuations agree on the support. -/
theorem bind_congr_support {α β : Type} (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a ((PMF.mem_support_iff _ _).2 ha)]

/-- INTERNAL: a fair tape of length `T` only has heads below `T`. -/
theorem subset_of_mem_support_tapeHeads {T : ℕ} {s : Finset ℕ} (hs : s ∈ (tapeHeads T).support) :
    s ⊆ Finset.range T := by
  rw [PMF.mem_support_iff, tapeHeads_apply] at hs
  by_contra h
  exact hs (if_neg h)

/-- INTERNAL: a fair tape grown by one bit is unchanged as seen by a test blind to that bit. -/
theorem tapeHeads_succ_map_of_blind {β : Type} (T : ℕ) (h : Finset ℕ → β)
    (hh : ∀ s, h (insert T s) = h s) :
    (tapeHeads (T + 1)).map h = (tapeHeads T).map h := by
  show ((tapeHeads T).bind fun s => ProbRAM.fair.bind fun b =>
      PMF.pure (if b then insert T s else s)).map h = _
  rw [PMF.map_bind]
  have : ∀ s, (ProbRAM.fair.bind fun b => PMF.pure (if b then insert T s else s)).map h =
      PMF.pure (h s) := by
    intro s
    rw [PMF.map_bind]
    have e : ∀ b : Bool, (PMF.pure (if b then insert T s else s)).map h = PMF.pure (h s) := by
      intro b; rw [PMF.pure_map]; cases b <;> simp [hh]
    simp only [e, PMF.bind_const]
  simp only [this]
  exact PMF.bind_pure_comp h (tapeHeads T)

/-- INTERNAL: **the unread rest of a fair tape is a fair tape.** -/
theorem tapeHeads_rest (T : ℕ) : ∀ c n : ℕ, c + n ≤ T →
    (tapeHeads T).map (fun s => tapeRest s c n) = tapeHeads n := by
  induction T with
  | zero =>
    intro c n h
    have hn : n = 0 := by omega
    subst hn
    simp only [tapeRest_zero]
    exact PMF.map_const _ _
  | succ T ih =>
    intro c n h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [tapeRest_zero]
      exact PMF.map_const _ _
    by_cases hle : c + n ≤ T
    · rw [tapeHeads_succ_map_of_blind T _ ?_, ih c n hle]
      intro s
      unfold tapeRest
      ext i
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_insert]
      constructor
      · rintro ⟨⟨j, ⟨hj | hj, hj'⟩, hji⟩, hi⟩
        · subst hj; omega
        · exact ⟨⟨j, ⟨hj, hj'⟩, hji⟩, hi⟩
      · rintro ⟨⟨j, ⟨hj, hj'⟩, hji⟩, hi⟩
        exact ⟨⟨j, ⟨Or.inr hj, hj'⟩, hji⟩, hi⟩
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hcT : c + n' = T := by omega
      show ((tapeHeads T).bind fun s => ProbRAM.fair.bind fun b =>
          PMF.pure (if b then insert T s else s)).map _ = (tapeHeads n').bind fun s =>
            ProbRAM.fair.bind fun b => PMF.pure (if b then insert n' s else s)
      rw [← ih c n' (by omega), PMF.bind_map, PMF.map_bind]
      apply bind_congr_support
      intro s hs
      have hsub := subset_of_mem_support_tapeHeads hs
      rw [PMF.map_bind]
      simp only [Function.comp]
      congr 1
      funext b
      rw [PMF.pure_map]
      congr 1
      have hlt : ∀ i ∈ s, i < T := fun i hi => Finset.mem_range.1 (hsub hi)
      unfold tapeRest
      ext i
      cases b
      · simp only [Bool.false_eq_true, if_false, Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨⟨j, ⟨hj, hj'⟩, hji⟩, _⟩
          have := hlt j hj
          exact ⟨⟨j, ⟨hj, hj'⟩, hji⟩, by omega⟩
        · rintro ⟨⟨j, ⟨hj, hj'⟩, hji⟩, hi⟩
          exact ⟨⟨j, ⟨hj, hj'⟩, hji⟩, by omega⟩
      · simp only [if_true, Finset.mem_filter, Finset.mem_image, Finset.mem_insert]
        constructor
        · rintro ⟨⟨j, ⟨hj | hj, hj'⟩, hji⟩, hi⟩
          · left; omega
          · have := hlt j hj
            right; exact ⟨⟨j, ⟨hj, hj'⟩, hji⟩, by omega⟩
        · rintro (hi | ⟨⟨j, ⟨hj, hj'⟩, hji⟩, hi⟩)
          · exact ⟨⟨T, ⟨Or.inl rfl, by omega⟩, by omega⟩, by omega⟩
          · exact ⟨⟨j, ⟨Or.inr hj, hj'⟩, hji⟩, by omega⟩

/-- INTERNAL: a piece that reads nothing leaves a fair tape behind. -/
theorem tapeLaw_const {α γ : Type} (π : α → ℕ) (v : α → γ) (a : α) :
    TapeLaw π v (fun _ => a) (PMF.pure (v a)) := by
  intro n T hT
  have h := tapeHeads_rest T (π a) n (hT ∅)
  rw [PMF.pure_bind, ← h, PMF.map_comp]
  rfl

/-- INTERNAL: a tape law gives the law of the view alone. -/
theorem TapeLaw.map_view {α γ : Type} {π : α → ℕ} {v : α → γ} {f : Finset ℕ → α} {G : PMF γ}
    (h : TapeLaw π v f G) (T : ℕ) (hT : ∀ s, π (f s) ≤ T) :
    (tapeHeads T).map (fun s => v (f s)) = G := by
  have := congrArg (PMF.map Prod.fst) (h 0 T (by simpa using hT))
  rw [PMF.map_comp, PMF.map_bind] at this
  simp only [tapeHeads, PMF.map_comp] at this
  have h2 : (G.bind fun a => PMF.map (Prod.fst ∘ fun s' => (a, s')) (PMF.pure (∅ : Finset ℕ))) = G := by
    simp only [PMF.pure_map]
    exact PMF.bind_pure G
  rw [h2] at this
  exact this

/-- INTERNAL: windows compose along a sequential bind. -/
theorem window_bind {α β : Type} {c₀ : ℕ} {π₁ : α → ℕ} {π₂ : β → ℕ}
    {g₁ : Finset ℕ → α} {g₂ : α → Finset ℕ → β} (P : α → Prop)
    (hw₁ : Window c₀ π₁ g₁) (hP : ∀ s, P (g₁ s))
    (hw₂ : ∀ x, P x → Window (π₁ x) π₂ (g₂ x)) :
    Window c₀ π₂ (fun s => g₂ (g₁ s) s) := by
  intro s
  obtain ⟨h1, h1'⟩ := hw₁ s
  obtain ⟨h2, h2'⟩ := hw₂ (g₁ s) (hP s) s
  refine ⟨h1.trans h2, fun s' hs' => ?_⟩
  have e1 : g₁ s' = g₁ s := h1' s' fun i hi hi' => hs' i hi (lt_of_lt_of_le hi' h2)
  simp only
  rw [e1]
  exact h2' s' fun i hi hi' => hs' i (h1.trans hi) hi'

/-- INTERNAL: windows survive deterministic post-processing that keeps the cursor. -/
theorem window_map {α β : Type} {c₀ : ℕ} {π : α → ℕ} {π' : β → ℕ} {f : Finset ℕ → α}
    (h : α → β) (hπ : ∀ a, π' (h a) = π a) (hw : Window c₀ π f) :
    Window c₀ π' (fun s => h (f s)) := by
  intro s
  obtain ⟨h1, h1'⟩ := hw s
  refine ⟨by rw [hπ]; exact h1, fun s' hs' => ?_⟩
  rw [hπ] at hs'
  simp only
  rw [h1' s' hs']

/-- INTERNAL: a constant result is windowed if it does not move the cursor back. -/
theorem window_const {α : Type} {c₀ : ℕ} {π : α → ℕ} (a : α) (h : c₀ ≤ π a) :
    Window c₀ π (fun _ => a) :=
  fun _ => ⟨h, fun _ _ => rfl⟩

/-- INTERNAL: a window may be checked from an earlier start. -/
theorem Window.mono {α : Type} {c₀ c₁ : ℕ} {π : α → ℕ} {f : Finset ℕ → α}
    (hw : Window c₁ π f) (h : c₀ ≤ c₁) : Window c₀ π f := by
  intro s
  obtain ⟨h1, h1'⟩ := hw s
  exact ⟨h.trans h1, fun s' hs' => h1' s' fun i hi hi' => hs' i (h.trans hi) hi'⟩

/-- INTERNAL: tape laws compose along a sequential bind of windowed pieces. -/
theorem tapeLaw_bind {α β γ δ : Type} {c₀ : ℕ} {π₁ : α → ℕ} {π₂ : β → ℕ}
    {v₁ : α → γ} {v₂ : β → δ} {g₁ : Finset ℕ → α} {g₂ : α → Finset ℕ → β}
    (P : α → Prop) {G₁ : PMF γ} {G₂ : γ → PMF δ}
    (hw₁ : Window c₀ π₁ g₁) (hP : ∀ s, P (g₁ s))
    (hw₂ : ∀ x, P x → Window (π₁ x) π₂ (g₂ x))
    (hl₁ : TapeLaw π₁ v₁ g₁ G₁) (hl₂ : ∀ x, P x → TapeLaw π₂ v₂ (g₂ x) (G₂ (v₁ x))) :
    TapeLaw π₂ v₂ (fun s => g₂ (g₁ s) s) (G₁.bind G₂) := by
  intro n T hT
  -- every reachable intermediate result meets the length hypothesis
  have hreach : ∀ s₀ s, π₂ (g₂ (g₁ s₀) s) + n ≤ T := by
    intro s₀ s
    let s'' := s₀.filter (· < π₁ (g₁ s₀)) ∪ s.filter (π₁ (g₁ s₀) ≤ ·)
    have e1 : g₁ s'' = g₁ s₀ := by
      apply (hw₁ s₀).2
      intro i _ hi
      simp [s'', hi, not_le_of_gt hi]
    have e2 : g₂ (g₁ s₀) s'' = g₂ (g₁ s₀) s := by
      apply (hw₂ (g₁ s₀) (hP s₀) s).2
      intro i hi _
      simp [s'', hi, not_lt_of_ge hi]
    have := hT s''
    simp only at this
    rw [e1, e2] at this
    exact this
  have hsplit := tapeHeads_split T g₁ π₁
    (fun s s' h => (hw₁ s).2 s' fun i _ hi => h i hi)
    (fun x s => (v₂ (g₂ x s), tapeRest s (π₂ (g₂ x s)) n))
    (by
      intro s₀ s s' h
      have e : g₂ (g₁ s₀) s' = g₂ (g₁ s₀) s :=
        (hw₂ (g₁ s₀) (hP s₀) s).2 s' fun i hi _ => h i hi
      simp only [e]
      congr 1
      apply tapeRest_congr
      intro i hi
      exact h i (le_trans (hw₂ (g₁ s₀) (hP s₀) s).1 hi))
  simp only at hsplit ⊢
  rw [hsplit, PMF.bind_map]
  have hstep : ∀ s, (tapeHeads T).map (fun t => (v₂ (g₂ (g₁ s) t), tapeRest t (π₂ (g₂ (g₁ s) t)) n))
      = (G₂ (v₁ (g₁ s))).bind fun z => (tapeHeads n).map fun s' => (z, s') :=
    fun s => hl₂ (g₁ s) (hP s) n T (hreach s)
  have hview : (tapeHeads T).map (fun s => v₁ (g₁ s)) = G₁ := by
    apply hl₁.map_view
    intro s
    have := hT s
    have h2 := (hw₂ (g₁ s) (hP s) s).1
    simp only at this
    omega
  calc (tapeHeads T).bind ((fun x => (tapeHeads T).map
          (fun s => (v₂ (g₂ x s), tapeRest s (π₂ (g₂ x s)) n))) ∘ g₁)
      = (tapeHeads T).bind (fun s => (G₂ (v₁ (g₁ s))).bind fun z =>
          (tapeHeads n).map fun s' => (z, s')) := by
        congr 1; funext s; exact hstep s
    _ = ((tapeHeads T).map (fun s => v₁ (g₁ s))).bind (fun y => (G₂ y).bind fun z =>
          (tapeHeads n).map fun s' => (z, s')) := by
        rw [PMF.bind_map]; rfl
    _ = (G₁.bind G₂).bind fun z => (tapeHeads n).map fun s' => (z, s') := by
        rw [hview, PMF.bind_bind]

/-- INTERNAL: tape laws survive deterministic post-processing that keeps the cursor. -/
theorem tapeLaw_map {α β γ δ : Type} {π : α → ℕ} {π' : β → ℕ} {v : α → γ} {v' : β → δ}
    {f : Finset ℕ → α} {G : PMF γ} (h : α → β) (k : γ → δ)
    (hπ : ∀ a, π' (h a) = π a) (hv : ∀ a, v' (h a) = k (v a)) (hl : TapeLaw π v f G) :
    TapeLaw π' v' (fun s => h (f s)) (G.map k) := by
  intro n T hT
  have h0 := hl n T (fun s => by have := hT s; simp only [hπ] at this; exact this)
  have e : (fun s => (v' (h (f s)), tapeRest s (π' (h (f s))) n)) =
      (fun p : γ × Finset ℕ => (k p.1, p.2)) ∘ (fun s => (v (f s), tapeRest s (π (f s)) n)) := by
    funext s; simp [hπ, hv]
  simp only
  rw [e, ← PMF.map_comp, h0, PMF.map_bind, PMF.bind_map]
  congr 1; funext z
  simp only [Function.comp, PMF.map_comp]
  rfl

/-- INTERNAL: a fold of windowed steps is windowed. -/
theorem window_foldl {ι β : Type} (π : β → ℕ) (P : β → Prop)
    (f : β → ι → Finset ℕ → β)
    (hP : ∀ b i s, P b → P (f b i s))
    (hw : ∀ b i, P b → Window (π b) π (f b i)) :
    ∀ (l : List ι) (b : β), P b →
      Window (π b) π (fun s => l.foldl (fun b' i => f b' i s) b) ∧
        ∀ s, P (l.foldl (fun b' i => f b' i s) b) := by
  intro l
  induction l with
  | nil => intro b hb; exact ⟨window_const b le_rfl, fun _ => hb⟩
  | cons i l ih =>
    intro b hb
    have hstep : ∀ s, P (f b i s) := fun s => hP b i s hb
    refine ⟨?_, fun s => (ih (f b i s) (hstep s)).2 s⟩
    exact window_bind (g₁ := f b i) (g₂ := fun b' s => l.foldl (fun b'' i => f b'' i s) b')
      P (hw b i hb) hstep (fun x hx => (ih x hx).1)

end Cellcounting.Analysis
