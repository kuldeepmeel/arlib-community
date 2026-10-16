import Cellcounting.Interface.Pseudocode

/-!
# Leaf elimination solves the nonroot equations (`lem:forest`, first part)

`scales.tex:128-140`: along an elimination order in which every vertex comes
after all its children, leaf elimination produces tree values satisfying every
nonroot margin equation; the final loads at the roots are their actual incident
sums; any tree vector satisfying the nonroot equations equals the produced one;
and integral data give integral values.

The first part of the file is generic: `tvStep` is the fold step of
`Pseudocode.treeValues`, for edges `t` with endpoints `R t ≠ Cv t`, and
`ElimValid` lists what the elimination order must satisfy.  The second part
instantiates it for the pseudocode, given `elimOrder_valid`.
-/

namespace Cellcounting.Analysis

open Finset

section generic

variable (R Cv : ℕ → ℕ) (marg : ℕ → ℚ)

/-- INTERNAL: one leaf-elimination step: the parent edge `t` of `v` gets the value
`marg v - load v`, which is added to the load of the other endpoint. -/
def tvStep (st : (ℕ → ℚ) × (ℕ → ℚ)) (vt : ℕ × ℕ) : (ℕ → ℚ) × (ℕ → ℚ) :=
  (Function.update st.1 (if vt.1 = R vt.2 then Cv vt.2 else R vt.2)
      (st.1 (if vt.1 = R vt.2 then Cv vt.2 else R vt.2) + (marg vt.1 - st.1 vt.1)),
    Function.update st.2 vt.2 (marg vt.1 - st.1 vt.1))

/-- INTERNAL: `t` is incident to `u`. -/
def Inc (u t : ℕ) : Prop := R t = u ∨ Cv t = u

/-- INTERNAL: the actual incident sum at `u` for tree values `Tv`. -/
def tLoadG (N : ℕ) (base : ℕ → ℚ) (Tv : ℕ → ℚ) (u : ℕ) : ℚ :=
  base u + ∑ t ∈ Finset.range N, ((if R t = u then Tv t else 0) + (if Cv t = u then Tv t else 0))

/-- INTERNAL: the requirements on an elimination order `l` for `N` edges. -/
structure ElimValid (N : ℕ) (l : List (ℕ × ℕ)) : Prop where
  lt : ∀ x ∈ l, x.2 < N
  inc : ∀ x ∈ l, x.1 = R x.2 ∨ x.1 = Cv x.2
  ne : ∀ t < N, R t ≠ Cv t
  nodup_snd : (l.map Prod.snd).Nodup
  nodup_fst : (l.map Prod.fst).Nodup
  cover : ∀ t < N, t ∈ l.map Prod.snd
  child : ∀ l1 v t l2, l = l1 ++ (v, t) :: l2 → ∀ t' < N, (R t' = v ∨ Cv t' = v) → t' ≠ t →
    t' ∈ l1.map Prod.snd

/-- INTERNAL: the endpoint of `t` other than `v`. -/
def oth (vt : ℕ × ℕ) : ℕ := if vt.1 = R vt.2 then Cv vt.2 else R vt.2

theorem tvStep_fst (st : (ℕ → ℚ) × (ℕ → ℚ)) (vt : ℕ × ℕ) (u : ℕ) :
    (tvStep R Cv marg st vt).1 u =
      st.1 u + (if u = oth R Cv vt then marg vt.1 - st.1 vt.1 else 0) := by
  simp only [tvStep, oth, Function.update_apply]
  split_ifs with h <;> simp_all

theorem tvStep_snd (st : (ℕ → ℚ) × (ℕ → ℚ)) (vt : ℕ × ℕ) (t : ℕ) :
    (tvStep R Cv marg st vt).2 t = if t = vt.2 then marg vt.1 - st.1 vt.1 else st.2 t := by
  simp only [tvStep, Function.update_apply]

theorem foldl_tvStep_snd_of_not_mem (l : List (ℕ × ℕ)) (s : (ℕ → ℚ) × (ℕ → ℚ)) (t : ℕ)
    (ht : t ∉ l.map Prod.snd) : (l.foldl (tvStep R Cv marg) s).2 t = s.2 t := by
  induction l generalizing s with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at ht
    rw [List.foldl_cons, ih _ ht.2, tvStep_snd, if_neg ht.1]

theorem foldl_tvStep_fst_of_not_oth (l : List (ℕ × ℕ)) (s : (ℕ → ℚ) × (ℕ → ℚ)) (u : ℕ)
    (hu : ∀ x ∈ l, oth R Cv x ≠ u) : (l.foldl (tvStep R Cv marg) s).1 u = s.1 u := by
  induction l generalizing s with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldl_cons, ih _ fun y hy => hu y (List.mem_cons_of_mem _ hy), tvStep_fst,
      if_neg (fun h => hu x List.mem_cons_self h.symm), add_zero]

/-- INTERNAL: the leaf-elimination invariant along a processed prefix. -/
theorem foldl_tvStep_inv (base : ℕ → ℚ) (l : List (ℕ × ℕ))
    (hinc : ∀ x ∈ l, x.1 = R x.2 ∨ x.1 = Cv x.2) (hne : ∀ x ∈ l, R x.2 ≠ Cv x.2)
    (hnd : (l.map Prod.snd).Nodup) :
    (∀ t, t ∉ l.map Prod.snd → (l.foldl (tvStep R Cv marg) (base, fun _ => 0)).2 t = 0) ∧
    ∀ u, (l.foldl (tvStep R Cv marg) (base, fun _ => 0)).1 u = base u +
      ∑ t ∈ (l.map Prod.snd).toFinset.filter (fun t => (R t = u ∨ Cv t = u) ∧ (u, t) ∉ l),
        (l.foldl (tvStep R Cv marg) (base, fun _ => 0)).2 t := by
  classical
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l x ih =>
    have hinc' : ∀ y ∈ l, y.1 = R y.2 ∨ y.1 = Cv y.2 := fun y hy => hinc y (by simp [hy])
    have hne' : ∀ y ∈ l, R y.2 ≠ Cv y.2 := fun y hy => hne y (by simp [hy])
    have hnd' : (l.map Prod.snd).Nodup := by
      rw [List.map_append] at hnd; exact (List.nodup_append.1 hnd).1
    have hxt : x.2 ∉ l.map Prod.snd := by
      rw [List.map_append] at hnd
      intro h
      have := (List.nodup_append.1 hnd).2.2 _ h x.2 (by simp)
      exact this rfl
    obtain ⟨ih1, ih2⟩ := ih hinc' hne' hnd'
    set s := l.foldl (tvStep R Cv marg) (base, fun _ => 0) with hs
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← hs]
    have hxinc := hinc x (by simp)
    have hxne := hne x (by simp)
    refine ⟨fun t ht => ?_, fun u => ?_⟩
    · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, not_or] at ht
      rw [tvStep_snd, if_neg ht.2, ih1 t ht.1]
    · rw [tvStep_fst, ih2 u]
      have hset : ((l ++ [x]).map Prod.snd).toFinset = insert x.2 (l.map Prod.snd).toFinset := by
        ext t; simp
      rw [hset, Finset.filter_insert]
      -- the old terms are unchanged
      have hold : ∑ t ∈ (l.map Prod.snd).toFinset.filter
            (fun t => (R t = u ∨ Cv t = u) ∧ (u, t) ∉ l ++ [x]),
            (tvStep R Cv marg s x).2 t =
          ∑ t ∈ (l.map Prod.snd).toFinset.filter (fun t => (R t = u ∨ Cv t = u) ∧ (u, t) ∉ l),
            s.2 t := by
        apply Finset.sum_congr
        · ext t
          simp only [Finset.mem_filter, List.mem_toFinset, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false, not_or]
          constructor
          · rintro ⟨h1, h2, h3, -⟩; exact ⟨h1, h2, h3⟩
          · rintro ⟨h1, h2, h3⟩
            refine ⟨h1, h2, h3, fun h => ?_⟩
            rw [← h] at hxt; exact hxt h1
        · intro t ht
          simp only [Finset.mem_filter, List.mem_toFinset] at ht
          have hne2 : t ≠ x.2 := fun h => hxt (by rw [← h]; exact ht.1)
          rw [tvStep_snd, if_neg hne2]
      have hcond : ((R x.2 = u ∨ Cv x.2 = u) ∧ (u, x.2) ∉ l ++ [x]) ↔ u = oth R Cv x := by
        have hnot : (u, x.2) ∉ l := fun h => hxt (List.mem_map.2 ⟨_, h, rfl⟩)
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, hnot, false_or,
          oth]
        obtain ⟨v, t⟩ := x
        simp only [Prod.mk.injEq, and_true] at hxinc hxne ⊢
        rcases hxinc with h | h <;> subst h
        · simp only [if_true]
          constructor
          · rintro ⟨h1 | h1, h2⟩
            · exact absurd h1.symm h2
            · exact h1.symm
          · rintro rfl; exact ⟨Or.inr rfl, fun h => hxne h.symm⟩
        · simp only [if_neg (Ne.symm hxne)]
          constructor
          · rintro ⟨h1 | h1, h2⟩
            · exact h1.symm
            · exact absurd h1.symm h2
          · rintro rfl; exact ⟨Or.inl rfl, fun h => hxne h⟩
      by_cases hu : u = oth R Cv x
      · rw [if_pos (hcond.2 hu), Finset.sum_insert, hold, if_pos hu, tvStep_snd, if_pos rfl]
        · ring
        · simp only [Finset.mem_filter, List.mem_toFinset, not_and]
          intro h; exact absurd h hxt
      · rw [if_neg (fun h => hu (hcond.1 h)), hold, if_neg hu]; ring

theorem tLoadG_eq_filter (N : ℕ) (hne : ∀ t < N, R t ≠ Cv t) (base Tv : ℕ → ℚ) (u : ℕ) :
    tLoadG R Cv N base Tv u =
      base u + ∑ t ∈ (Finset.range N).filter (fun t => R t = u ∨ Cv t = u), Tv t := by
  classical
  unfold tLoadG
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun t ht => ?_
  have := hne t (Finset.mem_range.1 ht)
  by_cases h1 : R t = u <;> by_cases h2 : Cv t = u
  · exact absurd (h1.trans h2.symm) this
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

/-- INTERNAL: the final state of leaf elimination. -/
def tvFin (base : ℕ → ℚ) (l : List (ℕ × ℕ)) : (ℕ → ℚ) × (ℕ → ℚ) :=
  l.foldl (tvStep R Cv marg) (base, fun _ => 0)

variable {R Cv marg}

/-- INTERNAL: at a split `l = l1 ++ x :: l2`, the incident sum of the processed
vertex decomposes into its parent edge and the already processed edges. -/
theorem split_facts {N : ℕ} {l : List (ℕ × ℕ)} (hv : ElimValid R Cv N l) (base : ℕ → ℚ)
    (l1 l2 : List (ℕ × ℕ)) (x : ℕ × ℕ) (hl : l = l1 ++ x :: l2) (Tv : ℕ → ℚ) :
    tLoadG R Cv N base Tv x.1 = base x.1 + Tv x.2 +
      ∑ t ∈ (l1.map Prod.snd).toFinset.filter (fun t => R t = x.1 ∨ Cv t = x.1), Tv t := by
  classical
  rw [tLoadG_eq_filter R Cv N hv.ne]
  have hxl : x ∈ l := by rw [hl]; simp
  have hx2 : x.2 ∉ l1.map Prod.snd := by
    have := hv.nodup_snd
    rw [hl, List.map_append, List.map_cons] at this
    intro h
    exact (List.nodup_append.1 this).2.2 _ h x.2 List.mem_cons_self rfl
  have hset : (Finset.range N).filter (fun t => R t = x.1 ∨ Cv t = x.1) =
      insert x.2 ((l1.map Prod.snd).toFinset.filter (fun t => R t = x.1 ∨ Cv t = x.1)) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, List.mem_toFinset]
    constructor
    · rintro ⟨ht, hinc⟩
      by_cases htx : t = x.2
      · exact Or.inl htx
      · right
        obtain ⟨v, t0⟩ := x
        exact ⟨hv.child l1 v t0 l2 hl t ht hinc htx, hinc⟩
    · rintro (rfl | ⟨ht, hinc⟩)
      · refine ⟨hv.lt x hxl, ?_⟩
        rcases hv.inc x hxl with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ht
        exact ⟨hv.lt y (by rw [hl]; simp [hy]), hinc⟩
  rw [hset, Finset.sum_insert]
  · ring
  · simp only [Finset.mem_filter, List.mem_toFinset, not_and]
    intro h; exact absurd h hx2

/-- INTERNAL: the produced tree values at a split. -/
theorem split_values {N : ℕ} {l : List (ℕ × ℕ)} (hv : ElimValid R Cv N l) (base : ℕ → ℚ)
    (l1 l2 : List (ℕ × ℕ)) (x : ℕ × ℕ) (hl : l = l1 ++ x :: l2) :
    (tvFin R Cv marg base l).2 x.2 = marg x.1 - (tvFin R Cv marg base l1).1 x.1 ∧
      ∀ t ∈ l1.map Prod.snd, (tvFin R Cv marg base l).2 t =
        (tvFin R Cv marg base l1).2 t := by
  have hnd := hv.nodup_snd
  rw [hl, List.map_append, List.map_cons] at hnd
  have hnd2 := (List.nodup_append.1 hnd)
  have hx2l2 : x.2 ∉ l2.map Prod.snd := (List.nodup_cons.1 hnd2.2.1).1
  simp only [tvFin]
  rw [hl, List.foldl_append, List.foldl_cons]
  refine ⟨?_, fun t ht => ?_⟩
  · rw [foldl_tvStep_snd_of_not_mem R Cv marg l2 _ _ hx2l2, tvStep_snd, if_pos rfl]
  · have h1 : t ∉ l2.map Prod.snd := fun h =>
      hnd2.2.2 t ht t (List.mem_cons_of_mem _ h) rfl
    have h2 : t ≠ x.2 := fun h => hnd2.2.2 t ht t (by rw [h]; exact List.mem_cons_self) rfl
    rw [foldl_tvStep_snd_of_not_mem R Cv marg l2 _ _ h1, tvStep_snd, if_neg h2]

/-- INTERNAL: the processed vertex's load at a split, in terms of final values. -/
theorem split_load {N : ℕ} {l : List (ℕ × ℕ)} (hv : ElimValid R Cv N l) (base : ℕ → ℚ)
    (l1 l2 : List (ℕ × ℕ)) (x : ℕ × ℕ) (hl : l = l1 ++ x :: l2) :
    (tvFin R Cv marg base l1).1 x.1 = base x.1 +
      ∑ t ∈ (l1.map Prod.snd).toFinset.filter (fun t => R t = x.1 ∨ Cv t = x.1),
        (tvFin R Cv marg base l).2 t := by
  classical
  have hsub : ∀ y ∈ l1, y ∈ l := fun y hy => by rw [hl]; simp [hy]
  have hnd1 : (l1.map Prod.snd).Nodup := by
    have := hv.nodup_snd; rw [hl, List.map_append] at this
    exact (List.nodup_append.1 this).1
  have hinv := (foldl_tvStep_inv R Cv marg base l1 (fun y hy => hv.inc y (hsub y hy))
    (fun y hy => hv.ne _ (hv.lt y (hsub y hy))) hnd1).2 x.1
  simp only [tvFin]
  rw [hinv]
  congr 1
  apply Finset.sum_congr
  · ext t
    simp only [Finset.mem_filter, List.mem_toFinset]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, h2, fun h => ?_⟩
      have := hv.nodup_fst
      rw [hl, List.map_append, List.map_cons] at this
      exact (List.nodup_append.1 this).2.2 _ (List.mem_map.2 ⟨_, h, rfl⟩) x.1
        List.mem_cons_self rfl
  · intro t ht
    simp only [Finset.mem_filter, List.mem_toFinset] at ht
    exact ((split_values hv base l1 l2 x hl).2 t ht.1).symm

/-- **Leaf elimination satisfies the nonroot equations.**
TEXLINE: sections/scales.tex:128-134 -/
theorem tvFin_nonroot {N : ℕ} {l : List (ℕ × ℕ)} (hv : ElimValid R Cv N l) (base : ℕ → ℚ)
    (x : ℕ × ℕ) (hx : x ∈ l) :
    tLoadG R Cv N base (tvFin R Cv marg base l).2 x.1 = marg x.1 := by
  obtain ⟨l1, l2, hl⟩ := List.append_of_mem hx
  rw [split_facts hv base l1 l2 x hl, (split_values hv base l1 l2 x hl).1,
    split_load hv base l1 l2 x hl]
  ring

/-- **The final loads at unprocessed vertices are their incident sums.**
TEXLINE: sections/scales.tex:113-126 -/
theorem tvFin_root {N : ℕ} {l : List (ℕ × ℕ)} (hv : ElimValid R Cv N l) (base : ℕ → ℚ)
    (u : ℕ) (hu : u ∉ l.map Prod.fst) :
    (tvFin R Cv marg base l).1 u = tLoadG R Cv N base (tvFin R Cv marg base l).2 u := by
  classical
  have hinv := (foldl_tvStep_inv R Cv marg base l hv.inc (fun y hy => hv.ne _ (hv.lt y hy))
    hv.nodup_snd).2 u
  simp only [tvFin] at hinv ⊢
  rw [hinv, tLoadG_eq_filter R Cv N hv.ne]
  congr 1
  apply Finset.sum_congr _ fun _ _ => rfl
  ext t
  simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2, -⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h1
    exact ⟨hv.lt y hy, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hv.cover t h1, h2, fun h => hu (List.mem_map.2 ⟨_, h, rfl⟩)⟩

/-- **Uniqueness of the nonroot completion.**
TEXLINE: sections/scales.tex:128-134 -/
theorem tvFin_unique {N : ℕ} {l : List (ℕ × ℕ)} (hv : ElimValid R Cv N l) (base : ℕ → ℚ)
    (Tv : ℕ → ℚ) (hTv : ∀ x ∈ l, tLoadG R Cv N base Tv x.1 = marg x.1) :
    ∀ t < N, Tv t = (tvFin R Cv marg base l).2 t := by
  classical
  have key : ∀ n, ∀ l1 l2 x, l1.length = n → l = l1 ++ x :: l2 →
      Tv x.2 = (tvFin R Cv marg base l).2 x.2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro l1 l2 x hlen hl
      have hx : x ∈ l := by rw [hl]; simp
      have hIH : ∀ t ∈ l1.map Prod.snd, Tv t = (tvFin R Cv marg base l).2 t := by
        intro t ht
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ht
        obtain ⟨a, b, hab⟩ := List.append_of_mem hy
        refine ih a.length ?_ a (b ++ x :: l2) y rfl ?_
        · rw [← hlen, hab]; simp
        · rw [hl, hab]; simp
      have h1 := hTv x hx
      have h2 := tvFin_nonroot (marg := marg) hv base x hx
      rw [split_facts hv base l1 l2 x hl] at h1 h2
      have h3 : ∑ t ∈ (l1.map Prod.snd).toFinset.filter (fun t => R t = x.1 ∨ Cv t = x.1),
          Tv t = ∑ t ∈ (l1.map Prod.snd).toFinset.filter (fun t => R t = x.1 ∨ Cv t = x.1),
          (tvFin R Cv marg base l).2 t := by
        refine Finset.sum_congr rfl fun t ht => ?_
        simp only [Finset.mem_filter, List.mem_toFinset] at ht
        exact hIH t ht.1
      linarith
  intro t ht
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (hv.cover t ht)
  obtain ⟨l1, l2, hl⟩ := List.append_of_mem hx
  exact key _ l1 l2 x rfl hl

/-- **Integrality** of leaf elimination for integral data. -/
theorem tvFin_int (base : ℕ → ℚ) (l : List (ℕ × ℕ)) (hb : ∀ u, ∃ k : ℤ, base u = k)
    (hm : ∀ u, ∃ k : ℤ, marg u = k) :
    (∀ u, ∃ k : ℤ, (tvFin R Cv marg base l).1 u = k) ∧
      ∀ t, ∃ k : ℤ, (tvFin R Cv marg base l).2 t = k := by
  simp only [tvFin]
  suffices h : ∀ s : (ℕ → ℚ) × (ℕ → ℚ), (∀ u, ∃ k : ℤ, s.1 u = k) → (∀ t, ∃ k : ℤ, s.2 t = k) →
      (∀ u, ∃ k : ℤ, (l.foldl (tvStep R Cv marg) s).1 u = k) ∧
        ∀ t, ∃ k : ℤ, (l.foldl (tvStep R Cv marg) s).2 t = k from
    h _ hb fun _ => ⟨0, by simp⟩
  induction l with
  | nil => intro s h1 h2; exact ⟨h1, h2⟩
  | cons x l ih =>
    intro s h1 h2
    rw [List.foldl_cons]
    apply ih
    · intro u
      rw [tvStep_fst]
      obtain ⟨a, ha⟩ := h1 u
      obtain ⟨b, hb⟩ := h1 x.1
      obtain ⟨c, hc⟩ := hm x.1
      split_ifs
      · exact ⟨a + (c - b), by rw [ha, hb, hc]; push_cast; ring⟩
      · exact ⟨a, by rw [ha]; ring⟩
    · intro t
      rw [tvStep_snd]
      obtain ⟨b, hb⟩ := h1 x.1
      obtain ⟨c, hc⟩ := hm x.1
      split_ifs
      · exact ⟨c - b, by rw [hb, hc]; push_cast; ring⟩
      · exact h2 t

end generic

end Cellcounting.Analysis
