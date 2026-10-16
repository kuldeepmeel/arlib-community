import Cellcounting.Analysis.FlowNet

/-!
# The Edmonds–Karp bound on shortest-path augmentations

`sections/scales.tex:13-18` cites Edmonds and Karp (`EK1972`, Theorem 1): the
shortest-augmenting-path algorithm uses `O(VE)` augmentations, which on the present
simple network is `O(V³)`, independently of the numerical capacities.  The paper does
not prove this.  It is stated here on an abstract residual capacity function
`res : ℕ → ℕ → ℕ` on the vertices `0, …, V - 1` (source `0`, sink `V - 1`):

* `IsResPath V res p`: `p` is a vertex list from `0` to `V - 1` along arcs of positive
  residual capacity;
* `pushAlong res p a`: push `a` units along the consecutive arcs of `p`
  (forward residuals drop by `a`, reverse residuals rise by `a`);
* `EKStep V res res'`: `res'` is `res` augmented along a *shortest* residual path by
  its bottleneck capacity;
* `edmondsKarp_bound`: any run of `K` such steps has `K ≤ V³`.

The paper does not prove the bound; it is proved here from scratch by EK1972's
argument (the same route as `OAI.ContingencyTables.EdmondsKarpBound.shortest_trace_bound`
in the reference formalization, which is stated over a different flow structure and is
not linked).  In namespace `EKBound`: `resDist` is the residual BFS distance;
`shortest_dist` labels the `i`-th vertex of a shortest path with level `i + 1`;
`step_mono` shows one augmentation never lowers a distance; `critical_arc` finds a
saturated arc going up one level; `reverse_arc` shows a revived arc was pushed
backwards.  Each step is charged to (critical arc, tail level) in `[0, V)³`, and a
repeated arc has a strictly higher tail level, so the charge is injective.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

/-- INTERNAL: `p` is a path from the source `0` to the sink `V - 1` along arcs of
positive residual capacity.
TEXLINE: sections/scales.tex:13-20 -/
def IsResPath (V : ℕ) (res : ℕ → ℕ → ℕ) (p : List ℕ) : Prop :=
  p.head? = some 0 ∧ p.getLast? = some (V - 1) ∧ (∀ x ∈ p, x < V) ∧
    p.IsChain (fun u v => 0 < res u v)

/-- INTERNAL: push `a` units along the consecutive arcs of the vertex list `p`.
TEXLINE: sections/scales.tex:19-20 -/
def pushAlong (res : ℕ → ℕ → ℕ) (p : List ℕ) (a : ℕ) (u v : ℕ) : ℕ :=
  res u v + a * (p.zip p.tail).count (v, u) - a * (p.zip p.tail).count (u, v)

/-- INTERNAL: one step of the shortest-augmenting-path algorithm: augment along a
shortest residual path by its bottleneck (minimum residual) capacity.
TEXLINE: sections/scales.tex:13-20 -/
def EKStep (V : ℕ) (res res' : ℕ → ℕ → ℕ) : Prop :=
  ∃ p : List ℕ, IsResPath V res p ∧ (∀ q, IsResPath V res q → p.length ≤ q.length) ∧
    ∃ a : ℕ, (∀ e ∈ p.zip p.tail, a ≤ res e.1 e.2) ∧ (∃ e ∈ p.zip p.tail, res e.1 e.2 = a) ∧
      res' = pushAlong res p a

namespace EKBound

/-- INTERNAL: `q` is a residual path from the source `0` to the vertex `y`; a
residual path in the sense of `IsResPath` is exactly one to `V - 1`.
TEXLINE: sections/scales.tex:13-20 -/
def PathTo (V : ℕ) (r : ℕ → ℕ → ℕ) (y : ℕ) (q : List ℕ) : Prop :=
  q.head? = some 0 ∧ q.getLast? = some y ∧ (∀ x ∈ q, x < V) ∧
    q.IsChain (fun u v => 0 < r u v)

/-- INTERNAL: the residual distance to `y`, counted in vertices of a shortest residual
path from `0` (meaningful only when `y` is reachable).
TEXLINE: sections/scales.tex:13-20 -/
noncomputable def resDist (V : ℕ) (r : ℕ → ℕ → ℕ) (y : ℕ) : ℕ :=
  sInf {n | ∃ q, PathTo V r y q ∧ q.length = n}

/-- INTERNAL: a residual path bounds the distance. -/
theorem resDist_le {V : ℕ} {r : ℕ → ℕ → ℕ} {y : ℕ} {q : List ℕ} (h : PathTo V r y q) :
    resDist V r y ≤ q.length :=
  Nat.sInf_le ⟨q, h, rfl⟩

/-- INTERNAL: a reachable vertex has a residual path of exactly its distance. -/
theorem resDist_spec {V : ℕ} {r : ℕ → ℕ → ℕ} {y : ℕ} (h : ∃ q, PathTo V r y q) :
    ∃ q, PathTo V r y q ∧ q.length = resDist V r y := by
  obtain ⟨q, hq⟩ := h
  exact Nat.sInf_mem (s := {n | ∃ q, PathTo V r y q ∧ q.length = n}) ⟨_, q, hq, rfl⟩

/-- INTERNAL: extend a residual path by one positive arc. -/
theorem PathTo.snoc {V : ℕ} {r : ℕ → ℕ → ℕ} {x y : ℕ} {q : List ℕ} (h : PathTo V r x q)
    (hy : y < V) (hxy : 0 < r x y) : PathTo V r y (q ++ [y]) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, by simp, ?_, ?_⟩
  · cases q with
    | nil => simp at h1
    | cons a l => simpa using h1
  · intro z hz
    simp only [List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact h3 z hz
    · exact hy
  · refine h4.append (List.isChain_singleton _) ?_
    intro a ha b hb
    rw [h2] at ha
    simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at ha hb
    subst ha hb
    exact hxy

/-- INTERNAL: one positive arc out of a reachable vertex raises the distance by at
most one. -/
theorem resDist_snoc {V : ℕ} {r : ℕ → ℕ → ℕ} {x y : ℕ} (hx : ∃ q, PathTo V r x q)
    (hy : y < V) (hxy : 0 < r x y) :
    (∃ q, PathTo V r y q) ∧ resDist V r y ≤ resDist V r x + 1 := by
  obtain ⟨q, hq, hl⟩ := resDist_spec hx
  have h := hq.snoc hy hxy
  refine ⟨⟨_, h⟩, (resDist_le h).trans ?_⟩
  simp [hl]

/-- INTERNAL: on a shortest residual path, the `i`-th vertex is at distance exactly
`i + 1` (the BFS level labelling of EK1972).
TEXLINE: sections/scales.tex:13-18 -/
theorem shortest_dist {V : ℕ} {r : ℕ → ℕ → ℕ} {p : List ℕ} (hp : IsResPath V r p)
    (hmin : ∀ q, IsResPath V r q → p.length ≤ q.length) (i : ℕ) (hi : i < p.length) :
    (∃ q, PathTo V r p[i] q) ∧ resDist V r p[i] = i + 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hp0 : ∀ h : 0 < p.length, p[0] = 0 := by
    intro h
    cases p with
    | nil => simp at h
    | cons a l => simpa using h1
  have hlast : ∀ h : p.length - 1 < p.length, p[p.length - 1] = V - 1 := by
    intro h
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem h] at h2
    simpa using h2
  have hlt : ∀ j (hj : j < p.length), p[j] < V := fun j hj => h3 _ (List.getElem_mem hj)
  have A : ∀ j (hj : j < p.length), (∃ q, PathTo V r p[j] q) ∧ resDist V r p[j] ≤ j + 1 := by
    intro j
    induction j with
    | zero =>
      intro hj
      have hq : PathTo V r p[0] [p[0]] := by
        refine ⟨by simp [hp0 hj], by simp, ?_, List.isChain_singleton _⟩
        intro z hz
        simp only [List.mem_singleton] at hz
        exact hz ▸ hlt 0 hj
      exact ⟨⟨_, hq⟩, resDist_le hq⟩
    | succ j ih =>
      intro hj
      obtain ⟨hr, hd⟩ := ih (by omega)
      obtain ⟨hr', hd'⟩ := resDist_snoc hr (hlt _ hj) (h4.getElem j hj)
      exact ⟨hr', by omega⟩
  have C : ∀ j (hj : j < p.length) k (hk : k ≤ j),
      resDist V r p[j] ≤ resDist V r (p[k]'(by omega)) + (j - k) := by
    intro j
    induction j with
    | zero =>
      intro hj k hk
      obtain rfl : k = 0 := by omega
      simp
    | succ j ih =>
      intro hj k hk
      rcases Nat.lt_or_ge j k with hjk | hjk
      · obtain rfl : k = j + 1 := by omega
        simp
      · have := ih (by omega) k hjk
        have := (resDist_snoc (A j (by omega)).1 (hlt _ hj) (h4.getElem j hj)).2
        omega
  have B : p.length ≤ resDist V r (V - 1) := by
    obtain ⟨q, hq, hl⟩ := resDist_spec (y := V - 1) ⟨p, h1, h2, h3, h4⟩
    exact hl ▸ hmin q hq
  refine ⟨(A i hi).1, le_antisymm (A i hi).2 ?_⟩
  have := C (p.length - 1) (by omega) i (by omega)
  rw [hlast (by omega)] at this
  omega

/-- INTERNAL: membership in the arc list of a vertex list. -/
theorem arc_of_mem_zip {p : List ℕ} {x y : ℕ} (h : (x, y) ∈ p.zip p.tail) :
    ∃ i, ∃ hi : i + 1 < p.length, p[i] = x ∧ p[i + 1] = y := by
  rw [List.mem_iff_getElem] at h
  obtain ⟨i, hi, he⟩ := h
  simp only [List.length_zip, List.length_tail] at hi
  refine ⟨i, by omega, ?_⟩
  rw [List.getElem_zip, List.getElem_tail] at he
  simp only [Prod.mk.injEq] at he
  exact he

/-- INTERNAL: every arc of a shortest residual path goes up exactly one level.
TEXLINE: sections/scales.tex:13-18 -/
theorem shortest_arc {V : ℕ} {r : ℕ → ℕ → ℕ} {p : List ℕ} (hp : IsResPath V r p)
    (hmin : ∀ q, IsResPath V r q → p.length ≤ q.length) {x y : ℕ}
    (h : (x, y) ∈ p.zip p.tail) :
    (∃ q, PathTo V r x q) ∧ (∃ q, PathTo V r y q) ∧ resDist V r y = resDist V r x + 1 ∧
      x < V ∧ y < V ∧ 0 < r x y ∧ resDist V r x < p.length := by
  obtain ⟨i, hi, rfl, rfl⟩ := arc_of_mem_zip h
  obtain ⟨hx, dx⟩ := shortest_dist hp hmin i (by omega)
  obtain ⟨hy, dy⟩ := shortest_dist hp hmin (i + 1) hi
  exact ⟨hx, hy, by omega, hp.2.2.1 _ (List.getElem_mem _), hp.2.2.1 _ (List.getElem_mem _),
    hp.2.2.2.getElem i hi, by omega⟩

/-- INTERNAL: a shortest residual path is simple, so it has at most `V` vertices.
TEXLINE: sections/scales.tex:13-18 -/
theorem shortest_length_le {V : ℕ} {r : ℕ → ℕ → ℕ} {p : List ℕ} (hp : IsResPath V r p)
    (hmin : ∀ q, IsResPath V r q → p.length ≤ q.length) : p.length ≤ V := by
  have hnd : p.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro i j hij
    have hi := (shortest_dist hp hmin i i.2).2
    have hj := (shortest_dist hp hmin j j.2).2
    simp only at hij
    rw [hij] at hi
    exact Fin.ext (by omega)
  rw [← List.toFinset_card_of_nodup hnd]
  calc p.toFinset.card ≤ (Finset.range V).card := by
        apply Finset.card_le_card
        intro x hx
        simpa using hp.2.2.1 x (List.mem_toFinset.mp hx)
    _ = V := Finset.card_range V

/-- INTERNAL: an arc that is positive after the push but was not before is the
reversal of an arc of the augmenting path. -/
theorem rev_of_new_arc {r : ℕ → ℕ → ℕ} {p : List ℕ} {a x y : ℕ} (h0 : r x y = 0)
    (h1 : 0 < pushAlong r p a x y) : (y, x) ∈ p.zip p.tail := by
  rw [← List.count_pos_iff]
  unfold pushAlong at h1
  rw [h0] at h1
  rcases Nat.eq_zero_or_pos ((p.zip p.tail).count (y, x)) with hc | hc
  · rw [hc] at h1
    simp at h1
  · exact hc

/-- INTERNAL: one shortest augmentation never decreases residual distances
(EK1972's monotonicity lemma), stated against an arbitrary path after the step.
TEXLINE: sections/scales.tex:13-18 -/
theorem step_mono {V : ℕ} {r r' : ℕ → ℕ → ℕ} (hs : EKStep V r r') :
    ∀ (q : List ℕ) (y : ℕ), PathTo V r' y q →
      (∃ q', PathTo V r y q') ∧ resDist V r y ≤ q.length := by
  obtain ⟨p, hp, hmin, a, -, -, rfl⟩ := hs
  intro q
  induction q using List.reverseRecOn with
  | nil => intro y h; simp [PathTo] at h
  | append_singleton l z ih =>
    intro y h
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.some.injEq] at h2
    subst h2
    rcases List.eq_nil_or_concat l with rfl | ⟨l', x, rfl⟩
    · simp only [List.nil_append, List.head?_cons, Option.some.injEq] at h1
      subst h1
      have hq : PathTo V r 0 [0] := ⟨rfl, rfl, h3, List.isChain_singleton _⟩
      exact ⟨⟨_, hq⟩, by simpa using resDist_le hq⟩
    · simp only [List.concat_eq_append] at h1 h3 h4 ih
      rw [List.isChain_append] at h4
      obtain ⟨h4a, -, h4c⟩ := h4
      have hxz : 0 < pushAlong r p a x z := h4c x (by simp) z (by simp)
      have hl : PathTo V (pushAlong r p a) x (l' ++ [x]) := by
        refine ⟨?_, by simp, fun w hw => h3 w (List.mem_append_left _ hw), h4a⟩
        cases l' with
        | nil => simpa using h1
        | cons b l'' => simpa using h1
      obtain ⟨hrx, hdx⟩ := ih x hl
      have hzV : z < V := h3 z (by simp)
      by_cases hpos : 0 < r x z
      · obtain ⟨hrz, hdz⟩ := resDist_snoc hrx hzV hpos
        refine ⟨hrz, ?_⟩
        simp only [List.concat_eq_append, List.length_append, List.length_singleton] at hdx ⊢
        omega
      · have hrev := rev_of_new_arc (by omega) hxz
        obtain ⟨hrz, -, hd, -⟩ := shortest_arc hp hmin hrev
        refine ⟨hrz, ?_⟩
        simp only [List.concat_eq_append, List.length_append, List.length_singleton] at hdx ⊢
        omega

/-- INTERNAL: distances only grow along one step, for vertices reachable after it. -/
theorem step_reach_mono {V : ℕ} {r r' : ℕ → ℕ → ℕ} (hs : EKStep V r r') {y : ℕ}
    (hy : ∃ q, PathTo V r' y q) :
    (∃ q, PathTo V r y q) ∧ resDist V r y ≤ resDist V r' y := by
  obtain ⟨q, hq, hl⟩ := resDist_spec hy
  exact hl ▸ step_mono hs q y hq

/-- INTERNAL: every shortest augmentation saturates a critical arc `(u, v)` going
up one level, with the tail's level below `V`.
TEXLINE: sections/scales.tex:13-18 -/
theorem critical_arc {V : ℕ} {r r' : ℕ → ℕ → ℕ} (hs : EKStep V r r') :
    ∃ u v, u < V ∧ v < V ∧ (∃ q, PathTo V r u q) ∧ resDist V r u < V ∧ 0 < r u v ∧
      r' u v = 0 ∧ resDist V r v = resDist V r u + 1 := by
  obtain ⟨p, hp, hmin, a, -, ⟨⟨u, v⟩, he, hea⟩, rfl⟩ := hs
  obtain ⟨hu, -, hd, huV, hvV, hpos, hlt⟩ := shortest_arc hp hmin he
  have hlen := shortest_length_le hp hmin
  refine ⟨u, v, huV, hvV, hu, by omega, hpos, ?_, hd⟩
  have hvu : (p.zip p.tail).count (v, u) = 0 := by
    rw [List.count_eq_zero]
    intro hrev
    have := (shortest_arc hp hmin hrev).2.2.1
    omega
  have huv : 0 < (p.zip p.tail).count (u, v) := List.count_pos_iff.mpr he
  unfold pushAlong
  simp only at hea
  rw [hvu, hea]
  have : a ≤ a * (p.zip p.tail).count (u, v) := Nat.le_mul_of_pos_right a huv
  omega

/-- INTERNAL: if an arc reappears in the residual graph, the step that brought it back
pushed along its reversal, one level down.
TEXLINE: sections/scales.tex:13-18 -/
theorem reverse_arc {V : ℕ} {r r' : ℕ → ℕ → ℕ} (hs : EKStep V r r') {u v : ℕ}
    (h0 : r u v = 0) (h1 : 0 < r' u v) :
    (∃ q, PathTo V r v q) ∧ (∃ q, PathTo V r u q) ∧ resDist V r u = resDist V r v + 1 := by
  obtain ⟨p, hp, hmin, a, -, -, rfl⟩ := hs
  obtain ⟨hv, hu, hd, -⟩ := shortest_arc hp hmin (rev_of_new_arc h0 h1)
  exact ⟨hv, hu, hd⟩

end EKBound

/-- **Edmonds–Karp.**  Augmenting along shortest residual paths by the bottleneck
capacity, from any starting capacities on `V ≥ 2` vertices, makes at most `V³`
augmentations.
PAPER: sections/scales.tex:13-18
BORROWED: Edmonds and Karp, J. ACM 19 (1972), Theorem 1 (`EK1972`): shortest augmenting
paths use `O(VE)` augmentations; here `E ≤ V²`, so `V · E / 2 ≤ V³`.  Proved here, not
assumed: the injective charge (critical arc, tail level) into `[0, V)³`. -/
theorem edmondsKarp_bound (V : ℕ) (hV : 2 ≤ V) (K : ℕ) (res : ℕ → ℕ → ℕ → ℕ)
    (h : ∀ k < K, EKStep V (res k) (res (k + 1))) : K ≤ V ^ 3 := by
  open EKBound in
  -- distances are monotone along the run, for vertices reachable at the later step
  have hiter : ∀ i j, i ≤ j → j ≤ K → ∀ y, (∃ q, PathTo V (res j) y q) →
      (∃ q, PathTo V (res i) y q) ∧ resDist V (res i) y ≤ resDist V (res j) y := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _ y hy; exact ⟨hy, le_rfl⟩
    | succ j hij ih =>
      intro hjK y hy
      obtain ⟨h1, h2⟩ := step_reach_mono (h j (by omega)) hy
      obtain ⟨h3, h4⟩ := ih (by omega) y h1
      exact ⟨h3, h4.trans h2⟩
  -- a zero residual that later becomes positive was raised at some intermediate step
  have hfind : ∀ u v k0 j, k0 ≤ j → res k0 u v = 0 → 0 < res j u v →
      ∃ k', k0 ≤ k' ∧ k' < j ∧ res k' u v = 0 ∧ 0 < res (k' + 1) u v := by
    intro u v k0 j hj h0
    induction j, hj using Nat.le_induction with
    | base => intro hp; omega
    | succ j hj ih =>
      intro hp
      by_cases hpj : 0 < res j u v
      · obtain ⟨k', h1, h2, h3, h4⟩ := ih hpj
        exact ⟨k', h1, by omega, h3, h4⟩
      · exact ⟨j, hj, by omega, by omega, hp⟩
  have hB : ∀ k < K, ∃ u v, u < V ∧ v < V ∧ (∃ q, PathTo V (res k) u q) ∧
      resDist V (res k) u < V ∧ 0 < res k u v ∧ res (k + 1) u v = 0 ∧
      resDist V (res k) v = resDist V (res k) u + 1 := fun k hk => critical_arc (h k hk)
  choose! u v hu hv hreach hdlt hpos hzero hdv using hB
  -- a critical arc that repeats has a strictly higher tail level
  have key : ∀ k1 k2, k1 < k2 → k2 < K → u k1 = u k2 → v k1 = v k2 →
      resDist V (res k1) (u k1) < resDist V (res k2) (u k2) := by
    intro k1 k2 h12 h2K hu12 hv12
    have hz := hzero k1 (by omega)
    have hp2 := hpos k2 h2K
    rw [← hu12, ← hv12] at hp2
    obtain ⟨k', hk1, hk2, hk0, hk'⟩ := hfind _ _ _ _ (by omega : k1 + 1 ≤ k2) hz hp2
    obtain ⟨hrv, -, hd'⟩ := reverse_arc (h k' (by omega)) hk0 hk'
    have m1 := (hiter k1 k' (by omega) (by omega) (v k1) hrv).2
    have hr2 := hreach k2 h2K
    rw [← hu12] at hr2 ⊢
    have m2 := (hiter k' k2 (by omega) (by omega) (u k1) hr2).2
    have := hdv k1 (by omega)
    omega
  -- charge each step to (critical arc, tail level); the charge is injective
  let f : ℕ → ℕ × ℕ × ℕ := fun k => (u k, v k, resDist V (res k) (u k))
  have hmaps : Set.MapsTo f (Finset.range K : Set ℕ)
      (Finset.range V ×ˢ Finset.range V ×ˢ Finset.range V : Finset (ℕ × ℕ × ℕ)) := by
    intro k hk
    simp only [Finset.coe_range, Set.mem_Iio] at hk
    simp [f, hu k hk, hv k hk, hdlt k hk]
  have hinj : Set.InjOn f (Finset.range K : Set ℕ) := by
    intro k1 hk1 k2 hk2 he
    simp only [Finset.coe_range, Set.mem_Iio] at hk1 hk2
    simp only [f, Prod.mk.injEq] at he
    obtain ⟨e1, e2, e3⟩ := he
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h12 | h21
    · have := key k1 k2 h12 hk2 e1 e2
      omega
    · have := key k2 k1 h21 hk1 e1.symm e2.symm
      omega
  have hc := Finset.card_le_card_of_injOn f hmaps hinj
  simp only [Finset.card_range, Finset.card_product] at hc
  calc K ≤ V * (V * V) := hc
    _ = V ^ 3 := by ring

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r8 · proved · `edmondsKarp_bound` from scratch via the `EKBound` level/critical-arc lemmas; no sorry
-/
