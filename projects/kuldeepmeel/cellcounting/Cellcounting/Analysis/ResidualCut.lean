import Cellcounting.Analysis.EdmondsKarpBound

/-!
# Residual capacities, augmentation and the min-cut bound

Pure flow theory behind `maxFlow_correct` (`sections/scales.tex:13-22`), stated on
capacity functions `ℕ → ℕ → ℕ` on the vertices `0, …, V - 1` (source `0`, sink `V - 1`).

* `ResInv V cap res g F`: the residual capacities `res` are `cap - g` for a skew-symmetric
  net flow `g`, conserved away from the source and sink, of value `F`.
* `resInv_init`: before any augmentation, `res = cap`, `g = 0`, `F = 0`.
* `resInv_push`: augmenting along a simple residual path `p` by `a`, no more than any
  residual capacity on it (`pushAlong res p a`), keeps the invariant with value `F + a`.
* `resInv_flow`: the positive part of `g` is an integral flow (`IsFlow`) of value `F`.
* `resInv_cut`: if a vertex set containing the source but not the sink has no residual
  arc leaving it, no flow has value above `F` (max-flow/min-cut, the easy half).
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Finset

/-- INTERNAL: the residual invariant of the augmenting-path algorithm.
TEXLINE: sections/scales.tex:13-20 -/
structure ResInv (V : ℕ) (cap res : ℕ → ℕ → ℕ) (g : ℕ → ℕ → ℤ) (F : ℕ) : Prop where
  res_eq : ∀ u v, u < V → v < V → (res u v : ℤ) = cap u v - g u v
  skew : ∀ u v, g u v = - g v u
  conserve : ∀ v, 0 < v → v + 1 < V → ∑ w ∈ range V, g v w = 0
  value : ∑ w ∈ range V, g 0 w = F

/-- INTERNAL: the invariant holds before the first augmentation. -/
theorem resInv_init (V : ℕ) (cap : ℕ → ℕ → ℕ) : ResInv V cap cap (fun _ _ => 0) 0 :=
  ⟨fun _ _ _ _ => by simp, fun _ _ => by simp, fun _ _ _ => by simp, by simp⟩

/-- INTERNAL: the positive part of the net flow is an integral flow of the same value. -/
theorem resInv_flow {V : ℕ} {cap res : ℕ → ℕ → ℕ} {g : ℕ → ℕ → ℤ} {F : ℕ}
    (h : ResInv V cap res g F) :
    ∃ f, IsFlow V cap f ∧ flowValue V f = F := by
  let f : ℕ → ℕ → ℕ := fun u v => if u < V ∧ v < V then (g u v).toNat else 0
  have hnet : ∀ u v, u < V → v < V → (f u v : ℤ) - f v u = g u v := by
    intro u v hu hv
    simp only [f, if_pos (And.intro hu hv), if_pos (And.intro hv hu)]
    rw [h.skew v u]
    exact Int.toNat_sub_toNat_neg _
  refine ⟨f, ⟨fun u v => ?_, fun v hv0 hv1 => ?_⟩, ?_⟩
  · simp only [f]
    split_ifs with huv
    · have := h.res_eq u v huv.1 huv.2
      have hr : (0 : ℤ) ≤ res u v := by positivity
      exact Int.toNat_le.2 (by linarith)
    · exact Nat.zero_le _
  · have key : (∑ u ∈ range V, (f u v : ℤ)) - ∑ w ∈ range V, (f v w : ℤ) = 0 := by
      rw [← Finset.sum_sub_distrib]
      calc ∑ u ∈ range V, ((f u v : ℤ) - f v u) = ∑ u ∈ range V, - g v u :=
            Finset.sum_congr rfl fun u hu => by
              rw [hnet u v (Finset.mem_range.1 hu) (by omega), h.skew]
        _ = 0 := by rw [Finset.sum_neg_distrib, h.conserve v hv0 hv1, neg_zero]
    have : ((∑ u ∈ range V, f u v : ℕ) : ℤ) = ((∑ w ∈ range V, f v w : ℕ) : ℤ) := by
      push_cast; linarith
    exact_mod_cast this
  · unfold flowValue
    rw [← Finset.sum_sub_distrib, ← h.value]
    by_cases hV : 0 < V
    · exact Finset.sum_congr rfl fun w hw => hnet 0 w hV (Finset.mem_range.1 hw)
    · simp [show V = 0 by omega]

/-- INTERNAL: the net flow of an integral flow out of a vertex set containing the source
but not the sink is its value. -/
theorem flow_out_of_set {V : ℕ} {cap : ℕ → ℕ → ℕ} {h : ℕ → ℕ → ℕ} (hh : IsFlow V cap h)
    (S : Finset ℕ) (hS : S ⊆ range V) (h0 : 0 ∈ S) (ht : V - 1 ∉ S) :
    ∑ u ∈ S, ∑ w ∈ range V \ S, ((h u w : ℤ) - h w u) = flowValue V h := by
  have hsplit : ∀ u ∈ S, ∑ w ∈ range V, ((h u w : ℤ) - h w u) =
      ∑ w ∈ range V \ S, ((h u w : ℤ) - h w u) + ∑ w ∈ S, ((h u w : ℤ) - h w u) :=
    fun u _ => (Finset.sum_sdiff hS).symm
  have hin : ∑ u ∈ S, ∑ w ∈ S, ((h u w : ℤ) - h w u) = 0 := by
    simp only [Finset.sum_sub_distrib]
    rw [Finset.sum_comm (s := S) (t := S) (f := fun u w => (h w u : ℤ))]
    ring
  have hcons : ∀ u ∈ S, u ≠ 0 → ∑ w ∈ range V, ((h u w : ℤ) - h w u) = 0 := by
    intro u hu hu0
    have huV := Finset.mem_range.1 (hS hu)
    have hne : u ≠ V - 1 := fun e => ht (e ▸ hu)
    have := hh.conserve u (by omega) (by omega)
    rw [Finset.sum_sub_distrib]
    have e : ((∑ w ∈ range V, h w u : ℕ) : ℤ) = ((∑ w ∈ range V, h u w : ℕ) : ℤ) := by rw [this]
    push_cast at e
    linarith
  calc ∑ u ∈ S, ∑ w ∈ range V \ S, ((h u w : ℤ) - h w u)
      = ∑ u ∈ S, ∑ w ∈ range V, ((h u w : ℤ) - h w u) := by
        rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hin, add_zero]
    _ = ∑ w ∈ range V, ((h 0 w : ℤ) - h w 0) := by
        rw [Finset.sum_eq_single_of_mem 0 h0 fun u hu hu0 => hcons u hu hu0]
    _ = flowValue V h := by unfold flowValue; rw [Finset.sum_sub_distrib]

/-- INTERNAL: max-flow/min-cut, the half the algorithm needs: a vertex set containing
the source but not the sink, with no residual arc leaving it, bounds every flow by `F`.
TEXLINE: sections/scales.tex:13-20 -/
theorem resInv_cut {V : ℕ} {cap res : ℕ → ℕ → ℕ} {g : ℕ → ℕ → ℤ} {F : ℕ}
    (hinv : ResInv V cap res g F) (S : Finset ℕ) (hS : S ⊆ range V) (h0 : 0 ∈ S)
    (ht : V - 1 ∉ S) (hclosed : ∀ u ∈ S, ∀ w ∈ range V \ S, res u w = 0)
    (h : ℕ → ℕ → ℕ) (hh : IsFlow V cap h) : flowValue V h ≤ F := by
  -- the cut capacity bounds every flow
  have hle : flowValue V h ≤ ∑ u ∈ S, ∑ w ∈ range V \ S, (cap u w : ℤ) := by
    rw [← flow_out_of_set hh S hS h0 ht]
    refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun w _ => ?_
    have := hh.le_cap u w
    have : (0 : ℤ) ≤ h w u := by positivity
    have : (h u w : ℤ) ≤ cap u w := by exact_mod_cast hh.le_cap u w
    linarith
  -- and the current net flow saturates the cut
  have hsat : ∑ u ∈ S, ∑ w ∈ range V \ S, (cap u w : ℤ) = F := by
    have hcap : ∀ u ∈ S, ∀ w ∈ range V \ S, (cap u w : ℤ) = g u w := by
      intro u hu w hw
      have := hinv.res_eq u w (Finset.mem_range.1 (hS hu))
        (Finset.mem_range.1 (Finset.mem_sdiff.1 hw).1)
      rw [hclosed u hu w hw] at this
      push_cast at this
      linarith
    rw [Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun w hw => hcap u hu w hw]
    have hin : ∑ u ∈ S, ∑ w ∈ S, g u w = 0 := by
      have e : ∑ u ∈ S, ∑ w ∈ S, g u w = - ∑ u ∈ S, ∑ w ∈ S, g u w := by
        conv_lhs => rw [Finset.sum_comm]
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun u _ => by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun w _ => hinv.skew w u
      linarith
    have hcons : ∀ u ∈ S, u ≠ 0 → ∑ w ∈ range V, g u w = 0 := by
      intro u hu hu0
      have huV := Finset.mem_range.1 (hS hu)
      have hne : u ≠ V - 1 := fun e => ht (e ▸ hu)
      exact hinv.conserve u (by omega) (by omega)
    calc ∑ u ∈ S, ∑ w ∈ range V \ S, g u w
        = ∑ u ∈ S, ∑ w ∈ range V, g u w := by
          rw [← add_zero (∑ u ∈ S, ∑ w ∈ range V \ S, g u w), ← hin, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun u _ => Finset.sum_sdiff hS
      _ = ∑ w ∈ range V, g 0 w :=
          Finset.sum_eq_single_of_mem 0 h0 fun u hu hu0 => hcons u hu hu0
      _ = F := hinv.value
  linarith

/-- INTERNAL: summing the multiplicities of the arcs `(v, w)` over all heads `w`. -/
theorem sum_count_fst (V v : ℕ) (l : List (ℕ × ℕ)) (hl : ∀ e ∈ l, e.2 < V) :
    ∑ w ∈ range V, l.count (v, w) = (l.map Prod.fst).count v := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.count_cons, List.map_cons, Finset.sum_add_distrib]
    rw [ih fun x hx => hl x (List.mem_cons_of_mem _ hx)]
    congr 1
    have he := hl e List.mem_cons_self
    obtain ⟨e1, e2⟩ := e
    simp only [beq_iff_eq, Prod.mk.injEq]
    by_cases h1 : e1 = v
    · subst h1
      rw [Finset.sum_eq_single_of_mem e2 (Finset.mem_range.2 he) fun w _ hw => by
        simp [Ne.symm hw]]
      simp
    · simp [h1]

/-- INTERNAL: summing the multiplicities of the arcs `(w, v)` over all tails `w`. -/
theorem sum_count_snd (V v : ℕ) (l : List (ℕ × ℕ)) (hl : ∀ e ∈ l, e.1 < V) :
    ∑ w ∈ range V, l.count (w, v) = (l.map Prod.snd).count v := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.count_cons, List.map_cons, Finset.sum_add_distrib]
    rw [ih fun x hx => hl x (List.mem_cons_of_mem _ hx)]
    congr 1
    have he := hl e List.mem_cons_self
    obtain ⟨e1, e2⟩ := e
    simp only [beq_iff_eq, Prod.mk.injEq]
    by_cases h2 : e2 = v
    · subst h2
      rw [Finset.sum_eq_single_of_mem e1 (Finset.mem_range.2 he) fun w _ hw => by
        simp [Ne.symm hw]]
      simp
    · simp [h2]

/-- INTERNAL: the tails of the arcs of a vertex list. -/
theorem arcs_map_fst (p : List ℕ) : (p.zip p.tail).map Prod.fst = p.dropLast := by
  induction p with
  | nil => rfl
  | cons x t ih =>
    cases t with
    | nil => rfl
    | cons y t' =>
      simp only [List.tail_cons, List.zip_cons_cons, List.map_cons, List.dropLast_cons₂]
      rw [← ih]; rfl

/-- INTERNAL: the heads of the arcs of a vertex list. -/
theorem arcs_map_snd (p : List ℕ) : (p.zip p.tail).map Prod.snd = p.tail :=
  List.map_snd_zip (by simp)

/-- INTERNAL: augmenting along a simple residual path by at most its bottleneck keeps
the residual invariant and adds the amount to the value.
TEXLINE: sections/scales.tex:13-20 -/
theorem resInv_push {V : ℕ} {cap res : ℕ → ℕ → ℕ} {g : ℕ → ℕ → ℤ} {F : ℕ}
    (hinv : ResInv V cap res g F) (hV : 2 ≤ V) (p : List ℕ) (hp : IsResPath V res p)
    (hnd : p.Nodup) (a : ℕ) (ha : ∀ e ∈ p.zip p.tail, a ≤ res e.1 e.2) :
    ResInv V cap (pushAlong res p a)
      (fun u v => g u v + a * ((p.zip p.tail).count (u, v) : ℤ) -
        a * ((p.zip p.tail).count (v, u) : ℤ)) (F + a) := by
  obtain ⟨hhead, hlast, hlt, -⟩ := hp
  set A := p.zip p.tail with hA
  have hAmem : ∀ e ∈ A, e.1 < V ∧ e.2 < V := fun e he =>
    ⟨hlt _ (List.of_mem_zip he).1, hlt _ (List.mem_of_mem_tail (List.of_mem_zip he).2)⟩
  have hAnd : A.Nodup := by
    have : (A.map Prod.fst).Nodup := by rw [hA, arcs_map_fst]; exact hnd.sublist (List.dropLast_sublist _)
    exact this.of_map _
  obtain ⟨t, rfl⟩ : ∃ t, p = 0 :: t := by
    cases p with
    | nil => simp at hhead
    | cons x t => simp at hhead; exact ⟨t, by rw [hhead]⟩
  have hne : (0 :: t) ≠ [] := List.cons_ne_nil _ _
  have hlastv : (0 :: t).getLast hne = V - 1 := by
    rw [List.getLast?_eq_getLast hne] at hlast; exact Option.some.inj hlast
  have hdl : ∀ v, (0 :: t).count v = ((0 :: t).dropLast).count v + if V - 1 = v then 1 else 0 := by
    intro v
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    rw [List.count_append, hlastv]
    simp [List.count_singleton]
  have hout : ∀ v, ∑ w ∈ range V, A.count (v, w) = ((0 :: t).dropLast).count v := fun v => by
    rw [sum_count_fst V v A fun e he => (hAmem e he).2, hA, arcs_map_fst]
  have hin : ∀ v, ∑ w ∈ range V, A.count (w, v) = t.count v := fun v => by
    rw [sum_count_snd V v A fun e he => (hAmem e he).1, hA, arcs_map_snd]; rfl
  refine ⟨fun u v hu hv => ?_, fun u v => by rw [hinv.skew u v]; ring, fun v hv0 hv1 => ?_, ?_⟩
  · have hc : A.count (u, v) ≤ 1 := by rw [List.Nodup.count hAnd]; split_ifs <;> omega
    have hle : a * A.count (u, v) ≤ res u v + a * A.count (v, u) := by
      rcases Nat.lt_or_ge (A.count (u, v)) 1 with h0 | h1
      · rw [show A.count (u, v) = 0 by omega]; simp
      · have hmem : (u, v) ∈ A := List.count_pos_iff.1 (by omega)
        rw [show A.count (u, v) = 1 by omega, mul_one]
        exact (ha _ hmem).trans (Nat.le_add_right _ _)
    unfold pushAlong
    rw [← hA]
    push_cast [hle]
    rw [hinv.res_eq u v hu hv]
    ring
  · simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hinv.conserve v hv0 hv1]
    simp only [← Finset.mul_sum]
    have h1 : ((∑ w ∈ range V, A.count (v, w) : ℕ) : ℤ) = ((∑ w ∈ range V, A.count (w, v) : ℕ) : ℤ) := by
      rw [hout, hin]
      have e : (0 :: t).count v = t.count v := by
        rw [List.count_cons]; simp [Ne.symm (Nat.pos_iff_ne_zero.1 hv0)]
      have := hdl v
      rw [if_neg (by omega), add_zero, e] at this
      rw [this]
    push_cast at h1
    rw [h1]; ring
  · simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hinv.value]
    simp only [← Finset.mul_sum]
    have h0 : t.count 0 = 0 := List.count_eq_zero.2 (List.nodup_cons.1 hnd).1
    have h1 : ((0 :: t).dropLast).count 0 = 1 := by
      have := hdl 0
      rw [if_neg (by omega)] at this
      rw [List.count_cons_self, h0] at this
      omega
    have e1 : ((∑ w ∈ range V, A.count (0, w) : ℕ) : ℤ) = 1 := by rw [hout, h1]; rfl
    have e2 : ((∑ w ∈ range V, A.count (w, 0) : ℕ) : ℤ) = 0 := by rw [hin, h0]; rfl
    push_cast at e1 e2
    rw [e1, e2]; push_cast; ring

end Cellcounting.Analysis
