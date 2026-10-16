import Cellcounting.Analysis.FlowNet
import Cellcounting.Interface.Pseudocode

/-!
# A flow of value `Σ r` in the feasibility network is a feasible table

`sections/scales.tex:8-13`: "An integral flow of value `N = Σ_i r_i = Σ_j c_j` is
exactly a feasible table: at that value every arc incident to the source or sink is
saturated."  In the network `netCap m n r c b` (`Analysis/FlowNet.lean`):

* `flowValue_le_netCap`: every flow has value at most `Σ r` (the cut at the source);
* `netSum_eq_of_feasible`: a feasible table forces `Σ r = Σ c`;
* `transport_flow_iff`: when `Σ r = Σ c`, a flow of value `Σ r` exists exactly when
  `Ω(r, c, b)` is nonempty.  A table `X` is the flow `X i j` on the row-to-column arcs
  with saturated source and sink arcs; conversely the row-to-column part of a flow of
  value `Σ r` is a table.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

/-- The instance with margins `r, c` and bounds `b` read through `ℕ` indices. -/
abbrev netInst (m n : ℕ) (r c : ℕ → ℕ) (b : ℕ → ℕ → ℕ) : Instance :=
  ⟨m, n, fun i => r i.val, fun j => c j.val, fun i j => b i.val j.val⟩

/-- INTERNAL: a sum over `range N` of a function supported on `[a, a + k)`. -/
theorem sum_range_block {M : Type} [AddCommMonoid M] (N a k : ℕ) (g : ℕ → M)
    (hN : a + k ≤ N) (hz : ∀ w, w < N → (w < a ∨ a + k ≤ w) → g w = 0) :
    ∑ w ∈ Finset.range N, g w = ∑ j ∈ Finset.range k, g (a + j) := by
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive g (Nat.zero_le a) (by omega : a ≤ N),
    ← Finset.sum_Ico_consecutive g (by omega : a ≤ a + k) hN,
    Finset.sum_Ico_eq_sum_range g a (a + k)]
  rw [Finset.sum_eq_zero (s := Finset.Ico 0 a) fun w hw => hz w (by simp at hw; omega)
      (by simp at hw; omega),
    Finset.sum_eq_zero (s := Finset.Ico (a + k) N) fun w hw => hz w (by simp at hw; omega)
      (by simp at hw; omega)]
  simp

/-- Every flow in the feasibility network has value at most `Σ r`: the arcs out of the
source carry at most `r i` each, and no arc enters it.
PAPER: sections/scales.tex:11-13 -/
theorem flowValue_le_netCap (m n : ℕ) (r c : ℕ → ℕ) (b : ℕ → ℕ → ℕ) (f : ℕ → ℕ → ℕ)
    (hf : IsFlow (m + n + 2) (netCap m n r c b) f) :
    flowValue (m + n + 2) f ≤ ∑ i ∈ Finset.range m, (r i : ℤ) := by
  have hsrc : ∑ v ∈ Finset.range (m + n + 2), (f 0 v : ℤ) ≤ ∑ i ∈ Finset.range m, (r i : ℤ) := by
    calc ∑ v ∈ Finset.range (m + n + 2), (f 0 v : ℤ)
        ≤ ∑ v ∈ Finset.range (m + n + 2), (netCap m n r c b 0 v : ℤ) :=
          Finset.sum_le_sum fun v _ => by exact_mod_cast hf.le_cap 0 v
      _ = ∑ i ∈ Finset.range m, (r i : ℤ) := by
          rw [sum_range_block (m + n + 2) 1 m _ (by omega) fun w _ hw => by
            simp only [netCap]; split_ifs <;> first | rfl | omega]
          refine Finset.sum_congr rfl fun j hj => ?_
          simp only [Finset.mem_range] at hj
          have : netCap m n r c b 0 (1 + j) = r j := by
            unfold netCap; rw [if_pos (by omega)]; congr 1; omega
          rw [this]
  have hin : 0 ≤ ∑ u ∈ Finset.range (m + n + 2), (f u 0 : ℤ) :=
    Finset.sum_nonneg fun _ _ => by positivity
  unfold flowValue
  linarith

/-- A feasible table has equal margin totals.
INTERNAL: both totals are the sum of all entries of the table.
TEXLINE: sections/scales.tex:11-12 -/
theorem netSum_eq_of_feasible (m n : ℕ) (r c : ℕ → ℕ) (b : ℕ → ℕ → ℕ)
    (h : Pseudocode.feasible (netInst m n r c b)) :
    ∑ i ∈ Finset.range m, r i = ∑ j ∈ Finset.range n, c j := by
  obtain ⟨X, hX⟩ := h
  simp only [Instance.Omega, Finset.mem_filter] at hX
  obtain ⟨-, hrow, hcol⟩ := hX
  rw [← Fin.sum_univ_eq_sum_range r, ← Fin.sum_univ_eq_sum_range c]
  calc ∑ i : Fin m, r i = ∑ i : Fin m, ∑ j : Fin n, X i j := by
        refine Finset.sum_congr rfl fun i _ => (hrow i).symm
    _ = ∑ j : Fin n, ∑ i : Fin m, X i j := Finset.sum_comm
    _ = ∑ j : Fin n, c j := Finset.sum_congr rfl fun j _ => hcol j

/-- INTERNAL: an arc function below the network capacities vanishes where they do. -/
theorem tf_zero {m n : ℕ} {r c : ℕ → ℕ} {b : ℕ → ℕ → ℕ} {g : ℕ → ℕ → ℕ}
    (hg : ∀ u v, g u v ≤ netCap m n r c b u v) (u v : ℕ)
    (h : ¬ (u = 0 ∧ 1 ≤ v ∧ v ≤ m) ∧ ¬ (1 ≤ u ∧ u ≤ m ∧ m + 1 ≤ v ∧ v ≤ m + n) ∧
      ¬ (m + 1 ≤ u ∧ u ≤ m + n ∧ v = m + n + 1)) : g u v = 0 := by
  have := hg u v
  unfold netCap at this
  rw [if_neg h.1, if_neg h.2.1, if_neg h.2.2] at this
  omega

/-- INTERNAL: what leaves the source. -/
theorem tf_src {m n : ℕ} {r c : ℕ → ℕ} {b : ℕ → ℕ → ℕ} {g : ℕ → ℕ → ℕ}
    (hg : ∀ u v, g u v ≤ netCap m n r c b u v) :
    ∑ v ∈ Finset.range (m + n + 2), g 0 v = ∑ i ∈ Finset.range m, g 0 (1 + i) :=
  sum_range_block _ 1 m _ (by omega) fun w _ hw => tf_zero hg 0 w (by omega)

/-- INTERNAL: what enters the source. -/
theorem tf_into_src {m n : ℕ} {r c : ℕ → ℕ} {b : ℕ → ℕ → ℕ} {g : ℕ → ℕ → ℕ}
    (hg : ∀ u v, g u v ≤ netCap m n r c b u v) :
    ∑ u ∈ Finset.range (m + n + 2), g u 0 = 0 :=
  Finset.sum_eq_zero fun u _ => tf_zero hg u 0 (by omega)

/-- INTERNAL: what enters row `i`. -/
theorem tf_row_in {m n : ℕ} {r c : ℕ → ℕ} {b : ℕ → ℕ → ℕ} {g : ℕ → ℕ → ℕ}
    (hg : ∀ u v, g u v ≤ netCap m n r c b u v) (i : ℕ) (hi : i < m) :
    ∑ u ∈ Finset.range (m + n + 2), g u (1 + i) = g 0 (1 + i) := by
  rw [sum_range_block _ 0 1 _ (by omega) fun w _ hw => tf_zero hg w (1 + i) (by omega)]
  simp

/-- INTERNAL: what leaves row `i`. -/
theorem tf_row_out {m n : ℕ} {r c : ℕ → ℕ} {b : ℕ → ℕ → ℕ} {g : ℕ → ℕ → ℕ}
    (hg : ∀ u v, g u v ≤ netCap m n r c b u v) (i : ℕ) (hi : i < m) :
    ∑ w ∈ Finset.range (m + n + 2), g (1 + i) w = ∑ j ∈ Finset.range n, g (1 + i) (1 + m + j) := by
  rw [sum_range_block _ (m + 1) n _ (by omega) fun w _ hw => tf_zero hg (1 + i) w (by omega)]
  exact Finset.sum_congr rfl fun j _ => by rw [show m + 1 + j = 1 + m + j by omega]

/-- INTERNAL: what enters column `j`. -/
theorem tf_col_in {m n : ℕ} {r c : ℕ → ℕ} {b : ℕ → ℕ → ℕ} {g : ℕ → ℕ → ℕ}
    (hg : ∀ u v, g u v ≤ netCap m n r c b u v) (j : ℕ) (hj : j < n) :
    ∑ u ∈ Finset.range (m + n + 2), g u (1 + m + j) = ∑ i ∈ Finset.range m, g (1 + i) (1 + m + j) :=
  sum_range_block _ 1 m _ (by omega) fun w _ hw => tf_zero hg w (1 + m + j) (by omega)

/-- INTERNAL: what leaves column `j`. -/
theorem tf_col_out {m n : ℕ} {r c : ℕ → ℕ} {b : ℕ → ℕ → ℕ} {g : ℕ → ℕ → ℕ}
    (hg : ∀ u v, g u v ≤ netCap m n r c b u v) (j : ℕ) (_hj : j < n) :
    ∑ w ∈ Finset.range (m + n + 2), g (1 + m + j) w = g (1 + m + j) (m + n + 1) := by
  rw [sum_range_block _ (m + n + 1) 1 _ (by omega) fun w _ hw => tf_zero hg (1 + m + j) w (by omega)]
  simp

/-- INTERNAL: the capacities themselves, entry by entry. -/
theorem tf_cap_src (m n : ℕ) (r c : ℕ → ℕ) (b : ℕ → ℕ → ℕ) (i : ℕ) (hi : i < m) :
    netCap m n r c b 0 (1 + i) = r i := by
  unfold netCap; rw [if_pos (by omega)]; congr 1; omega

/-- INTERNAL: the capacities themselves, entry by entry. -/
theorem tf_cap_cell (m n : ℕ) (r c : ℕ → ℕ) (b : ℕ → ℕ → ℕ) (i j : ℕ) (hi : i < m) (hj : j < n) :
    netCap m n r c b (1 + i) (1 + m + j) = b i j := by
  unfold netCap; rw [if_neg (by omega), if_pos (by omega)]; congr 1 <;> omega

/-- INTERNAL: the capacities themselves, entry by entry. -/
theorem tf_cap_snk (m n : ℕ) (r c : ℕ → ℕ) (b : ℕ → ℕ → ℕ) (j : ℕ) (hj : j < n) :
    netCap m n r c b (1 + m + j) (m + n + 1) = c j := by
  unfold netCap; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; congr 1; omega

/-- When the margin totals agree, a flow of value `Σ r` exists exactly when the
instance has a feasible table.
PAPER: sections/scales.tex:11-13 -/
theorem transport_flow_iff (m n : ℕ) (r c : ℕ → ℕ) (b : ℕ → ℕ → ℕ)
    (hsum : ∑ i ∈ Finset.range m, r i = ∑ j ∈ Finset.range n, c j) :
    (∃ f, IsFlow (m + n + 2) (netCap m n r c b) f ∧
        flowValue (m + n + 2) f = ∑ i ∈ Finset.range m, (r i : ℤ)) ↔
      Pseudocode.feasible (netInst m n r c b) := by
  constructor
  · rintro ⟨f, hf, hv⟩
    have hg := hf.le_cap
    unfold flowValue at hv
    simp only [← Nat.cast_sum] at hv
    rw [tf_src hg, tf_into_src hg] at hv
    have hval : ∑ i ∈ Finset.range m, f 0 (1 + i) = ∑ i ∈ Finset.range m, r i := by
      exact_mod_cast (by simpa using hv : ((∑ i ∈ Finset.range m, f 0 (1 + i) : ℕ) : ℤ) =
        ((∑ i ∈ Finset.range m, r i : ℕ) : ℤ))
    have hsat : ∀ i ∈ Finset.range m, f 0 (1 + i) = r i :=
      (Finset.sum_eq_sum_iff_of_le fun i hi =>
        (hg 0 (1 + i)).trans (tf_cap_src m n r c b i (Finset.mem_range.1 hi)).le).1 hval
    have hrow : ∀ i < m, ∑ j ∈ Finset.range n, f (1 + i) (1 + m + j) = r i := by
      intro i hi
      have h := hf.conserve (1 + i) (by omega) (by omega)
      rw [tf_row_in hg i hi, tf_row_out hg i hi] at h
      rw [← h, hsat i (Finset.mem_range.2 hi)]
    have hcolle : ∀ j ∈ Finset.range n,
        ∑ i ∈ Finset.range m, f (1 + i) (1 + m + j) ≤ c j := by
      intro j hj
      have hj' := Finset.mem_range.1 hj
      have h := hf.conserve (1 + m + j) (by omega) (by omega)
      rw [tf_col_in hg j hj', tf_col_out hg j hj'] at h
      rw [h]
      exact (hg _ _).trans (tf_cap_snk m n r c b j hj').le
    have htot : ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range m, f (1 + i) (1 + m + j) =
        ∑ j ∈ Finset.range n, c j := by
      rw [Finset.sum_comm, ← hsum]
      exact Finset.sum_congr rfl fun i hi => hrow i (Finset.mem_range.1 hi)
    have hcol := (Finset.sum_eq_sum_iff_of_le hcolle).1 htot
    refine ⟨fun i j => f (1 + i.val) (1 + m + j.val), ?_⟩
    simp only [Instance.Omega, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
    · have := (hg _ _).trans (tf_cap_cell m n r c b i j i.2 j.2).le
      omega
    · rw [Fin.sum_univ_eq_sum_range (fun j => f (1 + i.val) (1 + m + j)) n]
      exact hrow i i.2
    · rw [Fin.sum_univ_eq_sum_range (fun i => f (1 + i) (1 + m + j.val)) m]
      exact hcol j (Finset.mem_range.2 j.2)
  · rintro ⟨X, hX⟩
    simp only [Instance.Omega, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hX
    obtain ⟨hb, hrowX, hcolX⟩ := hX
    let Y : ℕ → ℕ → ℕ := fun i j => if h : i < m ∧ j < n then X ⟨i, h.1⟩ ⟨j, h.2⟩ else 0
    have hYb : ∀ i j, Y i j ≤ b i j := by
      intro i j
      simp only [Y]
      split_ifs with h
      · have := hb ⟨i, h.1⟩ ⟨j, h.2⟩
        simp only at this
        omega
      · exact Nat.zero_le _
    have hYrow : ∀ i < m, ∑ j ∈ Finset.range n, Y i j = r i := by
      intro i hi
      rw [← Fin.sum_univ_eq_sum_range (fun j => Y i j) n]
      have := hrowX ⟨i, hi⟩
      simp only at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [Y, hi, j.2]
    have hYcol : ∀ j < n, ∑ i ∈ Finset.range m, Y i j = c j := by
      intro j hj
      rw [← Fin.sum_univ_eq_sum_range (fun i => Y i j) m]
      have := hcolX ⟨j, hj⟩
      simp only at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Y, hj, i.2]
    have hself : ∀ u v, netCap m n r c Y u v ≤ netCap m n r c Y u v := fun _ _ => le_rfl
    refine ⟨netCap m n r c Y, ⟨fun u v => ?_, fun v hv0 hvV => ?_⟩, ?_⟩
    · unfold netCap
      split_ifs <;> first | exact le_rfl | exact hYb _ _
    · by_cases hv : v ≤ m
      · obtain ⟨i, rfl⟩ : ∃ i, v = 1 + i := ⟨v - 1, by omega⟩
        rw [tf_row_in hself i (by omega), tf_row_out hself i (by omega),
          tf_cap_src m n r c Y i (by omega), ← hYrow i (by omega)]
        exact (Finset.sum_congr rfl fun j hj =>
          tf_cap_cell m n r c Y i j (by omega) (Finset.mem_range.1 hj)).symm
      · obtain ⟨j, rfl⟩ : ∃ j, v = 1 + m + j := ⟨v - 1 - m, by omega⟩
        rw [tf_col_in hself j (by omega), tf_col_out hself j (by omega),
          tf_cap_snk m n r c Y j (by omega), ← hYcol j (by omega)]
        exact Finset.sum_congr rfl fun i hi =>
          tf_cap_cell m n r c Y i j (Finset.mem_range.1 hi) (by omega)
    · unfold flowValue
      simp only [← Nat.cast_sum]
      rw [tf_src hself, tf_into_src hself,
        Finset.sum_congr rfl fun i hi => tf_cap_src m n r c Y i (Finset.mem_range.1 hi)]
      simp

end Cellcounting.Analysis
