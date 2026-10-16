import Cellcounting.Analysis.NetworkVal
import Cellcounting.Analysis.MaxFlowCorrect
import Cellcounting.Analysis.TransportFlowIff

/-!
# The feasibility test decides `Ω ≠ ∅`

`feasible_val_proof` is the proof of `Cellcounting.feasible_val`
(`Interface/ProgramModel.lean`), kept here so that analysis files proving facts about the
tightening step (which calls `Program.feasible`) can use it.

`Program.feasible` compares the totals, builds the network of `sections/scales.tex:8-11`
(`network_val`) and compares its maximum flow value (`maxFlow_correct`) with `Σ r`; a flow
of that value is exactly a feasible table (`transport_flow_iff`).
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

/-- The program's preliminary deterministic flow test decides exactly the pseudocode
feasibility predicate.
INTERNAL: the proof of `Cellcounting.feasible_val`, placed below the interface file.
TEXLINE: sections/scales.tex:7-22 -/
theorem feasible_val_proof (m n : ℕ) (r c : List Cellcounting.Model.Operations.SNat) (b : List (List Cellcounting.Model.Operations.SNat)) (hr : r.length = m) (hc : c.length = n) : (Cellcounting.Program.feasible m n r c b).val = decide (Cellcounting.Pseudocode.feasible ⟨m, n, fun i => (r.getD i.val default).get, fun j => (c.getD j.val default).get, fun i j => ((b.getD i.val []).getD j.val default).get⟩) := by
  -- the totals: `sumN` adds the list
  have hfold : ∀ (l : List Model.Operations.SNat) (a : Model.Operations.SNat),
      (Arlib.Computation.Charged.foldl (fun acc x => Model.Operations.SNat.add acc x) l a).val.get =
        a.get + ∑ i ∈ Finset.range l.length, (l.getD i default).get := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons x l ih =>
      intro a
      rw [Arlib.Computation.Charged.val_foldl_cons, ih, Cellcounting.Interface.SNat.get_add, List.length_cons,
        Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      ring
  have hsum : ∀ (l : List Model.Operations.SNat),
      (Program.sumN l).val.get = ∑ i ∈ Finset.range l.length, (l.getD i default).get := by
    intro l
    simp only [Program.sumN, Arlib.Computation.Charged.val_bind]
    rw [hfold]
    simp
  obtain ⟨hsh, hcap⟩ := network_val m n r c b
  obtain ⟨⟨f, hf, hfv⟩, hopt⟩ := maxFlow_correct (m + n + 2) _ (by omega) hsh.1 hsh.2
  rw [hcap] at hf hopt
  have hle := flowValue_le_netCap m n _ _ _ f hf
  unfold Program.feasible
  simp only [Arlib.Computation.Charged.val_bind, Cellcounting.Interface.SNat.val_eq, hsum, hr, hc]
  have key := transport_flow_iff m n (fun i => (r.getD i default).get)
    (fun j => (c.getD j default).get) (fun i j => ((b.getD i []).getD j default).get)
  have htot_of := netSum_eq_of_feasible m n (fun i => (r.getD i default).get)
    (fun j => (c.getD j default).get) (fun i j => ((b.getD i []).getD j default).get)
  by_cases htot : ∑ x ∈ Finset.range m, (r.getD x default).get =
      ∑ x ∈ Finset.range n, (c.getD x default).get
  · simp only [htot, decide_true, if_true, Arlib.Computation.Charged.val_bind,
      Cellcounting.Interface.SNat.val_eq, hsum, hr]
    refine decide_eq_decide.2 ⟨fun hF => (key htot).1 ⟨f, hf, ?_⟩, fun hfeas => ?_⟩
    · rw [hfv, hF, ← htot]; push_cast; rfl
    · obtain ⟨g, hg, hgv⟩ := (key htot).2 hfeas
      have h1 := hopt g hg
      have ht : ((∑ x ∈ Finset.range m, (r.getD x default).get : ℕ) : ℤ) =
          ((∑ x ∈ Finset.range n, (c.getD x default).get : ℕ) : ℤ) := by rw [htot]
      push_cast at ht
      zify
      omega
  · simp only [htot, decide_false, Bool.false_eq_true, if_false,
      Arlib.Computation.Charged.val_pure]
    exact (decide_eq_false fun h => htot (htot_of h)).symm

end Cellcounting.Analysis
