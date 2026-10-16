import Cellcounting.Model.Run
import Cellcounting.Model.Prior
import Arlib.Computation.ChargedPMF
import Mathlib.Data.Nat.Log
import Cellcounting.Meta.ModelClosure
import Cellcounting.Interface.Encoding
import Cellcounting.Interface.Pseudocode
import Cellcounting.Interface.ProgramModel

/-!
# The estimate is a nonnegative rational on every execution

`Cellcounting.Analysis.fpras_nonneg_owner` (`sections/introduction.tex:24`,
`sections/algorithm.tex:600-602`): every value in the support of `output I ε δ`
is `≥ 0`.  The proof is deterministic.  It shows
`0 ≤ (Program.fpras I ε δ tape).val` for **every** coin family `tape`
(`fpras_val_nonneg`).  Then the support of `output` is the image of the tape
law under that value map (`PMF.support_map`, twice).

The invariant follows the program.
* Infeasible input: the output is `SRat.lit 0`.
* `p = 0`: the median of oracle outputs (`zeroRun_nonneg`).
* `p ≥ 1`: the median of `annealRun` outputs.  Each is `0` after an abort, or
  `C(0) ∏_j R̂_j` otherwise.  `C(0)` is a cast natural (`chainSetup_C0`).
  `R̂_j = (ΣG/N)/(n_0/N)` with `ΣG` a sum of quotients of oracle outputs
  (`observe_sumG`, `phase_prod`).
* The oracle `M_f · ∏ R̂_a · T̂` is nonnegative for any parameters
  (`oracle_nonneg`).  Its averages divide nonnegative sums by `N_in`, a cast
  natural (`oracleParams_Nq`).  Its summands are powers of two or
  `α · pow2Approx`, and the bisection in `pow2Approx` keeps both endpoints
  `≥ 0`.
* The median is an entry of the sorted list or the default `0`
  (`orderStat_nonneg`).

No accuracy property of the oracle, no `Prior` field, and no lemma of
`Interface/ProgramModel.lean` is used.

`Charged.val_bind` and `Charged.val_pure` are `rfl` lemmas.  If `simp` uses them
directly, the kernel replays the rewrite as a definitional check, and that check
unfolds literals such as `SRat.lit (1/16)` (`ratLen` of the literal) until it
times out.  The local copies `vb`/`vp` are proved by the lemma rather than by
`rfl`, so `simp` emits explicit rewrite steps.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis.Nonneg

open Arlib.Computation Cellcounting Cellcounting.Program Cellcounting.Model.Operations
  Cellcounting.Interface

/-- INTERNAL: `Charged.val_bind` for `Prog`, proved by the lemma rather than by `rfl`, so that
`simp` does not make the kernel unfold program literals. -/
theorem vb {α β : Type} (p : Prog α) (f : α → Prog β) : (p >>= f).val = (f p.val).val :=
  Charged.val_bind p f

/-- INTERNAL: `Charged.val_pure` for `Prog`, proved by the lemma rather than by `rfl`. -/
theorem vp {α : Type} (a : α) : (pure a : Prog α).val = a :=
  Charged.val_pure a

/-- INTERNAL: an invariant preserved by every step of a `Charged.foldl` holds at its end. -/
theorem foldl_inv {β ι : Type} (P : β → Prop) (f : β → ι → Prog β)
    (h : ∀ b a, P b → P (f b a).val) : ∀ (l : List ι) (b : β), P b → P (Charged.foldl f l b).val := by
  intro l
  induction l with
  | nil => intro b hb; simpa using hb
  | cons a l ih => intro b hb; simpa using ih _ (h b a hb)

/-- INTERNAL: the `Charged.repeatFor` form of `foldl_inv`. -/
theorem repeatFor_inv {β : Type} (P : β → Prop) (f : ℕ → β → Prog β)
    (h : ∀ i b, P b → P (f i b).val) (n : ℕ) (b : β) (hb : P b) :
    P (Charged.repeatFor f n b).val :=
  foldl_inv P _ (fun b a hb => h a b hb) _ b hb

/-- INTERNAL: the bisection of `pow2Approx` keeps both endpoints `≥ 0`, so its result is `≥ 0`.
TEXLINE: sections/evaluation.tex:15-37 -/
theorem pow2Approx_nonneg (P : OParams) (β : SRat) : 0 ≤ (pow2Approx P β).val.get := by
  unfold pow2Approx
  simp only [vb, vp]
  refine (repeatFor_inv (fun st : SRat × SRat => 0 ≤ st.1.get ∧ 0 ≤ st.2.get) _ ?_ _ _ ?_).1
  · rintro i ⟨lo, hi⟩ ⟨hlo, hhi⟩
    simp only [vb]
    have hmid : 0 ≤ ((SRat.add lo hi).val.mul (SRat.lit (1 / 2)).val).val.get := by
      simp only [Interface.SRat.get_mul, Interface.SRat.get_add, Interface.SRat.get_lit]; positivity
    split <;> simp_all
  · simp

/-- INTERNAL: a natural number read as a sealed rational is `≥ 0`. -/
theorem toRat_nonneg (x : SNat) : 0 ≤ (SNat.toRat x).val.get := by
  simp

/-- INTERNAL: the divisor `N_in` of the oracle averages is a cast natural. -/
theorem oracleParams_Nq (C : Ctx) (ξin θ : SRat) : 0 ≤ (oracleParams C ξin θ).val.Nq.get := by
  unfold oracleParams
  simp only [vb, vp]
  exact toRat_nonneg _

/-- INTERNAL: an average of powers of two, over a nonnegative divisor, is `≥ 0`. -/
theorem ratioAvg_nonneg (C : Ctx) (P : OParams) (hP : 0 ≤ P.Nq.get) (tape : Coins ℕ)
    (x y : List SNat) (a cur : ℕ) : 0 ≤ (ratioAvg C P tape x y a cur).val.1.get := by
  unfold ratioAvg
  simp only [vb, vp, Interface.SRat.get_div]
  refine div_nonneg ?_ hP
  refine repeatFor_inv (fun st : SRat × ℕ => 0 ≤ st.1.get) _ ?_ _ _ ?_
  · rintro i ⟨s, c⟩ hs
    simp only [vb, vp, Interface.SRat.get_add, Interface.SRat.get_zpow2] at hs ⊢
    positivity
  · simp

/-- INTERNAL: an average of `α · pow2Approx β` with `α` a quotient of naturals is `≥ 0`. -/
theorem corrAvg_nonneg (C : Ctx) (P : OParams) (hP : 0 ≤ P.Nq.get) (tape : Coins ℕ)
    (x y : List SNat) (j cur : ℕ) : 0 ≤ (corrAvg C P tape x y j cur).val.1.get := by
  unfold corrAvg
  simp only [vb, vp, Interface.SRat.get_div]
  refine div_nonneg ?_ hP
  refine repeatFor_inv (fun st : SRat × ℕ => 0 ≤ st.1.get) _ ?_ _ _ ?_
  · rintro i ⟨s, c⟩ hs
    simp only [vb, vp, Interface.SRat.get_add, Interface.SRat.get_mul,
      Interface.SRat.get_div, Interface.SNat.get_toRat] at hs ⊢
    exact add_nonneg hs (mul_nonneg (by positivity) (pow2Approx_nonneg _ _))
  · simp

/-- INTERNAL: the weight oracle `M_f · ∏ R̂_a · T̂` returns a nonnegative rational for every
input, parameter and coin family.
TEXLINE: sections/evaluation.tex:15-37 -/
theorem oracle_nonneg (C : Ctx) (tape : Coins ℕ) (x y : List SNat) (j : ℕ) (ξin θ : SRat)
    (cur : ℕ) : 0 ≤ (oracle C tape x y j ξin θ cur).val.1.get := by
  unfold oracle
  simp only [vb, vp, Interface.SRat.get_mul, Interface.SNat.get_toRat]
  have hP := oracleParams_Nq C ξin θ
  refine mul_nonneg (mul_nonneg (by positivity) ?_) (corrAvg_nonneg _ _ hP _ _ _ _ _)
  refine repeatFor_inv (fun st : SRat × ℕ => 0 ≤ st.1.get) _ ?_ _ _ ?_
  · rintro i ⟨s, c⟩ hs
    simp only [vb, vp, Interface.SRat.get_mul] at hs ⊢
    exact mul_nonneg hs (ratioAvg_nonneg _ _ hP _ _ _ _ _)
  · simp

/-- INTERNAL: observing one state keeps `ΣG` nonnegative. -/
theorem observeState_sumG (C : Ctx) (K : Chain) (tape : Coins ℕ) (j : ℕ) (st : Obs)
    (hs : 0 ≤ st.sumG.get) : 0 ≤ (observeState C K tape j st).val.sumG.get := by
  unfold observeState
  simp only [vb]
  split
  · simp only [vb, vp, Interface.SRat.get_add, Interface.SRat.get_div]
    exact add_nonneg hs (div_nonneg (oracle_nonneg _ _ _ _ _ _ _ _) (oracle_nonneg _ _ _ _ _ _ _ _))
  · simpa using hs
  · simpa using hs

/-- INTERNAL: the sum `ΣG_j` of an observation trajectory is `≥ 0`. -/
theorem observe_sumG (C : Ctx) (K : Chain) (tape : Coins ℕ) (Ph : Phase) (j : ℕ)
    (w : List (List SRat)) (S0 : List Bool) (cur : ℕ) :
    0 ≤ (observe C K tape Ph j w S0 cur).val.sumG.get := by
  unfold observe
  simp only [vb]
  refine repeatFor_inv (fun st : Obs => 0 ≤ st.sumG.get) _ ?_ _ _ ?_
  · intro i st hs
    simp only [vb]
    exact observeState_sumG _ _ _ _ _ hs
  · exact observeState_sumG _ _ _ _ _ (by simp)

/-- INTERNAL: a phase keeps the running product of ratio estimates nonnegative. -/
theorem phase_prod (C : Ctx) (K : Chain) (tape : Coins ℕ) (Ph : Phase) (j : ℕ) (st : Run)
    (hs : 0 ≤ st.prod.get) : 0 ≤ (phase C K tape Ph j st).val.prod.get := by
  unfold phase
  split
  · simpa using hs
  · simp only [vb]
    split
    · simpa using hs
    · simp only [vb]
      split
      · simp only [vb]
        split
        · simp only [vb, vp, Interface.SRat.get_mul,
            Interface.SRat.get_div, Interface.SNat.get_toRat]
          exact mul_nonneg hs (div_nonneg (div_nonneg (observe_sumG _ _ _ _ _ _ _ _) (by positivity))
            (div_nonneg (by positivity) (by positivity)))
        · simp only [vp, Interface.SRat.get_mul,
            Interface.SRat.get_div, Interface.SNat.get_toRat]
          exact mul_nonneg hs (div_nonneg (div_nonneg (observe_sumG _ _ _ _ _ _ _ _) (by positivity))
            (div_nonneg (by positivity) (by positivity)))
      · simpa using hs

/-- INTERNAL: one annealing run returns `0` or `C(0) ∏_j R̂_j`, which is `≥ 0` when `C(0)` is.
TEXLINE: sections/algorithm.tex:600-602 -/
theorem annealRun_nonneg (C : Ctx) (K : Chain) (tape : Coins ℕ) (Ph : Phase)
    (w0 : List (List SRat)) (C0 : SRat) (hC0 : 0 ≤ C0.get) (cur : ℕ) :
    0 ≤ (annealRun C K tape Ph w0 C0 cur).val.1.get := by
  unfold annealRun
  simp only [vb]
  split
  · simp
  · simp only [vb, vp, Interface.SRat.get_mul]
    refine mul_nonneg hC0 ?_
    refine repeatFor_inv (fun st : Run => 0 ≤ st.prod.get) _ ?_ _ _ ?_
    · intro i st hs; exact phase_prod _ _ _ _ _ _ hs
    · simp

/-- INTERNAL: `C(0) = M_f ∏_s (b_s + 1)` is a cast natural. -/
theorem chainSetup_C0 (C : Ctx) (Pm : Params) (pS : SNat) (ε : SRat) :
    0 ≤ (chainSetup C Pm pS ε).val.2.2.2.get := by
  unfold chainSetup
  simp only [vb, vp]
  exact toRat_nonneg _

/-- INTERNAL: `foldl_inv` when the step only preserves the invariant on list members. -/
theorem foldl_inv_mem {β ι : Type} (P : β → Prop) (f : β → ι → Prog β) :
    ∀ (l : List ι), (∀ b a, a ∈ l → P b → P (f b a).val) →
      ∀ b, P b → P (Charged.foldl f l b).val := by
  intro l
  induction l with
  | nil => intro _ b hb; simpa using hb
  | cons a l ih =>
    intro h b hb
    simpa using ih (fun b a' ha' hb' => h b a' (List.mem_cons_of_mem _ ha') hb') _
      (h b a List.mem_cons_self hb)

/-- INTERNAL: every entry of the list is `≥ 0`. -/
def AllNonneg (l : List SRat) : Prop := ∀ z ∈ l, 0 ≤ z.get

/-- INTERNAL: appending a nonnegative entry to a nonnegative list. -/
theorem push_nonneg (l : List SRat) (x : SRat) (hl : AllNonneg l) (hx : 0 ≤ x.get) :
    AllNonneg (Cellcounting.Model.Operations.push l x).val := by
  intro z hz
  simp only [Interface.val_push, List.mem_append, List.mem_singleton] at hz
  rcases hz with hz | rfl
  · exact hl z hz
  · exact hx

/-- INTERNAL: inserting a nonnegative entry into a nonnegative list. -/
theorem insertAsc_nonneg (l : List SRat) (x : SRat) (hl : AllNonneg l) (hx : 0 ≤ x.get) :
    AllNonneg (insertAsc l x).val := by
  unfold insertAsc
  simp only [vb]
  have step : ∀ (st : List SRat × Bool) (y : SRat), y ∈ l → AllNonneg st.1 →
      AllNonneg (((if st.2 = true then do
          let o ← Cellcounting.Model.Operations.push st.1 y
          pure (o, true)
        else do
          let before ← SRat.lt x y
          if before = true then do
            let o ← Cellcounting.Model.Operations.push st.1 x
            let o' ← Cellcounting.Model.Operations.push o y
            pure (o', true)
          else do
            let o ← Cellcounting.Model.Operations.push st.1 y
            pure (o, false)) : Prog (List SRat × Bool)).val.1) := by
    rintro ⟨acc, done⟩ y hy hacc
    have hy' := hl y hy
    dsimp only at hacc ⊢
    split
    · simp only [vb, vp]
      exact push_nonneg _ _ hacc hy'
    · simp only [vb]
      split
      · simp only [vb, vp]
        exact push_nonneg _ _ (push_nonneg _ _ hacc hx) hy'
      · simp only [vb, vp]
        exact push_nonneg _ _ hacc hy'
  have hst := foldl_inv_mem (fun st : List SRat × Bool => AllNonneg st.1) _ l step
    ([], false) (by simp [AllNonneg])
  split
  · simpa using hst
  · exact push_nonneg _ _ hst hx

/-- INTERNAL: an order statistic of a nonnegative list is `≥ 0` (the default past its end is `0`). -/
theorem orderStat_nonneg (outs : List SRat) (idx : ℕ) (h : AllNonneg outs) :
    0 ≤ (orderStat outs idx).val.get := by
  unfold orderStat
  simp only [vb, Interface.val_get]
  have hs := foldl_inv_mem (fun acc : List SRat => AllNonneg acc) (fun acc x => insertAsc acc x) outs
    (fun acc x hx hacc => insertAsc_nonneg acc x hacc (h x hx)) [] (by simp [AllNonneg])
  rw [List.getD_eq_getElem?_getD]
  cases hz : (Charged.foldl (fun acc x => insertAsc acc x) outs []).val[idx]? with
  | none => simp
  | some z => simpa using hs z (List.mem_of_getElem? hz)

/-- INTERNAL: the `p = 0` run is one oracle call. -/
theorem zeroRun_nonneg (C : Ctx) (Hn : ℕ) (ε : SRat) (tape : Coins ℕ) (cur : ℕ) :
    0 ≤ (zeroRun C Hn ε tape cur).val.1.get := by
  unfold zeroRun
  simp only [vb]
  exact oracle_nonneg _ _ _ _ _ _ _ _

/-- INTERNAL: the answer of every execution of the algorithm, on every coin family, is `≥ 0`.
TEXLINE: sections/introduction.tex:24 -/
theorem fpras_val_nonneg (I : Instance) (ε δ : ℚ) (tape : Coins ℕ) :
    0 ≤ (Program.fpras I ε δ tape).val := by
  unfold Program.fpras
  simp only [vb]
  split
  · simp only [vb]
    split
    · simp only [vb, Interface.SRat.val_output]
      refine orderStat_nonneg _ _ ?_
      refine repeatFor_inv (fun st : List SRat × ℕ => AllNonneg st.1) _ ?_ _ _ (by simp [AllNonneg])
      intro i st hs
      simp only [vb, vp]
      exact push_nonneg _ _ hs (zeroRun_nonneg _ _ _ _ _)
    · simp only [vb, Interface.SRat.val_output]
      refine orderStat_nonneg _ _ ?_
      refine repeatFor_inv (fun st : List SRat × ℕ => AllNonneg st.1) _ ?_ _ _ (by simp [AllNonneg])
      intro i st hs
      simp only [vb, vp]
      refine push_nonneg _ _ hs (annealRun_nonneg _ _ _ _ _ _ ?_ _)
      with_reducible apply chainSetup_C0
  · simp

end Cellcounting.Analysis.Nonneg

/-- Proof-side owner for `Cellcounting.fpras_nonneg`; its statement is fixed by the proof charter.
PAPER: sections/introduction.tex:24 -/
theorem Cellcounting.Analysis.fpras_nonneg_owner (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m) (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1) : ∀ Zhat ∈ (output I ε δ).support, 0 ≤ Zhat := by
  intro Zhat hZ
  simp only [output, run, PMF.support_map, Set.mem_image] at hZ
  obtain ⟨_, ⟨c, -, rfl⟩, rfl⟩ := hZ
  exact Cellcounting.Analysis.Nonneg.fpras_val_nonneg I ε δ c

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · `fpras_nonneg_owner` via `Nonneg.fpras_val_nonneg`, a per-tape invariant; closed outright
-/
