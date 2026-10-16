import Cellcounting.Interface.Encoding

/-!
# Every execution reads a bounded number of fair bits

INTERNAL infrastructure for `Interface/ProgramModel.lean`. No paper claim is stated here.

`tapeLength I ε δ` is the supremum of `flipsRead I ε δ` over all tapes
(`Interface.tapeLength_eq`).  On `ℕ` an unbounded supremum is `0`, so the tape
law of `Model/Run.lean` only covers every execution if that set is bounded above.
`flipsRead_bddAbove` proves it for every input, with no hypothesis on `ε`, `δ` or
the shape of `I`.

The argument does not count anything.  For fixed input, the whole charged result
of each program piece, viewed as a function of the tape, takes **finitely many
values** (`FinR`).  A fair-bit read takes two; a step that does not read the tape
takes one; sequencing keeps finiteness (`fr_bind`), and so does a loop whose length
is fixed before it starts (`fr_foldl`, `fr_loop`).  Every loop of the program has
such a length, so `Program.fpras` has finitely many charged results over all tapes,
and so finitely many flip counts.  The proofs follow the program text in the same
order as `Analysis/PhaseWindow.lean`.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Cellcounting Arlib.Computation Cellcounting.Program Cellcounting.Model.Operations

/-- INTERNAL: over all tapes, `f` has finitely many charged results. -/
def FinR {α : Type} (f : Finset ℕ → Prog α) : Prop := (Set.range f).Finite

/-- INTERNAL: a computation that ignores the tape has one result. -/
theorem fr_const {α : Type} (p : Prog α) : FinR (fun _ => p) := by
  unfold FinR
  rw [Set.range_const]
  exact Set.finite_singleton p

/-- INTERNAL: sequencing keeps finitely many results. -/
theorem fr_bind {α β : Type} {p : Finset ℕ → Prog α} {q : α → Finset ℕ → Prog β}
    (h₁ : FinR p) (h₂ : ∀ a, FinR (q a)) : FinR (fun s => p s >>= fun a => q a s) := by
  unfold FinR at *
  refine (h₁.biUnion fun x _ => (h₂ x.val).image (fun y => x >>= fun _ => y)).subset ?_
  rintro _ ⟨s, rfl⟩
  exact Set.mem_biUnion (Set.mem_range_self s) ⟨q (p s).val s, Set.mem_range_self s, rfl⟩

/-- INTERNAL: a step that does not read the tape. -/
theorem fr_det {α β : Type} (p : Prog α) {q : α → Finset ℕ → Prog β}
    (h : ∀ a, FinR (q a)) : FinR (fun s => p >>= fun a => q a s) :=
  fr_bind (fr_const p) h

/-- INTERNAL: a fold over a list fixed before the loop starts. -/
theorem fr_foldl {ι β : Type} {f : β → ι → Finset ℕ → Prog β}
    (h : ∀ b a, FinR (f b a)) :
    ∀ (l : List ι) (b : β), FinR (fun s => Charged.foldl (fun b a => f b a s) l b) := by
  intro l
  induction l with
  | nil => intro b; exact fr_const _
  | cons a l ih => intro b; exact fr_bind (h b a) fun x => ih x

/-- INTERNAL: a `repeatFor` loop. -/
theorem fr_loop {β : Type} {f : ℕ → β → Finset ℕ → Prog β}
    (h : ∀ r b, FinR (f r b)) (n : ℕ) (b : β) :
    FinR (fun s => Charged.repeatFor (fun r b => f r b s) n b) :=
  fr_foldl (f := fun b r => f r b) (fun b r => h r b) (List.range n) b

/-- INTERNAL: strip every leading step that does not read the tape. -/
macro "frdet" : tactic => `(tactic| repeat (refine fr_det _ fun _ => ?_))

/-- INTERNAL: one fair bit has two possible results. -/
theorem fr_flip (a : ℕ) : FinR (fun s => (Coins.flip a (Coins.ofFinset s) : Prog Bool)) := by
  unfold FinR
  refine (Set.finite_range (fun b : Bool =>
    (Charged.op (randOpcode Model.Operations.Op RandOp.flip) b : Prog Bool))).subset ?_
  rintro _ ⟨s, rfl⟩
  exact ⟨decide (a ∈ s), rfl⟩

/-- INTERNAL: one fair bit and the advanced cursor. -/
theorem coin_finR (cur : ℕ) : FinR (fun s => coin (Coins.ofFinset s) cur) :=
  fr_bind (fr_flip cur) fun _ => fr_const _

/-- INTERNAL: `k` fair bits. -/
theorem uniformBits_finR (k cur : ℕ) :
    FinR (fun s => uniformBits (Coins.ofFinset s) k cur) := by
  refine fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => ?_
  refine fr_loop (fun r b => ?_) k _
  refine fr_bind (coin_finR _) fun x => ?_
  obtain ⟨bit, c⟩ := x
  refine fr_det _ fun _ => ?_
  split
  · exact fr_det _ fun _ => fr_const _
  · exact fr_const _

/-- INTERNAL: the dyadic integer draw. -/
theorem dyadicDraw_finR (M : SNat) (ζ : SRat) (cur : ℕ) :
    FinR (fun s => dyadicDraw (Coins.ofFinset s) M ζ cur) := by
  refine fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => ?_
  refine fr_bind (uniformBits_finR _ _) fun x => ?_
  obtain ⟨Y, c⟩ := x
  exact fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => fr_const _

/-- INTERNAL: the bin-walk Metropolis decision. -/
theorem binAccept_finR (C : Ctx) (aq : SRat) (x y v w : List SNat) (cur : ℕ) :
    FinR (fun s => binAccept C (Coins.ofFinset s) aq x y v w cur) := by
  refine fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => ?_
  split
  · exact fr_const _
  · refine fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => ?_
    refine fr_bind (uniformBits_finR _ _) fun z => ?_
    obtain ⟨Y, c⟩ := z
    refine fr_det _ fun _ => fr_det _ fun _ => ?_
    split
    · exact fr_const _
    · exact fr_const _

/-- INTERNAL: one bin-walk step. -/
theorem walkStep_finR (C : Ctx) (P : OParams) (aq : SRat) (x y : List SNat)
    (st : List SNat × ℕ) :
    FinR (fun s => walkStep C P (Coins.ofFinset s) aq x y st) := by
  refine fr_bind (uniformBits_finR _ _) fun z => ?_
  obtain ⟨u, c⟩ := z
  refine fr_det _ fun _ => ?_
  split
  · refine fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => ?_
    refine fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => ?_
    split
    · refine fr_det _ fun _ => ?_
      split
      · exact fr_const _
      · exact fr_det _ fun _ => fr_det _ fun _ => binAccept_finR _ _ _ _ _ _ _
    · refine fr_det _ fun _ => ?_
      split
      · exact fr_const _
      · exact fr_det _ fun _ => fr_det _ fun _ => binAccept_finR _ _ _ _ _ _ _
  · exact fr_const _

/-- INTERNAL: one bin sample. -/
theorem sampleBin_finR (C : Ctx) (P : OParams) (aq : SRat) (x y : List SNat) (cur : ℕ) :
    FinR (fun s => sampleBin C P (Coins.ofFinset s) aq x y cur) := by
  refine fr_det _ fun _ => ?_
  split
  · exact fr_const _
  · refine fr_det _ fun _ => fr_det _ fun _ => ?_
    exact fr_loop (fun _ b => walkStep_finR C P aq x y b) _ _

/-- INTERNAL: the ratio average. -/
theorem ratioAvg_finR (C : Ctx) (P : OParams) (x y : List SNat) (a cur : ℕ) :
    FinR (fun s => ratioAvg C P (Coins.ofFinset s) x y a cur) := by
  refine fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => ?_
  refine fr_det _ fun _ => fr_det _ fun _ => ?_
  refine fr_bind ?_ fun z => ?_
  · refine fr_loop (fun _ b => ?_) _ _
    refine fr_bind (sampleBin_finR _ _ _ _ _ _) fun z => ?_
    obtain ⟨v, c⟩ := z
    refine fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => ?_
    exact fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => fr_const _
  · exact fr_det _ fun _ => fr_const _

/-- INTERNAL: the bin offsets. -/
theorem binOffsets_finR (C : Ctx) (P : OParams) (v : List SNat) (cur : ℕ) :
    FinR (fun s => binOffsets C P (Coins.ofFinset s) v cur) := by
  refine fr_det _ fun _ => ?_
  refine fr_loop (fun _ b => ?_) _ _
  refine fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => ?_
  refine fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => ?_
  refine fr_det _ fun _ => ?_
  refine fr_bind (dyadicDraw_finR _ _ _) fun z => ?_
  obtain ⟨off, c⟩ := z
  exact fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => fr_const _

/-- INTERNAL: the correction average. -/
theorem corrAvg_finR (C : Ctx) (P : OParams) (x y : List SNat) (j cur : ℕ) :
    FinR (fun s => corrAvg C P (Coins.ofFinset s) x y j cur) := by
  refine fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => ?_
  refine fr_bind ?_ fun z => ?_
  · refine fr_loop (fun _ b => ?_) _ _
    refine fr_bind (sampleBin_finR _ _ _ _ _ _) fun z => ?_
    obtain ⟨v, c⟩ := z
    refine fr_det _ fun _ => ?_
    refine fr_bind (binOffsets_finR _ _ _ _) fun z => ?_
    obtain ⟨zz, lp, c2⟩ := z
    frdet
    exact fr_const _
  · exact fr_det _ fun _ => fr_const _

/-- INTERNAL: the weight oracle. -/
theorem oracle_finR (C : Ctx) (x y : List SNat) (j : ℕ) (ξin θ : SRat) (cur : ℕ) :
    FinR (fun s => oracle C (Coins.ofFinset s) x y j ξin θ cur) := by
  refine fr_det _ fun _ => fr_det _ fun _ => ?_
  refine fr_bind ?_ fun z => ?_
  · refine fr_loop (fun _ b => ?_) _ _
    refine fr_bind (ratioAvg_finR _ _ _ _ _ _) fun z => ?_
    obtain ⟨r, c⟩ := z
    exact fr_det _ fun _ => fr_const _
  · refine fr_bind (corrAvg_finR _ _ _ _ _ _) fun z => ?_
    obtain ⟨T, c⟩ := z
    exact fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => fr_const _

/-- INTERNAL: the implemented `λ(S)`. -/
theorem lam_finR (C : Ctx) (K : Chain) (S : List Bool) (k : Kind) (a : ℕ)
    (w : List (List SRat)) (cur : ℕ) :
    FinR (fun s => lam C K (Coins.ofFinset s) S k a w cur) := by
  refine fr_det _ fun xy => ?_
  obtain ⟨x, y⟩ := xy
  refine fr_bind (oracle_finR _ _ _ _ _ _ _) fun z => ?_
  obtain ⟨h, c⟩ := z
  frdet
  split
  · frdet; exact fr_const _
  · exact fr_const _

/-- INTERNAL: the dyadic acceptance threshold. -/
theorem acceptTest_finR (K : Chain) (c : SRat) (cur : ℕ) :
    FinR (fun s => acceptTest K (Coins.ofFinset s) c cur) := by
  frdet
  refine fr_bind (uniformBits_finR _ _) fun z => ?_
  obtain ⟨Y, c'⟩ := z
  frdet
  exact fr_const _

/-- INTERNAL: one implemented Metropolis transition. -/
theorem step_finR (C : Ctx) (K : Chain) (a : ℕ) (w : List (List SRat)) (S : List Bool)
    (cur : ℕ) :
    FinR (fun s => step C K (Coins.ofFinset s) a w S cur) := by
  refine fr_bind (coin_finR _) fun z => ?_
  obtain ⟨hold, c1⟩ := z
  dsimp only
  split
  · exact fr_const _
  · refine fr_bind (dyadicDraw_finR _ _ _) fun z => ?_
    obtain ⟨u1, c2⟩ := z
    refine fr_bind (dyadicDraw_finR _ _ _) fun z => ?_
    obtain ⟨u2, c3⟩ := z
    frdet
    dsimp only
    split
    · exact fr_const _
    · frdet
      refine fr_bind (lam_finR _ _ _ _ _ _ _) fun z => ?_
      obtain ⟨lNew, c4⟩ := z
      refine fr_bind (lam_finR _ _ _ _ _ _ _) fun z => ?_
      obtain ⟨lOld, c5⟩ := z
      frdet
      dsimp only
      split
      all_goals
        refine fr_bind (acceptTest_finR _ _ _) fun z => ?_
        obtain ⟨ok, c6⟩ := z
        dsimp only
        split
        · exact fr_const _
        · exact fr_const _

/-- INTERNAL: the initial transversal sampler. -/
theorem mu0_finR (K : Chain) (cur : ℕ) :
    FinR (fun s => mu0 K (Coins.ofFinset s) cur) := by
  frdet
  refine fr_loop (fun _ b => ?_) _ _
  frdet
  refine fr_bind (dyadicDraw_finR _ _ _) fun z => ?_
  obtain ⟨k, c1⟩ := z
  frdet
  refine fr_bind (dyadicDraw_finR _ _ _) fun z => ?_
  obtain ⟨rank, c2⟩ := z
  frdet
  exact fr_const _

/-- INTERNAL: the capped restart. -/
theorem restart_finR (C : Ctx) (K : Chain) (Ph : Phase) (ws : List (List (List SRat)))
    (j : ℕ) (S0 : List Bool) (cur : ℕ) :
    FinR (fun s => restart C K (Coins.ofFinset s) Ph ws j S0 cur) := by
  frdet
  refine fr_loop (fun _ st => ?_) _ _
  split
  · exact fr_const _
  · split
    · exact fr_const _
    · frdet
      split
      · exact fr_const _
      · frdet
        refine fr_bind (step_finR _ _ _ _ _ _) fun z => ?_
        obtain ⟨S', c'⟩ := z
        frdet
        split
        · frdet
          split
          · frdet; exact fr_const _
          · exact fr_const _
        · exact fr_const _

/-- INTERNAL: observing one state. -/
theorem observeState_finR (C : Ctx) (K : Chain) (j : ℕ) (st : Obs) :
    FinR (fun s => observeState C K (Coins.ofFinset s) j st) := by
  frdet
  split
  · refine fr_det _ fun _ => fr_det _ fun xy => ?_
    obtain ⟨x, y⟩ := xy
    refine fr_bind (oracle_finR _ _ _ _ _ _ _) fun z => ?_
    obtain ⟨hNext, c1⟩ := z
    refine fr_bind (oracle_finR _ _ _ _ _ _ _) fun z => ?_
    obtain ⟨hCur, c2⟩ := z
    frdet
    exact fr_const _
  · frdet; exact fr_const _
  · exact fr_const _

/-- INTERNAL: the `N_av` observations of a phase. -/
theorem observe_finR (C : Ctx) (K : Chain) (Ph : Phase) (j : ℕ) (w : List (List SRat))
    (S0 : List Bool) (cur : ℕ) :
    FinR (fun s => observe C K (Coins.ofFinset s) Ph j w S0 cur) := by
  refine fr_det _ fun z => fr_det _ fun zq => fr_det _ fun row => fr_det _ fun tab => ?_
  refine fr_bind (observeState_finR C K j ⟨S0, z, tab, zq, cur⟩) fun st0 => ?_
  refine fr_loop (fun _ st => ?_) _ _
  refine fr_bind (step_finR _ _ _ _ _ _) fun z => ?_
  obtain ⟨S', c'⟩ := z
  exact observeState_finR C K j ⟨S', st.n0, st.nT, st.sumG, c'⟩

/-- INTERNAL: one annealing phase has finitely many results. -/
theorem phase_finR (C : Ctx) (K : Chain) (Ph : Phase) (j : ℕ) (st : Run) :
    FinR (fun s => phase C K (Coins.ofFinset s) Ph j st) := by
  unfold phase
  split
  · exact fr_const _
  · refine fr_bind (mu0_finR _ _) fun z => ?_
    obtain ⟨S0, c1⟩ := z
    refine fr_bind (restart_finR _ _ _ _ _ _ _) fun rs => ?_
    split
    · exact fr_const _
    · frdet
      refine fr_bind (observe_finR _ _ _ _ _ _ _) fun o => ?_
      frdet
      split
      · frdet
        split
        · frdet; exact fr_const _
        · exact fr_const _
      · exact fr_const _

/-- INTERNAL: one annealing run (`p ≥ 1`) has finitely many results. -/
theorem annealRun_finR (C : Ctx) (K : Chain) (Ph : Phase) (w0 : List (List SRat)) (C0 : SRat)
    (cur : ℕ) :
    FinR (fun s => annealRun C K (Coins.ofFinset s) Ph w0 C0 cur) := by
  refine fr_det _ fun one => ?_
  refine fr_bind ?_ fun st => ?_
  · exact fr_loop (fun j st => phase_finR C K Ph j st) _ _
  · split
    · frdet; exact fr_const _
    · frdet; exact fr_const _

/-- INTERNAL: one `p = 0` run has finitely many results. -/
theorem zeroRun_finR (C : Ctx) (Hn : ℕ) (ε : SRat) (cur : ℕ) :
    FinR (fun s => zeroRun C Hn ε (Coins.ofFinset s) cur) := by
  exact fr_det _ fun _ => fr_det _ fun _ => fr_det _ fun _ => oracle_finR _ _ _ _ _ _ _

/-- INTERNAL: the whole algorithm has finitely many charged results over all tapes. -/
theorem fpras_finR (I : Instance) (ε δ : ℚ) :
    FinR (fun s => Program.fpras I ε δ (Coins.ofFinset s)) := by
  frdet
  split
  · frdet
    split
    · frdet
      refine fr_bind (fr_loop (fun _ st => ?_) _ _) fun _ => ?_
      · refine fr_bind (zeroRun_finR _ _ _ _) fun z => ?_
        obtain ⟨z, c⟩ := z
        frdet; exact fr_const _
      · frdet; exact fr_const _
    · frdet
      refine fr_bind (fr_loop (fun _ st => ?_) _ _) fun _ => ?_
      · refine fr_bind (annealRun_finR _ _ _ _ _ _) fun z => ?_
        obtain ⟨z, c⟩ := z
        frdet; exact fr_const _
      · frdet; exact fr_const _
  · frdet; exact fr_const _

/-- INTERNAL: **the fair bits read are bounded over all tapes**, for every input.  So the
supremum `tapeLength I ε δ` is attained and bounds every execution's reads.
TEXLINE: sections/introduction.tex:30-33 -/
theorem flipsRead_bddAbove (I : Instance) (ε δ : ℚ) :
    BddAbove (Set.range (Interface.flipsRead I ε δ)) := by
  refine (((fpras_finR I ε δ).image fun p => p.cost (Op.rand RandOp.flip)).subset ?_).bddAbove
  rintro _ ⟨s, rfl⟩
  exact ⟨_, Set.mem_range_self s, rfl⟩

end Cellcounting.Analysis
