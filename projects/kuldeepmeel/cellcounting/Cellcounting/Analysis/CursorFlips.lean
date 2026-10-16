import Cellcounting.Analysis.PhaseWindow

/-!
# Every randomized program piece moves its cursor at most once per fair bit it pays for

INTERNAL infrastructure for `Interface/ProgramModel.lean`. No paper claim is stated here.

`Interface.flipsRead` counts the `RandOp.flip` operations an execution is charged
for, while the `_tape` lemmas of `ProgramModel.lean` need a bound on the tape
cursor the program ends at.  The two are tied together here: for each piece of
`Model/Program.lean` that reads fair bits, started at cursor `c₀`, the returned
cursor is at most `c₀` plus the piece's flip cost (`CurLe`).  The only step that
moves the cursor is `coin`, which advances it by one and pays for one flip;
every other step leaves it alone and costs a nonnegative number of flips.  The
proofs follow the program text in the same order as `Analysis/PhaseWindow.lean`.

The top-level facts are `annealRun_curLe` and `zeroRun_curLe`, the two kinds of
single run, from which `ProgramModel.lean` bounds the cursor after the `R` runs of
`Program.fpras` by `flipsRead`.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Cellcounting Arlib.Computation Cellcounting.Program Cellcounting.Model.Operations

/-- INTERNAL: the number of fair bits a charged computation pays for. -/
def flipCost {α : Type} (p : Prog α) : ℕ := p.cost (Op.rand RandOp.flip)

/-- INTERNAL: `f`, started at cursor `c₀`, ends at a cursor `π` at most `c₀` plus the
number of fair bits it pays for. -/
def CurLe {α : Type} (c₀ : ℕ) (π : α → ℕ) (f : Finset ℕ → Prog α) : Prop :=
  ∀ s, π (f s).val ≤ c₀ + flipCost (f s)

/-- INTERNAL: flips of a sequence add. -/
theorem flipCost_bind {α β : Type} (p : Prog α) (q : α → Prog β) :
    flipCost (p >>= q) = flipCost p + flipCost (q p.val) := rfl

/-- INTERNAL: `pure` costs no flip. -/
theorem flipCost_pure {α : Type} (a : α) : flipCost (pure a : Prog α) = 0 := rfl

/-- INTERNAL: `pure` does not move the cursor forward. -/
theorem cl_pure {α : Type} {c₀ : ℕ} {π : α → ℕ} (a : α) (h : π a ≤ c₀) :
    CurLe c₀ π (fun _ => (pure a : Prog α)) := by
  intro s
  rw [flipCost_pure]
  simpa using h

/-- INTERNAL: a step that does not read the tape only adds cost. -/
theorem cl_det {α β : Type} {c₀ : ℕ} {π : β → ℕ} (p : Prog α) {q : α → Finset ℕ → Prog β}
    (h : ∀ a, CurLe c₀ π (q a)) :
    CurLe c₀ π (fun s => p >>= fun a => q a s) := by
  intro s
  have := h p.val s
  show π (q p.val s).val ≤ c₀ + (flipCost p + flipCost (q p.val s))
  omega

/-- INTERNAL: sequencing two pieces. -/
theorem cl_bind {α β : Type} {c₀ : ℕ} {π₁ : α → ℕ} {π : β → ℕ} {p : Finset ℕ → Prog α}
    {q : α → Finset ℕ → Prog β} (h₁ : CurLe c₀ π₁ p)
    (h₂ : ∀ a, CurLe (π₁ a) π (q a)) :
    CurLe c₀ π (fun s => p s >>= fun a => q a s) := by
  intro s
  have e1 := h₁ s
  have e2 := h₂ (p s).val s
  show π (q (p s).val s).val ≤ c₀ + (flipCost (p s) + flipCost (q (p s).val s))
  omega

/-- INTERNAL: a fold of pieces. -/
theorem cl_foldl {ι β : Type} (π : β → ℕ) {f : β → ι → Finset ℕ → Prog β}
    (h : ∀ b a, CurLe (π b) π (f b a)) :
    ∀ (l : List ι) (b : β) {c₀ : ℕ}, π b ≤ c₀ →
      CurLe c₀ π (fun s => Charged.foldl (fun b a => f b a s) l b) := by
  intro l
  induction l with
  | nil =>
    intro b c₀ hc s
    show π b ≤ c₀ + flipCost (Charged.foldl (fun b a => f b a s) [] b)
    omega
  | cons a l ih =>
    intro b c₀ hc
    exact cl_bind (π₁ := π) (fun s => by have := h b a s; beta_reduce; omega) fun x => ih x le_rfl

/-- INTERNAL: a `repeatFor` loop of pieces. -/
theorem cl_loop {β : Type} (π : β → ℕ) {f : ℕ → β → Finset ℕ → Prog β}
    (h : ∀ r b, CurLe (π b) π (f r b)) (n : ℕ) (b : β) {c₀ : ℕ}
    (hc : π b ≤ c₀) :
    CurLe c₀ π (fun s => Charged.repeatFor (fun r b => f r b s) n b) :=
  cl_foldl (f := fun b r => f r b) π (fun b r => h r b) (List.range n) b hc

/-- INTERNAL: strip every leading step that does not read the tape. -/
macro "cldet" : tactic => `(tactic| repeat (refine cl_det _ fun _ => ?_))

/-- INTERNAL: one fair bit moves the cursor by one and pays for one flip. -/
theorem coin_curLe (cur : ℕ) :
    CurLe cur Prod.snd (fun s => coin (Coins.ofFinset s) cur) := by
  intro s
  show cur + 1 ≤ cur + (CostVec.one (Op.rand RandOp.flip) (Op.rand RandOp.flip) + 0)
  simp

/-- INTERNAL: `k` fair bits. -/
theorem uniformBits_curLe (k cur : ℕ) :
    CurLe cur Prod.snd (fun s => uniformBits (Coins.ofFinset s) k cur) := by
  refine cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => ?_
  refine cl_loop Prod.snd (fun r b => ?_) k _ le_rfl
  refine cl_bind (coin_curLe _) fun x => ?_
  obtain ⟨bit, c⟩ := x
  refine cl_det _ fun _ => ?_
  split
  · exact cl_det _ fun _ => cl_pure _ le_rfl
  · exact cl_pure _ le_rfl

/-- INTERNAL: the dyadic integer draw. -/
theorem dyadicDraw_curLe (M : SNat) (ζ : SRat) (cur : ℕ) :
    CurLe cur Prod.snd (fun s => dyadicDraw (Coins.ofFinset s) M ζ cur) := by
  refine cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => ?_
  refine cl_bind (uniformBits_curLe _ _) fun x => ?_
  obtain ⟨Y, c⟩ := x
  exact cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => cl_pure _ le_rfl

/-- INTERNAL: the bin-walk Metropolis decision. -/
theorem binAccept_curLe (C : Ctx) (aq : SRat) (x y v w : List SNat) (cur : ℕ) :
    CurLe cur Prod.snd (fun s => binAccept C (Coins.ofFinset s) aq x y v w cur) := by
  refine cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => ?_
  split
  · exact cl_pure _ le_rfl
  · refine cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => ?_
    refine cl_bind (uniformBits_curLe _ _) fun z => ?_
    obtain ⟨Y, c⟩ := z
    refine cl_det _ fun _ => cl_det _ fun _ => ?_
    split
    · exact cl_pure _ le_rfl
    · exact cl_pure _ le_rfl

/-- INTERNAL: one bin-walk step. -/
theorem walkStep_curLe (C : Ctx) (P : OParams) (aq : SRat) (x y : List SNat)
    (st : List SNat × ℕ) :
    CurLe st.2 Prod.snd (fun s => walkStep C P (Coins.ofFinset s) aq x y st) := by
  refine cl_bind (uniformBits_curLe _ _) fun z => ?_
  obtain ⟨u, c⟩ := z
  refine cl_det _ fun _ => ?_
  split
  · refine cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => ?_
    refine cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => ?_
    split
    · refine cl_det _ fun _ => ?_
      split
      · exact cl_pure _ le_rfl
      · exact cl_det _ fun _ => cl_det _ fun _ => binAccept_curLe _ _ _ _ _ _ _
    · refine cl_det _ fun _ => ?_
      split
      · exact cl_pure _ le_rfl
      · exact cl_det _ fun _ => cl_det _ fun _ => binAccept_curLe _ _ _ _ _ _ _
  · exact cl_pure _ le_rfl

/-- INTERNAL: one bin sample. -/
theorem sampleBin_curLe (C : Ctx) (P : OParams) (aq : SRat) (x y : List SNat) (cur : ℕ) :
    CurLe cur Prod.snd (fun s => sampleBin C P (Coins.ofFinset s) aq x y cur) := by
  refine cl_det _ fun _ => ?_
  split
  · exact cl_pure _ le_rfl
  · refine cl_det _ fun _ => cl_det _ fun _ => ?_
    exact cl_loop Prod.snd (fun _ b => walkStep_curLe C P aq x y b) _ _ le_rfl

/-- INTERNAL: the ratio average. -/
theorem ratioAvg_curLe (C : Ctx) (P : OParams) (x y : List SNat) (a cur : ℕ) :
    CurLe cur Prod.snd (fun s => ratioAvg C P (Coins.ofFinset s) x y a cur) := by
  refine cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => ?_
  refine cl_det _ fun _ => cl_det _ fun _ => ?_
  refine cl_bind (π₁ := Prod.snd) ?_ fun z => ?_
  · refine cl_loop Prod.snd (fun _ b => ?_) _ _ le_rfl
    refine cl_bind (sampleBin_curLe _ _ _ _ _ _) fun z => ?_
    obtain ⟨v, c⟩ := z
    refine cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => ?_
    exact cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => cl_pure _ le_rfl
  · exact cl_det _ fun _ => cl_pure _ le_rfl

/-- INTERNAL: the bin offsets. -/
theorem binOffsets_curLe (C : Ctx) (P : OParams) (v : List SNat) (cur : ℕ) :
    CurLe cur (fun r : List SRat × SNat × ℕ => r.2.2)
      (fun s => binOffsets C P (Coins.ofFinset s) v cur) := by
  refine cl_det _ fun _ => ?_
  refine cl_loop (fun r : List SRat × SNat × ℕ => r.2.2) (fun _ b => ?_) _ _ le_rfl
  refine cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => ?_
  refine cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => ?_
  refine cl_det _ fun _ => ?_
  refine cl_bind (dyadicDraw_curLe _ _ _) fun z => ?_
  obtain ⟨off, c⟩ := z
  exact cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => cl_pure _ le_rfl

/-- INTERNAL: the correction average. -/
theorem corrAvg_curLe (C : Ctx) (P : OParams) (x y : List SNat) (j cur : ℕ) :
    CurLe cur Prod.snd (fun s => corrAvg C P (Coins.ofFinset s) x y j cur) := by
  refine cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => ?_
  refine cl_bind (π₁ := Prod.snd) ?_ fun z => ?_
  · refine cl_loop Prod.snd (fun _ b => ?_) _ _ le_rfl
    refine cl_bind (sampleBin_curLe _ _ _ _ _ _) fun z => ?_
    obtain ⟨v, c⟩ := z
    refine cl_det _ fun _ => ?_
    refine cl_bind (binOffsets_curLe _ _ _ _) fun z => ?_
    obtain ⟨zz, lp, c2⟩ := z
    cldet
    exact cl_pure _ le_rfl
  · exact cl_det _ fun _ => cl_pure _ le_rfl

/-- INTERNAL: the weight oracle. -/
theorem oracle_curLe (C : Ctx) (x y : List SNat) (j : ℕ) (ξin θ : SRat) (cur : ℕ) :
    CurLe cur Prod.snd (fun s => oracle C (Coins.ofFinset s) x y j ξin θ cur) := by
  refine cl_det _ fun _ => cl_det _ fun _ => ?_
  refine cl_bind (π₁ := Prod.snd) ?_ fun z => ?_
  · refine cl_loop Prod.snd (fun _ b => ?_) _ _ le_rfl
    refine cl_bind (ratioAvg_curLe _ _ _ _ _ _) fun z => ?_
    obtain ⟨r, c⟩ := z
    exact cl_det _ fun _ => cl_pure _ le_rfl
  · refine cl_bind (corrAvg_curLe _ _ _ _ _ _) fun z => ?_
    obtain ⟨T, c⟩ := z
    exact cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => cl_pure _ le_rfl

/-- INTERNAL: the implemented `λ(S)`. -/
theorem lam_curLe (C : Ctx) (K : Chain) (S : List Bool) (k : Kind) (a : ℕ)
    (w : List (List SRat)) (cur : ℕ) :
    CurLe cur Prod.snd (fun s => lam C K (Coins.ofFinset s) S k a w cur) := by
  refine cl_det _ fun xy => ?_
  obtain ⟨x, y⟩ := xy
  refine cl_bind (oracle_curLe _ _ _ _ _ _ _) fun z => ?_
  obtain ⟨h, c⟩ := z
  cldet
  split
  · cldet; exact cl_pure _ le_rfl
  · exact cl_pure _ le_rfl

/-- INTERNAL: the dyadic acceptance threshold. -/
theorem acceptTest_curLe (K : Chain) (c : SRat) (cur : ℕ) :
    CurLe cur Prod.snd (fun s => acceptTest K (Coins.ofFinset s) c cur) := by
  cldet
  refine cl_bind (uniformBits_curLe _ _) fun z => ?_
  obtain ⟨Y, c'⟩ := z
  cldet
  exact cl_pure _ le_rfl

/-- INTERNAL: one implemented Metropolis transition. -/
theorem step_curLe (C : Ctx) (K : Chain) (a : ℕ) (w : List (List SRat)) (S : List Bool)
    (cur : ℕ) :
    CurLe cur Prod.snd (fun s => step C K (Coins.ofFinset s) a w S cur) := by
  refine cl_bind (coin_curLe _) fun z => ?_
  obtain ⟨hold, c1⟩ := z
  dsimp only
  split
  · exact cl_pure _ le_rfl
  · refine cl_bind (dyadicDraw_curLe _ _ _) fun z => ?_
    obtain ⟨u1, c2⟩ := z
    refine cl_bind (dyadicDraw_curLe _ _ _) fun z => ?_
    obtain ⟨u2, c3⟩ := z
    cldet
    dsimp only
    split
    · exact cl_pure _ le_rfl
    · cldet
      refine cl_bind (lam_curLe _ _ _ _ _ _ _) fun z => ?_
      obtain ⟨lNew, c4⟩ := z
      refine cl_bind (lam_curLe _ _ _ _ _ _ _) fun z => ?_
      obtain ⟨lOld, c5⟩ := z
      cldet
      dsimp only
      split
      all_goals
        refine cl_bind (acceptTest_curLe _ _ _) fun z => ?_
        obtain ⟨ok, c6⟩ := z
        dsimp only
        split
        · exact cl_pure _ le_rfl
        · exact cl_pure _ le_rfl

/-- INTERNAL: the initial transversal sampler. -/
theorem mu0_curLe (K : Chain) (cur : ℕ) :
    CurLe cur Prod.snd (fun s => mu0 K (Coins.ofFinset s) cur) := by
  cldet
  refine cl_loop Prod.snd (fun _ b => ?_) _ _ le_rfl
  cldet
  refine cl_bind (dyadicDraw_curLe _ _ _) fun z => ?_
  obtain ⟨k, c1⟩ := z
  cldet
  refine cl_bind (dyadicDraw_curLe _ _ _) fun z => ?_
  obtain ⟨rank, c2⟩ := z
  cldet
  exact cl_pure _ le_rfl

/-- INTERNAL: the capped restart. -/
theorem restart_curLe (C : Ctx) (K : Chain) (Ph : Phase) (ws : List (List (List SRat)))
    (j : ℕ) (S0 : List Bool) (cur : ℕ) :
    CurLe cur Restart.cur (fun s => restart C K (Coins.ofFinset s) Ph ws j S0 cur) := by
  cldet
  refine cl_loop Restart.cur (fun _ st => ?_) _ _ le_rfl
  split
  · exact cl_pure _ le_rfl
  · split
    · exact cl_pure _ le_rfl
    · cldet
      split
      · exact cl_pure _ le_rfl
      · cldet
        refine cl_bind (π₁ := Prod.snd) (step_curLe _ _ _ _ _ _) fun z => ?_
        obtain ⟨S', c'⟩ := z
        cldet
        split
        · cldet
          split
          · cldet; exact cl_pure _ le_rfl
          · exact cl_pure _ le_rfl
        · exact cl_pure _ le_rfl

/-- INTERNAL: observing one state. -/
theorem observeState_curLe (C : Ctx) (K : Chain) (j : ℕ) (st : Obs) :
    CurLe st.cur Obs.cur (fun s => observeState C K (Coins.ofFinset s) j st) := by
  cldet
  split
  · refine cl_det _ fun _ => cl_det _ fun xy => ?_
    obtain ⟨x, y⟩ := xy
    refine cl_bind (oracle_curLe _ _ _ _ _ _ _) fun z => ?_
    obtain ⟨hNext, c1⟩ := z
    refine cl_bind (oracle_curLe _ _ _ _ _ _ _) fun z => ?_
    obtain ⟨hCur, c2⟩ := z
    cldet
    exact cl_pure _ le_rfl
  · cldet; exact cl_pure _ le_rfl
  · exact cl_pure _ le_rfl

/-- INTERNAL: the `N_av` observations of a phase. -/
theorem observe_curLe (C : Ctx) (K : Chain) (Ph : Phase) (j : ℕ) (w : List (List SRat))
    (S0 : List Bool) (cur : ℕ) :
    CurLe cur Obs.cur (fun s => observe C K (Coins.ofFinset s) Ph j w S0 cur) := by
  refine cl_det _ fun z => cl_det _ fun zq => cl_det _ fun row => cl_det _ fun tab => ?_
  refine cl_bind (observeState_curLe C K j ⟨S0, z, tab, zq, cur⟩) fun st0 => ?_
  refine cl_loop Obs.cur (fun _ st => ?_) _ _ le_rfl
  refine cl_bind (step_curLe _ _ _ _ _ _) fun z => ?_
  obtain ⟨S', c'⟩ := z
  exact observeState_curLe C K j ⟨S', st.n0, st.nT, st.sumG, c'⟩

/-- INTERNAL: **one annealing phase reads only its own stretch of tape.** -/
theorem phase_curLe (C : Ctx) (K : Chain) (Ph : Phase) (j : ℕ) (st : Run) :
    CurLe st.cur Run.cur (fun s => phase C K (Coins.ofFinset s) Ph j st) := by
  unfold phase
  split
  · exact cl_pure _ le_rfl
  · refine cl_bind (mu0_curLe _ _) fun z => ?_
    obtain ⟨S0, c1⟩ := z
    refine cl_bind (restart_curLe _ _ _ _ _ _ _) fun rs => ?_
    split
    · exact cl_pure _ le_rfl
    · cldet
      refine cl_bind (observe_curLe _ _ _ _ _ _ _) fun o => ?_
      cldet
      split
      · cldet
        split
        · cldet; exact cl_pure _ le_rfl
        · exact cl_pure _ le_rfl
      · exact cl_pure _ le_rfl

/-- INTERNAL: one annealing run (`p ≥ 1`) reads only its own stretch of tape. This is the
window hypothesis the repaired `repeatRuns_tape` needs for the `p ≥ 1` runs. -/
theorem annealRun_curLe (C : Ctx) (K : Chain) (Ph : Phase) (w0 : List (List SRat)) (C0 : SRat)
    (cur : ℕ) :
    CurLe cur Prod.snd (fun s => annealRun C K (Coins.ofFinset s) Ph w0 C0 cur) := by
  refine cl_det _ fun one => ?_
  refine cl_bind (π₁ := Run.cur) ?_ fun st => ?_
  · exact cl_loop Run.cur (fun j st => phase_curLe C K Ph j st) _ _ le_rfl
  · split
    · cldet; exact cl_pure _ le_rfl
    · cldet; exact cl_pure _ le_rfl

/-- INTERNAL: one `p = 0` run reads only its own stretch of tape. -/
theorem zeroRun_curLe (C : Ctx) (Hn : ℕ) (ε : SRat) (cur : ℕ) :
    CurLe cur Prod.snd (fun s => zeroRun C Hn ε (Coins.ofFinset s) cur) := by
  exact cl_det _ fun _ => cl_det _ fun _ => cl_det _ fun _ => oracle_curLe _ _ _ _ _ _ _

end Cellcounting.Analysis
