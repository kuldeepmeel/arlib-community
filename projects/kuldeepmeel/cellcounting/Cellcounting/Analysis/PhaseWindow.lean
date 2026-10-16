import Cellcounting.Analysis.TapeWindow
import Cellcounting.Model.Program

/-!
# Every randomized program piece reads only its own stretch of tape

INTERNAL infrastructure for `Interface/ProgramModel.lean`. No paper claim is stated here.

For each piece of `Model/Program.lean` that reads fair bits, started at cursor
`c₀`, the result is determined by the bits in `[c₀, c₁)`, where `c₁ ≥ c₀` is
the returned cursor (`Window`, `TapeWindow.lean`).  This is what lets the
`_tape` lemmas of `ProgramModel.lean` be chained along the program
(`tapeLaw_bind`).  The proofs follow the program text: deterministic steps
are transparent (`w_det`), fair-bit reads are `coin_window`, sequencing is
`w_bind`, and loops are `w_loop`.

The top-level facts are `phase_window` (used by `annealRun_tape`), and
`annealRun_window` and `zeroRun_window`, the window hypotheses of the repaired
`repeatRuns_tape` (`repeatRuns_tape_of_window`) for the two kinds of single run.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Cellcounting Arlib.Computation Cellcounting.Program Cellcounting.Model.Operations

/-- INTERNAL: the value of a charged fold is the fold of the values. -/
theorem val_foldl' {ι β : Type} (f : β → ι → Prog β) :
    ∀ (l : List ι) (b : β), (Charged.foldl f l b).val = l.foldl (fun b a => (f b a).val) b := by
  intro l
  induction l with
  | nil => intro b; rfl
  | cons a l ih => intro b; rw [Charged.val_foldl_cons, ih]; rfl

/-- INTERNAL: the value of a charged `repeatFor` is the fold of the values. -/
theorem val_repeatFor' {β : Type} (f : ℕ → β → Prog β) (n : ℕ) (b : β) :
    (Charged.repeatFor f n b).val = (List.range n).foldl (fun b r => (f r b).val) b :=
  val_foldl' _ _ _

/-- INTERNAL: `pure` is windowed if it does not move the cursor back. -/
theorem w_pure {α : Type} {c₀ : ℕ} {π : α → ℕ} (a : α) (h : c₀ ≤ π a) :
    Window c₀ π (fun _ => (pure a : Prog α).val) :=
  window_const a h

/-- INTERNAL: a step that does not read the tape is transparent. -/
theorem w_det {α β : Type} {c₀ : ℕ} {π : β → ℕ} (p : Prog α) {q : α → Finset ℕ → Prog β}
    (h : ∀ a, Window c₀ π (fun s => (q a s).val)) :
    Window c₀ π (fun s => (p >>= fun a => q a s).val) :=
  h p.val

/-- INTERNAL: sequencing two windowed pieces. -/
theorem w_bind {α β : Type} {c₀ : ℕ} {π₁ : α → ℕ} {π : β → ℕ} {p : Finset ℕ → Prog α}
    {q : α → Finset ℕ → Prog β} (h₁ : Window c₀ π₁ (fun s => (p s).val))
    (h₂ : ∀ a, Window (π₁ a) π (fun s => (q a s).val)) :
    Window c₀ π (fun s => (p s >>= fun a => q a s).val) :=
  window_bind (fun _ => True) h₁ (fun _ => trivial) (fun x _ => h₂ x)

/-- INTERNAL: a `repeatFor` loop of windowed steps. -/
theorem w_loop {β : Type} (π : β → ℕ) {f : ℕ → β → Finset ℕ → Prog β}
    (h : ∀ r b, Window (π b) π (fun s => (f r b s).val)) (n : ℕ) (b : β) {c₀ : ℕ}
    (hc : c₀ ≤ π b) :
    Window c₀ π (fun s => (Charged.repeatFor (fun r b => f r b s) n b).val) := by
  have := (window_foldl π (fun _ => True) (fun b r s => (f r b s).val) (fun _ _ _ _ => trivial)
    (fun b r _ => h r b) (List.range n) b trivial).1
  simp only [val_repeatFor']
  exact this.mono hc

/-- INTERNAL: strip every leading step that does not read the tape. -/
macro "wdet" : tactic => `(tactic| repeat (refine w_det _ fun _ => ?_))

/-- INTERNAL: one fair bit reads exactly position `cur`. -/
theorem coin_window (cur : ℕ) :
    Window cur Prod.snd (fun s => (coin (Coins.ofFinset s) cur).val) := by
  intro s
  refine ⟨Nat.le_succ cur, fun s' hs' => ?_⟩
  have h := hs' cur le_rfl (Nat.lt_succ_self cur)
  show ((Coins.flip cur (Coins.ofFinset s') : Prog Bool).val, cur + 1) =
    ((Coins.flip cur (Coins.ofFinset s) : Prog Bool).val, cur + 1)
  simp only [Coins.val_flip, Coins.heads'_ofFinset]
  congr 1
  exact decide_eq_decide.2 h.symm

/-- INTERNAL: `k` fair bits. -/
theorem uniformBits_window (k cur : ℕ) :
    Window cur Prod.snd (fun s => (uniformBits (Coins.ofFinset s) k cur).val) := by
  refine w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => ?_
  refine w_loop Prod.snd (fun r b => ?_) k _ le_rfl
  refine w_bind (coin_window _) fun x => ?_
  obtain ⟨bit, c⟩ := x
  refine w_det _ fun _ => ?_
  split
  · exact w_det _ fun _ => w_pure _ le_rfl
  · exact w_pure _ le_rfl

/-- INTERNAL: the dyadic integer draw. -/
theorem dyadicDraw_window (M : SNat) (ζ : SRat) (cur : ℕ) :
    Window cur Prod.snd (fun s => (dyadicDraw (Coins.ofFinset s) M ζ cur).val) := by
  refine w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => ?_
  refine w_bind (uniformBits_window _ _) fun x => ?_
  obtain ⟨Y, c⟩ := x
  exact w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => w_pure _ le_rfl

/-- INTERNAL: the bin-walk Metropolis decision. -/
theorem binAccept_window (C : Ctx) (aq : SRat) (x y v w : List SNat) (cur : ℕ) :
    Window cur Prod.snd (fun s => (binAccept C (Coins.ofFinset s) aq x y v w cur).val) := by
  refine w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => ?_
  split
  · exact w_pure _ le_rfl
  · refine w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => ?_
    refine w_bind (uniformBits_window _ _) fun z => ?_
    obtain ⟨Y, c⟩ := z
    refine w_det _ fun _ => w_det _ fun _ => ?_
    split
    · exact w_pure _ le_rfl
    · exact w_pure _ le_rfl

/-- INTERNAL: one bin-walk step. -/
theorem walkStep_window (C : Ctx) (P : OParams) (aq : SRat) (x y : List SNat)
    (st : List SNat × ℕ) :
    Window st.2 Prod.snd (fun s => (walkStep C P (Coins.ofFinset s) aq x y st).val) := by
  refine w_bind (uniformBits_window _ _) fun z => ?_
  obtain ⟨u, c⟩ := z
  refine w_det _ fun _ => ?_
  split
  · refine w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => ?_
    refine w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => ?_
    split
    · refine w_det _ fun _ => ?_
      split
      · exact w_pure _ le_rfl
      · exact w_det _ fun _ => w_det _ fun _ => binAccept_window _ _ _ _ _ _ _
    · refine w_det _ fun _ => ?_
      split
      · exact w_pure _ le_rfl
      · exact w_det _ fun _ => w_det _ fun _ => binAccept_window _ _ _ _ _ _ _
  · exact w_pure _ le_rfl

/-- INTERNAL: one bin sample. -/
theorem sampleBin_window (C : Ctx) (P : OParams) (aq : SRat) (x y : List SNat) (cur : ℕ) :
    Window cur Prod.snd (fun s => (sampleBin C P (Coins.ofFinset s) aq x y cur).val) := by
  refine w_det _ fun _ => ?_
  split
  · exact w_pure _ le_rfl
  · refine w_det _ fun _ => w_det _ fun _ => ?_
    exact w_loop Prod.snd (fun _ b => walkStep_window C P aq x y b) _ _ le_rfl

/-- INTERNAL: the ratio average. -/
theorem ratioAvg_window (C : Ctx) (P : OParams) (x y : List SNat) (a cur : ℕ) :
    Window cur Prod.snd (fun s => (ratioAvg C P (Coins.ofFinset s) x y a cur).val) := by
  refine w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => ?_
  refine w_det _ fun _ => w_det _ fun _ => ?_
  refine w_bind (π₁ := Prod.snd) ?_ fun z => ?_
  · refine w_loop Prod.snd (fun _ b => ?_) _ _ le_rfl
    refine w_bind (sampleBin_window _ _ _ _ _ _) fun z => ?_
    obtain ⟨v, c⟩ := z
    refine w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => ?_
    exact w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => w_pure _ le_rfl
  · exact w_det _ fun _ => w_pure _ le_rfl

/-- INTERNAL: the bin offsets. -/
theorem binOffsets_window (C : Ctx) (P : OParams) (v : List SNat) (cur : ℕ) :
    Window cur (fun r : List SRat × SNat × ℕ => r.2.2)
      (fun s => (binOffsets C P (Coins.ofFinset s) v cur).val) := by
  refine w_det _ fun _ => ?_
  refine w_loop (fun r : List SRat × SNat × ℕ => r.2.2) (fun _ b => ?_) _ _ le_rfl
  refine w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => ?_
  refine w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => ?_
  refine w_det _ fun _ => ?_
  refine w_bind (dyadicDraw_window _ _ _) fun z => ?_
  obtain ⟨off, c⟩ := z
  exact w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => w_pure _ le_rfl

/-- INTERNAL: the correction average. -/
theorem corrAvg_window (C : Ctx) (P : OParams) (x y : List SNat) (j cur : ℕ) :
    Window cur Prod.snd (fun s => (corrAvg C P (Coins.ofFinset s) x y j cur).val) := by
  refine w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => ?_
  refine w_bind (π₁ := Prod.snd) ?_ fun z => ?_
  · refine w_loop Prod.snd (fun _ b => ?_) _ _ le_rfl
    refine w_bind (sampleBin_window _ _ _ _ _ _) fun z => ?_
    obtain ⟨v, c⟩ := z
    refine w_det _ fun _ => ?_
    refine w_bind (binOffsets_window _ _ _ _) fun z => ?_
    obtain ⟨zz, lp, c2⟩ := z
    wdet
    exact w_pure _ le_rfl
  · exact w_det _ fun _ => w_pure _ le_rfl

/-- INTERNAL: the weight oracle. -/
theorem oracle_window (C : Ctx) (x y : List SNat) (j : ℕ) (ξin θ : SRat) (cur : ℕ) :
    Window cur Prod.snd (fun s => (oracle C (Coins.ofFinset s) x y j ξin θ cur).val) := by
  refine w_det _ fun _ => w_det _ fun _ => ?_
  refine w_bind (π₁ := Prod.snd) ?_ fun z => ?_
  · refine w_loop Prod.snd (fun _ b => ?_) _ _ le_rfl
    refine w_bind (ratioAvg_window _ _ _ _ _ _) fun z => ?_
    obtain ⟨r, c⟩ := z
    exact w_det _ fun _ => w_pure _ le_rfl
  · refine w_bind (corrAvg_window _ _ _ _ _ _) fun z => ?_
    obtain ⟨T, c⟩ := z
    exact w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => w_pure _ le_rfl

/-- INTERNAL: the implemented `λ(S)`. -/
theorem lam_window (C : Ctx) (K : Chain) (S : List Bool) (k : Kind) (a : ℕ)
    (w : List (List SRat)) (cur : ℕ) :
    Window cur Prod.snd (fun s => (lam C K (Coins.ofFinset s) S k a w cur).val) := by
  refine w_det _ fun xy => ?_
  obtain ⟨x, y⟩ := xy
  refine w_bind (oracle_window _ _ _ _ _ _ _) fun z => ?_
  obtain ⟨h, c⟩ := z
  wdet
  split
  · wdet; exact w_pure _ le_rfl
  · exact w_pure _ le_rfl

/-- INTERNAL: the dyadic acceptance threshold. -/
theorem acceptTest_window (K : Chain) (c : SRat) (cur : ℕ) :
    Window cur Prod.snd (fun s => (acceptTest K (Coins.ofFinset s) c cur).val) := by
  wdet
  refine w_bind (uniformBits_window _ _) fun z => ?_
  obtain ⟨Y, c'⟩ := z
  wdet
  exact w_pure _ le_rfl

/-- INTERNAL: one implemented Metropolis transition. -/
theorem step_window (C : Ctx) (K : Chain) (a : ℕ) (w : List (List SRat)) (S : List Bool)
    (cur : ℕ) :
    Window cur Prod.snd (fun s => (step C K (Coins.ofFinset s) a w S cur).val) := by
  refine w_bind (coin_window _) fun z => ?_
  obtain ⟨hold, c1⟩ := z
  dsimp only
  split
  · exact w_pure _ le_rfl
  · refine w_bind (dyadicDraw_window _ _ _) fun z => ?_
    obtain ⟨u1, c2⟩ := z
    refine w_bind (dyadicDraw_window _ _ _) fun z => ?_
    obtain ⟨u2, c3⟩ := z
    wdet
    dsimp only
    split
    · exact w_pure _ le_rfl
    · wdet
      refine w_bind (lam_window _ _ _ _ _ _ _) fun z => ?_
      obtain ⟨lNew, c4⟩ := z
      refine w_bind (lam_window _ _ _ _ _ _ _) fun z => ?_
      obtain ⟨lOld, c5⟩ := z
      wdet
      dsimp only
      split
      all_goals
        refine w_bind (acceptTest_window _ _ _) fun z => ?_
        obtain ⟨ok, c6⟩ := z
        dsimp only
        split
        · exact w_pure _ le_rfl
        · exact w_pure _ le_rfl

/-- INTERNAL: the initial transversal sampler. -/
theorem mu0_window (K : Chain) (cur : ℕ) :
    Window cur Prod.snd (fun s => (mu0 K (Coins.ofFinset s) cur).val) := by
  wdet
  refine w_loop Prod.snd (fun _ b => ?_) _ _ le_rfl
  wdet
  refine w_bind (dyadicDraw_window _ _ _) fun z => ?_
  obtain ⟨k, c1⟩ := z
  wdet
  refine w_bind (dyadicDraw_window _ _ _) fun z => ?_
  obtain ⟨rank, c2⟩ := z
  wdet
  exact w_pure _ le_rfl

/-- INTERNAL: the capped restart. -/
theorem restart_window (C : Ctx) (K : Chain) (Ph : Phase) (ws : List (List (List SRat)))
    (j : ℕ) (S0 : List Bool) (cur : ℕ) :
    Window cur Restart.cur (fun s => (restart C K (Coins.ofFinset s) Ph ws j S0 cur).val) := by
  wdet
  refine w_loop Restart.cur (fun _ st => ?_) _ _ le_rfl
  split
  · exact w_pure _ le_rfl
  · split
    · exact w_pure _ le_rfl
    · wdet
      split
      · exact w_pure _ le_rfl
      · wdet
        refine w_bind (π₁ := Prod.snd) (step_window _ _ _ _ _ _) fun z => ?_
        obtain ⟨S', c'⟩ := z
        wdet
        split
        · wdet
          split
          · wdet; exact w_pure _ le_rfl
          · exact w_pure _ le_rfl
        · exact w_pure _ le_rfl

/-- INTERNAL: observing one state. -/
theorem observeState_window (C : Ctx) (K : Chain) (j : ℕ) (st : Obs) :
    Window st.cur Obs.cur (fun s => (observeState C K (Coins.ofFinset s) j st).val) := by
  wdet
  split
  · refine w_det _ fun _ => w_det _ fun xy => ?_
    obtain ⟨x, y⟩ := xy
    refine w_bind (oracle_window _ _ _ _ _ _ _) fun z => ?_
    obtain ⟨hNext, c1⟩ := z
    refine w_bind (oracle_window _ _ _ _ _ _ _) fun z => ?_
    obtain ⟨hCur, c2⟩ := z
    wdet
    exact w_pure _ le_rfl
  · wdet; exact w_pure _ le_rfl
  · exact w_pure _ le_rfl

/-- INTERNAL: the `N_av` observations of a phase. -/
theorem observe_window (C : Ctx) (K : Chain) (Ph : Phase) (j : ℕ) (w : List (List SRat))
    (S0 : List Bool) (cur : ℕ) :
    Window cur Obs.cur (fun s => (observe C K (Coins.ofFinset s) Ph j w S0 cur).val) := by
  refine w_det _ fun z => w_det _ fun zq => w_det _ fun row => w_det _ fun tab => ?_
  refine w_bind (observeState_window C K j ⟨S0, z, tab, zq, cur⟩) fun st0 => ?_
  refine w_loop Obs.cur (fun _ st => ?_) _ _ le_rfl
  refine w_bind (step_window _ _ _ _ _ _) fun z => ?_
  obtain ⟨S', c'⟩ := z
  exact observeState_window C K j ⟨S', st.n0, st.nT, st.sumG, c'⟩

/-- INTERNAL: **one annealing phase reads only its own stretch of tape.** -/
theorem phase_window (C : Ctx) (K : Chain) (Ph : Phase) (j : ℕ) (st : Run) :
    Window st.cur Run.cur (fun s => (phase C K (Coins.ofFinset s) Ph j st).val) := by
  unfold phase
  split
  · exact w_pure _ le_rfl
  · refine w_bind (mu0_window _ _) fun z => ?_
    obtain ⟨S0, c1⟩ := z
    refine w_bind (restart_window _ _ _ _ _ _ _) fun rs => ?_
    split
    · exact w_pure _ le_rfl
    · wdet
      refine w_bind (observe_window _ _ _ _ _ _ _) fun o => ?_
      wdet
      split
      · wdet
        split
        · wdet; exact w_pure _ le_rfl
        · exact w_pure _ le_rfl
      · exact w_pure _ le_rfl

/-- INTERNAL: one annealing run (`p ≥ 1`) reads only its own stretch of tape. This is the
window hypothesis the repaired `repeatRuns_tape` needs for the `p ≥ 1` runs. -/
theorem annealRun_window (C : Ctx) (K : Chain) (Ph : Phase) (w0 : List (List SRat)) (C0 : SRat)
    (cur : ℕ) :
    Window cur Prod.snd (fun s => (annealRun C K (Coins.ofFinset s) Ph w0 C0 cur).val) := by
  refine w_det _ fun one => ?_
  refine w_bind (π₁ := Run.cur) ?_ fun st => ?_
  · exact w_loop Run.cur (fun j st => phase_window C K Ph j st) _ _ le_rfl
  · split
    · wdet; exact w_pure _ le_rfl
    · wdet; exact w_pure _ le_rfl

/-- INTERNAL: one `p = 0` run reads only its own stretch of tape. -/
theorem zeroRun_window (C : Ctx) (Hn : ℕ) (ε : SRat) (cur : ℕ) :
    Window cur Prod.snd (fun s => (zeroRun C Hn ε (Coins.ofFinset s) cur).val) := by
  exact w_det _ fun _ => w_det _ fun _ => w_det _ fun _ => oracle_window _ _ _ _ _ _ _

end Cellcounting.Analysis
