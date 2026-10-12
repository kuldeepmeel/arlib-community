import Esa22Copy.Interface.Pseudocode

/-!
# The relaxed Algorithm 2

The paper's Algorithm 2 (`algo:bfinal`, esa22-final.tex:567-591): Algorithm 1
(`Interface.Pseudocode`) with line `check` removed, so it never outputs `⊥`.
It is an analysis device only — claim `claim:errfail` (esa22-final.tex:545-562)
bounds the error of Algorithm 1 off `⊥` by the error of this algorithm.

The state is a bare `Snapshot` (no `Option`): there is no `⊥` to carry.  The
lines are the pseudocode's own (`pick`, `drop`, `full`, `throw`, `halve`), so the
two algorithms differ only in the missing test.  Both size tests stay the
literal equality `full`, never `≥`: in Algorithm 2, `|𝒳|` *can* exceed
`thresh` after a throw that removes nothing.
-/

set_option autoImplicit false

namespace Esa22Copy.Analysis

open Esa22Copy.Interface (Snapshot)
open Esa22Copy.Interface.Pseudocode

variable {α : Type} [DecidableEq α] [Fintype α]

/-- **One iteration of Algorithm 2** (esa22-final.tex:572-581): drop, pick, and
if `|𝒳| = thresh`, throw and halve `p` — with no test for `⊥` afterwards.

PAPER: esa22-final.tex:567-591 -/
noncomputable def relaxedStep (thr w : ℕ) (st : Snapshot α) (a : α) : PMF (Snapshot α) :=
  (pick w st.level a (drop a st.sample)).bind fun X =>
    if full thr X then
      (throw X).map fun Y => (⟨Y, halve st.level⟩ : Snapshot α)
    else PMF.pure ⟨X, st.level⟩

/-- **The loop of Algorithm 2**, over the stream in order.

PAPER: esa22-final.tex:567-591 -/
noncomputable def relaxedLoop (thr w : ℕ) : List α → Snapshot α → PMF (Snapshot α)
  | [], st => PMF.pure st
  | a :: s, st => (relaxedStep thr w st a).bind (relaxedLoop thr w s)

/-- **Algorithm 2's output** `|𝒳|/p = |𝒳| · 2ᵏ`, with the paper's `thresh` and
blocks of `m + 1` bits, exactly the parameters `Pseudocode.answer` uses.

PAPER: esa22-final.tex:567-591 (line `boutput`) -/
noncomputable def relaxedAnswer (ε δ : ℝ) (s : List α) : PMF ℕ :=
  (relaxedLoop (thresh ε δ s.length) (s.length + 1) s init).map
    fun st => st.sample.card * 2 ^ st.level

/-- INTERNAL: unfolding equation for `relaxedLoop` on a cons. -/
theorem relaxedLoop_cons (thr w : ℕ) (a : α) (s : List α) (st : Snapshot α) :
    relaxedLoop thr w (a :: s) st = (relaxedStep thr w st a).bind (relaxedLoop thr w s) :=
  rfl

/-- INTERNAL: Algorithm 2's loop over a concatenation runs the two parts in turn. -/
theorem relaxedLoop_append (thr w : ℕ) (l₁ l₂ : List α) (st : Snapshot α) :
    relaxedLoop thr w (l₁ ++ l₂) st = (relaxedLoop thr w l₁ st).bind (relaxedLoop thr w l₂) := by
  induction l₁ generalizing st with
  | nil => simp [relaxedLoop]
  | cons a l ih =>
    simp only [List.cons_append, relaxedLoop_cons, PMF.bind_bind]
    congr 1
    funext x
    exact ih x

end Esa22Copy.Analysis
