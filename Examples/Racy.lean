import Paralever.Lib.Notation

/-! # Anti-vacuity: programs where `par_seq_eq`'s conclusion is false

Everything else in `Examples/` shows the *hypothesis* failing — `indepB … = false`, or an obligation
that cannot be discharged. That leaves open the question a reader will actually ask: is `WellFormed`
doing any work, or would `ParSeqEq` hold anyway? This file answers it by refuting the conclusion.

Two counterexamples, in increasing strength:

* `DetectedRace` — concurrent writes to one cell. The race check fires at the first step, so the
  parallel program has **no** terminating outcome while the sequential one has one.
* `OrderDependent` — the parallel program reaches an outcome the sequential one **never** reaches,
  both of them terminating normally. Here the race is not visible at the first step: the two
  branches first touch disjoint cells, and only the following step conflicts.

Rationale: `docs/semantics.md` (absorbing `wrong`), `docs/theory.md` §9. -/

namespace Paralever.Examples.Racy
open Paralever

/-! ### A detected race has no terminating outcome

`Conf.wrong` is absorbing, so a program whose first step detects a race reaches no `.pure` leaf at
all — per Reynolds, racy programs are excluded rather than given a behaviour. -/

namespace DetectedRace

def shared : Loc := 0

def wA : ParM Unit := .write shared (.int 1) .pure
def wB : ParM Unit := .write shared (.int 2) .pure

/-- Both branches write `shared`, so the very first step is a detected race. -/
theorem step_wrong (σ : State) : stepC (.run (ParM.parPair wA wB) σ) = [.wrong] := rfl

/-- **No schedule of the parallel program terminates.** -/
theorem par_no_outcome (σ : State) (r : Unit × Unit) (σ' : State) :
    ¬ Reaches (.run (ParM.parPair wA wB) σ) (.run (.pure r) σ') := by
  intro h
  rcases Reaches.single_step (step_wrong σ) h with heq | hr
  · simp [ParM.parPair] at heq
  · exact absurd (Reaches.terminal rfl hr) (by simp)

/-- The sequential composition has no `par` node, hence nothing to check. -/
theorem seq_wellFormed (σ : State) : WellFormed (ParM.seqPair wA wB) σ := trivial

/-- …and it terminates, at its canonical outcome. -/
theorem seq_reaches (σ : State) :
    Reaches (.run (ParM.seqPair wA wB) σ)
            (.run (.pure (runSeq (ParM.seqPair wA wB) σ).1) (runSeq (ParM.seqPair wA wB) σ).2) :=
  (wellFormed_canonical _ σ _ _ (seq_wellFormed σ)).mpr rfl

/-- **The conclusion of `par_seq_eq` is false here.** One side terminates, the other cannot. -/
theorem not_parSeqEq (σ : State) : ¬ ParSeqEq (ParM.parPair wA wB) (ParM.seqPair wA wB) σ :=
  fun h => par_no_outcome σ _ _ ((h _ _).mpr (seq_reaches σ))

end DetectedRace

/-! ### An outcome the sequential program never reaches

The sharper case. `observer` writes its own cell and *then* reads `shared`; `mutator` writes
`shared`. The first step is race-free — `own` and `shared` are different cells — so the parallel
program is free to run `mutator` to completion first, after which `observer`'s read sees `99`
instead of the `1` it would have seen sequentially. -/

namespace OrderDependent

def shared : Loc := 0
def own : Loc := 1

/-- Writes its own cell, then reports what `shared` holds. -/
def observer : ParM Val := .write own (.int 7) (fun _ => .read shared .pure)

/-- Overwrites `shared`. -/
def mutator : ParM Unit := .write shared (.int 99) .pure

def σ0 : State
  | 0 => .int 1
  | _ => .int 0

/-- After `mutator` alone. -/
def σr : State := σ0.update shared (.int 99)

/-- …and then after `observer`'s own write. The state the schedule below ends in. -/
def σrw : State := σr.update own (.int 7)

theorem σrw_shared : σrw shared = .int 99 := rfl

/-! #### The parallel program, on the schedule that runs `mutator` first -/

theorem s₀ : stepC (.run (ParM.parPair observer mutator) σ0)
    = [.run (ParM.parPair (.read shared .pure) mutator) (σ0.update own (.int 7)),
       .run (ParM.parPair observer (.pure ())) σr] := rfl

theorem s₁ : stepC (.run (ParM.parPair observer (.pure ())) σr)
    = [.run (ParM.parPair (.read shared .pure) (.pure ())) σrw] := rfl

theorem s₂ : stepC (.run (ParM.parPair (.read shared ParM.pure) (.pure ())) σrw)
    = [.run (ParM.parPair (.pure (.int 99)) (.pure ())) σrw] := rfl

theorem s₃ : stepC (.run (ParM.parPair (ParM.pure (Val.int 99)) (.pure ())) σrw)
    = [.run (.pure (.int 99, ())) σrw] := rfl

/-- **The parallel program reaches `(99, ())`** — `observer` read `mutator`'s write. -/
theorem par_reaches : Reaches (.run (ParM.parPair observer mutator) σ0)
    (.run (.pure (.int 99, ())) σrw) := by
  have h₁ : Reaches (.run (ParM.parPair observer mutator) σ0)
      (.run (ParM.parPair observer (.pure ())) σr) :=
    Reaches.single (by rw [s₀]; simp)
  have h₂ : Reaches (.run (ParM.parPair observer mutator) σ0)
      (.run (ParM.parPair (ParM.read shared ParM.pure) (.pure ())) σrw) :=
    h₁.tail (by rw [s₁]; simp)
  have h₃ : Reaches (.run (ParM.parPair observer mutator) σ0)
      (.run (ParM.parPair (ParM.pure (Val.int 99)) (.pure ())) σrw) :=
    h₂.tail (by rw [s₂]; simp)
  exact h₃.tail (by rw [s₃]; simp)

/-- Running `observer`'s own write first leaves `read shared` against `write shared`, which the race
check does catch. -/
theorem s₀' : stepC (.run (ParM.parPair (ParM.read shared ParM.pure) mutator)
    (σ0.update own (.int 7))) = [.wrong] := rfl

/-- **The other schedule aborts.** So this program reaches a normal outcome under one schedule and
`wrong` under another — the race is real, it is just not visible at the first step. -/
theorem par_reaches_wrong : Reaches (.run (ParM.parPair observer mutator) σ0) .wrong := by
  have h₁ : Reaches (.run (ParM.parPair observer mutator) σ0)
      (.run (ParM.parPair (ParM.read shared ParM.pure) mutator) (σ0.update own (.int 7))) :=
    Reaches.single (by rw [s₀]; simp)
  exact h₁.tail (by rw [s₀']; simp)

theorem not_safe : ¬ Safe (.run (ParM.parPair observer mutator) σ0) :=
  fun hs => hs par_reaches_wrong

/-! #### The sequential program reaches `(1, ())`, and nothing else -/

theorem seq_wellFormed : WellFormed (ParM.seqPair observer mutator) σ0 := trivial

theorem seq_runSeq : (runSeq (ParM.seqPair observer mutator) σ0).1 = (.int 1, ()) := rfl

/-- The sequential read happens before the write, so it sees `1`; `wellFormed_canonical` makes that
the *only* outcome. -/
theorem seq_not_reaches (σ' : State) :
    ¬ Reaches (.run (ParM.seqPair observer mutator) σ0) (.run (.pure (.int 99, ())) σ') := by
  intro h
  have hc := (wellFormed_canonical _ σ0 _ σ' seq_wellFormed).mp h
  have e : (Val.int 99, ()) = (runSeq (ParM.seqPair observer mutator) σ0).1 :=
    congrArg Prod.fst hc
  rw [seq_runSeq] at e
  exact absurd e (by decide)

/-- **`par_seq_eq`'s conclusion is false, with both sides terminating.** The parallel program
produces a result the sequential one cannot. -/
theorem not_parSeqEq :
    ¬ ParSeqEq (ParM.parPair observer mutator) (ParM.seqPair observer mutator) σ0 :=
  fun h => seq_not_reaches σrw ((h _ _).mp par_reaches)

/-! #### …and the hypothesis is exactly what rules this out -/

theorem not_indep (σ σ' : State) :
    indepB (accesses observer σ) (accesses mutator σ') = false := rfl

/-- The all-pairs check fails too — there is only one pair, and it is this one. -/
theorem not_indepAll :
    indepAllB (childFootprints (Childs.cons observer (Childs.cons mutator Childs.nil)) σ0)
      = false := rfl

/-- `WellFormed` fails, which is why `par_seq_eq` never applied. -/
theorem not_wellFormed : ¬ WellFormed (ParM.parPair observer mutator) σ0 := by
  intro h
  obtain ⟨hi, -⟩ := h
  rw [← indepAllB_iff, not_indepAll] at hi
  exact Bool.noConfusion hi

end OrderDependent

end Paralever.Examples.Racy
