import Paralever.Search.ExplainHtml
import Paralever.Lang.Core
import Paralever.Pragma.ArrRef

/-! # Anti-vacuity: a pointer that strayed into another array

Every write below goes through `ArrRef.loc`; the only fault is an index out of range. `State` is
total, so that does nothing until it collides with another thread — and then it is an ordinary race.

Both halves are here, and the second is the honest one: `Aliasing`, `Underflow` and `ReadWrite` are
rejected with a checked counterexample, while `Stray` is **accepted** — `ParSeqEq` holds and the
program is still wrong, because `par_seq_eq` is equivalence, not memory safety.
-- ref: `docs/semantics.md` -/

namespace Paralever.Examples.Pointers
open Paralever Paralever.Lang

-- `rfl` and `decide` here reduce a lowered `ParProg` against a concrete heap; the default depth is
-- not enough to unfold `runSeq`/`follow` through `readAs`/`writeAs`.
set_option maxRecDepth 4000

def σ0 : State := fun _ => .int 0
def ρ0 : Regs := fun _ => 0

/-- Three arrays, at known bases. `A` is the one every stray pointer starts from. -/
def A : ArrRef := ⟨0, 10⟩
def B : ArrRef := ⟨100, 10⟩
def C : ArrRef := ⟨1000, 10⟩

/-! ### The stray address is an ordinary location

`ArrRef.loc` puts no bound on `i`, and nothing needs `loc_mem` in order to *write*. -/

theorem stray_loc : A.loc 1000 = 1000 := rfl

theorem stray_inhabited : σ0 (A.loc 1000) = .int 0 := rfl

/-- …and it is not in `A`. The predicate that would have caught it is a `Prop`, used in proofs,
never a check that runs. -/
theorem stray_not_inRange : ¬ A.InRange (A.loc 1000) := by
  unfold ArrRef.InRange ArrRef.loc A; grind

/-! ### Accepted: the stray write lands where nobody looks

`A.loc 1000` is `1000`, `B` covers `100..109`, so the obligation holds — on a program that writes 7
to a cell it does not own. -/

namespace Stray

def prog : ParProg :=
  ParProg.par [ ParProg.store (A.loc 1000) (.lit 7), ParProg.store (B.loc 0) (.lit 1) ]

theorem wf : prog.wfB = true := by decide

/-- **The theorem holds.** Both runs commit the same stray write at the same place. -/
theorem par_seq_eq : ParSeqEq (prog.execPar ρ0) (prog.execSeq ρ0) σ0 :=
  ParProg.par_seq_eq wf ρ0 σ0

theorem seq_writes_stray : (runSeq (prog.execSeq ρ0) σ0).2 1000 = .int 7 := rfl

/-- A pointer out of range inside *one* thread is not a race either — the analysis is about threads,
not about bounds. -/
def oneThread : ParProg :=
  ParProg.block [ ParProg.store (A.loc 1000) (.lit 7), ParProg.store (B.loc 0) (.lit 1) ]

theorem oneThread_wf : oneThread.wfB = true := by decide

end Stray

/-! ### Rejected: the stray write aliases another array

With `C` at base `1000`, `A.loc 1000` *is* `C.loc 0` — neither thread changed, the arrays met. -/

namespace Aliasing

theorem the_alias : A.loc 1000 = C.loc 0 := rfl

def prog : ParProg :=
  ParProg.par [ ParProg.store (A.loc 1000) (.lit 7), ParProg.store (C.loc 0) (.lit 1) ]

/-- The obligation fails. -/
theorem not_wf : prog.wfB = false := by decide

/-- The scan names the location, and nothing else. -/
theorem the_site :
    (raceSites (prog.execPar ρ0) σ0).map RaceSite.conflicts = [[1000]] := by decide

/-- **The counterexample, checked.** `findWrongFrom` returned `[0]`; `follow_sound` turns it into a
run (`docs/race-search.md`). -/
theorem reaches_wrong : Reaches (.run (prog.execPar ρ0) σ0) .wrong :=
  follow_sound [0] _ _ rfl

theorem not_safe : ¬ Safe (.run (prog.execPar ρ0) σ0) := fun h => h reaches_wrong

#eval IO.println
  (explainParM rawName 8 (prog.execPar ρ0) (prog.execSeq ρ0) σ0 [1000])
#html explainHtmlParM rawName 8 (prog.execPar ρ0) (prog.execSeq ρ0) σ0 [1000]

end Aliasing

/-! ### Rejected: arithmetic *before* an array based at zero

`Loc := Nat`, so `A.base - 1` truncates to `A.loc 0`. What C would call undefined behaviour is here
a silent alias — silent until a second thread touches that cell. -/

namespace Underflow

theorem truncates : (A.base - 1 : Loc) = A.loc 0 := rfl

def prog : ParProg :=
  ParProg.par [ ParProg.store (A.base - 1) (.lit 7), ParProg.store (A.loc 0) (.lit 1) ]

theorem not_wf : prog.wfB = false := by decide

theorem reaches_wrong : Reaches (.run (prog.execPar ρ0) σ0) .wrong :=
  follow_sound [0] _ _ rfl

theorem not_safe : ¬ Safe (.run (prog.execPar ρ0) σ0) := fun h => h reaches_wrong

end Underflow

/-! ### Rejected: the stray write aliases a cell another thread reads -/

namespace ReadWrite

def prog : ParProg :=
  ParProg.par [ ParProg.store (A.loc 1000) (.lit 7), ParProg.load 0 (C.loc 0) ]

theorem not_wf : prog.wfB = false := by decide

theorem reaches_wrong : Reaches (.run (prog.execPar ρ0) σ0) .wrong :=
  follow_sound [0] _ _ rfl

theorem not_safe : ¬ Safe (.run (prog.execPar ρ0) σ0) := fun h => h reaches_wrong

end ReadWrite

end Paralever.Examples.Pointers
