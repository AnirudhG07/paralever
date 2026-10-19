import Paralever.Lang.Core
import Paralever.Compile.Exec

/-! # Running a `ParProg` on real threads

`execTask` spawns a Lean `Task` at every `par` node and runs everything else on the current thread.
A `ParProg` lowers into `ParM`, so it inherits that. `runTask_eq` is what makes it trustworthy: the
spawned run provably computes the canonical sequential answer whenever `wfB` holds, and
`runTask_eq_runTaskSeq` makes a benchmark against the single-threaded run fair. -/

namespace Paralever.Lang
open Paralever

namespace ParProg

/-! ## Running it on real threads

A `ParProg` lowers into `ParM`, so it inherits `Compile/Exec.lean`'s `execTask`: one `Task` per
`par` child. `runTask_eq` is `execTask_get` at `execPar s ρ` — not a claim that the threads happen
to agree, but that the spawned run computes the canonical sequential answer whenever `wfB` holds. -/

/-- Run the program on real threads: one `Task` per thread of every `parallel` block. -/
def runTask (s : ParProg) (ρ : Regs) (σ : State) : Regs × State :=
  (execTask (execPar s ρ) σ).get

/-- **The threaded run computes the sequential answer.** The decidable check is the whole
hypothesis, so a program that `decide` accepts may be executed on real threads with the sequential
result guaranteed. -/
theorem runTask_eq {s : ParProg} (h : wfB s = true) (ρ : Regs) (σ : State) :
    runTask s ρ σ = runSeq (execPar s ρ) σ :=
  execTask_get _ σ (wfB_wellFormed h ρ σ)

/-- Run the **sequential reading** through the same interpreter: `execSeq` has no `par` node, so
nothing is spawned and every thread of every block runs in order on this thread.

This is the comparison point for `runTask`. Both go through `execTask`, so a timing difference
between them is the parallelism and nothing else. -/
def runTaskSeq (s : ParProg) (ρ : Regs) (σ : State) : Regs × State :=
  (execTask (execSeq s ρ) σ).get

/-- The single-threaded run computes the canonical answer too. -/
theorem runTaskSeq_eq {s : ParProg} (h : wfB s = true) (ρ : Regs) (σ : State) :
    runTaskSeq s ρ σ = runSeq (execSeq s ρ) σ :=
  execTask_get _ σ (wfB_wellFormedSeq_all.1 s h ρ σ)

/-- **The spawned run and the single-threaded run agree.** Not observed on an example — proved, from
the decidable check alone. So a benchmark of the two measures speed and nothing else: whatever the
scheduler does, the answers are equal. -/
theorem runTask_eq_runTaskSeq {s : ParProg} (h : wfB s = true) (ρ : Regs) (σ : State) :
    runTask s ρ σ = runTaskSeq s ρ σ := by
  rw [runTask_eq h, runTaskSeq_eq h, execPar_runSeq_all.1 s ρ σ]

/-- The heap cells `probes` hold after a single-threaded run, for comparing against `evalTask`. -/
def evalTaskSeq (s : ParProg) (σ : State) (probes : List Loc) : List Val :=
  let σ' := (runTaskSeq s (fun _ => 0) σ).2
  probes.map σ'

/-- The heap cells `probes` hold after a threaded run — the `#eval`-friendly form. -/
def evalTask (s : ParProg) (σ : State) (probes : List Loc) : List Val :=
  let σ' := (runTask s (fun _ => 0) σ).2
  probes.map σ'
end ParProg

end Paralever.Lang
