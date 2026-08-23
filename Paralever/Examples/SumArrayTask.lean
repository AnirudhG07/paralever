import Paralever.Compile.TaskFacts
import Paralever.Examples.SumArray

/-! # SumArray, the "second model": real `Task`, no `ParM`

`Examples/SumArray.lean` proves `sumRange_par_seq_eq` against `ParM`'s abstract interleaving
semantics — general (any schedule), but gated on `WellFormed` and on the one open case in
`Theory/Decomposition.lean`.

This file proves the *same reduce algorithm* correct a completely different way: write it
directly against Lean's real `Task` (genuine `Task.spawn`, not the `ParM` model), and check
correctness by computation against `sumRangePure` — the identical pure spec `SumArray.lean` already
uses, so both models are answerable to the same ground truth. See `Compile/TaskFacts.lean` for
why this method is complete-but-weaker: no `WellFormed`, no schedule quantification, but also no
ability to even express a data race, since `Task` is `rfl`-trivial in the logic.
-/

namespace Paralever.Examples.SumArrayTask

open Paralever Paralever.Examples.SumArray

/-- Sum one chunk as a genuinely spawned `Task` — this call really does hand work to Lean's task
scheduler, unlike anything in `ParM`. -/
def sumChunkTask (vals : List Int) (locs : List Loc) : Task Int :=
  Task.spawn (fun _ => sumRangePure (arrayState vals) locs)

/-- One `Task.spawn` per chunk, combined via `combineTasks` (the same algorithm as core's
`Task.mapList`, `docs/theory.md`/`papers.md`). -/
def sumRangeParTask (vals : List Int) (chunks : ChunkPlan) : Task Int :=
  combineTasks (List.foldl (· + ·) 0) .default false (chunks.map (sumChunkTask vals)) []

/-- Correctness by computation, not by an independence proof: unconditional on `vals`/`chunks` —
no `WellFormed`, no `Indep`, because there is no shared mutable state for those to protect against.
Each chunk closes over its own copy of the (immutable) `vals`; nothing to race on. -/
theorem sumRangeParTask_eq (vals : List Int) (chunks : ChunkPlan) :
    (sumRangeParTask vals chunks).get
      = (chunks.map (sumRangePure (arrayState vals))).foldl (· + ·) 0 := by
  unfold sumRangeParTask
  rw [combineTasks_eq]
  congr 1
  rw [List.map_map]
  rfl

/-! Concrete checks, both even and uneven chunking, reusing `SumArray.lean`'s exact fixtures — same
inputs the `ParM` model was checked against. -/

example : (sumRangeParTask vals8 evenPlan8).get = 36 := rfl
example : (sumRangeParTask vals8 unevenPlan8).get = 36 := rfl

end Paralever.Examples.SumArrayTask
