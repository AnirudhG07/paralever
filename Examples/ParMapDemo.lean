import Paralever.Pragma.ParMap
import Paralever.Lib.Cost
import Examples.MergeSort

/-! # Sorting independent batches with an existing pure function

`mergeSortPure` is `MergeSort.lean`'s own pure spec, imported unchanged: no `ParM` rewrite, no
locations, no footprint proof. `parMap` (`Pragma/ParMap.lean`) applies it to batches each branch
owns outright, so `parMap_wellformed` is unconditional. The six standard steps, with step 6 coming
out an *equality* — see below. Rationale: `docs/cost.md`. -/

namespace Paralever.Examples.ParMapDemo
open Paralever Paralever.Pragma.ParMap Paralever.Examples.MergeSort

def batches : List (List Int) := [[5, 3, 8], [1, 9, 2], [7, 4, 6]]

/-! ### pure -/

def sortedBatchesPure : List (List Int) := batches.map mergeSortPure

/-! ### seq -/

def sortedBatchesSeq : ParM (List (List Int)) := seqMap mergeSortPure batches

/-! ### par -/

def sortedBatchesPar : ParM (List (List Int)) := parMap mergeSortPure batches

/-! ### pure = seq -/

theorem pure_eq_seq (σ : State) : (runSeq sortedBatchesSeq σ).1 = sortedBatchesPure := by
  simp [sortedBatchesSeq, sortedBatchesPure, seqMap, batches, runSeq]

example : sortedBatchesPure = [[3, 5, 8], [1, 2, 9], [4, 6, 7]] := by
  simp [sortedBatchesPure, batches, mergeSortPure, mergePure]

/-! ### seq = par -/

/-- No side condition at all — `parMap_wellformed`/`parMap_par_seq_eq` are unconditional in the
function and the chunking, because every branch of the parallel tree is a bare `.pure`. -/
theorem seq_eq_par (σ : State) : sortedBatchesPar ∥≡ sortedBatchesSeq from σ :=
  parMap_par_seq_eq mergeSortPure batches σ

/-! ### time par = time seq

Step 6 is **false** here, and the honest statement is the equality below. `time` counts parallel
rounds of *memory* operations (`docs/cost.md`), and `parMap f chunks` is `parAll` over branches that
are each a bare `ParM.pure`: no reads, no writes, so `work = time = 0` on both sides and there are
no rounds to save. Showing a speedup for the pure computation inside `mergeSortPure` would need a
different cost measure — `docs/cost.md`'s "what this does not claim". -/

theorem work_eq (σ : State) : work sortedBatchesPar σ = work sortedBatchesSeq σ :=
  work_parAll_eq_seqAll _ σ

theorem time_par_zero (σ : State) : time sortedBatchesPar σ = 0 :=
  time_zero_of_work_zero _ σ (parMap_wellformed mergeSortPure batches σ)
    (work_parMap_zero mergeSortPure batches σ)

theorem time_seq_zero (σ : State) : time sortedBatchesSeq σ = 0 :=
  time_zero_of_work_zero _ σ
    (wellFormed_of_seqAll _ σ (parMap_wellformed mergeSortPure batches σ))
    (by rw [← work_eq]; exact work_parMap_zero mergeSortPure batches σ)

theorem time_eq (σ : State) : time sortedBatchesPar σ = time sortedBatchesSeq σ := by
  rw [time_par_zero, time_seq_zero]

end Paralever.Examples.ParMapDemo
