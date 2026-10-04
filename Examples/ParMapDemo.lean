import Paralever.Pragma.ParMap
import Examples.MergeSort

/-! # Example: parallelizing an existing pure function, unmodified

The direct answer to "someone already wrote a pure recursive function, I want `par_seq_eq` about
running it in parallel." `mergeSortPure` is `MergeSort.lean`'s own pure spec — imported here as-is,
no `ParM` rewrite, no locations, no footprint proof. `parMap` (`Pragma/ParMap.lean`) is the whole
mechanism: sort three independent batches in parallel, get `par_seq_eq` for free because
`parMap_wellformed` is unconditional. -/

namespace Paralever.Examples.ParMapDemo
open Paralever Paralever.Pragma.ParMap Paralever.Examples.MergeSort

def batches : List (List Int) := [[5, 3, 8], [1, 9, 2], [7, 4, 6]]

/-- Sort every batch in parallel, using `mergeSortPure` exactly as `MergeSort.lean` defined it. -/
def sortedBatchesPar : ParM (List (List Int)) := parMap mergeSortPure batches

example : (runSeq sortedBatchesPar (fun _ => .int 0)).1 = [[3, 5, 8], [1, 2, 9], [4, 6, 7]] := by
  simp [sortedBatchesPar, batches, parMap, runSeq, mergeSortPure, mergePure]

/-- No side condition at all — `parMap_wellformed`/`parMap_par_seq_eq` are unconditional on the
function and the chunking. -/
theorem sortedBatchesPar_par_seq_eq (σ : State) :
    sortedBatchesPar ∥≡ seqMap mergeSortPure batches from σ :=
  parMap_par_seq_eq mergeSortPure batches σ

end Paralever.Examples.ParMapDemo
