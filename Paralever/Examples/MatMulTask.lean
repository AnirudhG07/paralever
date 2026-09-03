import Paralever.Compile.TaskFacts
import Paralever.Examples.MatMul

/-! # MatMul, the "second model": real `Task`, no `ParM`

Same relationship as `SumArrayTask.lean` to `SumArray.lean`: `MatMul.lean` proves `matmulPar`
correct against `ParM`'s abstract interleaving semantics, gated on `WellFormed`. This file computes
the *same* matrix product a completely different way — one real `Task.spawn` per output cell, via
`Compile/TaskFacts.lean`'s `parTasks` — and checks correctness by computation against
`MatMul.lean`'s own `cellCompute`-shape arithmetic, expressed here directly over `List Int` (no
`ParM`, no shared mutable state: each task only *reads* the two input lists, closed over
immutably, and *returns* its cell's value — `SortTask.lean`'s safety subtlety, satisfied by
construction since there is nothing here to write to until every task has already finished). -/

namespace Paralever.Examples.MatMulTask

/-- Cell `p`'s value, computed directly against `List Int` inputs — the `Task`-model's own spec,
answerable to the same `A*I=A` ground truth `MatMul.lean`'s `σ2` checks. -/
def cellPure (n : Nat) (avals bvals : List Int) (p : Nat) : Int :=
  (List.range n).foldl (fun acc k => acc + avals.getD (p / n * n + k) 0 * bvals.getD (k * n + p % n) 0) 0

/-- One real `Task.spawn` per output cell — genuinely handed to Lean's task scheduler, unlike
anything in `MatMul.lean`. -/
def matmulTask (n : Nat) (avals bvals : List Int) : Task (List Int) :=
  parTasks id ((List.range (n * n)).map (fun p (_ : Unit) => cellPure n avals bvals p))

/-- Correctness by computation, not by an independence proof — unconditional on `n`/`avals`/
`bvals`, because `parTasks` never touches shared mutable state for `WellFormed`/`Indep` to protect. -/
theorem matmulTask_eq (n : Nat) (avals bvals : List Int) :
    (matmulTask n avals bvals).get = (List.range (n * n)).map (cellPure n avals bvals) := by
  unfold matmulTask
  rw [parTasks_eq]
  simp only [id, List.map_map]
  congr 1

/-! `A = [[1,2],[3,4]]`, `B = I` — `A*I` should equal `A`, matching `MatMul.lean`'s `σ2` check. -/

example : (matmulTask 2 [1, 2, 3, 4] [1, 0, 0, 1]).get = [1, 2, 3, 4] := rfl

end Paralever.Examples.MatMulTask
