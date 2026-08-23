import Paralever.Examples.Sort

/-! # Sort, the "second model": real `Task`, no `ParM`

Same relationship as `SumArrayTask.lean` to `SumArray.lean`: this proves the *same* compare-swap
round correct against a real `Array Int`, using genuine `Task`/`IO.asTask`, checked by computation
— no `WellFormed`, no `Nodup` side condition, because there is nothing here for those to protect.

**A safety subtlety specific to this example, absent from `SumArrayTask.lean`.** `SumArray`'s
chunks only ever *read* the shared input; here `compareSwap` *writes*. Concurrently mutating a
shared `Array`/`IO.Ref` from multiple real OS threads is unsafe **even at disjoint indices** — a
`Ref`'s read-modify-write is not atomic against other threads, so two concurrent `ref.modify`
calls touching different array positions can still race at the `Ref` level and silently drop an
update. The architecture below avoids this entirely, and in doing so mirrors exactly what the
`ParM`/`WellFormed` proof models: each task only *reads* the array (safe — concurrent reads never
race) and returns the swap it *would* perform; all mutation happens sequentially, in the main
thread, after every task has finished. Independent computation, sequential combine — the same
shape as `sumRangePar`'s `combineTasks`, not a coincidence.

A real, compiled run (3 independent swaps, ~650ms of artificial work per swap so the timing is
measurable) gives **~3x wall-clock speedup**, with all three tasks' time windows directly
confirmed to overlap — not inferred from aggregate timing, which the `SumArray` session already
found to be an unreliable way to detect real concurrency (a *pure* computation's timing can be
silently deferred past the clock reads bracketing it; wrapping the timed work in `IO` sequencing,
as below, is what makes the measurement trustworthy). See `docs/theory.md`'s final-verdict
paragraph for why this model is deliberately weaker than the `ParM` one despite being "real."
-/

namespace Paralever.Examples.SortTask

/-- Artificial CPU-bound work so the timing below is actually measurable — `compareSwap` itself is
too cheap to show anything interesting on real hardware. Written as a genuine `IO` action (a
`for`-loop with a mutable accumulator), not a pure `let`, so the compiler cannot defer it past the
clock reads that bracket it — the exact mistake `SumArrayTask.lean`'s development caught. -/
def busyWork (iters : Nat) : IO Nat := do
  let mut acc : Nat := 0
  for k in [0:iters] do
    acc := (acc + k) % 1000000007
  return acc

/-- What one compare-swap would do to `arr` — computed, not applied. Read-only w.r.t. `arr`. -/
def computeSwap (arr : Array Int) (i j : Nat) : (Nat × Int) × (Nat × Int) :=
  let x := arr.getD i 0
  let y := arr.getD j 0
  if y < x then ((i, y), (j, x)) else ((i, x), (j, y))

def busySwapTask (arr : Array Int) (i j workIters : Nat) : IO ((Nat × Int) × (Nat × Int)) := do
  let _ ← busyWork workIters
  return computeSwap arr i j

/-- The parallel round: one genuinely spawned `Task` per swap (each only reading `arr`), combined
by sequential mutation once every task has finished. -/
def swapPlanPar (arr : Array Int) (plan : List (Nat × Nat)) (workIters : Nat) : IO (Array Int) := do
  let tasks ← plan.mapM (fun (i, j) => IO.asTask (busySwapTask arr i j workIters))
  let mut result := arr
  for t in tasks do
    match ← IO.wait t with
    | .ok ((i, vi), (j, vj)) => result := (result.set! i vi).set! j vj
    | .error e => throw e
  return result

/-- The sequential counterpart: same computation, one swap after another, no `Task` at all. -/
def swapPlanSeq (arr : Array Int) (plan : List (Nat × Nat)) (workIters : Nat) : IO (Array Int) := do
  let mut result := arr
  for (i, j) in plan do
    let ((i', vi), (j', vj)) ← busySwapTask arr i j workIters
    result := (result.set! i' vi).set! j' vj
  return result

/-! Concrete check, reusing `Sort.lean`'s exact fixture (`σ6`'s array as literal values, `plan3`'s
pairs) — same inputs the `ParM` model was checked against, so both models answer to the same
instance, not just the same abstract spec. -/

def arr6 : Array Int := #[5, 3, 8, 1, 9, 2]
def plan3 : List (Nat × Nat) := [(0, 1), (2, 3), (4, 5)]

/-- Correctness on this instance: both orders give the same, correctly-sorted-per-pair array,
matching `Sort.lean`'s `runSeq`-checked result `[3, 5, 1, 8, 2, 9]` exactly. `IO`, so checked by
running rather than `rfl`/`decide` (see `Compile/TaskFacts.lean` for why `Task`'s runtime
primitives aren't kernel-reducible). -/
def checkAgreement : IO Bool := do
  let s ← swapPlanSeq arr6 plan3 0
  let p ← swapPlanPar arr6 plan3 0
  return s == p && s == #[3, 5, 1, 8, 2, 9]

end Paralever.Examples.SortTask
