import Bench.Verdict

/-! # Wall clock, and the honesty conditions on it

The first timing code in the repository, and it lives in a library that `lake build` does not
elaborate anything against for a reason: a wall clock inside elaboration is not reproducible, and a
slow machine must not fail CI. Every number in `docs/scale.md` was obtained with `/usr/bin/time`
around the executable; this module does the same from inside, so that the script is committed.

Two conditions, both recorded with every measurement rather than assumed:

* **a timing is labelled with the parallelism in force.** The corpus is fanned out across cores,
  so a row measured while fifteen siblings ran is not comparable with one measured alone. `jobs` is
  carried in the row, and a report that mixes values says so.
* **a timing is a median, not a single run.** One run measures the page cache as much as the code.

Rationale: `docs/bench.md`. -/

namespace Paralever.Bench

/-- Milliseconds, kept as a `Nat` so a row is exactly reproducible in a `#guard` when a test wants
to pin one. -/
abbrev Ms := Nat

/-- Time one action, discarding nothing: the value and the elapsed milliseconds. -/
def timed {α : Type} (act : IO α) : IO (α × Ms) := do
  let t0 ← IO.monoMsNow
  let v ← act
  let t1 ← IO.monoMsNow
  pure (v, t1 - t0)

/-- Time a pure computation. `act` is forced by `pure ∘ f`, which is enough because every stage this
harness times ends in a `Bool`, a `Nat` or a `String` -- there is no lazy structure left to force.
A stage whose result is a large unevaluated tree would need `timedForced` instead. -/
def timedPure {α : Type} (f : Unit → α) : IO (α × Ms) := timed (pure (f ()))

/-- Time a pure computation, forcing it through `toString` first, for a stage whose result is a
structure rather than a scalar. The rendered size is **returned** rather than discarded: a guard
that only pretended to use it would be dead code the compiler may delete, and then the timing would
measure nothing. -/
def timedForced {α : Type} [ToString α] (f : Unit → α) : IO (α × Nat × Ms) := do
  let t0 ← IO.monoMsNow
  let n := (toString (f ())).length
  let t1 ← IO.monoMsNow
  pure (f (), n, t1 - t0)

/-- Repeat an action and keep the **median**, with the minimum and maximum beside it so a noisy
measurement is visible rather than averaged away. -/
structure Samples where
  median : Ms
  min    : Ms
  max    : Ms
  runs   : Nat
  deriving Repr, Inhabited, DecidableEq, BEq

def Samples.line (s : Samples) : String :=
  toString s.median ++ " ms (min " ++ toString s.min ++ ", max " ++ toString s.max
    ++ ", n=" ++ toString s.runs ++ ")"

/-- The median of a non-empty list; `0` for an empty one, which no caller produces. -/
def medianOf (xs : List Ms) : Ms :=
  let s := xs.mergeSort (fun a b => a ≤ b)
  match s.length with
  | 0 => 0
  | n => s.getD (n / 2) 0

def samplesOf (xs : List Ms) : Samples :=
  ⟨medianOf xs, xs.foldl min (xs.headD 0), xs.foldl max 0, xs.length⟩

/-- Run `act` `n` times and summarise. `n = 0` is treated as one run, so a caller cannot ask for a
summary of nothing. -/
def repeatTimed {α : Type} (n : Nat) (act : IO α) : IO (α × Samples) := do
  let reps := max 1 n
  let mut ms : List Ms := []
  let mut last : Option α := none
  for _ in [0:reps] do
    let (v, t) ← timed act
    ms := t :: ms
    last := some v
  match last with
  | some v => pure (v, samplesOf ms)
  | none   => panic! "repeatTimed: no run"

/-! ## Fanning the corpus out

One job per entry, `jobs` of them at a time. `IO.asTask` plus `IO.wait` rather than a dependency:
the work is coarse (a file read, a lowering, a `decide`), so chunking by core is as good as a work
queue and has no scheduler to get wrong. -/

/-- How many jobs to run at once. `0` means "ask the machine", which is `nproc` where there is one
and a conservative 4 where there is not -- Lean core exposes no processor count, and guessing high
would make every timing a contended timing. -/
def resolveJobs (requested : Nat) : IO Nat := do
  if requested > 0 then return requested
  try
    let out ← IO.Process.output { cmd := "nproc", args := #[] }
    match out.stdout.trimAscii.toNat? with
    | some n => return max 1 n
    | none   => return 4
  catch _ => return 4

/-- Split a list into `n` round-robin groups, so a slow entry does not land every sibling in one
chunk. -/
def stripe {α : Type} (n : Nat) (xs : List α) : List (List α) :=
  let k := max 1 n
  (List.range k).map (fun i =>
    (xs.zipIdx.filter (fun p => p.2 % k == i)).map Prod.fst)

/-- **Run one job per entry, `jobs` at a time.** Order is restored before returning, so a report
does not depend on which core finished first. -/
def mapParallel {α β : Type} (jobs : Nat) (xs : List α) (f : α → IO β) : IO (List β) := do
  if jobs ≤ 1 then
    xs.mapM f
  else
    -- index each entry, run the stripes concurrently, then sort back
    let indexed := xs.zipIdx
    let groups := stripe jobs indexed
    let tasks ← groups.mapM (fun g =>
      IO.asTask (g.mapM (fun (x, i) => do let y ← f x; pure (i, y))))
    let mut acc : List (Nat × β) := []
    for t in tasks do
      match ← IO.wait t with
      | .ok rows   => acc := acc ++ rows
      | .error e   => throw e
    pure ((acc.mergeSort (fun a b => a.1 ≤ b.1)).map Prod.snd)

end Paralever.Bench
