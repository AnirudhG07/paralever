import Lang.Core.Exec
import Paralever.Compile.ExecArr
import Lang.Core.Analysis
import Bench.Time

/-! # Does the fork pay, and from what matrix size?

`Bench/Run.lean` measures *checking*. This measures *running*: a sequential matrix multiply, the
program `autoPar` proposes for it, and the two executed by `execTask` at a sequence of matrix
sizes.

The comparison is fair by theorem rather than by inspection. `rewrite_sound` says the rewrite
preserves the heap with no hypothesis, and `runTask_eq_runTaskSeq` says the spawned run and the
flattened run agree whenever `wfB` does — so a difference between the two columns is time, and the
checksum column is there to catch it if it ever is not.

Both runs go through `Core/Semantics.lean`'s `State`, which is a *function*: `σ.update l v` is a
closure, so a read after `k` writes walks `k` frames and the heap never shrinks. That is why peak
resident memory is a column here and not an afterthought — `docs/scale.md` § What would fix the
rest.

Rationale: `docs/bench.md`. -/

namespace Paralever.Bench.Threads
open Paralever Paralever.Lang

/-! ## Peak memory

`VmHWM` in `/proc/self/status` is the high-water mark of resident memory for the whole process, in
kilobytes. It is cumulative and never falls, so a row reports the peak *after* its own run and the
growth over the row before it is what that size cost. On a kernel without `/proc` the column is
reported as zero rather than guessed at. -/
def peakRssKb : IO Nat := do
  try
    let txt ← IO.FS.readFile "/proc/self/status"
    let line := (txt.splitOn "\n").find? (·.startsWith "VmHWM:")
    match line with
    | none   => pure 0
    | some l => pure ((l.splitOn " ").filterMap (·.toNat?) |>.head?.getD 0)
  catch _ => pure 0

/-! ## The kernel, written sequentially

`C := A × B` at `n × n` as a straight `;`-chain: no `parallel` block is written by hand. Finding the
threads is `autoPar`'s job, which is the point of the measurement. -/

/-- One `(i, j)` cell: the accumulator, the `n`-step dot product, then the store. This is one
register-closed segment, so it is the unit `atoms` hands the planner. -/
def cell (n aBase bBase cBase i j : Nat) : ParProg :=
  ParProg.block <|
    ParProg.set 2 (.lit 0)
      :: (List.range n).flatMap (fun k =>
            [ ParProg.load 0 (aBase + i * n + k)
            , ParProg.load 1 (bBase + k * n + j)
            , ParProg.set 2 (.add (.reg 2) (.mul (.reg 0) (.reg 1))) ])
      ++ [ ParProg.store (cBase + i * n + j) (.reg 2) ]

/-- The sequential program. `A` at `0`, `B` at `n²`, `C` at `2n²`. -/
def matmulSeq (n : Nat) : ParProg :=
  ParProg.block <| (List.range n).flatMap fun i =>
    (List.range n).map (cell n 0 (n*n) (2*n*n) i)

/-- `C := A × B` with one thread per band of rows — the shape a parallelizer with a fixed thread
budget would emit, kept as the control against `autoPar`'s own choice. -/
def matmulBanded (n threads : Nat) : ParProg :=
  let b := (n + threads - 1) / max 1 threads
  ParProg.par <| (List.range threads).map fun t =>
    ParProg.block <| (List.range b).filterMap fun r =>
      let i := t * b + r
      if i ≥ n then none
      else some (ParProg.block ((List.range n).map (cell n 0 (n*n) (2*n*n) i)))

/-- Memory operations plus register assignments: `n²(3n + 2)`. Counted rather than measured, since
the shape above is fixed. -/
def instructions (n : Nat) : Nat := n * n * (3 * n + 2)

/-- Nodes in the term, walked once so a timing never pays for building it. -/
partial def size : ParProg → Nat
  | .seq a b   => size a + size b
  | .par cs    => cs.foldl (fun acc c => acc + size c) 1
  | .label _ b => 1 + size b
  | _          => 1

/-- How many threads the top-level forks of a program carry, summed. -/
partial def threadsOf : ParProg → Nat
  | .par cs    => cs.length
  | .seq a b   => threadsOf a + threadsOf b
  | .label _ b => threadsOf b
  | _          => 0

/-- `A` and `B` filled with small non-zero values, `C` zero. -/
def heap (n : Nat) : State :=
  fun l => .int (if l < 2 * n * n then ((l % 7 : Nat) : Int) + 1 else 0)

/-- The array heap the twin runs on: `A`, `B` and `C` laid out as `heap` lays them out. -/
def aheap (n : Nat) : AState :=
  ⟨Array.ofFn (n := 3 * n * n) fun i =>
      .int (if i.val < 2 * n * n then ((i.val % 7 : Nat) : Int) + 1 else 0)⟩

/-- Force an array run: every cell of `C` summed, which is O(1) a cell here. -/
def forceCArr (n : Nat) (a : AState) : Int :=
  (List.range (n * n)).foldl
    (fun acc i => match a.get (2 * n * n + i) with | .int v => acc + v | _ => acc) 0

/-- Force the whole run: every cell of `C` is read back and summed. Without this the returned
`State` is an unevaluated closure and the timing measures nothing. -/
def forceC (n : Nat) (σ : State) : Int :=
  (List.range (n * n)).foldl
    (fun acc i => match σ (2 * n * n + i) with | .int v => acc + v | _ => acc) 0

/-! ## One row of the curve -/

structure Row where
  n         : Nat
  instrs    : Nat
  threads   : Nat
  planMs    : Ms
  seqMs     : Ms
  parMs     : Ms
  bandMs    : Ms
  arrMs     : Ms
  peakMb    : Nat
  /-- the runs' checksums, which `rewrite_sound` and `runTask_eq_runTaskSeq` say must be equal -/
  agree     : Bool
  deriving Repr, Inhabited

/-- Run one size: plan it, then time the sequential run, `autoPar`'s program, and the 16-band
control. Each term is walked once before it is timed, so no column pays for building it. -/
def row (n threads reps : Nat) (plan : Bool) : IO Row := do
  let s := matmulSeq n
  let σ := heap n
  let ρ : Regs := fun _ => 0
  let _ ← IO.lazyPure fun _ => size s
  let b := matmulBanded n threads
  let _ ← IO.lazyPure fun _ => size b
  let (vs, sSam) ← repeatTimed reps (IO.lazyPure fun _ => forceC n (ParProg.runTaskSeq s ρ σ).2)
  let (vb, bSam) ← repeatTimed reps (IO.lazyPure fun _ => forceC n (ParProg.runTask b ρ σ).2)
  let (va, aSam) ← repeatTimed reps (IO.lazyPure fun _ =>
    forceCArr n (execArr (ParProg.execPar b ρ) (aheap n)).2)
  let mut planMs := 0
  let mut parMs := 0
  let mut nthreads := threadsOf b
  let mut ok := vs == vb && vs == va
  if plan then
    let (p, planSam) ← repeatTimed 1 (IO.lazyPure fun _ => ParProg.autoPar s)
    let _ ← IO.lazyPure fun _ => size p
    let (vp, pSam) ← repeatTimed reps (IO.lazyPure fun _ => forceC n (ParProg.runTask p ρ σ).2)
    planMs := planSam.median
    parMs := pSam.median
    nthreads := threadsOf p
    ok := ok && vs == vp
  let kb ← peakRssKb
  pure { n, instrs := instructions n, threads := nthreads
       , planMs, seqMs := sSam.median, parMs
       , bandMs := bSam.median, arrMs := aSam.median, peakMb := kb / 1024, agree := ok }

/-- `a / b` to two decimals, without a `Float`. -/
def ratio (a b : Nat) : String :=
  if b == 0 then "--"
  else
    let h := a * 100 / b
    toString (h / 100) ++ "." ++ (if h % 100 < 10 then "0" else "") ++ toString (h % 100) ++ "x"

def pad (w : Nat) (s : String) : String := "".pushn ' ' (w - min w s.length) ++ s

def Row.line (r : Row) : String :=
  pad 5 (toString r.n) ++ pad 13 (toString r.instrs) ++ pad 9 (toString r.threads)
    ++ pad 9 (toString r.planMs) ++ pad 9 (toString r.seqMs) ++ pad 9 (toString r.parMs)
    ++ pad 9 (ratio r.seqMs r.parMs) ++ pad 9 (toString r.bandMs)
    ++ pad 9 (ratio r.seqMs r.bandMs) ++ pad 9 (toString r.arrMs)
    ++ pad 9 (ratio r.seqMs r.arrMs) ++ pad 9 (toString r.peakMb)
    ++ (if r.agree then "" else "   DISAGREE")

def header : String :=
  pad 5 "n" ++ pad 13 "instrs" ++ pad 9 "threads" ++ pad 9 "plan ms" ++ pad 9 "seq ms"
    ++ pad 9 "auto ms" ++ pad 9 "speedup" ++ pad 9 "band ms" ++ pad 9 "speedup" ++ pad 9 "peak MB"
    ++ "\n" ++ "".pushn '-' 90

/-- Walk the sizes, stopping once a row costs more than `ceilingMs`. Each row is flushed as it is
produced, so a curve that is cut short still reports what it reached. -/
partial def curve (sizes : List Nat) (threads reps ceilingMs : Nat) (plan : Bool) :
    IO (List Row) := do
  let mut rows : List Row := []
  for n in sizes do
    let r ← row n threads reps plan
    IO.println r.line
    (← IO.getStdout).flush
    rows := rows ++ [r]
    if max r.seqMs (max r.parMs r.bandMs) > ceilingMs then
      IO.println s!"(stopped: n = {n} already costs {max r.seqMs (max r.parMs r.bandMs)} ms)"
      (← IO.getStdout).flush
      break
  pure rows

/-! ## Is the spawn reaching the scheduler?

`execChilds` spawns with `Task.spawn fun _ => (execTask p σ).get`. The body never mentions the
lambda's argument, so a compiler free to float it computes the child on the *calling* thread and
leaves the task with nothing to do. This probe is that shape with arithmetic in it and no heap, so
the only question it asks is where the work runs: wall time against CPU time answers it. -/

def busy : Nat → Nat → Nat
  | 0,     acc => acc
  | n + 1, acc => busy n ((acc * 1664525 + 1013904223) % 2147483647)

/-- `execChilds`' spawn shape, with real work in it. -/
def spawnLikeExecChilds (k work : Nat) : Nat :=
  let ts := (List.range k).map (fun i => Task.spawn fun _ => busy work i)
  (ts.map Task.get).foldl (· + ·) 0

/-- `execArrChilds`' *recursion* shape, which `spawnLikeExecChilds` does not have: spawn one,
recurse, then `get`. If the compiler sinks the `let` to its use site, the spawn happens only when
the `get` is about to block, and the whole fork runs on one thread. -/
def spawnRec : Nat → Nat → Nat
  | 0,     _    => 0
  | k + 1, work =>
      let t := Task.spawn fun _ => busy work k
      let rest := spawnRec k work
      t.get + rest

/-- The same recursion, but the spawned closure captures a large boxed-`Val` array, as
`execArrChilds`' does. Arithmetic only inside, so any CPU-time collapse is about what the closure
carries across the thread boundary and not about the work. -/
def spawnRecArr (cells : Array Val) : Nat → Nat → Nat
  | 0,     _    => 0
  | k + 1, work =>
      let t := Task.spawn fun _ =>
        busy work (match cells[k]? with | some (.int v) => v.toNat | _ => 1)
      let rest := spawnRecArr cells k work
      t.get + rest

/-- The same again, but each child also *writes* its own copy of the array first, which is what a
child's first store does. -/
def spawnRecArrW (cells : Array Val) : Nat → Nat → Nat
  | 0,     _    => 0
  | k + 1, work =>
      let t := Task.spawn fun _ =>
        let c := cells.setIfInBounds k (.int 7)
        busy work (match c[k]? with | some (.int v) => v.toNat | _ => 1)
      let rest := spawnRecArrW cells k work
      t.get + rest

/-- `k` children, each hammering **its own** cell `work` times: disjoint writes, no shared row or
column, no join to speak of. If this does not get cores, nothing about matmul's access pattern is
to blame and the fault is in running a `ParM` term inside a task. -/
def disjointPar (k work : Nat) : ParProg :=
  ParProg.par <| (List.range k).map fun i =>
    ParProg.block (ParProg.store i (.lit 0)
      :: (List.range work).flatMap (fun _ =>
            [ParProg.load 1 i, ParProg.store i (.add (.reg 1) (.lit 1))]))

/-- The same children run one after another through the same executor. -/
def disjointSeq (k work : Nat) : ParProg :=
  ParProg.block <| (List.range k).map fun i =>
    ParProg.block (ParProg.store i (.lit 0)
      :: (List.range work).flatMap (fun _ =>
            [ParProg.load 1 i, ParProg.store i (.add (.reg 1) (.lit 1))]))

def disjointProbe (k work : Nat) : IO Unit := do
  let ρ : Regs := fun _ => 0
  let a : AState := AState.zeros (k + 8)
  let p := disjointPar k work
  let q := disjointSeq k work
  let _ ← IO.lazyPure fun _ => size p + size q
  let (_, x) ← repeatTimed 1 (IO.lazyPure fun _ =>
    let r := (execArr (ParProg.execPar p ρ) a).2
    (List.range k).foldl (fun (acc : Int) i =>
      match r.get i with | .int v => acc + v | _ => acc) 0)
  let (_, y) ← repeatTimed 1 (IO.lazyPure fun _ =>
    let r := (execArr (ParProg.execPar q ρ) a).2
    (List.range k).foldl (fun (acc : Int) i =>
      match r.get i with | .int v => acc + v | _ => acc) 0)
  IO.println s!"{k} children x {work} read-modify-writes on disjoint cells"
  IO.println s!"  forked {x.median} ms   unforked {y.median} ms   gain {ratio y.median x.median}"
  (← IO.getStdout).flush

/-- Allocating work rather than arithmetic: `busy` never touches the heap, and `execArr` allocates
a `ParM` node and an `AState` at every step. This is the only other variable between them. -/
def busyAlloc : Nat → List Nat → Nat
  | 0,     acc => acc.length
  | n + 1, acc => busyAlloc n (n :: acc)

def spawnRecAlloc : Nat → Nat → Nat
  | 0,     _    => 0
  | k + 1, work =>
      let t := Task.spawn fun _ => busyAlloc work []
      let rest := spawnRecAlloc k work
      t.get + rest

/-- `execArr` inside a task, with **nothing** shared between children: each builds its own program
and its own heap inside its own task. No `par` node, no `execArrChilds`, no common `ρ`, no common
array. If this does not get cores, the fault is in running a `ParM` term on a worker thread and
nowhere else. -/
def spawnRecExec (k work : Nat) : Int :=
  match k with
  | 0     => 0
  | j + 1 =>
      let t := Task.spawn fun _ =>
        let prog := ParProg.block (ParProg.store 0 (.lit 0)
          :: (List.range work).flatMap (fun _ =>
                [ParProg.load 1 0, ParProg.store 0 (.add (.reg 1) (.lit 1))]))
        match (execArr (ParProg.execPar prog (fun _ => 0)) (AState.zeros 8)).2.get 0 with
        | .int v => v
        | _      => 0
      let rest := spawnRecExec j work
      t.get + rest

/-- The same again, but every child starts from **one** `AState` and **one** `Regs`, as
`execArrChilds` makes them. The programs are still built per child inside the task, so the only
thing that changed from `spawnRecExec` is who owns the heap and the register file. -/
def spawnRecExecShared (a : AState) (ρ : Regs) (k work : Nat) : Int :=
  match k with
  | 0     => 0
  | j + 1 =>
      let t := Task.spawn fun _ =>
        let prog := ParProg.block (ParProg.store j (.lit 0)
          :: (List.range work).flatMap (fun _ =>
                [ParProg.load 1 j, ParProg.store j (.add (.reg 1) (.lit 1))]))
        match (execArr (ParProg.execPar prog ρ) a).2.get j with
        | .int v => v
        | _      => 0
      let rest := spawnRecExecShared a ρ j work
      t.get + rest

def spawnProbe (k work : Nat) : IO Unit := do
  let (_, a) ← repeatTimed 1 (IO.lazyPure fun _ => spawnLikeExecChilds k work)
  IO.println s!"{k} spawned tasks x {work} steps, map-then-get: {a.median} ms wall (compare against CPU time)"
  let (_, b) ← repeatTimed 1 (IO.lazyPure fun _ => spawnRec k work)
  IO.println s!"{k} spawned tasks x {work} steps, spawn-recurse-get: {b.median} ms wall"
  let arr : Array Val := Array.ofFn (n := 49152) fun i => .int ((i.val % 7 : Nat) + 1)
  let _ ← IO.lazyPure fun _ => arr.size
  let (_, c) ← repeatTimed 1 (IO.lazyPure fun _ => spawnRecArr arr k work)
  IO.println s!"{k} spawned tasks x {work} steps, closure carries a 49152-cell Val array: {c.median} ms wall"
  let (_, d) ← repeatTimed 1 (IO.lazyPure fun _ => spawnRecArrW arr k work)
  IO.println s!"{k} spawned tasks x {work} steps, same and each child writes it: {d.median} ms wall"
  let (_, e) ← repeatTimed 1 (IO.lazyPure fun _ => spawnRecAlloc k (work / 20))
  IO.println s!"{k} spawned tasks x {work / 20} allocating steps: {e.median} ms wall"
  let (_, f) ← repeatTimed 1 (IO.lazyPure fun _ => spawnRecExec k (work / 100))
  IO.println s!"{k} spawned tasks x {work / 100} execArr steps, nothing shared: {f.median} ms wall"
  let a0 := AState.zeros (k + 8)
  let ρ0 : Regs := fun _ => 0
  let _ ← IO.lazyPure fun _ => a0.size
  let (_, g) ← repeatTimed 1 (IO.lazyPure fun _ => spawnRecExecShared a0 ρ0 k (work / 100))
  IO.println s!"{k} spawned tasks x {work / 100} execArr steps, one shared heap and Regs: {g.median} ms wall"
  (← IO.getStdout).flush

/-! ## Registers against memory

`Regs = Reg → Int` and `State = Loc → Val` are the same shape: `set` and `update` both prepend a
closure frame. So a cost difference between them is not about registers or memory, it is about how
often a program reads back what it just wrote. These four shapes separate the two. -/

/-- `%0 := %0 + 1`, `n` times: read-modify-write on one register. -/
def regAcc (n : Nat) : ParProg :=
  ParProg.block (ParProg.set 0 (.lit 0)
    :: (List.range n).map (fun _ => ParProg.set 0 (.add (.reg 0) (.lit 1))))

/-- `A[0] := A[0] + 1`, `n` times: read-modify-write on one cell. -/
def memAcc (n : Nat) : ParProg :=
  ParProg.block (ParProg.store 0 (.lit 0)
    :: (List.range n).flatMap (fun _ =>
          [ParProg.load 1 0, ParProg.store 0 (.add (.reg 1) (.lit 1))]))

/-- `%0 := k`, `n` times: a register written `n` times and never read back. -/
def regWrite (n : Nat) : ParProg :=
  ParProg.block ((List.range n).map (fun k => ParProg.set 0 (.lit (Int.ofNat k))))

/-- `A[k] := 1` at `n` distinct cells, never read back. -/
def memWrite (n : Nat) : ParProg :=
  ParProg.block ((List.range n).map (fun k => ParProg.store k (.lit 1)))

/-- Write `n` distinct cells, then read an *unwritten* one back `n` times. Every read walks past
every write, because `update` prepends and the cell being read is at the base of the chain. This is
matmul's shape: `A` and `B` are never written, so each thread reads them past all of its own writes
to `C`. -/
def buriedRead (n : Nat) : ParProg :=
  ParProg.block ((List.range n).map (fun k => ParProg.store (k + 1) (.lit 1))
    ++ (List.range n).map (fun _ => ParProg.load 0 0))

/-- The same reads, with nothing written first: the chain is empty, so each read is O(1). -/
def freshRead (n : Nat) : ParProg :=
  ParProg.block ((List.range n).map (fun _ => ParProg.load 0 0))

/-- Run one shape and force its answer: the register file for a register shape, the heap for a
memory one. -/
def shapeMs (name : String) (p : ParProg) (reg : Bool) (reps : Nat) : IO Ms := do
  let ρ : Regs := fun _ => 0
  let σ : State := fun _ => .int 0
  let _ ← IO.lazyPure fun _ => size p
  let (_, sam) ← repeatTimed reps (IO.lazyPure fun _ =>
    let r := ParProg.runTaskSeq p ρ σ
    if reg then r.1 0 else match r.2 0 with | .int v => v | _ => 0)
  IO.println s!"  {name} {sam.median} ms"
  (← IO.getStdout).flush
  pure sam.median

def regVsMem (sizes : List Nat) (reps : Nat) : IO Unit := do
  IO.println "read-modify-write against write-only, registers against memory"
  for n in sizes do
    IO.println s!"n = {n}"
    let _ ← shapeMs "register accumulate  %0 := %0 + 1 " (regAcc n) true reps
    let _ ← shapeMs "memory   accumulate  A[0] := A[0]+1" (memAcc n) false reps
    let _ ← shapeMs "register write-only  %0 := k       " (regWrite n) true reps
    let _ ← shapeMs "memory   write-only  A[k] := 1     " (memWrite n) false reps
    let _ ← shapeMs "buried   read        A[0] after n writes" (buriedRead n) true reps
    let _ ← shapeMs "fresh    read        A[0], nothing written" (freshRead n) true reps

/-! ## The array twin on its own

The function-heap columns dominate a mixed run, so a CPU-against-wall reading of the whole thing
says nothing about the array. This walks the array column alone. -/

def arrayOnly (sizes : List Nat) (threads reps : Nat) : IO Unit := do
  IO.println (pad 5 "n" ++ pad 13 "instrs" ++ pad 9 "threads" ++ pad 10 "forked ms"
    ++ pad 14 "instr/ms" ++ pad 11 "no-fork ms" ++ pad 9 "gain")
  IO.println ("".pushn '-' 71)
  for n in sizes do
    let b := matmulBanded n threads
    let ρ : Regs := fun _ => 0
    let _ ← IO.lazyPure fun _ => size b
    let (_, sam) ← repeatTimed reps (IO.lazyPure fun _ =>
      forceCArr n (execArr (ParProg.execPar b ρ) (aheap n)).2)
    -- the same program with no fork at all: with an array heap there is no chain to shorten, so
    -- any gap between these two columns is cores and nothing else
    let sq := matmulSeq n
    let _ ← IO.lazyPure fun _ => size sq
    let (_, qsam) ← repeatTimed reps (IO.lazyPure fun _ =>
      forceCArr n (execArr (ParProg.execPar sq ρ) (aheap n)).2)
    let i := instructions n
    IO.println (pad 5 (toString n) ++ pad 13 (toString i) ++ pad 9 (toString threads)
      ++ pad 10 (toString sam.median)
      ++ pad 14 (if sam.median == 0 then "--" else toString (i / sam.median))
      ++ pad 11 (toString qsam.median) ++ pad 9 (ratio qsam.median sam.median))
    (← IO.getStdout).flush


/-! ## Where the fork's parallelism goes

`execArrChilds` spawns a `Task` per child. `execArrNS` is the same executor with that one line
changed to a direct call and nothing else, so the gap between them is what `Task.spawn` buys on
this workload — not what it buys on arithmetic, which `spawnProbe` already shows is real. -/

mutual

def execArrNS {α : Type} : ParM α → AState → α × AState
  | .pure a,      σ => (a, σ)
  | .read l k,    σ => execArrNS (k (σ.get l)) σ
  | .write l v k, σ => execArrNS (k ()) (σ.set l v)
  | .par cs k,    σ =>
      let r := execArrChildsNS cs σ
      execArrNS (k r.1) (joinArr σ r.2)

def execArrChildsNS {αs : List Type} : Childs ParM αs → AState → Results αs × List AState
  | .nil,       _ => ((), [])
  | .cons p ps, σ =>
      let r := execArrNS p σ
      match execArrChildsNS ps σ with
      | (rs, ss) => ((r.1, rs), r.2 :: ss)

end

/-- Build the children's `ParM` terms and nothing else: every child's first node forced, no heap
touched. Separates lowering cost from execution cost. -/
def lowerOnly (s : ParProg) (ρ : Regs) : Nat :=
  match ParProg.execPar s ρ with
  | .pure _      => 1
  | .read _ _    => 2
  | .write _ _ _ => 3
  | .par cs _    => 4 + childCount cs
where
  childCount {αs : List Type} : Childs ParM αs → Nat
    | .nil => 0
    | .cons _ ps => 1 + childCount ps

/-- Forked against the identical unforked executor on the **same** program, so the shape, the
lowering and the join are all held fixed and only the spawn varies. -/
def forkProbe (sizes : List Nat) (threads reps : Nat) : IO Unit := do
  IO.println "same banded program, same executor; the only difference is Task.spawn."
  IO.println (pad 5 "n" ++ pad 13 "instrs" ++ pad 9 "threads" ++ pad 9 "lower" ++ pad 11 "spawn ms"
    ++ pad 12 "direct ms" ++ pad 9 "gain" ++ pad 11 "flat ms")
  IO.println ("".pushn '-' 79)
  for n in sizes do
    let b := matmulBanded n threads
    let ρ : Regs := fun _ => 0
    let _ ← IO.lazyPure fun _ => size b
    let (_, lsam) ← repeatTimed reps (IO.lazyPure fun _ => lowerOnly b ρ)
    let (_, ssam) ← repeatTimed reps (IO.lazyPure fun _ =>
      forceCArr n (execArr (ParProg.execPar b ρ) (aheap n)).2)
    let (_, dsam) ← repeatTimed reps (IO.lazyPure fun _ =>
      forceCArr n (execArrNS (ParProg.execPar b ρ) (aheap n)).2)
    let sq := matmulSeq n
    let _ ← IO.lazyPure fun _ => size sq
    let (_, qsam) ← repeatTimed reps (IO.lazyPure fun _ =>
      forceCArr n (execArrNS (ParProg.execPar sq ρ) (aheap n)).2)
    IO.println (pad 5 (toString n) ++ pad 13 (toString (instructions n)) ++ pad 9 (toString threads)
      ++ pad 9 (toString lsam.median) ++ pad 11 (toString ssam.median)
      ++ pad 12 (toString dsam.median) ++ pad 9 (ratio dsam.median ssam.median)
      ++ pad 11 (toString qsam.median))
    (← IO.getStdout).flush

end Paralever.Bench.Threads
