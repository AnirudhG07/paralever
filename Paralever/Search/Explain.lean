import Paralever.Search.RaceSearch
import Paralever.Lib.Render

/-! # Explaining the counterexample

`RaceSearch` finds a `Schedule`; this prints it. Everything is derived from `step`'s own equations,
so this is one more interpreter over the same term and can report nothing the semantics does not.
-- ref: `docs/race-search.md`, `docs/semantics.md` -/

namespace Paralever

/-! ### The trace -/

/-- One step: who moved, what they did, and at an abort the forking node's pending actions. -/
structure StepView where
  /-- Child indices from the root to the thread that moved, or to the fork that aborted. -/
  path   : List Nat
  action : Option Label
  /-- The value a read observed, or the value a write stored. -/
  value  : Option Val
  /-- At a racing step, one entry per child of the forking node: its pending actions, with values.
  -/
  groups : Option (List (List (Label × Option Val)))
  /-- The heap *after* this step; `none` at the abort, which has none. -/
  heap   : Option State

/-- Whether this step is the race detection rather than a move. -/
def StepView.racing (v : StepView) : Bool := v.groups.isSome

/-- Replay a schedule against the real semantics, recording each step. Stops early if the schedule
runs off the end of a successor list, or at `wrong`. -/
def traceSchedule {τ : Type} : Conf τ → Schedule → List StepView
  | _,        []     => []
  | .wrong,   _      => []
  | .run p σ, i :: s =>
      match (step p σ)[i]? with
      | none    => []
      | some c' =>
          let a := attribution p σ i
          let v := match a.action with
            | some (.read l)  => some (σ l)
            | some (.write l) => c'.heap?.map (fun σ' => σ' l)
            | none            => none
          ⟨a.path, a.action, v, a.abort, c'.heap?⟩ :: traceSchedule c' s
  termination_by _ s => s.length

/-- The heap a schedule ends in, or `none` if it aborts or runs off the end. -/
def finalHeap {τ : Type} (p : ParM τ) (σ : State) (s : Schedule) : Option State :=
  (follow (.run p σ) s).bind Conf.heap?

private def padTo (s : String) (w : Nat) : String :=
  if s.length ≥ w then s else s ++ String.ofList (List.replicate (w - s.length) ' ')

private def rule (c : String) (w : Nat) : String :=
  String.join (List.replicate w c)

/-- How a report prints an address. `rawName` is the bare location; a layout supplies `W2[0, 3]`
(`Lang/Layout.lean`). A function rather than a `Layout` so `Search/` need not know layouts exist. -/
abbrev LocName := Loc → String

/-- Addresses as plain numbers. -/
def rawName : LocName := toString

/-- `xs` as text, at most `n` entries then a count. A 60-write footprint is otherwise a line some
600 characters wide, which no pane shows and no reader needs. -/
def clipStr (lb rb : String) (n : Nat) (xs : List String) : String :=
  lb ++ ", ".intercalate (xs.take n) ++
    (if xs.length ≤ n then "" else ", … +" ++ toString (xs.length - n) ++ " more") ++ rb

/-- A set of locations: braces, as `Indep`'s clauses are written. -/
def clipSet (n : Nat) (xs : List String) : String := clipStr "{" "}" n xs

/-- An ordered sequence, such as a schedule. -/
def clipList (n : Nat) (xs : List String) : String := clipStr "[" "]" n xs

/-- `clipStr` on locations, named. -/
def clipNames (nm : LocName) (n : Nat) (ls : List Loc) : String := clipSet n (ls.map nm)

/-- `clipStr` on raw locations. -/
def clipLocs (n : Nat) (ls : List Loc) : String := clipNames rawName n ls

/-- Locations in order of first mention, without repeats. -/
def nubLocs (ls : List Loc) : List Loc :=
  ls.foldl (fun acc l => if acc.contains l then acc else acc ++ [l]) []

def showLabel (nm : LocName) : Label → String
  | .read l  => "read [" ++ nm l ++ "]"
  | .write l => "write [" ++ nm l ++ "]"

/-- A thread's name: its path through the fork tree, so nesting is visible (`T1.0`). The empty path
is the thread that is not inside any fork. -/
def threadName (path : List Nat) : String :=
  if path.isEmpty then "main" else "T" ++ ".".intercalate (path.map toString)

/-- The thread names appearing in a trace, in order of first move. The race detection itself belongs
to no thread, so it contributes no column. -/
def columnsOf (vs : List StepView) : List String :=
  vs.foldl (fun acc v =>
    let n := threadName v.path
    if v.racing || acc.contains n then acc else acc ++ [n]) []

/-- What one step did, as a cell. The renderers below print a racing step as its own full-width row
rather than as a cell, but `cellOf` still has to say something true about it: an abort is not a
join, and both have no action. -/
def cellOf (nm : LocName) (v : StepView) : String :=
  if v.racing then "✗ race" else
  match v.action, v.value with
  | some (.read l),  some x => "read [" ++ nm l ++ "] → " ++ showVal x
  | some (.write l), some x => "write [" ++ nm l ++ "] ← " ++ showVal x
  | some a,          none   => showLabel nm a
  | none,            _      => "join"

/-- The pairs of children that conflict at a racing node, with the locations witnessing it. -/
def conflictPairs (gs : List (List Label)) : List (Nat × Nat × List Loc) :=
  let idx := gs.zipIdx
  idx.flatMap fun (g, i) =>
    idx.filterMap fun (h, j) =>
      if j > i && racing g h then
        some (i, j, nubLocs (g.filterMap fun a =>
          if h.any (fun b => a.conflicts b) then some a.loc else none))
      else none

/-! ### Rows

A counterexample's information is at the end of the trace, so a long one collapses in the middle. -/

/-- A line of the rendered trace. -/
inductive TraceRow where
  /-- Step number (1-based) and what happened. -/
  | step   : Nat → StepView → TraceRow
  /-- How many steps were dropped, and how they split over threads. -/
  | elided : Nat → List (String × Nat) → TraceRow

/-- How many steps each thread took, in order of first move. -/
def threadTally (vs : List StepView) : List (String × Nat) :=
  (columnsOf vs).map fun c =>
    (c, (vs.filter fun v => !v.racing && threadName v.path == c).length)

/-- Keep the first `h` steps and the last `t`, collapsing the middle. -/
def traceRows (h t : Nat) (vs : List StepView) : List TraceRow :=
  let rows := vs.zipIdx.map fun (v, k) => TraceRow.step (k + 1) v
  if vs.length ≤ h + t then rows
  else
    let mid := (vs.drop h).take (vs.length - t - h)
    rows.take h ++ [TraceRow.elided mid.length (threadTally mid)] ++
      rows.drop (vs.length - t)

/-! ### The report model

One model, two renderers: `reportOf` builds the content, `renderText` prints it, and
`Search/ExplainHtml.lean` renders the same `Report` as a widget. Structured rather than
pre-formatted, so a widget can highlight the cell that moved while text pads columns. -/

/-- One heap cell at one step. -/
structure Cell where
  loc     : String
  value   : String
  /-- Whether this step changed it. -/
  changed : Bool

/-- One event of the execution: a thread acting at a time step. Several threads can share a step —
that is what a parallel program does, and it is how the two conflicting actions appear, since
`racingAll` rejects them for being ready at the *same* instant. -/
structure Step where
  /-- The time step, from `0`. -/
  time   : Nat
  /-- The thread, by `threadName`. -/
  thread : String
  action : String
  /-- The heap after this action, or `[]` when it never ran. -/
  state  : List Cell
  /-- This action did not execute: it is one of the pair that clash. -/
  pending : Bool

/-- A report item. -/
inductive Item where
  | step   : Step → Item
  /-- How many steps were dropped from the middle of a long trace, and how they split. -/
  | elided : Nat → List (String × Nat) → Item
  /-- The step at which the parallel program aborts, and why. -/
  | abort  : Nat → String → Item
  /-- A labelled final state. -/
  | line   : String → String → Item
  | note   : String → Item

abbrev Report := List Item

/-! ### Building it -/

/-- Cells of `σ` over `ls`, comma-separated. -/
def stateLine (nm : LocName) (σ : State) (ls : List Loc) (n : Nat := 8) : String :=
  let cells := ls.map fun l => nm l ++ "↦" ++ showVal (σ l)
  ", ".intercalate (cells.take n) ++
    (if ls.length ≤ n then "" else ", +" ++ toString (ls.length - n) ++ " more")

/-- A step's cells, comma-separated. -/
def cellsLine (cs : List Cell) (n : Nat := 8) : String :=
  ", ".intercalate ((cs.take n).map fun c => c.loc ++ "↦" ++ c.value) ++
    (if cs.length ≤ n then "" else ", +" ++ toString (cs.length - n) ++ " more")

/-- The locations where two heaps disagree. -/
def heapDiff (σ₁ σ₂ : State) (ls : List Loc) : List Loc :=
  ls.filter fun l => σ₁ l != σ₂ l

/-- One pending action as a reader sees an executed one: `write [9] ← 2`, not `write [9]`. -/
def pendingAction (nm : LocName) : Label × Option Val → String
  | (.read l,  _)      => "read [" ++ nm l ++ "]"
  | (.write l, some v) => "write [" ++ nm l ++ "] ← " ++ showVal v
  | (.write l, none)   => "write [" ++ nm l ++ "]"

/-- Which threads collided and where. Says `write to` only when no read is involved. -/
def abortReason (nm : LocName) (v : StepView) : String :=
  let gs := (v.groups.getD []).map (fun g => g.map Prod.fst)
  let pairs := conflictPairs gs
  let names := (pairs.flatMap fun t =>
      [threadName (v.path ++ [t.1]), threadName (v.path ++ [t.2.1])]).foldl
    (fun acc n => if acc.contains n then acc else acc ++ [n]) []
  let locs := nubLocs (pairs.flatMap fun t => t.2.2)
  let allWrites := locs.all fun l => gs.all fun g => g.all fun a => a.loc != l || a.isWrite
  ", ".intercalate names ++ (if allWrites then " write to: " else " access: ") ++
    clipNames nm 8 locs

/-- A pending action together with the thread about to perform it. -/
abbrev PendAct := String × (Label × Option Val)

/-- The conflicting pending actions in *child* order — the order `seqPair` would run them in. -/
def pendingList (v : StepView) : List PendAct :=
  let gs := v.groups.getD []
  let locs := nubLocs ((conflictPairs (gs.map fun g => g.map Prod.fst)).flatMap fun t => t.2.2)
  gs.zipIdx.flatMap fun (g, i) =>
    (g.filter fun a => locs.contains a.1.loc).map fun a => (threadName (v.path ++ [i]), a)

/-- The locations the conflict is about. -/
def conflictLocs (v : StepView) : List Loc :=
  nubLocs ((conflictPairs ((v.groups.getD []).map fun g => g.map Prod.fst)).flatMap fun t => t.2.2)

/-- Run pending actions in a given order: the heap it leaves, and what each read observed. A
read/write race leaves the *heap* unchanged and differs only in the value read, so both have to be
reported for the comparison below to mean anything. -/
def runPending (nm : LocName) : State → List PendAct → State × List String
  | σ, []                            => (σ, [])
  | σ, (_, (.write l, some v)) :: r  => runPending nm (σ.update l v) r
  | σ, (_, (.write _, none))   :: r  => runPending nm σ r
  | σ, (t, (.read l, _))       :: r  =>
      let rest := runPending nm σ r
      (rest.1, (t ++ " reads " ++ showVal (σ l)) :: rest.2)

/-- What one ordering is observed to do: the conflicting cells it leaves, and what its reads saw. -/
def outcomeOf (nm : LocName) (σ : State) (locs : List Loc) (o : List PendAct) : String :=
  let r := runPending nm σ o
  ", ".intercalate ((locs.map fun l => nm l ++ "↦" ++ showVal (r.1 l)) ++ r.2)

/-- **An ordering that actually disagrees.** The clashing actions are simultaneous and unordered, so
their listing order is a presentation choice — but not an arbitrary one: child order is what
`seqPair` runs, so listing them that way reproduces the sequential outcome and makes the race look
harmless. This picks the first candidate ordering whose *observable* differs from child order, so
the rows a reader follows top to bottom really do land somewhere else.

Only two orderings are tried, which settles every two-thread race; with more clashing threads both
candidates can agree, and then child order is reported and the two outcome lines coincide. -/
def divergingOrder (nm : LocName) (σ : State) (locs : List Loc) (pend : List PendAct) :
    List PendAct :=
  let outSeq := outcomeOf nm σ locs pend
  ([pend.reverse, pend].find? fun o => outcomeOf nm σ locs o != outSeq).getD pend.reverse

/-- **The actions that clash**, one per thread, at the step they were both ready. These are the
labels `racingAll` refused — read off the same `pendingChilds` the check ranged over, not a summary
of it — so a reader sees the contradiction rather than a verdict about it.

They are ordinary steps in every other respect, carrying the heap as it stands at that instant: no
cell is marked, because neither action ran. Only `pending` distinguishes them. -/
def pendingSteps (nm : LocName) (ls : List Loc) (time : Nat) (σ : State) (o : List PendAct) :
    List Item :=
  let cells := ls.map fun l => Cell.mk (nm l) (showVal (σ l)) false
  o.map fun (t, a) => Item.step ⟨time, t, pendingAction nm a, cells, true⟩

/-- The moves of an interleaving as report items, numbered from `0`. A long trace keeps its first
`head` steps and last `tail`, collapsing the middle. Each cell is flagged against the heap the step
started from. -/
def stepItems (nm : LocName) (ls : List Loc) (σ : State) (vs : List StepView)
    (head : Nat := 5) (tail : Nat := 14) : List Item :=
  let moves := vs.filter (fun v => !v.racing)
  let befores := σ :: moves.map (fun v => (v.heap).getD σ)
  let steps := moves.zipIdx.map fun (v, k) =>
    let before := (befores[k]?).getD σ
    let after  := (v.heap).getD before
    Item.step ⟨k, threadName v.path, cellOf nm v,
      ls.map (fun l => ⟨nm l, showVal (after l), after l != before l⟩), false⟩
  if steps.length ≤ head + tail then steps
  else
    let mid := (moves.drop head).take (moves.length - tail - head)
    steps.take head ++ [Item.elided mid.length (threadTally mid)] ++
      steps.drop (moves.length - tail)

/-- **The counterexample.** Every action that ran, then the two that could not, then what the
sequential run leaves instead. -/
def reportOf {τ : Type} (nm : LocName) (fuel : Nat) (p pseq : ParM τ) (σ : State)
    (ls : List Loc) : Report :=
  let ls := nubLocs ls
  let σseq := (runSeq pseq σ).2
  let sites := raceSites p σ
  let seqItem := Item.line "Sequential" (stateLine nm σseq ls)
  -- phase 1 is complete for the obligation, so on a clean program phase 2 would walk the whole
  -- interleaving space to re-derive what the scan already settled
  if sites.isEmpty then [.note "No counterexample: no par node fails Bernstein.", seqItem]
  else
  match findWrongGuided (targetsOf sites) fuel (.run p σ) with
  | some sch =>
      let vs := traceSchedule (.run p σ) sch
      let moves := vs.filter (fun v => !v.racing)
      let σnow := ((moves.reverse.head?).bind (fun v => v.heap)).getD σ
      stepItems nm ls σ vs ++
        (match (vs.filter (fun v => v.racing)).head? with
         | some v =>
             let pend := pendingList v
             let locs := conflictLocs v
             let order := divergingOrder nm σnow locs pend
             pendingSteps nm ls moves.length σnow order ++
               [ .abort moves.length (abortReason nm v),
                 -- only the cells the conflict is about: the rest of the heap is not in question,
                 -- and the aborted run has no final state to compare anyway
                 .line "Parallel" (outcomeOf nm σnow locs order),
                 .line "Sequential" (outcomeOf nm σnow locs pend) ]
         | none   => [.abort moves.length "unknown", seqItem])
  | none =>
      match findDivergence fuel p σ ls with
      | some (s₁, s₂, l) =>
          let fin := fun (h : Option State) =>
            match h with
            | some h => stateLine nm h ls ++ " (differs at " ++
                clipNames nm 8 (heapDiff h σseq ls) ++ ")"
            | none   => "aborts"
          stepItems nm ls σ (traceSchedule (.run p σ) s₁) ++
            [.line "Parallel A" (fin (finalHeap p σ s₁))] ++
          stepItems nm ls σ (traceSchedule (.run p σ) s₂) ++
            [.line "Parallel B" (fin (finalHeap p σ s₂)),
             .note ("Schedules disagree at " ++ nm l ++ "."), seqItem]
      | none =>
          [ .note ("No counterexample within " ++ toString fuel ++ " steps."), seqItem ]

/-! ### Rendering it as text -/

/-- A step or elision as table cells; `none` for the items that are plain lines. The identifier is
`step:thread`, so two threads at one step are two rows with the same step number — which is how the
clashing pair reads. -/
private def rowOf : Item → Option (List String)
  | .step s     => some [toString s.time ++ ":" ++ s.thread, s.action,
      if s.pending then "pending" else cellsLine s.state]
  | .elided n t => some ["⋮", toString n ++ " steps elided (" ++
      ", ".intercalate (t.map fun (c, k) => c ++ " ×" ++ toString k) ++ ")"]
  | _           => none

/-- The items that are plain lines. -/
private def lineOf : Item → String
  | .abort n reason => "Parallel aborts at Step " ++ toString n ++ ". Reason: " ++ reason ++ "."
  | .line k v       => k ++ ": " ++ v
  | .note s         => s
  | _               => ""

/-- Each column as wide as the widest cell it holds. A short row contributes to column `0` only. -/
private def colWidthsOf (rows : List (List String)) (header : List String) : List Nat :=
  header.zipIdx.map fun (h, i) =>
    rows.foldl (fun m row =>
      if row.length == header.length then max m ((row[i]?).getD "").length
      else if i == 0 then max m ((row[0]?).getD "").length
      else m) h.length

/-- Cells padded to their columns. The last is not padded: trailing spaces serve nothing and break
`#guard_msgs`. -/
private def renderCells (ws : List Nat) (cells : List String) : String :=
  "  ".intercalate (cells.zipIdx.map fun (c, i) =>
    if i + 1 == cells.length then c else padTo c ((ws[i]?).getD 0))

/-- A run of consecutive rows, with its header. -/
private def flushRows (rows : List (List String)) : List String :=
  if rows.isEmpty then []
  else
    let header := ["step:thread", "action", "state"]
    let ws := colWidthsOf rows header
    renderCells ws header :: rows.map (renderCells ws)

/-- Walk the items, batching consecutive rows into a table and emitting the rest as lines. -/
private def layout : List Item → List (List String) → List String
  | [],      pend => flushRows pend
  | i :: is, pend =>
      match rowOf i with
      | some row => layout is (pend ++ [row])
      | none     => flushRows pend ++ [lineOf i] ++ layout is []

/-- A `Report` as text. -/
def renderText (r : Report) : String := "\n".intercalate (layout r [])

/-- The counterexample for a `ParM` program, given its sequential counterpart and the locations to
show. -/
def explainParM {τ : Type} (nm : LocName) (fuel : Nat) (p pseq : ParM τ) (σ : State)
    (ls : List Loc) : String :=
  renderText (reportOf nm fuel p pseq σ ls)

/-- The counterexample for a `Prog`. -/
def explainProg (p : Prog) (σ : State) : String :=
  explainParM rawName p.stepBound p.toParM p.toSeq σ p.locs

/-! ## Examples -/

section Examples

private def σ0 : State := fun _ => .int 0

/-- Two threads, one cell: the abort is the first step, so no thread ever moves. -/
private def tiny : Prog := .par (.wr 5 7) (.wr 5 9)

/--
info: step:thread  action         state
0:T1         write [5] ← 9  pending
0:T0         write [5] ← 7  pending
Parallel aborts at Step 0. Reason: T0, T1 write to: {5}.
Parallel: 5↦7
Sequential: 5↦9
-/
#guard_msgs in
#eval IO.println (explainProg tiny σ0)

/-- Each side writes its own cells before colliding on `[9]`. -/
private def late : Prog :=
  .par (.seq (.wr 10 1) (.wr 9 1)) (.seq (.wr 20 1) (.wr 9 2))

/--
info: step:thread  action          state
0:T0         write [10] ← 1  10↦1, 9↦0, 20↦0
1:T1         write [20] ← 1  10↦1, 9↦0, 20↦1
2:T1         write [9] ← 2   pending
2:T0         write [9] ← 1   pending
Parallel aborts at Step 2. Reason: T0, T1 write to: {9}.
Parallel: 9↦1
Sequential: 9↦2
-/
#guard_msgs in
#eval IO.println (explainProg late σ0)

/-- A read against a write: `access`, not `write to`. -/
private def rw : Prog := .par (.seq (.wr 1 1) (.rd 9)) (.seq (.wr 2 1) (.wr 9 2))

/--
info: step:thread  action         state
0:T0         write [1] ← 1  1↦1, 9↦0, 2↦0
1:T1         write [2] ← 1  1↦1, 9↦0, 2↦1
2:T1         write [9] ← 2  pending
2:T0         read [9]       pending
Parallel aborts at Step 2. Reason: T0, T1 access: {9}.
Parallel: 9↦2, T0 reads 2
Sequential: 9↦2, T0 reads 0
-/
#guard_msgs in
#eval IO.println (explainProg rw σ0)

/-- Shared reads are not a race, so there is nothing to find. -/
private def clean : Prog := .par (.seq (.rd 0) (.wr 1 1)) (.seq (.rd 0) (.wr 2 2))

/--
info: No counterexample: no par node fails Bernstein.
Sequential: 0↦0, 1↦1, 2↦2
-/
#guard_msgs in
#eval IO.println (explainProg clean σ0)

/-- The conflict is between grandchildren, so `attribution`'s path reaches `T1.0` and `T1.1`. -/
private def nested : Prog :=
  .seq (.wr 1 1) (.par (.wr 2 2) (.par (.seq (.rd 3) (.wr 7 1)) (.seq (.rd 4) (.wr 7 2))))

/--
info: step:thread  action         state
0:main       write [1] ← 1  1↦1, 2↦0, 3↦0, 7↦0, 4↦0
1:T0         write [2] ← 2  1↦1, 2↦2, 3↦0, 7↦0, 4↦0
2:T1.0       read [3] → 0   1↦1, 2↦2, 3↦0, 7↦0, 4↦0
3:T1.1       read [4] → 0   1↦1, 2↦2, 3↦0, 7↦0, 4↦0
4:T1.1       write [7] ← 2  pending
4:T1.0       write [7] ← 1  pending
Parallel aborts at Step 4. Reason: T1.0, T1.1 write to: {7}.
Parallel: 7↦1
Sequential: 7↦2
-/
#guard_msgs in
#eval IO.println (explainProg nested σ0)

-- the clashing pair: two threads, one step, with the values they would have stored
/--
info: [(2, "T1", "write [9] ← 2"), (2, "T0", "write [9] ← 1")]
-/
#guard_msgs in
#eval (reportOf rawName late.stepBound late.toParM late.toSeq σ0 late.locs).filterMap
  (fun i => match i with
    | .step s => if s.pending then some (s.time, s.thread, s.action) else none
    | _       => none)

-- the `changed` flag a widget highlights: only the cell this step wrote
/--
info: [["10"], ["20"], [], []]
-/
#guard_msgs in
#eval (reportOf rawName late.stepBound late.toParM late.toSeq σ0 late.locs).filterMap
  (fun i => match i with
    | .step s => some (s.state.filter (fun c => c.changed) |>.map (fun c => c.loc))
    | _       => none)

end Examples

end Paralever
