import Bench.Time
import Tool.Run

/-! # One kernel, one row

The harness proper. Every number in a row comes from a function that already exists and is already
gated somewhere else in the tree — this module reads files, times the calls and classifies the
answer, and decides nothing:

| what | whose code |
|---|---|
| reading either front end | `Tool.loadAny` |
| the hypothesis, at every heap | `ParProg.wfB` |
| the verdict, at this heap and at every heap | `ParProg.verdictHere`, `ParProg.verdictAnywhere` |
| why a refusal happened | `ParProg.widenedBy`, `ParProg.refusedAt`, `ParProg.probeCells` |
| how wide the program is | `Lang.threadCount` |
| a file's own claim | `Lang.claimHolds` |

A row that disagreed with `paralever check` would be a bug in this module, which is the property
worth having: there is one verdict in the project and the harness is not a second opinion.

Rationale: `docs/bench.md`. -/

namespace Paralever.Bench
open Paralever Paralever.Lang

/-- One measured kernel. `label` is what the corpus declares; everything else is measured. -/
structure Row where
  name      : String
  /-- `"prl"` or `"mlir"` — which front end read it. -/
  kind      : String
  reach     : Reach
  /-- the declared label for the general question: a race at some heap -/
  label     : Bool
  /-- the declared label for the per-heap question: a race at the heap the file declares. Separate,
  because scoring the exact check against the general label books `scatter` as a false negative
  when it is answering a different question correctly. -/
  labelHere : Bool
  /-- `wfB` refuses, i.e. a race is reported for every heap. `none` when the file did not load. -/
  anyHeap   : Option Bool
  /-- the exact per-heap check reports a race -/
  thisHeap  : Option Bool
  cell      : Cell
  /-- `ParProg.widenedBy` — why the footprint is a bound rather than the exact set -/
  widened   : List String
  /-- how many heaps the bounded probe looked at, when it looked -/
  probed    : Nat
  threads   : Nat
  /-- the file's `assert`, when it states one -/
  claimHeld : Option Bool
  readMs    : Ms
  checkMs   : Ms
  /-- how many jobs were in flight while this row was measured. A timing taken alongside fifteen
  siblings is not comparable with one taken alone, so the number travels with it. -/
  jobs      : Nat
  note      : String := ""
  deriving Repr, Inhabited

/-- Classify one answer into the taxonomy. The `HeapVerdict` is passed whole rather than reduced to
a `Bool` first, because `unknown` is a third answer and flattening it would book an inconclusive
program as a false positive. -- ref: `Lang/Verdict.lean`, which prints the same three cases -/
def classify (label : Bool) (reach : Reach) (any : Option HeapVerdict)
    (widened : List String) : Cell :=
  match reach with
  | .unmodelled why => .unreachable why
  | .overCeiling    => .overCeiling
  | .reachable      =>
    match any with
    | none              => .unreachable "the front end could not read it"
    | some .proved      => if label then .falseAcceptance else .proved
    | some (.race _ _)  =>
        if label then .soundRefusal
        else .falseRefusal
          (if widened.any (fun w => w.startsWith "a computed address") then .computedAddress
           else if widened.any (fun w => w.startsWith "a branch") then .branch
           else .genuinelyRacy)
    -- `wfB` refused and the bounded probe found nothing: refusing a racy program is still right,
    -- but about a race-free one this is the open case the SMT route exists for
    | some (.unknown n) => if label then .soundRefusal else .inconclusive n

/-- What the matrix sees. `unknown` is **no answer** rather than "racy": counting it as a race
would make every inconclusive race-free program a false positive, and `Lang/Verdict.lean` does not
claim a race there either -- it prints `Inconclusive`. -/
def reportedRacy : HeapVerdict → Option Bool
  | .proved    => some false
  | .race _ _  => some true
  | .unknown _ => none

/-- **One kernel through the pipeline.** `jobs` is recorded, not used: the caller fixes the
parallelism and the row states what it was. -/
def runOne (jobs : Nat) (e : Entry String) : IO Row := do
  let loaded : Except String ((Compiled × Tool.Kind × List String) × Ms) ←
    try
      let r ← timed (Tool.loadAny e.item)
      pure (Except.ok r)
    catch ex => pure (Except.error (toString ex))
  match loaded with
  | .error msg =>
      pure { name := e.name, kind := "?", reach := e.reach, label := e.racy
           , labelHere := e.racyAtDeclared
           , anyHeap := none, thisHeap := none
           , cell := .unreachable msg, widened := [], probed := 0, threads := 0
           , claimHeld := none, readMs := 0, checkMs := 0, jobs := jobs, note := msg }
  | .ok ((c, k, notes), readMs) => do
      let widened := ParProg.widenedBy c.prog
      -- the two checks, timed together: exactly the work `paralever check` does
      let ((here, any), _, checkMs) ← timedForced (fun _ =>
        (reprStr (ParProg.verdictHere c.layout c.prog),
         reprStr (ParProg.verdictAnywhere c.layout c.prog)))
      let _ := (here, any)
      let vHere := ParProg.verdictHere c.layout c.prog
      let vAny  := ParProg.verdictAnywhere c.layout c.prog
      let probed := match vAny with | .unknown n => n | _ => 0
      pure { name := e.name
           , kind := match k with | .prl => "prl" | .mlir => "mlir"
           , reach := e.reach, label := e.racy, labelHere := e.racyAtDeclared
           , anyHeap := reportedRacy vAny, thisHeap := reportedRacy vHere
           , cell := classify e.racy e.reach (some vAny) widened
           , widened := widened, probed := probed
           , threads := ParProg.threadCount c.prog
           , claimHeld := if c.claim.isSome then some (Lang.claimHolds c) else none
           , readMs := readMs, checkMs := checkMs, jobs := jobs
           , note := String.intercalate "; " notes }

/-- **The corpus, fanned out.** `jobs = 1` is the mode to quote a timing from; the default asks the
machine and is the mode to get a verdict table from quickly. Either way every row carries the
`jobs` it was measured under. -/
def runCorpus (requested : Nat) (corpus : List (Entry String)) : IO (List Row) := do
  let jobs ← resolveJobs requested
  mapParallel jobs corpus (runOne jobs)

/-! ## Scoring a run

The matrices come from `Bench.Verdict`, which `MLIR/Corpus.lean` also calls, so a run of this
harness and that module's build gates cannot disagree. -/

/-- The rows as entries, labelled for whichever question is being scored. -/
def rowsToEntries (here : Bool) (rows : List Row) : List (Entry String) :=
  rows.map (fun r =>
    { name := r.name, item := "", racy := if here then r.labelHere else r.label
    , reach := r.reach })

/-- **Both matrices over a finished run, each against its own label**, plus the gap between them.
The general matrix asks "racy at some heap" and the exact one asks "racy at the heap the file
declares"; `Examples/Language/scatter.prl` answers `true` to the first and `false` to the second, so
one label for both would record a correct answer as an error. -/
def scoreRun (rows : List Row) : TwoMatrices :=
  let byName : String → Option Row := fun n => rows.find? (fun r => r.name == n)
  { anyHeap  := confusionOf (rowsToEntries false rows) (fun e => (byName e.name).bind (·.anyHeap))
  , thisHeap := confusionOf (rowsToEntries true rows) (fun e => (byName e.name).bind (·.thisHeap))
  , gap      := gapOf (rowsToEntries false rows)
                  (fun e => (byName e.name).bind (·.anyHeap))
                  (fun e => (byName e.name).bind (·.thisHeap)) }

/-- The soundness gate: no row may be a false acceptance. -/
def runIsSound (rows : List Row) : Bool := soundnessHolds (rows.map Row.cell)

end Paralever.Bench
