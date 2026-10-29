import Bench.Run
import Bench.Manifest

/-! # What a run prints

Three shapes of the same rows: a table to read, a CSV to plot, and the Markdown `docs/bench.md`
quotes. Nothing here computes a verdict — the rows arrive already decided by `Bench/Run.lean`,
which decided nothing either and asked `Lang/Verdict.lean`.

Rationale: `docs/bench.md`. -/

namespace Paralever.Bench
open Paralever Paralever.Lang

private def pad (w : Nat) (s : String) : String := s ++ "".pushn ' ' (w - min w s.length)

/-- The name column, wide enough for the longest name in the run plus a space. A fixed width
truncated `reduction-split-no` into its neighbour. -/
def nameWidth (rows : List Row) : Nat :=
  (rows.map (fun r => r.name.length)).foldl Nat.max 6 + 2

private def yn : Option Bool → String
  | some true  => "racy"
  | some false => "free"
  | none       => "—"

/-! ## The table -/

def Row.line (w : Nat) (r : Row) : String :=
  pad w r.name ++ pad 6 r.kind
    ++ pad 7 (if r.label then "racy" else "free")
    ++ pad 7 (if r.labelHere then "racy" else "free")
    ++ pad 7 (yn r.anyHeap) ++ pad 7 (yn r.thisHeap)
    ++ pad 6 (toString r.threads)
    ++ pad 8 (toString r.checkMs ++ "ms")
    ++ r.cell.word

def header (w : Nat) : String :=
  pad w "kernel" ++ pad 6 "front" ++ pad 7 "label" ++ pad 7 "lbl@h" ++ pad 7 "any" ++ pad 7 "this"
    ++ pad 6 "thr" ++ pad 8 "check" ++ "cell"

/-- The precision gap, as names: refused for every heap, accepted at this one. -/
def gapRows (rows : List Row) : List String :=
  (rows.filter (fun r => r.anyHeap == some true && r.thisHeap == some false)).map Row.name

/-- The inconclusive rows, with how far the probe looked. -/
def inconclusiveRows (rows : List Row) : List (String × Nat) :=
  (rows.filterMap (fun r =>
    match r.cell with
    | .inconclusive n => some (r.name, n)
    | _               => none))

/-- False refusals, grouped by the clause that widened the footprint. -/
def refusalsByCause (rows : List Row) : List (String × String) :=
  rows.filterMap (fun r =>
    match r.cell with
    | .falseRefusal c => some (r.name, c.word)
    | _               => none)

/-- **The run, as a report.** The two matrices, the gap between them, the attribution of every
refusal, and then a row per kernel. The soundness line is first because it is the only one that can
fail a build. -/
def report (rows : List Row) : String :=
  let m := scoreRun rows
  let jobsSeen := (rows.map Row.jobs).eraseDups
  let total := (rows.map (fun r => r.readMs + r.checkMs)).foldl (· + ·) 0
  "soundness      " ++ (if runIsSound rows then "OK — no false acceptance"
                        else "FAILED — a program labelled racy was accepted")
    ++ "\nkernels        " ++ toString rows.length
    ++ "\nany heap       " ++ m.anyHeap.line
    ++ "\nthis heap      " ++ m.thisHeap.line
    ++ "\nsensitivity    " ++ toString m.anyHeap.sensitivity.1 ++ "/"
                            ++ toString m.anyHeap.sensitivity.2 ++ " of the racy caught"
    ++ "\nspecificity    " ++ toString m.anyHeap.specificity.1 ++ "/"
                            ++ toString m.anyHeap.specificity.2 ++ " of the race-free proved"
    ++ "\nprecision gap  " ++ toString (gapRows rows)
    ++ "\ninconclusive   " ++ toString (inconclusiveRows rows)
    ++ "\nfalse refusals " ++ toString (refusalsByCause rows)
    ++ "\njobs in flight " ++ toString jobsSeen
                            ++ (if jobsSeen == [1] then " (timings uncontended)"
                                else " — timings were taken under contention")
    ++ "\ntotal measured " ++ toString total ++ " ms"
    ++ "\n\n" ++ header (nameWidth rows) ++ "\n"
    ++ "\n".intercalate (rows.map (Row.line (nameWidth rows)))

/-! ## CSV

One row per kernel, so a plot does not need this module. -/

def csvHeader : String :=
  "name,front,label,label_here,any_heap,this_heap,cell,threads,probed,read_ms,check_ms,jobs"

def Row.csv (r : Row) : String :=
  String.intercalate ","
    [ r.name, r.kind
    , if r.label then "racy" else "free"
    , if r.labelHere then "racy" else "free"
    , yn r.anyHeap, yn r.thisHeap
    , "\"" ++ r.cell.word ++ "\""
    , toString r.threads, toString r.probed
    , toString r.readMs, toString r.checkMs, toString r.jobs ]

def csv (rows : List Row) : String :=
  csvHeader ++ "\n" ++ "\n".intercalate (rows.map Row.csv) ++ "\n"

/-! ## Markdown, for `docs/bench.md` -/

def markdown (rows : List Row) : String :=
  let m := scoreRun rows
  "| kernel | front | label | any heap | this heap | threads | cell |\n"
    ++ "|---|---|---|---|---|---|---|\n"
    ++ "\n".intercalate (rows.map (fun r =>
        "| `" ++ r.name ++ "` | " ++ r.kind ++ " | "
          ++ (if r.label then "racy" else "race-free") ++ " | "
          ++ yn r.anyHeap ++ " | " ++ yn r.thisHeap ++ " | "
          ++ toString r.threads ++ " | " ++ r.cell.word ++ " |"))
    ++ "\n\nAny heap: " ++ m.anyHeap.line ++ ". This heap: " ++ m.thisHeap.line
    ++ ". Gap: " ++ toString m.gap ++ ".\n"

end Paralever.Bench
