import Lang.Verdict
import Lang.Core.Heaps
import Lang.Compile.Print
import Lang.Load
import Lang.Core.Exec
import Paralever.Search.Explain

/-! # Views of a compiled file, for `#eval`

Addresses print as the buffer cells they are (`Layout.show`), so a verdict or a counterexample reads
in the vocabulary of the program that was written. -/

namespace Paralever.Lang
open Paralever

namespace ParProg

mutual

/-- Steps a full run takes: one per memory action, one per join. Mirrors `Prog.stepBound`, which is
the fuel a schedule search needs. -- ref: `Paralever/Search/RaceSearch.lean` -/
def stepBound : ParProg → Nat
  | .load _ _      => 1
  | .store _ _     => 1
  | .loadAt _ _ _  => 1
  | .storeAt _ _ _ => 1
  | .set _ _       => 0
  | .seq a b       => stepBound a + stepBound b
  | .par ss        => stepBoundAll ss + ss.length
  | .label _ s     => stepBound s
  | .synchronize         => 0
  | .print _             => 0
  | .ifElse _ t e  => max (stepBound t) (stepBound e)
  -- every point's memory actions, plus one join per forked thread
  | .loop n        => n.threadCount * n.threadOps + n.threadCount

def stepBoundAll : List ParProg → Nat
  | []      => 0
  | s :: ss => stepBound s + stepBoundAll ss

end

/-- Threads at the top level of the program. -/
def threadCount : ParProg → Nat
  | .par ss     => ss.length
  | .label _ s  => threadCount s
  | .seq a b    => max (threadCount a) (threadCount b)
  | .loop n     => n.threadCount
  | _           => 1

end ParProg

/-- The `assert` block, under the verdict, or nothing when the file states no claim. -/
def claimLines (c : Compiled) : String :=
  match c.claim with
  | none    => ""
  | some cl => "\n  claim     " ++ claimBlock c cl "            "

/-- The file's name and the verdict, and nothing else. This is what a bare `paralever FILE` adds to
what `run` prints, so the two commands say the same things about the program and differ only in
whether the equivalence was proved. -- ref: `docs/cli.md` § A file on its own -/
def verdictReport (name : String) (c : Compiled) : String :=
  name ++ "\n  verdict   " ++ verdictBlock c "            " ++ claimLines c ++ "\n"

/-- Steps above which the `rounds` line states a bound instead of measuring one.

**Rounds are the one figure in this report that is not proportional to the text.** `time` walks the
program, so a rolled nest — whose whole point is that the term does not grow with the trip counts —
is exactly the program it cannot walk: `wfB` decides a 10⁹-point gemm in no measurable time and
`time` would take 10⁹ steps over it. `stepBound` is the closed form, and above this ceiling it is
what the line reports. -- ref: `docs/loops.md` § What rolling does not make cheap -/
def roundsCeiling : Nat := 10000000

/-- The `rounds` line: the two measured spans, or the bound when the program is over the ceiling. -/
def roundsText (c : Compiled) (ρ : Regs) : String :=
  let b := ParProg.stepBound c.prog
  if roundsCeiling < b then
    "not run — " ++ toString b ++ " steps, over the ceiling of " ++ toString roundsCeiling
  else
    toString (time (ParProg.execPar c.prog ρ) c.layout.state) ++ " parallel, "
      ++ toString (time (ParProg.execSeq c.prog ρ) c.layout.state) ++ " sequential"

/-- Memory, footprint and verdict. -/
def checkReport (name : String) (c : Compiled) : String :=
  let L := c.layout
  let nm := c.locName
  let f := ParProg.footprintOf c.prog
  let stray := L.strayLocs f
  let ρ : Regs := fun _ => 0
  name
    ++ "\n  memory    " ++ ", ".intercalate (L.bufs.map (fun p =>
          p.name ++ toString p.shape ++ " @" ++ toString p.base
            ++ (if c.dead.contains p.name then " (freed)" else "")))
    ++ "  (" ++ toString L.size ++ " cells)"
    ++ "\n  reads     " ++ clipNames nm 10 (nubLocs f.reads)
    ++ "\n  writes    " ++ clipNames nm 10 (nubLocs f.writes)
    ++ (if stray.isEmpty then "" else "\n  stray     " ++ clipLocs 10 stray ++ " — outside every buffer")
    ++ "\n  threads   " ++ toString (ParProg.threadCount c.prog)
    ++ "\n  rounds    " ++ roundsText c ρ
    ++ "\n  verdict   " ++ verdictBlock c "            " ++ claimLines c ++ "\n"

/-- Cells of one buffer the default `run` view prints before it says how many it left out.
`--all-cells` lifts the limit, and `-n` prints all of the buffer it names. -/
def runCells : Nat := 32

/-! ## What a `print` writes

A print is erased from `execPar` and `execSeq`, so no interpreter produces its output and this is
the only place one means anything. The walk below runs every statement that is *not* a print or a
`seq`/`ifElse` spine through `runSeq ∘ execSeq` — the interpreter the theorems are about — so the
heap a print sees is the heap the semantics gives rather than a second reading of the program.
`Test/Print.lean` gates that: the heap this walk leaves equals the heap `runTaskSeq` leaves.
-- ref: `docs/print.md` § Where the output comes from -/

/-- `xs` in runs of `n`. `Layout.chunk` is private, so a print has its own; the fuel is the list's
own length, which is what makes it structural. -/
private def rows (n : Nat) : Nat → List String → List (List String)
  | _,        [] => []
  | 0,        xs => [xs]
  | fuel + 1, xs => xs.take (max n 1) :: rows n fuel (xs.drop (max n 1))

/-- `nm[1, 2]`, or `nm` when there is no subscript. -/
private def subName (nm : String) (idx : List Nat) : String :=
  if idx.isEmpty then nm else nm ++ "[" ++ ", ".intercalate (idx.map toString) ++ "]"

/-- A buffer's cells on one line: a scalar is its value, a vector a list, a matrix a list of rows.
One line per `print`, unlike `run`'s view of the whole heap, because a print sits in a sequence of
them and a reader is following that sequence. -/
private def bufValues (shape : List Nat) (b : Loc) (σ : State) : String :=
  let n := cells shape
  let keep := min n runCells
  let vals := (List.range keep).map (fun k => showVal (σ (b + k)))
  let more := if n == keep then "" else ", … +" ++ toString (n - keep) ++ " more"
  match shape with
  | []     => showVal (σ b)
  | [_]    => "[" ++ ", ".intercalate vals ++ more ++ "]"
  | _ :: c :: _ =>
      let w := max c 1
      let rows := (rows w vals.length vals).map (fun r => "[" ++ ", ".intercalate r ++ "]")
      "[" ++ ", ".intercalate rows ++ more ++ "]"

/-- One `print` statement's line, at the register file and heap that reach it. A cell and a buffer
print as `name = value`, so output says what it is without a label. -/
def showItems (is : List PrintItem) (ρ : Regs) (σ : State) : String :=
  " ".intercalate (is.map fun
    | .text t         => t
    | .exp e          => toString (e.eval ρ)
    | .cell nm idx l  => subName nm idx ++ " = " ++ showVal (σ l)
    | .at nm a e      =>
        nm ++ "[" ++ toString (e.eval ρ) ++ "] = " ++ showVal (σ (a.addr (e.eval ρ)))
    | .buf nm shape b => nm ++ " = " ++ bufValues shape b σ)

/-- The lines a program writes, and the register file and heap it leaves. -/
def outOf : ParProg → Regs → State → List String × Regs × State
  | .print is,       ρ, σ => ([showItems is ρ σ], ρ, σ)
  | .seq a b,        ρ, σ =>
      let (o, ρ', σ')    := outOf a ρ σ
      let (o', ρ'', σ'') := outOf b ρ' σ'
      (o ++ o', ρ'', σ'')
  | .ifElse c t e,   ρ, σ => if c.eval ρ != 0 then outOf t ρ σ else outOf e ρ σ
  | .label _ s,      ρ, σ => outOf s ρ σ
  | s,               ρ, σ => let (ρ', σ') := runSeq (ParProg.execSeq s ρ) σ; ([], ρ', σ')

/-- The program's output. -/
def outputOf (c : Compiled) : List String := (outOf c.prog (fun _ => 0) c.layout.state).1

/-- The heap the output walk leaves — the gate's left-hand side. -/
def heapAfterOut (c : Compiled) : State := (outOf c.prog (fun _ => 0) c.layout.state).2.2

/-- The output, with a heading, or nothing at all when the program has no `print`. -/
def outReport (c : Compiled) : String :=
  match outputOf c with
  | []  => ""
  | out => "output — what this program's print statements wrote, on the canonical run\n"
             ++ "\n".intercalate out ++ "\n\n"

/-- The program's output and nothing around it: what `--quiet` prints. A program with no `print` is
then silent, which is the honest answer — `print` is the only thing a program says on its own.
-- ref: `docs/cli.md` § Verbosity -/
def quietReport (c : Compiled) : String :=
  match outputOf c with
  | []  => ""
  | out => "\n".intercalate out ++ "\n"

/-- The heap a run leaves: the canonical order, or one `Task` per thread of every fork. -/
def heapAfter (c : Compiled) (threads : Bool) : State :=
  let ρ : Regs := fun _ => 0
  if threads then (ParProg.runTask c.prog ρ c.layout.state).2
             else (ParProg.runTaskSeq c.prog ρ c.layout.state).2

/-- `-n`'s argument: `C` is a buffer, `C[1, 2]` one cell of it. -/
def splitIdx (sel : String) : Except String (String × Option (List Nat)) :=
  let trim := fun (s : String) => s.trimAscii.toString
  match (trim sel).splitOn "[" with
  | [n]       => .ok (trim n, none)
  | [n, rest] =>
      let rest := trim rest
      if !rest.endsWith "]" then .error s!"-n {sel}: a subscript needs a closing ']'"
      else match ((rest.dropEnd 1).toString.splitOn ",").mapM (fun t => (trim t).toNat?) with
        | some idx => .ok (trim n, some idx)
        | none     => .error s!"-n {sel}: a subscript is a comma-separated list of numbers"
  | _         => .error s!"-n {sel}: one subscript, not two"

/-- A buffer's cells, with the note that says which buffer is no longer live. A freed buffer still
has an address, and a later one is placed on its cells, so the two print the same numbers. -/
def bufferLine (c : Compiled) (σ : State) (budget : Option Nat) (p : Placed) : String :=
  let r := p.renderUpTo σ budget
  if c.dead.contains p.name then
    match r.splitOn "\n" with
    | first :: rest => "\n".intercalate ((first ++ "   (freed)") :: rest)
    | []            => r
  else r

/-- The heap after a run, as the buffers that were declared, with a legend: the columns are not
self-explaining and the heap is the only thing a run produces. -/
def runReport (c : Compiled) (threads : Bool) (allCells : Bool := false) : String :=
  let L := c.layout
  let σ := heapAfter c threads
  let n := L.bufs.length
  outReport c
    ++ "heap after the run — the cells the program left behind, which is most of what it says\n"
    ++ toString L.size ++ " cells in " ++ toString n
    ++ (if n == 1 then " buffer" else " buffers")
    ++ (if c.dead.isEmpty then "" else ", " ++ toString c.dead.length ++ " of them freed")
    ++ ", addressed 0 to " ++ toString (L.size - 1) ++ "\n"
    ++ "NAME [dims] @base — the buffer's first cell in that flat heap; cells row-major from there\n"
    ++ (if threads then "on real threads: one Task per thread of every parallel block\n" else "")
    ++ "\n"
    ++ "\n".intercalate (L.bufs.map (bufferLine c σ (if allCells then none else some runCells)))
    ++ "\n"

/-- One buffer of the heap after the run, or one cell of it: what `-n` answers.
-- ref: docs/cli.md § What `run` prints -/
def runCell (c : Compiled) (threads : Bool) (sel : String) : Except String String := do
  let (name, idx?) ← splitIdx sel
  let L := c.layout
  let σ := heapAfter c threads
  match L.bufs.find? (fun p => p.name == name) with
  | none   =>
      .error (s!"-n {sel}: no buffer named '{name}' — this program declares "
        ++ ", ".intercalate (L.bufs.map (fun p => p.name)))
  | some p =>
      match idx? with
      | none     => .ok (bufferLine c σ none p)
      | some idx =>
          if !L.inRange name idx then
            .error s!"-n {sel}: outside {name} {p.shape}"
          else
            let l := L.at name idx
            .ok s!"{name}[{", ".intercalate (idx.map toString)}] @{l}  {showVal (σ l)}"

/-- The interleaving that realizes a race, replayed against `step`. -/
def raceReport (c : Compiled) : String :=
  let ρ : Regs := fun _ => 0
  let f := ParProg.footprintOf c.prog
  explainParM c.locName (ParProg.stepBound c.prog)
    (ParProg.execPar c.prog ρ) (ParProg.execSeq c.prog ρ) c.layout.state
    (nubLocs (f.reads ++ f.writes))

/-- The autoparallelized program, as `.prl`, with the plan's numbers.

A `synchronize` is outside the proved route (`AutoPar.rewriteOk`), so a program with one is reported
through `ParProg.autoPar` instead: each phase planned on its own, the barriers kept, and the result
checked by `wfB` rather than proved. -- ref: docs/autopar.md § Synchronization -/
def parReport (c : Compiled) : String :=
  if !ParProg.barrierFree c.prog then
    let p := ParProg.autoPar c.prog
    toPrl { c with prog := p }
      ++ "\n-- phases " ++ toString (ParProg.phases (ParProg.flatten c.prog)).length
      ++ ", greedy route (a barrier is outside the proved one)"
      ++ "\n-- independent " ++ toString (ParProg.wfB p) ++ "\n"
  else
  let p := AutoPar.rewrite c.prog
  let (d, l, s) := AutoPar.quality c.prog
  toPrl { c with prog := p }
    ++ "\n-- units " ++ toString (AutoPar.units c.prog).length
    ++ ", stages " ++ toString (AutoPar.planOf c.prog).length
    ++ ", depth " ++ toString d ++ " (sequential " ++ toString s
    ++ ", lower bound " ++ toString l ++ ")"
    ++ "\n-- committed " ++ toString (AutoPar.rewriteOk c.prog)
    ++ ", optimal " ++ toString (AutoPar.optimalB c.prog) ++ "\n"

end Paralever.Lang
