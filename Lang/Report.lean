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
  | .ifElse _ t e  => max (stepBound t) (stepBound e)

def stepBoundAll : List ParProg → Nat
  | []      => 0
  | s :: ss => stepBound s + stepBoundAll ss

end

/-- Threads at the top level of the program. -/
def threadCount : ParProg → Nat
  | .par ss     => ss.length
  | .label _ s  => threadCount s
  | .seq a b    => max (threadCount a) (threadCount b)
  | _           => 1

end ParProg

/-- Memory, footprint and verdict. -/
def checkReport (name : String) (c : Compiled) : String :=
  let L := c.layout
  let nm := c.locName
  let f := ParProg.footprintOf c.prog
  let stray := L.strayLocs f
  let ρ : Regs := fun _ => 0
  let sites := raceSites (ParProg.execPar c.prog ρ) L.state
  let verdict :=
    if ParProg.wfB c.prog then "independent — par = seq under every schedule (wfB = true)"
    else if sites.isEmpty then "footprint over-approximated: wfB says no, the heap check says yes"
    else "RACY — " ++ toString sites.length ++ " conflicting fork(s): "
          ++ clipNames nm 8 (sites.flatMap (fun s => s.conflicts))
  name
    ++ "\n  memory    " ++ ", ".intercalate (L.bufs.map (fun p =>
          p.name ++ toString p.shape ++ " @" ++ toString p.base
            ++ (if c.dead.contains p.name then " (freed)" else "")))
    ++ "  (" ++ toString L.size ++ " cells)"
    ++ "\n  reads     " ++ clipNames nm 10 (nubLocs f.reads)
    ++ "\n  writes    " ++ clipNames nm 10 (nubLocs f.writes)
    ++ (if stray.isEmpty then "" else "\n  stray     " ++ clipLocs 10 stray ++ " — outside every buffer")
    ++ "\n  threads   " ++ toString (ParProg.threadCount c.prog)
    ++ "\n  rounds    " ++ toString (time (ParProg.execPar c.prog ρ) L.state)
    ++ " parallel, " ++ toString (time (ParProg.execSeq c.prog ρ) L.state) ++ " sequential"
    ++ "\n  verdict   " ++ verdict ++ "\n"

/-- The heap after a run, as the buffers that were declared, with a legend: the columns are not
self-explaining and the heap is the only thing a run produces. -/
def runReport (c : Compiled) (threads : Bool) : String :=
  let ρ : Regs := fun _ => 0
  let L := c.layout
  let σ := if threads then (ParProg.runTask c.prog ρ L.state).2
                      else (ParProg.runTaskSeq c.prog ρ L.state).2
  let n := L.bufs.length
  "heap after the run — a .prl program has no print statement, so this is its output\n"
    ++ toString L.size ++ " cells in " ++ toString n
    ++ (if n == 1 then " buffer" else " buffers")
    ++ (if c.dead.isEmpty then "" else ", " ++ toString c.dead.length ++ " of them freed")
    ++ ", addressed 0 to " ++ toString (L.size - 1) ++ "\n"
    ++ "NAME [dims] @base — the buffer's first cell in that flat heap; cells row-major from there\n"
    ++ (if threads then "on real threads: one Task per thread of every parallel block\n" else "")
    ++ "\n"
    -- a freed buffer still has an address, and a later one is placed on its cells, so the two
    -- print the same numbers. Say which is dead rather than leave the reader to guess.
    ++ "\n".intercalate (L.bufs.map fun p =>
         let r := p.render σ
         if c.dead.contains p.name then
           match r.splitOn "\n" with
           | first :: rest => "\n".intercalate ((first ++ "   (freed)") :: rest)
           | []            => r
         else r)
    ++ "\n"

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
  if !ParProg.synchronizeFree c.prog then
    let p := ParProg.autoPar c.prog
    print { c with prog := p }
      ++ "\n-- phases " ++ toString (ParProg.phases (ParProg.flatten c.prog)).length
      ++ ", greedy route (a barrier is outside the proved one)"
      ++ "\n-- independent " ++ toString (ParProg.wfB p) ++ "\n"
  else
  let p := AutoPar.rewrite c.prog
  let (d, l, s) := AutoPar.quality c.prog
  print { c with prog := p }
    ++ "\n-- units " ++ toString (AutoPar.units c.prog).length
    ++ ", stages " ++ toString (AutoPar.planOf c.prog).length
    ++ ", depth " ++ toString d ++ " (sequential " ++ toString s
    ++ ", lower bound " ++ toString l ++ ")"
    ++ "\n-- committed " ++ toString (AutoPar.rewriteOk c.prog)
    ++ ", optimal " ++ toString (AutoPar.optimalB c.prog) ++ "\n"

end Paralever.Lang
