import Paralever.AutoPar.Rewrite
import Lang.Report

namespace Paralever.Examples.AutoPar
open Paralever Paralever.Lang Paralever.AutoPar

/-! `chain.prl` is written as a straight line of nine statements. The pass turns it into three
stages without being told anything, and the five steps below are the whole algorithm, each one
evaluated on this program. -/

def chain : Compiled := prl_file "../Language/chain.prl"
abbrev p : ParProg := chain.prog

/-! ## Step 0 · What was written -/

/--
info: buf a[5]

a[0] := 3
a[1] := 4
%0 := a[0]
a[2] := (%0 * %0)
%1 := a[1]
a[3] := (%1 * %1)
%2 := a[2]
%3 := a[3]
a[4] := (%2 + %3)
-/
#guard_msgs in
#eval IO.println (toPrl chain)

/-! ## Step 1 · `units` — cut the chain into register-closed segments

The unit is not the statement. `%0 := a[0]` and `a[2] := %0 * %0` must stay together: registers are
thread-private, so a fork between them would leave the second reading a stale copy. `atoms` cuts
only where no register is live across the cut, which here gives five units from nine statements. -/

#guard (units p).length == 5

-- each unit's memory footprint: reads on the left, writes on the right. This is all the
-- scheduler ever looks at
/--
info: unit 0  reads []  writes [0]
unit 1  reads []  writes [1]
unit 2  reads [0]  writes [2]
unit 3  reads [1]  writes [3]
unit 4  reads [2, 3]  writes [4]
-/
#guard_msgs in
#eval IO.println ("\n".intercalate ((units p).zipIdx.map fun (u, i) =>
  let f := ParProg.footprintOf u
  "unit " ++ toString i ++ "  reads " ++ toString f.reads ++ "  writes " ++ toString f.writes))

/-! ## Step 2 · `preds` — the dependence DAG, in one scoreboard pass

Bernstein's three clauses are the three kinds of edge: a read after a write (RAW), a write after a
write (WAW), a write after a read (WAR). One left-to-right pass over the units reads them all off a
`lastWriter`/`readersSince` board — no pairwise scan. -/

-- unit 2 must follow unit 0 (it reads `a[0]`), unit 3 must follow 1, and unit 4 follows both 2
-- and 3; units 0 and 1 depend on nothing, so they may start together
#guard preds (units p) == [[], [], [0], [1], [2, 3]]

/-! ## Step 3 · `critical` — the lower bound

Earliest possible start of each unit, then the largest finish. No schedule of these units — fork–join
or otherwise — can have smaller depth than this, so it is what makes "optimal" a certificate rather
than an estimate. -/

#guard asap (units p) == [0, 0, 1, 1, 3]
#guard critical (units p) == 6

/-! ## Step 4 · `plan` — the schedule

One left-to-right pass. Each unit either extends the thread being built, opens a new thread beside
it, or forces a new stage, and those three cases are the three ways a dependence can fall. Nothing
is ever reordered, which is why the soundness theorem needs no commutation lemma.

Here: two threads, then two threads, then one. -/

#guard (planOf p).map (fun stage => stage.length) == [2, 2, 1]

/-! ## Step 5 · `rewrite` — emit, but only behind the gate

`rewriteOk` is checked *inside* `rewrite`: no register may flow between threads, and the emitted
program must pass `wfB`. A plan failing either is discarded and the original returned unchanged,
which is why `rewrite_sound` below has no hypothesis. -/

#guard rewriteOk p

/--
info: buf a[5]

parallel {
  a[0] := 3
} | {
  a[1] := 4
}
parallel {
  %0 := a[0]
  a[2] := (%0 * %0)
} | {
  %1 := a[1]
  a[3] := (%1 * %1)
}
parallel {
  %2 := a[2]
  %3 := a[3]
  a[4] := (%2 + %3)
}

-- units 5, stages 3, depth 6 (sequential 9, lower bound 6)
-- committed true, optimal true
-/
#guard_msgs in
#eval IO.println (parReport chain)

-- depth 6 against a sequential 9, and 6 is the bound, so this plan is optimal — reported, not
-- claimed: `optimalB` is `depth (rewrite p) == critical (units p)`
#guard quality p == (6, 6, 9)
#guard optimalB p

/-! ## What the pass is worth

`rewrite_sound` holds for **every** program with nothing to supply: the gate is inside `rewrite`,
so a program it declines comes back unchanged and the equation is trivially true for it. -/

example (ρ : Regs) (σ : State) :
    (runSeq (ParProg.execPar (rewrite p) ρ) σ).2 = (runSeq (ParProg.execSeq p ρ) σ).2 :=
  rewrite_sound p ρ σ

-- and because the rewrite stays well-formed, `par_seq_eq` lifts that from one schedule to all
example (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar (rewrite p) ρ) (ParProg.execSeq (rewrite p) ρ) σ :=
  rewrite_parSeqEq p (by decide) ρ σ

/-! ## Where it declines

A loop-carried dependence has nothing to find, and the pass says so rather than inventing a fork:
one thread, the sequential depth, and the bound agreeing there was no parallelism. -/

def carried : ParProg := paralever {
  %0 := [0]; [1] := %0 + 1;
  %1 := [1]; [2] := %1 + 1;
  %2 := [2]; [3] := %2 + 1
}

-- one stage of one thread: the pass found nothing, and the bound agrees there was nothing
#guard (planOf carried).map (fun stage => stage.length) == [1]
#guard quality carried == (6, 6, 6)
#guard optimalB carried

/-! ## Synchronization

`phases.prl` has two phases separated by a `synchronize`. Both write disjoint buffers and only read
`A`, so Bernstein accepts running all eight statements together — and without the barrier `autoPar`
does exactly that. The barrier is what keeps them apart.

A barrier is outside this route: `emit` wraps every stage in a `par`, so one reaching the plan would
land inside a thread, and carrying a register across it needs a liveness condition `rewriteOk` does
not state. `ParProg.autoPar` is the route that honours a barrier, and `parReport` uses it for a
program that has one. -- ref: `docs/autopar.md` § Synchronization -/

def synchronized : Compiled := prl_file "../Language/phases.prl"

#guard !ParProg.synchronizeFree synchronized.prog
#guard !rewriteOk synchronized.prog
#guard (ParProg.phases (ParProg.flatten synchronized.prog)).map List.length == [8, 8]

/-- One fork of four per phase, with the barrier between them. -/
private def forks (p : ParProg) : List Nat :=
  (ParProg.flatten p).map fun s => match s with | .par ts => ts.length | _ => 1

#guard forks (ParProg.autoPar synchronized.prog) == [4, 1, 4]

/-- The same program with the barrier dropped: one fork of eight, which is what it forbids. -/
def unsynchronized : ParProg :=
  ParProg.block ((ParProg.flatten synchronized.prog).filter (fun s => !s.isSynchronize))

#guard forks (ParProg.autoPar unsynchronized) == [8]

-- the proposal still passes the proved check, and the printed result reads back as itself
#guard ParProg.wfB (ParProg.autoPar synchronized.prog)
#guard roundTrips (toPrl { synchronized with prog := ParProg.autoPar synchronized.prog })

end Paralever.Examples.AutoPar
