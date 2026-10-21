import Lang.Report

namespace Paralever.Examples.Files
open Paralever Paralever.Lang

/-! ## The nine files

`prl_file` reads and compiles the file *while this Lean file elaborates*, so each definition below
holds a program literal. No command line is involved, and `by decide` further down sees the
program, never the reader. -/

-- ANCHOR: site-prl-file
def sum     : Compiled := prl_file "sum.prl"
def matmul  : Compiled := prl_file "matmul.prl"
def stencil : Compiled := prl_file "stencil.prl"
def pipeline: Compiled := prl_file "pipeline.prl"
def control : Compiled := prl_file "control.prl"
def chain   : Compiled := prl_file "chain.prl"
def arena   : Compiled := prl_file "arena.prl"
def race    : Compiled := prl_file "race.prl"
def scatter : Compiled := prl_file "scatter.prl"
-- ANCHOR_END: site-prl-file

/-! ## 1 · A file that is accepted

`checkReport` is what `paralever check` prints, as a plain function. Three threads, three rounds
instead of nine, and a verdict that is the metatheorem's hypothesis discharged by evaluation. -/

/--
info: sum.prl
  memory    A[6] @0, out[3] @6  (9 cells)
  reads     {A[0], A[1], A[2], A[3], A[4], A[5]}
  writes    {out[0], out[1], out[2]}
  threads   3
  rounds    3 parallel, 9 sequential
  verdict   independent — par = seq under every schedule (wfB = true)
-/
#guard_msgs in
#eval IO.println (checkReport "sum.prl" sum)

-- running it fills the buffers the file declared
/--
info: heap after the run — a .prl program has no print statement, so this is its output
9 cells in 2 buffers, addressed 0 to 8
NAME [dims] @base — the buffer's first cell in that flat heap; cells row-major from there

A [6] @0  [1, 2, 3, 4, 5, 6]
out [3] @6  [3, 7, 11]
-/
#guard_msgs in
#eval IO.println (runReport sum false)

/-! ## 2 · The payoff: one theorem per accepted file

Nothing is supplied by hand. `wfB` decides Bernstein on the quoted program and `par_seq_eq` turns
that Boolean into equality of outcomes under *every* schedule. -/

-- ANCHOR: site-file-theorem
theorem sum_ok (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar sum.prog ρ) (ParProg.execSeq sum.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ
-- ANCHOR_END: site-file-theorem

theorem matmul_ok (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar matmul.prog ρ) (ParProg.execSeq matmul.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

theorem stencil_ok (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar stencil.prog ρ) (ParProg.execSeq stencil.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

theorem pipeline_ok (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar pipeline.prog ρ) (ParProg.execSeq pipeline.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

theorem control_ok (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar control.prog ρ) (ParProg.execSeq control.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

/-- `free` emits no node, so reusing a buffer's cells proves exactly like never freeing them. -/
theorem arena_ok (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar arena.prog ρ) (ParProg.execSeq arena.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

/-! ## 3 · A file that is refused, and the counterexample that says why

Both threads write `x[0]`. `raceReport` replays a found schedule against the real `step`, so the
interleaving printed is one the semantics admits — and the last two lines are the whole point: the
parallel reading and the sequential reading end with different memory. -/

/--
info: race.prl
  memory    x[1] @0, log[2] @1  (3 cells)
  reads     {}
  writes    {log[0], x[0], log[1]}
  threads   2
  rounds    2 parallel, 4 sequential
  verdict   RACY — 1 conflicting fork(s): {x[0]}
-/
#guard_msgs in
#eval IO.println (checkReport "race.prl" race)

/--
info: step:thread  action              state
0:T0         write [log[0]] ← 1  log[0]↦1, x[0]↦0, log[1]↦0
1:T1         write [log[1]] ← 1  log[0]↦1, x[0]↦0, log[1]↦1
2:T1         write [x[0]] ← 9    pending
2:T0         write [x[0]] ← 7    pending
Parallel aborts at Step 2. Reason: T0, T1 write to: {x[0]}.
Parallel: x[0]↦7
Sequential: x[0]↦9
-/
#guard_msgs in
#eval IO.println (raceReport race)

example : ParProg.wfB race.prog = false := by decide

/-! ## 4 · The third verdict: refused, but not racy

`scatter.prl` writes `dst[idx[i]]`. The address is computed, so the syntactic footprint has to
claim all of `dst`, and `wfB` refuses. At the heap the file declares, the three indices miss each
other and the exact check accepts. The tool reports *which of the two checks disagreed*, rather
than calling it a race. -/

/--
info: scatter.prl
  memory    idx[3] @0, dst[3] @3  (6 cells)
  reads     {idx[0], idx[1], idx[2]}
  writes    {dst[0], dst[1], dst[2]}
  threads   3
  rounds    2 parallel, 6 sequential
  verdict   footprint over-approximated: wfB says no, the heap check says yes
-/
#guard_msgs in
#eval IO.println (checkReport "scatter.prl" scatter)

/-! ## 5 · The answers, pinned

A change that keeps a verdict but breaks an answer still fails the build. -/

private def after (c : Compiled) : State :=
  (ParProg.runTaskSeq c.prog (fun _ => 0) c.layout.state).2

#guard (List.range 3).map (fun i => after sum (6 + i))     == [.int 3, .int 7, .int 11]
#guard (List.range 4).map (fun i => after matmul (8 + i))  == [.int 19, .int 22, .int 43, .int 50]
#guard (List.range 4).map (fun i => after stencil (5 + i)) == [.int 3, .int 5, .int 7, .int 9]
#guard after pipeline 4 == .int 25
#guard after control 1  == .int 6

-- the same heap on real threads, which `runTask_eq` guarantees for every program `wfB` accepts
#guard (ParProg.runTask matmul.prog (fun _ => 0) matmul.layout.state).2 8 == Val.int 19

end Paralever.Examples.Files
