import Lang.Load
import Lang.Report

/-! # `funcs.prl` and `sortnet.prl` — programs written with `def`, and the theorems about them

A call is written out where it stands (`docs/prl.md` § *Functions*), so the program this module is
about is the expanded one: `wfB`, `par_seq_eq` and the register allocator see a `ParProg` with no
trace of a `def` in it, exactly as they see no trace of a `for` once it is unrolled.

What the program does: four rows of a 4 × 4 matrix times one vector, the four rows at the same time,
then a scaling pass after the barrier. Every thread reads the whole of `V`, which is the case
Bernstein's condition admits and a disjointness condition would refuse. -/

namespace Paralever.Examples.Functions
open Paralever Paralever.Lang

set_option maxRecDepth 100000

def file : Compiled := prl_file "funcs.prl"

/--
info: funcs.prl
  memory    M[4, 4] @0, V[4] @16, Y[4] @20, Z[4] @24  (28 cells)
  reads     {M[0, 0], V[0], M[0, 1], V[1], M[0, 2], V[2], M[0, 3], V[3], M[1, 0], M[1, 1], … +14 more}
  writes    {Y[0], Y[1], Y[2], Y[3], Z[0], Z[1], Z[2], Z[3]}
  threads   4
  rounds    17 parallel, 44 sequential
  verdict   every heap  Proved: Yes — wfB accepts: the threads' footprints are pairwise independent
-/
#guard_msgs in
#eval IO.println (checkReport "funcs.prl" file)

/-! ## The expansion

Not one register of this file is named by the file. `%s`, `%a` and `%b` belong to `dot` and `%x` to
`scale`, and each is renamed where its call is written out, so no call can clobber a register
another is holding. A `parfor` body is one call site however many threads it unrolls to: the threads
share the index, and registers are thread-private — each thread is handed the pre-fork register file
and what it leaves is discarded — so sharing one index across threads is not sharing a value.
-- ref: `docs/prl.md` § Hygiene -/

#guard file.regs.map Prod.fst == ["s'1", "a'2", "b'3", "x'4"]
#guard file.regs.all (fun r => (r.1.splitOn "'").length == 2)

/-! ## What holds of it -/

/-- Bernstein's condition at every fork, decided on the syntax. The threads write
`Y[0] … Y[3]` and all four read every cell of `V`. -/
example : ParProg.wfB file.prog = true := by decide

/-- **Parallel equals sequential**, for every register file, every heap and every schedule. -/
theorem funcs_par_seq_eq (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar file.prog ρ) (ParProg.execSeq file.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

-- the row sums, since `V` is all ones, and then twice them
private def after : State := (ParProg.runTaskSeq file.prog (fun _ => 0) file.layout.state).2

#guard (List.range 4).map (fun i => after (20 + i)) == [Val.int 6, .int 22, .int 38, .int 54]
#guard (List.range 4).map (fun i => after (24 + i)) == [Val.int 12, .int 44, .int 76, .int 108]

-- and the `par` reading on real threads leaves that same heap, which is `runTask_eq`
#guard (ParProg.runTask file.prog (fun _ => 0) file.layout.state).2 20 == Val.int 6

/-! ## A sorting network

`sortnet.prl` is odd-even transposition sort on eight cells: eight phases, and inside a phase every
comparator touches a different pair, so a phase's comparators run at the same time and a
`synchronize` separates one phase from the next. The comparator is one `def`, called 28 times.

Both arms of its `if` write both cells of the pair, so the footprint of a comparator is its pair
whichever way the comparison goes (`docs/block-ir.md` § *Control flow*) — which is why `wfB` accepts
at every heap rather than at this one. The theorem is therefore about every input: whatever the
sequential network computes from a heap, every schedule of the parallel one computes the same
thing. -/

def net : Compiled := prl_file "sortnet.prl"

#guard net.layout.bufs.map (fun p => p.name) == ["A"]
-- eight forks and the barriers between them, rather than one fork of everything
#guard (ParProg.flatten net.prog).length == 17
-- two registers for 28 comparators: the comparator is one call site inside two unrolled loops
#guard net.regs.map Prod.fst == ["x'1", "y'2"]

example : ParProg.wfB net.prog = true := by decide

/-- **Parallel equals sequential**, for every register file, every heap and every schedule. The
network's own correctness is not claimed here; its agreement with its sequential reading is. -/
theorem sortnet_par_seq_eq (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar net.prog ρ) (ParProg.execSeq net.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

-- the declared heap is 5, 3, 8, 1, 7, 2, 6, 4, and both readings leave it sorted
#guard (List.range 8).map (fun i =>
    (ParProg.runTaskSeq net.prog (fun _ => 0) net.layout.state).2 i)
  == (List.range 8).map (fun i => Val.int (Int.ofNat i + 1))

#guard (List.range 8).map (fun i =>
    (ParProg.runTask net.prog (fun _ => 0) net.layout.state).2 i)
  == (List.range 8).map (fun i => Val.int (Int.ofNat i + 1))

end Paralever.Examples.Functions
