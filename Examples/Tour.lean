import Prl.Report
import Paralever.AutoPar.Print

namespace Paralever.Examples.Tour
open Paralever Paralever.Prl Paralever.Prl.ParProg

/-! # The whole project, on one program

Five claims, each one evaluated or proved here. Every other directory under `Examples/` is one of
these five in depth. -/

/-! ## 1 · Write a parallel program

Square two numbers side by side, then add the squares. `paralever { … }` is surface syntax that
elaborates to a `ParProg`, which is *data* — no Lean closures, so the program can be printed,
measured, searched and decided. -/

def squares : ParProg := paralever {
  [0] := 3;
  [1] := 4;
  parallel { %0 := [0]; [2] := %0 * %0 }
           | { %0 := [1]; [3] := %0 * %0 };
  %0 := [2];
  %1 := [3];
  [4] := %0 + %1
}

/-! ## 2 · The independence obligation is a `Bool`

Bernstein's three conditions, computed from the syntax: the threads' writes are disjoint, and
neither reads what the other writes. The kernel evaluates it. -/

#guard (ParProg.footprintOf squares).reads  == [0, 1, 2, 3]
#guard (ParProg.footprintOf squares).writes == [0, 1, 2, 3, 4]
#guard wfB squares

/-! ## 3 · …and it buys an equality, under *every* schedule

This is the metatheorem. `ParSeqEq` says the two programs can finish in exactly the same
answer-and-memory pairs — an equality of two sets, not an inclusion — so nothing is left to the
scheduler. -/

theorem squares_ok (ρ : Regs) (σ : State) :
    ParSeqEq (execPar squares ρ) (execSeq squares ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

-- and it computes 3·3 + 4·4
#guard (runSeq (execPar squares (fun _ => 0)) (fun _ => .int 0)).2 4 == Val.int 25

/-! ## 4 · Break it, and the counterexample is printed

Point both threads at the same cell. `wfB` now refuses, and the search returns the interleaving
that realizes the race — replayed against the real `step`, so it is an execution the semantics
admits, not an illustration. The last two lines are why the hypothesis is load-bearing. -/

def clash : Prog := .par (.seq (.wr 10 1) (.wr 9 1)) (.seq (.wr 20 1) (.wr 9 2))

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
#eval IO.println (explainProg clash (fun _ => .int 0))

/-! ## 5 · Hand it a sequential program and it finds the parallelism itself

`rewrite` groups the statements into stages and emits the forks. `rewrite_sound` holds for every
program with no hypothesis to supply, because the check is inside the rewrite: a program it cannot
schedule safely comes back unchanged. -/

def straightLine : ParProg := paralever {
  [0] := 3; [1] := 4;
  %0 := [0]; [2] := %0 * %0;
  %1 := [1]; [3] := %1 * %1
}

/--
info: paralever {
  parallel { [0] := 3 } | { [1] := 4 };
  parallel { %0 := [0]; [2] := (%0 * %0) } | { %1 := [1]; [3] := (%1 * %1) }
}
-- units      4
-- stages     2
-- threads    4
-- depth      3  (sequential 6, lower bound 3)
-- optimal    true
-- committed  true
-/
#guard_msgs in
#eval IO.println (AutoPar.report straightLine)

example (ρ : Regs) (σ : State) :
    (runSeq (execPar (AutoPar.rewrite straightLine) ρ) σ).2
      = (runSeq (execSeq straightLine ρ) σ).2 :=
  AutoPar.rewrite_sound straightLine ρ σ

/-! ## Where to go next

| directory | question it answers |
|---|---|
| `Programs/` | how do I prove *my* algorithm equivalent? |
| `Language/` | how do I write and check a `.prl` file? |
| `Mlir/` | how do I bring a program in from MLIR? |
| `AutoPar/` | what exactly does the pass do, step by step? |
| `Races/` | what does a failure look like, and is the hypothesis load-bearing? |
| `Threads/` | does any of this actually run? |
-/

end Paralever.Examples.Tour
