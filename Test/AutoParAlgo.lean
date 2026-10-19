import Paralever.AutoPar.Rewrite
import Paralever.Lang.Exec

/-! # The rewrite, on programs

`rewrite_sound` is proved for every program, so these gates are not about soundness. They pin the
*quality*: which tree the pass picks, and whether it reaches the critical-path bound. A regression
here means the scheduler changed shape. -- ref: docs/autopar-algorithm.md -/

namespace Paralever.Test.AutoParAlgo
open Paralever Paralever.Lang Paralever.Lang.ParProg Paralever.AutoPar

/-- Probe a program both ways: the rewrite on real threads, the original sequentially. -/
def agrees (p : ParProg) (σ : State) (probes : List Loc) : Bool :=
  evalTask (rewrite p) σ probes == evalTaskSeq p σ probes

/-! ### Two independent chains, written interleaved

The case greedy prefix grouping gets wrong: it stops a group at the first conflict, so it emits
three stages (depth 5) where one stage of two threads does it in 3. -/

def ex1 : ParProg := paralever {
  [0] := 1; %0 := [0]; [1] := R 0; [2] := 3; %1 := [2]; [3] := R 1 }

#guard (units ex1).length == 4
#guard (planOf ex1).length == 1                   -- one stage …
#guard (threads (planOf ex1)).length == 2         -- … holding two threads
#guard quality ex1 == (3, 3, 6)                   -- depth, bound, sequential
#guard optimalB ex1
#guard rewriteOk ex1
#guard agrees ex1 (fun _ => .int 0) [0,1,2,3]

/-! ### The N

`a3` needs both `a1` and `a2`; `a4` needs only `a2`. The plan reaches 8, the dependence DAG's
critical path is 7, and 7 is **not** attainable: it needs `a3` concurrent with `a2`, which `wfB`
rejects. So `optimalB` is `false` here and that is the fork–join shape, not the scheduler. -/

def a1 : ParProg := paralever { %3 := [20]; [0] := R 3; [10] := R 3; [11] := R 3 }
def a2 : ParProg := paralever { [1] := 3 }
def a3 : ParProg := paralever { %0 := [0]; %1 := [1]; [2] := R 0 + R 1 }
def a4 : ParProg := paralever { %2 := [1]; [3] := R 2; [4] := R 2; [5] := R 2 }

def eN : ParProg := block [a1, a2, a3, a4]

#guard (units eN).length == 4
#guard (planOf eN).length == 2
#guard (threads (planOf eN)).length == 4
#guard quality eN == (8, 7, 12)
#guard !optimalB eN
#guard rewriteOk eN
#guard agrees eN (fun _ => .int 7) [0,1,2,3,4,5,10,11]

/-- The tree that would reach the bound of 7 pairs `a1;a3` against `a2;a4`, which puts `a3`'s read
of `[1]` beside `a2`'s write of it. `wfB` rejects it, so 8 is the floor for a fork–join rewrite. -/
example : wfB (.par [block [a1, a3], block [a2, a4]]) = false := by decide
example : depth (.par [block [a1, a3], block [a2, a4]]) = 7 := by decide

/-! ### Merge sort, four elements

Divide-and-conquer dependence DAGs are series-parallel, so the pass recovers the recursion tree it
never saw — `atoms` threw it away with the `;`-chain — and attains the bound. -/

def ms4 : ParProg := paralever {
  %0 := [0]; %1 := [1]; [0] := AExp.min (R 0) (R 1); [1] := AExp.max (R 0) (R 1);
  %2 := [2]; %3 := [3]; [2] := AExp.min (R 2) (R 3); [3] := AExp.max (R 2) (R 3);
  %4 := [0]; %5 := [1]; %6 := [2]; %7 := [3];
  [10] := AExp.min (R 4) (R 6);
  [11] := AExp.min (AExp.max (R 4) (R 6)) (AExp.min (R 5) (R 7));
  [12] := AExp.max (AExp.max (R 4) (R 6)) (AExp.min (R 5) (R 7));
  [13] := AExp.max (R 5) (R 7) }

def input4 : State := fun l =>
  .int (if l = 0 then 3 else if l = 1 then 1 else if l = 2 then 4 else if l = 3 then 1 else 0)

#guard (planOf ms4).length == 2
#guard quality ms4 == (12, 12, 16)
#guard optimalB ms4
#guard evalTask (rewrite ms4) input4 [10,11,12,13] == [.int 1, .int 1, .int 3, .int 4]
#guard agrees ms4 input4 [10,11,12,13]

/-! ### A loop-carried chain has nothing to find

`A[i] := A[i-1] + 1` is genuinely sequential, so the plan is one thread and the depth is the
sequential one. The gate is that the pass does not pretend otherwise. -/

def carried : ParProg := paralever {
  %0 := [0]; [1] := R 0 + 1; %1 := [1]; [2] := R 1 + 1; %2 := [2]; [3] := R 2 + 1 }

#guard (threads (planOf carried)).length == 1
#guard (quality carried).1 == (quality carried).2.2
#guard agrees carried (fun _ => .int 1) [0,1,2,3]

/-! ### Reused registers fall back

Registers are thread-private, so a chain that reuses `%0` across segments has register flow between
what would be siblings. `noRegFlow` is on raw read sets, which is stronger than the liveness
`atoms` actually establishes, so the gate declines and the program is returned unchanged — sound,
and the parallelism is lost. -- ref: docs/autopar-algorithm.md § What the gate still refuses -/

def reused : ParProg := paralever {
  [10] := 1; [11] := 2; %0 := [10]; [12] := R 0; %0 := [11]; [13] := R 0 }

#guard agrees reused (fun _ => .int 0) [10,11,12,13]

end Paralever.Test.AutoParAlgo
