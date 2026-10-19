import Paralever.Lang.Notation
import Paralever.Lang.AutoParSound
import Paralever.Lang.Exec
import Paralever.AutoPar.Rewrite

/-! # `autoPar` regression tests

Three programs whose rewrite used to change the answer. Each one pins a different reason a register
may not cross a fork boundary. The last section compares the two routes on all three.
-- ref: docs/autopar.md -/

namespace Paralever.Test.AutoPar
open Paralever Paralever.Lang Paralever.Lang.ParProg Paralever.AutoPar

def σ0 : State := fun _ => .int 0

/-! ### 1. A register must not be split from the statement that consumes it

The N: `i3` depends on `i1` and `i2`, `i4` on `i2` alone. Flattening to statements let the load of
`t0` land in one stage and the store that reads it in the next, where the fork had already discarded
it. -/

def nShape : ParProg := paralever {
  [10] := 1;
  [11] := 2;
  %0 := [10]; %1 := [11]; [12] := R 0 + R 1;
  %2 := [11]; [13] := R 2 * 2
}

/-- The register-connected statements stay together: four segments, of sizes 1, 1, 3, 2. -/
example : (atoms (flatten nShape)).map (fun g => g.length) = [1, 1, 3, 2] := by decide

/-- The rewrite computes what the original computes. -/
example : evalTask (autoPar nShape) σ0 [10,11,12,13] = evalTaskSeq nShape σ0 [10,11,12,13] := by
  decide

example : evalTaskSeq nShape σ0 [12,13] = [.int 3, .int 4] := by decide
example : wfB (autoPar nShape) = true := by decide

/-! ### 2. A reused register must not pin the whole program together

Liveness has to kill: `%0` is rewritten by every iteration, so it is never live across a boundary
and all three segments fork. Without the kill, `%0` would look live from the first statement to the
last and nothing would ever be separable. -/

def reuse : ParProg := paralever {
  %0 := [0]; [100] := R 0;
  %0 := [1]; [101] := R 0;
  %0 := [2]; [102] := R 0
}

example : (atoms (flatten reuse)).map (fun g => g.length) = [2, 2, 2] := by decide
example : hasPar (autoPar reuse) = true := by decide

def σin : State := fun l => if l < 3 then .int (l + 1 : Nat) else .int 0

example : evalTask (autoPar reuse) σin [100,101,102] = evalTaskSeq reuse σin [100,101,102] := by
  decide

/-! ### 3. A conditional write must not kill

`regFootprint`'s write set is a *may*-write — a conditional's is the union of its branches — so
killing on it would declare `%0` dead when only the untaken branch assigns it. `regKills` is the
must-write, and with it no boundary is offered here at all. -/

def cond : ParProg := paralever {
  %0 := 5;
  if (R 1) { %0 := 1 } else { [7] := 9 };
  [8] := R 0
}

/-- One segment: there is no legal cut, so nothing is forked. -/
example : (atoms (flatten cond)).map (fun g => g.length) = [3] := by decide
example : hasPar (autoPar cond) = false := by decide
example : evalTask (autoPar cond) σ0 [7,8] = evalTaskSeq cond σ0 [7,8] := by decide
example : evalTaskSeq cond σ0 [8] = [.int 5] := by decide

/-! ### The theorem, at these programs

`par_block_heap` is the general statement; here is its hypothesis holding on a concrete group. -/

example : noRegFlow [paralever { [10] := 1 }, paralever { [11] := 2 }] = true := by decide

/-! ### The two routes, side by side

`autoPar` proposes and `wfB` checks, per program; `AutoPar.rewrite` is proved for every program and
so refuses more. These gates pin where the two disagree, and they are expected to **fail** when the
gate is weakened — that failure is the notification, not a break.
-- ref: docs/autopar.md § The two routes -/

/-- The N: both routes fork it, and `rewrite` reaches the dependence DAG's bound. -/
example : hasPar (autoPar nShape) = true := by decide
example : hasPar (rewrite nShape) = true := by decide
example : depth (autoPar nShape) = 4 := by decide
example : quality nShape = (4, 4, 7) := by decide
example : optimalB nShape = true := by decide

/-- A reused register: `atoms` kills it by liveness, so `autoPar` forks all three segments and
reaches depth 2. `noRegFlow` is on raw read sets, sees `%0` read in a later thread, and declines —
so the proved route returns the program sequential and gives up a 3× depth reduction. -/
example : hasPar (autoPar reuse) = true := by decide
example : depth (autoPar reuse) = 2 := by decide
example : rewriteOk reuse = false := by decide
example : hasPar (rewrite reuse) = false := by decide
example : quality reuse = (6, 2, 6) := by decide

/-- A conditional write: neither route finds parallelism, and both are right. `emit` builds a
`par` node per stage unconditionally, so `rewrite` returns a **one-thread** fork where `autoPar`
special-cases a singleton group back to a plain statement. Same depth, same heap, extra node. -/
example : hasPar (autoPar cond) = false := by decide
example : hasPar (rewrite cond) = true := by decide
example : (threads (planOf cond)).length = 1 := by decide
example : depth (rewrite cond) = depth cond := by decide

end Paralever.Test.AutoPar
