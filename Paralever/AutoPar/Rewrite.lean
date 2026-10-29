import Paralever.AutoPar.Sound
import Paralever.AutoPar.Dag
import Lang.Core.Notation

/-! # The rewrite, end to end

`paralever { … }` → `ParProg` → a scheduled `ParProg` → surface text again. The round trip is
closed: `surface` emits what `paralever { … }` parses, so a rewritten program can be pasted back
into the language it came from. -- ref: docs/autopar-algorithm.md § Round trip -/

namespace Paralever.AutoPar
open Paralever Paralever.Lang Paralever.Lang.ParProg

/-! ## Units

The scheduling unit is a register-closed segment, not a statement: a load and the store consuming
its register are one unit and are never split across a fork.
-- ref: Lang/Core/Analysis.lean `atoms`, docs/autopar.md -/

/-- The chain's units, in order. -/
def units (p : ParProg) : List ParProg := (atoms (flatten p)).map block

/-- **The units run like the program.** Three regroupings, one lemma each. -/
theorem units_faithful (p : ParProg) (ρ : Regs) (σ : State) :
    runSeq (execSeq (block (units p)) ρ) σ = runSeq (execSeq p ρ) σ := by
  show runSeq (execSeq (block ((atoms (flatten p)).map block)) ρ) σ = _
  rw [runSeq_block_map, atoms_flatten, runSeq_flatten]

/-! ## The rewrite -/

/-- The plan for a program. -/
def planOf (p : ParProg) : Plan := plan (units p)

/-- Whether the plan may be committed: the program has no `synchronize`, no register flows between
threads, and the emitted program passes the independence check. The last two are what the soundness
theorems need; the first is a boundary, not a theorem's hypothesis — `emit` wraps every stage in a
`par`, so a barrier reaching the plan would end up inside a thread, and carrying a register across
one needs a liveness condition this route does not yet state. `ParProg.autoPar` is the route that
honours a barrier. -- ref: docs/autopar.md § Synchronization -/
def rewriteOk (p : ParProg) : Bool :=
  barrierFree p && noRegFlow (threads (planOf p)) && wfB (emit (planOf p))

/-- **The rewrite.** The analysis is untrusted; `rewriteOk` is the proved gate, and a program whose
plan does not pass it is returned unchanged. -/
def rewrite (p : ParProg) : ParProg := if rewriteOk p then emit (planOf p) else p

/-- **`seq = par` for the rewrite, unconditionally.** The rewritten program, read in parallel,
leaves exactly the heap the original leaves read sequentially — for every program, with no
hypothesis, because the gate is checked inside `rewrite`. -/
-- ANCHOR: site-rewrite-sound
theorem rewrite_sound (p : ParProg) (ρ : Regs) (σ : State) :
    (runSeq (execPar (rewrite p) ρ) σ).2 = (runSeq (execSeq p ρ) σ).2 := by
  unfold rewrite
  by_cases h : rewriteOk p = true
  · simp only [h, ite_true]
    have hflow : noRegFlow (threads (plan (units p))) = true := by
      simp only [rewriteOk, Bool.and_eq_true] at h; exact h.1.2
    exact rewrite_heap p (units p) (plan_units (units p)) (units_faithful p) hflow ρ σ
  · simp only [h, ite_false, Bool.false_eq_true]
    exact execPar_runSeq_all.1 p ρ σ ▸ rfl
-- ANCHOR_END: site-rewrite-sound

/-- **The rewrite stays well-formed.** So `par_seq_eq` applies to the result, lifting
`rewrite_sound` from one schedule to every schedule. -/
theorem rewrite_wf (p : ParProg) (hp : wfB p = true) : wfB (rewrite p) = true := by
  unfold rewrite
  by_cases h : rewriteOk p = true
  · simp only [h, ite_true]
    simp only [rewriteOk, Bool.and_eq_true] at h
    exact h.2
  · simp only [h, ite_false, Bool.false_eq_true]; exact hp

/-- **Every schedule of the rewrite agrees with the original.** `rewrite_wf` feeds `par_seq_eq`,
which is the project's metatheorem; `rewrite_sound` ties its sequential side back to `p`. -/
theorem rewrite_parSeqEq (p : ParProg) (hp : wfB p = true) (ρ : Regs) (σ : State) :
    ParSeqEq (execPar (rewrite p) ρ) (execSeq (rewrite p) ρ) σ :=
  ParProg.par_seq_eq (rewrite_wf p hp) ρ σ

/-! ## Quality

`critical` is a lower bound for *any* schedule of the units, so `depth (rewrite p) = critical` is a
certificate that the plan is optimal — and when it is larger, the difference is the price of the
fork–join shape. -- ref: docs/autopar-algorithm.md § The bound -/

/-- The plan's depth, the critical path, and the sequential depth. -/
def quality (p : ParProg) : Nat × Nat × Nat :=
  (depth (rewrite p), critical (units p), depth p)

/-- Whether the plan attains the lower bound. -/
def optimalB (p : ParProg) : Bool := depth (rewrite p) == critical (units p)

/-! ### The pass, evaluated

`quality` reads `(what the pass emits, the bound, the sequential depth)`. -/

section Demo

/-- Two independent squarings, written one after the other. -/
private def chain : ParProg := paralever {
  [0] := 3; [1] := 4;
  %0 := [0]; [2] := %0 * %0;
  %1 := [1]; [3] := %1 * %1
}

-- six statements become four units, two stages, and depth 3 instead of 6
#guard (units chain).length == 4
#guard (planOf chain).length == 2
#guard quality chain == (3, 3, 6)
#guard optimalB chain
#guard rewriteOk chain
#guard wfB (rewrite chain)

/-- A loop-carried dependence: every statement needs the one before it. -/
private def carried : ParProg := paralever {
  %0 := [0]; [1] := %0 + 1;
  %1 := [1]; [2] := %1 + 1
}

-- nothing to find, and the pass reports that rather than inventing a fork
#guard quality carried == (4, 4, 4)
#guard optimalB carried

-- Where the bound is *not* attained, the pass says so rather than claiming otherwise: the
-- smallest such shape is the **N**, pinned at `quality = (8, 7, 12)` with `optimalB = false` in
-- `Test/AutoParAlgo.lean`. Fork--join terms are series-parallel and dependence DAGs are not.

end Demo

end Paralever.AutoPar
