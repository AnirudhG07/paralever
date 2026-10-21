import Paralever.Tactic
import Lang.Load

/-! # The two tactics, as build gates

`paralever_check` either closes the goal or fails, so the race-free cases below are gates in the
strongest sense available: the file does not compile unless the tactic found the proof. The racy
case is gated on its message, because what the tactic owes a user there is an explanation.
-- ref: `docs/race-search.md` § In tactic position -/

namespace Test.Tactic
open Paralever Paralever.Lang

set_option maxRecDepth 100000

def sumF : Compiled     := prl_file "../Examples/Language/sum.prl"
def scatterF : Compiled := prl_file "../Examples/Language/scatter.prl"
def raceF : Compiled    := prl_file "../Examples/Language/race.prl"

/-! ## The route `wfB` licenses, at every heap -/

example (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar sumF.prog ρ) (ParProg.execSeq sumF.prog ρ) σ := by
  paralever_check

/-! ## The per-heap route, where a computed address makes the footprint a bound -/

example :
    ParSeqEq (ParProg.execPar scatterF.prog zeroRegs) (ParProg.execSeq scatterF.prog zeroRegs)
      scatterF.layout.state := by
  paralever_check

/-! ## A `ParM` written by hand rather than compiled -/

def w0 : ParM Unit := ParM.write 0 (.int 1) (fun _ => .pure ())
def w1 : ParM Unit := ParM.write 1 (.int 2) (fun _ => .pure ())

example : ParSeqEq (ParM.parPair w0 w1) (ParM.seqPair w0 w1) zeroHeap := by
  paralever_check

/-! ## And the program for which there is no theorem

Both checks refuse, so the tactic fails — and the failure carries the interleaving that reaches
`wrong`, which is the thing a user needs and a `decide` that returns `false` does not give. -/

/--
error: paralever_check: this program has a race, so no instance of `par_seq_eq` exists for it — 1 conflicting fork(s), on {0}.
  step:thread  action         state
  0:T0         write [1] ← 1  1↦1, 0↦0, 2↦0
  1:T1         write [2] ← 1  1↦1, 0↦0, 2↦1
  2:T1         write [0] ← 9  pending
  2:T0         write [0] ← 7  pending
  Parallel aborts at Step 2. Reason: T0, T1 write to: {0}.
  Parallel: 0↦7
  Sequential: 0↦9
-/
#guard_msgs in
example :
    ParSeqEq (ParProg.execPar raceF.prog zeroRegs) (ParProg.execSeq raceF.prog zeroRegs)
      raceF.layout.state := by
  paralever_check

/-! ## `paralever_race` on its own

A diagnostic: it leaves the goal alone, logs the trace where a widget cannot render, and says which
heap it ran at when the goal quantifies over one. On a race-free program there is no interleaving to
show, and the line above says why. -/

/--
info: the exact check finds no conflicting access at this heap, so the obligation holds here
`ρ` is a variable, so the registers are all 0 below
`σ` is a variable, so the heap below is the one whose cells are all 0: what it shows holds at that heap, not at every heap
No counterexample: no par node fails Bernstein.
Sequential: 0↦0, 1↦0, 2↦0, 3↦0, 4↦0, 5↦0, 6↦0, 7↦0, +1 more
-/
#guard_msgs in
example (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar sumF.prog ρ) (ParProg.execSeq sumF.prog ρ) σ := by
  paralever_race
  paralever_check

end Test.Tactic
