import Paralever.AutoPar.Chain

/-! # The schedule

A `Plan` is a **two-level consecutive partition** of the unit chain: units group into threads,
threads group into stages, and nothing is ever reordered. That restriction is what makes the rewrite
provable with `par_block_heap` alone — a scheduler that moved units past one another would need a
commutation theorem instead. -- ref: docs/autopar-algorithm.md § The shape of a plan -/

namespace Paralever.AutoPar
open Paralever Paralever.Lang Paralever.Lang.ParProg

/-- Stages, each a list of threads, each thread a list of units — all in program order. -/
abbrev Plan := List (List (List ParProg))

/-- The emitted program: one `parallel` block per stage, one thread per child. -/
def emit (pl : Plan) : ParProg := block (pl.map fun st => .par (st.map block))

/-- Every thread of the plan, in order, each blocked into one statement. The list
`par_block_heap`'s hypothesis is about. -/
def threads (pl : Plan) : List ParProg := pl.flatten.map block

/-- Every unit of the plan, in order. -/
def planUnits (pl : Plan) : List ParProg := pl.flatten.flatten

/-! ## Building a plan

One left-to-right pass. Each unit either extends the current thread, opens a new thread beside it,
or forces a new stage — and the three cases are exactly the three ways a dependence can fall.
-- ref: docs/autopar-algorithm.md § The pass -/

/-- Does `x` conflict with anything in `ts`, so that no fork may hold them side by side?
-- ref: Lang/Core/Analysis.lean `canParSeg` -/
def mustFollow (ts : List (List ParProg)) (x : ParProg) : Bool :=
  ts.any (fun t => t.any (fun u => !ParProg.canParSeg u x))

/-- The pass. `cur` is the thread being built, `stage` the threads already closed in this stage. -/
def planGo (cur : List ParProg) (stage : List (List ParProg)) : List ParProg → Plan
  | []      => [stage ++ [cur]]
  | x :: xs =>
      if mustFollow stage x then
        -- x must follow a thread that is already a sibling here: only a join can order them
        (stage ++ [cur]) :: planGo [x] [] xs
      else if mustFollow [cur] x then
        planGo (cur ++ [x]) stage xs -- x follows this thread: extend it
      else
        planGo [x] (stage ++ [cur]) xs  -- independent of everything open: new thread

/-- **The schedule.** -/
def plan : List ParProg → Plan
  | []      => []
  | x :: xs => planGo [x] [] xs

/-! ### The three cases, on three-unit chains

Each `#guard` below is the shape of the plan — one number per stage, counting its threads. -/

section Demo
private def wr (l : Loc) : ParProg := .store l (.lit 1)
private def rd (r : Reg) (l : Loc) : ParProg := .load r l

-- all independent: one stage, three threads
#guard (plan [wr 0, wr 1, wr 2]).map (fun stage => stage.length) == [3]
-- a chain of dependences: one thread holding all three, which is the sequential program back
#guard (plan [wr 0, rd 0 0, wr 0]).map (fun stage => stage.length) == [1]
-- `wr 1` is independent of `wr 0`, so it opens a second thread beside it; `rd 0 0` conflicts with
-- a *closed sibling*, which only a join can order, so it forces a new stage
#guard (plan [wr 0, wr 1, rd 0 0]).map (fun stage => stage.length) == [2, 1]
-- and nothing is ever reordered, whatever the plan: `plan_units` below is this as a theorem
#guard (planUnits (plan [wr 0, wr 1, rd 0 0])).length == 3
end Demo

/-! ## Order preservation, structurally

The plan is a partition, so its units are the units it was given — no `DecidableEq ParProg`, no
check at run time, and the soundness theorem gets this as an equation rather than a hypothesis. -/

/-- The pass partitions: its units are what was closed, plus what is open, plus what is left. -/
theorem planGo_units : ∀ (xs cur : List ParProg) (stage : List (List ParProg)),
    planUnits (planGo cur stage xs) = stage.flatten ++ cur ++ xs := by
  intro xs
  induction xs with
  | nil => intro cur stage; simp [planGo, planUnits]
  | cons x rest ih =>
      intro cur stage
      by_cases h1 : mustFollow stage x = true
      · simp only [planGo, h1, ite_true, planUnits, List.flatten_cons, List.flatten_append]
        rw [show (planGo [x] [] rest).flatten.flatten = planUnits (planGo [x] [] rest) from rfl,
          ih [x] []]
        simp
      · by_cases h2 : mustFollow [cur] x = true
        · simp only [planGo, h1, h2, ite_true, ite_false, Bool.false_eq_true]
          rw [ih (cur ++ [x]) stage]; simp
        · simp only [planGo, h1, h2, ite_false, Bool.false_eq_true]
          rw [ih [x] (stage ++ [cur])]; simp

/-- **A plan's units are the chain it was built from.** -/
theorem plan_units (us : List ParProg) : planUnits (plan us) = us := by
  match us with
  | []      => rfl
  | x :: xs => rw [plan, planGo_units]; simp

end Paralever.AutoPar
