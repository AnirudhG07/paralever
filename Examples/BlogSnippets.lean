import Paralever.Lang.Imp
import Paralever.Lang.Exec
import Paralever.Lang.Cost
import Paralever.Search.Explain
import Paralever.AutoPar.Rewrite

/-! # The code quoted in the blog post

Every Lean block the post shows lives here, so the post cannot drift from the library. The regions
are named with `ANCHOR` comments and rendered to HTML by `verso-snippets`.
-- ref: docs/race-search.md, docs/cost.md, docs/autopar-algorithm.md -/

namespace BlogSnippets
open Paralever Paralever.Lang Paralever.Lang.ParProg

/-! ## The hook -/

-- ANCHOR: hook
/-- Square two inputs in parallel, then add the squares. -/
def pipeline : ParProg := paralever {
  [0] := 3;
  [1] := 4;
  parallel { %0 := [0]; [2] := R 0 * R 0 }
           | { %0 := [1]; [3] := R 0 * R 0 };
  %0 := [2];
  %1 := [3];
  [4] := R 0 + R 1
}

-- the independence obligation is a Bool, and the kernel evaluates it
example : wfB pipeline = true := by decide

/-- The parallel reading and the sequential reading agree, under *every* schedule. -/
theorem pipeline_ok (ρ : Regs) (σ : State) :
    ParSeqEq (execPar pipeline ρ) (execSeq pipeline ρ) σ :=
  par_seq_eq (by decide) ρ σ

-- and it computes 3*3 + 4*4
example : (runSeq (execPar pipeline (fun _ => 0)) (fun _ => .int 0)).2 4 = .int 25 := by decide
-- ANCHOR_END: hook

/-! ## Shared reads -/

-- ANCHOR: shared
/-- Three threads, all of which read `[2]`. Bernstein admits this; `∗`-disjointness does not. -/
def shared : ParProg := paralever {
  %0 := [0];
  %1 := [1];
  [2] := R 0 + R 1;
  parallel { %3 := [2]; [3] := R 3 * 2 }
    | { %4 := [2]; [4] := R 4 - 1 }
    | { [5] := 7 }
}

-- the footprint is a fold over the syntax: reads on the left, writes on the right
example : footprintOf shared = ⟨[0, 1, 2, 2], [2, 3, 4, 5]⟩ := rfl
example : wfB shared = true := by decide
-- ANCHOR_END: shared

/-! ## Kernels -/

-- ANCHOR: kernels
/-- **A 1-D stencil**, at every size and window: `out[i] := Σ_{k<w} inp[i+k]`.
The obligation is discharged once, for all `n` and `w`, from one range inequality. -/
theorem stencil_ok (n w inp out : Nat) (h : inp + n + w ≤ out) :
    wfB (stencilK n w inp out (fun _ => .lit 1)) = true :=
  wfB_stencilK n w inp out _ (fun i j _ hj k hk => by grind)

/-- **A dense layer**: `out[i] := Σ_j W[i,j] * x[j] + b[i]`. Every thread reads *all* of `x`,
which is exactly the shared-read pattern separating conjunction rejects. -/
theorem dense_ok (rows cols wgt xs bias out : Nat)
    (h1 : wgt + rows * cols ≤ xs) (h2 : xs + cols ≤ bias) (h3 : bias + rows ≤ out) :
    wfB (denseK rows cols wgt xs bias out) = true := by
  refine wfB_denseK rows cols wgt xs bias out (fun i j hi hj k hk => ⟨?_, ?_⟩)
    (fun i j hi hj => by grind)
  · have : j * cols + k < rows * cols := by
      rw [show j * cols + k = lin cols j k from rfl]; exact lin_lt hj hk
    grind
  · grind

/-- **Bias add**: `out[i,j] := inp[i,j] + bias[j]`. Every row reads the same bias vector. -/
theorem biasAdd_ok (rows cols inp bias out : Nat)
    (h1 : inp + rows * cols ≤ bias) (h2 : bias + cols ≤ out) :
    wfB (biasAddK rows cols inp bias out) = true := by
  refine wfB_biasAddK rows cols inp bias out (fun i j i' j' _ hj _ hj' hne => ?_)
    (fun i j i' j' hi hj hi' hj' => ⟨?_, ?_⟩)
  · rw [Nat.add_assoc, Nat.add_assoc]
    exact lin_ne_of_ne hj hj' hne
  · have : i * cols + j < rows * cols := by
      rw [show i * cols + j = lin cols i j from rfl]; exact lin_lt hi hj
    have : i' * cols + j' < rows * cols := by
      rw [show i' * cols + j' = lin cols i' j' from rfl]; exact lin_lt hi' hj'
    grind
  · have : i * cols + j < rows * cols := by
      rw [show i * cols + j = lin cols i j from rfl]; exact lin_lt hi hj
    grind
-- ANCHOR_END: kernels

/-! ## Real threads -/

-- ANCHOR: tasks
-- `runTask` spawns one Lean `Task` per thread of every `parallel` block.
#check @runTask

-- The real-threads run leaves exactly the heap the canonical sequential run leaves. The `Task`
-- scheduler may interleave however it likes; `wfB` is what makes the outcome independent of it.
#check @runTask_eq

-- So a wall-clock comparison of the two is fair *by theorem* rather than by observation.
#check @runTask_eq_runTaskSeq

-- run the pipeline on real threads and read cell 4 back
#eval evalTask pipeline (fun _ => .int 0) [4]
-- ANCHOR_END: tasks

/-! ## Time -/

-- ANCHOR: timing
-- Work is unchanged: the same memory operations run either way, so parallelism buys nothing in
-- total operations. Conflating this with time is the usual mistake.
#check @work_par_eq_seq

-- Par ≤ Seq in rounds, for every program the check accepts — the cost counterpart of
-- `par_seq_eq`, out of the same `Bool`.
#check @ParProg.time_le

-- Strictly fewer rounds when both branches actually do something. `max` at a fork is stipulated
-- nowhere in the cost semantics; it is derived, and independence is what earns it.
#check @time_par_lt_seq

-- the pipeline: the same work either way, fewer rounds in parallel
#eval (work (execPar pipeline (fun _ => 0)) (fun _ => .int 0),
       work (execSeq pipeline (fun _ => 0)) (fun _ => .int 0))
#eval (time (execPar pipeline (fun _ => 0)) (fun _ => .int 0),
       time (execSeq pipeline (fun _ => 0)) (fun _ => .int 0))
-- ANCHOR_END: timing

/-! ## A race, and how it is found -/

-- ANCHOR: racy
/-- Both threads work for a while, then both write `[9]`. -/
def late : Prog :=
  .par (.seq (.wr 10 1) (.wr 9 1))
       (.seq (.wr 20 1) (.wr 9 2))

/-- Everything starts at `0`. -/
def σ0 : State := fun _ => .int 0

-- Phase 1 walks the tree and collects every fork whose children fail Bernstein. It is linear in
-- the program, and it *is* the obligation: `raceSites_nil_iff` says an empty list is race freedom.
#eval raceSites late.toParM σ0

-- so the program is rejected, by evaluation rather than by search
example : wellFormedB late.toParM σ0 = false := by decide

-- Phase 2 is a bounded search, aimed at the cells phase 1 named. It returns a `Schedule`, and
-- `follow_sound` turns any schedule that replays into a `Reaches` proof — so a wrong guess
-- cannot produce a wrong claim, it just fails to find anything.
#check @follow_sound

-- the counterexample, replayed against the real `step`
#eval IO.println (explainProg late σ0)
-- ANCHOR_END: racy

end BlogSnippets
