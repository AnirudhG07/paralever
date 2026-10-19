# Making a sequential program parallel

`Paralever/AutoPar/` turns a `;`-chain into a tree of `parallel` blocks and **proves the rewrite
preserves the outcome**. `Lang/Analysis.lean`'s `autoPar` is a greedy sketch whose claim is checked
per program; this is the same job done so the claim is a theorem.

Both routes are live, and this one is not a superset: its gate is stricter, so it refuses chains
`autoPar` forks. `autopar.md` § *The two routes* has the measured comparison, and this file builds
on `Lang/Analysis.lean` throughout (`flatten`, `atoms`, `canParSeg`, `regFootprint`) rather than
replacing it.

```text
  paralever { … }  ──►  ParProg  ──►  units  ──►  plan  ──►  ParProg  ──►  paralever { … }
                        (tree)      (segments)  (stages ×    (tree)        (surface)
                                                 threads)
                          │                                    │
                          └──────────── rewrite_sound ─────────┘
```

Entry point: `rewrite : ParProg → ParProg`. Round trip: `surface`, `report`.

## The theorem

```lean
theorem rewrite_sound (p : ParProg) (ρ : Regs) (σ : State) :
    (runSeq (execPar (rewrite p) ρ) σ).2 = (runSeq (execSeq p ρ) σ).2
```

No hypothesis. The rewritten program, read in parallel, leaves exactly the heap the original leaves
read sequentially — for every program. That is possible because `rewrite` *checks* its own plan
(`rewriteOk`) and returns `p` unchanged when the check fails: the analysis is untrusted and the gate
is proved, the architecture of `Search/RaceSearch.lean`.

Heap, not the pair: `execPar` at a `par` node hands the continuation the pre-fork register file
(`Lang/Core.lean`), so there is nothing to say about registers after a fork.

One schedule or all of them: `rewrite_sound` is about `runSeq`. `rewrite_wf` carries `wfB` through
the rewrite, which feeds `par_seq_eq`, so `rewrite_parSeqEq` gives every schedule.

## Units

The scheduling unit is a **register-closed segment** (`atoms`, `Lang/Analysis.lean`), not a
statement. A load and the store that consumes its register are one unit and are never split across a
fork, because a register written on one side of a fork boundary and read on the other reads a stale
value — not a race, so `wfB` cannot see it. `docs/autopar.md` has that counterexample.

```lean
def units (p : ParProg) : List ParProg := (atoms (flatten p)).map block
```

## The shape of a plan

A `Plan` is a **two-level consecutive partition**: units group into threads, threads group into
stages, and nothing moves past anything.

```text
  units    u₁  u₂  u₃  u₄  u₅  u₆
           └──┬──┘  └┬┘  └──┬──┘
  threads    t₁      t₂     t₃
             └───┬───┘      │
  stages      stage₁      stage₂

  emit  =  par[t₁, t₂] ; par[t₃]
```

Order preservation is the load-bearing restriction. It makes `planUnits (plan us) = us` a
*structural* theorem (`plan_units`) rather than a run-time check, and it means the proof needs only
`par_block_heap`. A scheduler that reordered units would need a commutation theorem — independent
statements may be transposed — and that is not proved here.

What it costs: some schedules are unreachable. On the N (`Test/AutoParAlgo.lean`) the best
fork–join depth is 8 while the dependence DAG's critical path is 7, and the 7-tree is *racy*, so
nothing is lost there. Whether order preservation itself ever costs anything is open.

## The pass

One left-to-right fold. For each unit, the three ways a dependence can fall are the three cases:

```text
  does it conflict with an earlier thread of this stage?
      yes  ──►  close the stage          (only a join can order them)
      no   ──►  does it conflict with the thread being built?
                    yes  ──►  extend that thread
                    no   ──►  open a new thread beside it
```

Worked, on two independent chains written interleaved (`[0]:=1; %0:=[0]; [1]:=R0; [2]:=3; …`):

```text
  u₁          new thread            cur=[u₁]
  u₂  conflicts with cur            cur=[u₁,u₂]
  u₃  independent of everything     stage=[[u₁,u₂]]  cur=[u₃]
  u₄  conflicts with cur            cur=[u₃,u₄]
  ──► parallel { u₁; u₂ } | { u₃; u₄ }        depth 3, sequential 6, bound 3
```

Greedy prefix grouping gets 5 here, because one conflicting unit ends its group even when
everything after it is free.

## The bound

`Dag.lean` builds the dependence DAG in one scoreboard pass — Bernstein's three clauses *are* the
three kinds of edge — and `critical` is its longest path.

```text
  for each unit i:
      reads  l :  edge lastWriter[l] → i          RAW   W∩R
      writes l :  edge lastWriter[l] → i          WAW   W∩W
                  edge r → i  for r ∈ readers[l]  WAR   R∩W
      then update lastWriter and readers
```

`critical` is a lower bound on the depth of *any* schedule of those units, so `optimalB` —
`depth (rewrite p) == critical (units p)` — is a certificate, not an estimate. When it is `false`
the difference is the price of the fork–join shape, which may or may not be payable; the N is a case
where it is not.

Cost is `depth`, counted off the syntax (`+` at a `seq`, `foldr max` at a `par`, memory operations
only). `Lib/Cost.lean`'s `time` is the real model but needs a heap and is quadratic in `work` to
evaluate, which a scheduling heuristic cannot afford.

## How the proof goes

```text
1.  execPar and execSeq agree under runSeq                      execPar_runSeq_all
2.  execSeq of a `par` restores the register file, so EVERY
    thread of the whole plan runs at the initial registers       stages_seqAll
3.  threads in order, each at the initial ρ,  =  the chain,
    when no register flows between them                          fork_heap
4.  a chain of blocks runs like the flat chain                   runSeq_block_map
5.  the plan's units are the program's statements                plan_units
                                                                 atoms_flatten
                                                                 runSeq_flatten
```

Step 2 is the whole idea: because a fork restores `ρ`, a *chain* of forks never advances it, so the
top-level plan is in exactly the position `fork_heap` was written for — one level up from a single
`par`. Steps 4 and 5 are the bookkeeping that `docs/autopar.md` recorded as open.

## What the gate still refuses

`rewriteOk` requires `noRegFlow` on **raw** register read sets: no thread may read a register an
earlier thread writes. That is stronger than the liveness `atoms` actually establishes — a segment
that writes `%0` and then reads it has `%0` in its raw read set even though the value is local. So a
chain that reuses `%0` across segments is declined and returned sequential:

```text
  [10] := 1; [11] := 2; %0 := [10]; [12] := R 0; %0 := [11]; [13] := R 0
  ──► returned unchanged                      rewriteOk = false
```

Sound, and the parallelism is lost. Two ways out, in order of value:

- **Make registers survive the join.** `execPar`'s `par` case discards the children's register
  files; merging them instead (guarded by register-Bernstein among siblings) removes the constraint
  at the source, and registers can be renamed per thread at emission where memory cells cannot —
  a `Loc` is reached by a computed address, so the cell *is* the name. `docs/autopar.md` § the
  register bug has the argument.
- **Weaken `noRegFlow` to liveness.** `agree_run_all` would have to be restated over a statement
  *list* with `liveIn` in place of the raw read set.

Also refused, by construction rather than by the gate: anything the footprint over-approximates.
`A[B[i]]` reports the whole array, so scatters serialise; `whileAtMost` is nested `ifElse` whose
footprint is the branch union, so iterations look dependent. Conservative, never unsound.
