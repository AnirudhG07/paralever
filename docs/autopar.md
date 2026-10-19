# `autoPar`: proposing a parallelisation, and why registers decide its shape

`Lang/Analysis.lean` turns a sequential `ParProg` into a forked one. The analysis is **untrusted** —
it proposes, `wfB` checks — which is `Search/RaceSearch.lean`'s architecture. This note records the
one thing `wfB` cannot check, and the theorem that covers it.

**This file is about registers**: why they, and not memory, decide the shape of any rewrite. The
pass built on that conclusion, and the proof that its rewrite preserves the heap for every program,
are in [`autopar-algorithm.md`](./autopar-algorithm.md). The two routes coexist; see
[The two routes](#the-two-routes) below for what each one buys.

## The gap `wfB` does not close

`wfB` rules out memory races. The way a rewrite goes wrong here is not a race.

```text
execPar (.par ss) ρ  =  bind (parAll (execParAll ss ρ)) (fun _ => pure ρ)
                                                                    ^^^
```

A `par` node hands every thread a copy of the *pre-fork* register file and the continuation gets
that same file back. Register writes do not survive a join — in **both** readings, so the parallel
and sequential readings agree and `wfB` sees nothing wrong. What changes is the answer.

```text
%0 := [10];  %1 := [11];  [12] := R 0 + R 1
```

Split the two loads into one stage and the store into the next, and the store reads the pre-fork
`%0` and `%1`. The program that computed `3` computes `0`, and `wfB` returns `true`.

## The unit of scheduling is a segment, not a statement

A boundary may be placed only where no register is **live** across it. The three ingredients, each
forced by a program that breaks without it:

| | why |
|---|---|
| `regFootprint` | a statement's register reads and writes, the analogue of `footprintOf` |
| `regKills` | the registers a statement *certainly* writes |
| `liveIn` | backward liveness: `reads(s) ++ (liveIn rest \ regKills s)` |

`cutOK pre post` is then `disjointB (regFootprintsOf pre).writes (liveIn post)`, and `atoms` cuts the
chain wherever that holds. The resulting segments, not the statements, are what `groups` schedules.

**Why liveness and not just the read set.** A reused register — `%0 := [i]; A[i] := R 0`, repeated —
is written before every use, so it is never live across a boundary. Killing is what lets the three
copies fork; without it `%0` appears live from the first statement to the last and no boundary is
ever legal.

**Why `regKills` and not `regFootprint`'s writes.** `regFootprint (.ifElse c t e)` has the *union* of
the branches' writes, because either may run. Liveness must kill on what *must* be written:

```text
%0 := 5;  if (R 1) { %0 := 1 } else { [7] := 9 };  [8] := R 0
```

Only the `then` branch assigns `%0`. Killing on the may-write set declares `%0` dead after the
conditional, offers a boundary after the first statement, and `[8]` reads `0` instead of `5`.
`regKills (.ifElse _ t e)` is the intersection, and no boundary is offered.

`regKills (.par _) = []`: a fork writes no register the parent can see, so it kills nothing.

## What registers do *not* constrain

`canParSeg`, the test for "may these two segments be siblings", is memory-Bernstein alone. Threads
get a private file, so two siblings may clobber the same register freely — and reused `%0` means
they routinely do. The register condition is a property of the **boundary**, not of a pair, and
`atoms` has already enforced it. (`canPar`, which keeps the register clause, remains the conservative
pairwise notion `dependences` reports with.)

## The theorem

`Lang/AutoParSound.lean`, built in three steps.

1. `regs_frame` — a statement changes only the registers in its register write set.
2. `agree_run_all` — if two files agree on a set `R` covering what the statement reads, it leaves
   the same heap under both and the files still agree on `R`. Stated with `R` as a parameter, not
   with the statement's own read set, because a conditional's write set names registers only one
   branch assigns: "the files agree on the writes" is false for `ifElse`.
3. `fork_heap` / **`par_block_heap`** — a `par` node and the `;`-chain it replaces leave the same
   heap, when no register flows between the segments.

```text
par_block_heap :  noRegFlow g = true →
  (runSeq (execPar (.par g) ρ) σ).2 = (runSeq (execSeq (block g) ρ) σ).2
```

The heap, not the pair: the register file after a fork is the pre-fork one by construction, so the
*output* is what the two readings share. Composed with `par_seq_eq` at `autoPar p`, this says the
proposal computes the original's heap under every schedule.

**Still open.** `par_block_heap`'s hypothesis `noRegFlow` is stated on raw read sets, so it is
stronger than what `atoms` establishes — `atoms` uses `liveIn`, which is strictly more permissive
(the `reuse` program above satisfies the liveness condition and fails `noRegFlow`). Lifting the
theorem to `autoPar p` end to end needs `agree_run_all` restated over a statement *list* with
liveness rather than read sets, and the bookkeeping that `(atoms ss).flatten = ss` and that `groups`
preserves order. Until then the end-to-end claim is checked per program by the `#guard`s in
`Test/AutoPar.lean`, not proved.

## Fork–join is series-parallel

Dependence DAGs are not. The smallest obstruction is the **N**: `i1 → i3`, `i2 → i3`, `i2 → i4`,
with `i1` and `i4` unrelated. No fork–join term starts `i4` before `i1` finishes, because `i4` is
either parallel to `i1` — and then cannot wait for `i2` — or after it. Measured, with `i1` and `i4`
long (`Test/AutoPar.lean`'s shape, scaled):

| shape | span |
|---|---|
| sequential | 17 |
| `par[i1,i2]; par[i3,i4]` — what `autoPar` emits | 13 |
| `par[i1, (i2;i4)]; i3` | 11 |
| `i2; par[i4, (i1;i3)]` | **10** |
| the DAG's critical path | **9** |

So nesting is worth 13 → 10, and 10 > 9 is irreducible. Recognising series-parallel digraphs is
linear time (Valdes, Tarjan & Lawler, STOC'79; SIAM J. Comput. 11:298–313, 1982); no SP-ization
algorithm is known that bounds the critical-path increase by a constant factor.

`autoPar` emits the stage-wise shape — the 13 — because `groups` partitions into barriers. Emitting
the nested shape is the open engineering problem, and the N is also why no *online* algorithm can be
optimal: a scheduler that forks `i1 ∥ i2` and joins for `i3` has killed `i2`'s thread before `i4`
arrives.

## The two routes

Both survive, because neither dominates. `autoPar` here proposes and `wfB` is `decide`d on the
result, per program. `AutoPar.rewrite` builds on this file's `flatten`, `atoms`, `canParSeg` and
`regFootprint`, and carries `rewrite_sound` for *every* program — at the cost of a stricter gate.

Measured on `Test/AutoPar.lean`'s three programs (`depth` is the syntactic span of `Dag.lean`):

| program | `autoPar` | `AutoPar.rewrite` | why they differ |
|---|---|---|---|
| the **N** | forks, depth 4 | forks, depth 4 = the DAG's bound | agree; only `rewrite` certifies it |
| reused `%0` | forks, depth 2 | **declines**, depth 6 | `noRegFlow` is on raw read sets; `atoms` had already killed `%0` by liveness |
| conditional kill | no fork, depth 2 | one-thread fork, depth 2 | `emit` builds a `par` per stage unconditionally; `autoPar` collapses a singleton group |

Two things to read off it.

**The gate costs real parallelism.** On the reused-`%0` chain the plan the pass computed is 1 stage
of 3 threads at depth 2 — equal to the DAG's lower bound — and `rewriteOk` throws it away for a
sequential depth of 6. `noRegFlow` asks that no register written by one thread is read by a later
one, which is strictly stronger than the liveness `atoms` establishes at each boundary. Weakening it
means restating `agree_run_all` over a statement list with `liveIn`; removing it means merging the
children's register files at the join (`Lang/Core.lean`'s `par` case) under Bernstein on registers,
with per-thread renaming at emission. Registers admit renaming and memory cells do not — a `Loc` is
reached by a computed address, so the cell *is* its name.

**`emit` always emits a fork.** `emit pl = block (pl.map fun st => .par (st.map block))` has no
singleton case, so a program with nothing to parallelise comes back wrapped in a one-thread
`parallel { … }`. Harmless — same depth, same heap, `wfB` true, `rewrite_sound` unaffected — but it
is visible in `surface`, and changing it would mean reproving `stages_seqAll` and `emit_heap` around
a two-case `emit`. Recorded, not fixed.

`Test/AutoPar.lean` § *The two routes, side by side* pins every number above. Those gates are
expected to **fail** when the gate is weakened; that failure is the notification.
