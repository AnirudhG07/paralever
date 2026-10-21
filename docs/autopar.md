# `autoPar`: proposing a parallelisation, and why registers decide its shape

`Lang/Core/Analysis.lean` turns a sequential `ParProg` into a forked one. The analysis is **untrusted** —
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
%0 := [10];  %1 := [11];  [12] := %0 + %1
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

**Why liveness and not just the read set.** A reused register — `%0 := [i]; A[i] := %0`, repeated —
is written before every use, so it is never live across a boundary. Killing is what lets the three
copies fork; without it `%0` appears live from the first statement to the last and no boundary is
ever legal.

**Why `regKills` and not `regFootprint`'s writes.** `regFootprint (.ifElse c t e)` has the *union* of
the branches' writes, because either may run. Liveness must kill on what *must* be written:

```text
%0 := 5;  if (%1) { %0 := 1 } else { [7] := 9 };  [8] := %0
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

`Lang/Core/AutoParSound.lean`, built in three steps.

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

## Synchronization

A `synchronize` is a statement that ends a phase. Nothing before it and nothing after it is grouped
into one fork, whatever the dependence analysis thinks. The word is `synchronize` rather than `fence`
because a fence in common usage is a memory-ordering instruction (`mfence`, `atomic_thread_fence`),
and this is not one: the program has no relaxed memory to order.

The construct exists because Bernstein is a question about memory, and a programmer's reason for
ordering two phases need not be one. `Examples/Language/phases.prl` is the minimal case:

```text
buf A[4] = arange     phase 1: writes B, reads A
buf B[4]              phase 2: writes C, reads A
buf C[4]
                              w₁ ∩ w₂ = B ∩ C = ∅
for i in 4 {                  w₁ ∩ r₂ = B ∩ A = ∅
  %0 := A[i]                  w₂ ∩ r₁ = C ∩ A = ∅
  B[i] := %0 * %0
}                     so Bernstein accepts one fork of eight,
                      and without the barrier that is what `autoPar` emits
synchronize

for i in 4 {
  %1 := A[i]
  C[i] := %1 + 1
}
```

With the barrier, `autoPar` emits two forks of four and keeps the barrier between them; without it,
one fork of eight. `Test/Lang.lean` § *Synchronization* pins both numbers, so the construct is
demonstrably load-bearing rather than decorative.

### What it means, and what it does not

At run time a `synchronize` is a no-op: `execPar .synchronize ρ = .pure ρ`, its footprint is
`Footprint.empty`, and `wfB .synchronize = true`. It has to be — `par` is a structured fork–join, so
by the time the next statement runs there is nothing left to wait for. The whole content of the
statement is the constraint it puts on the parallelizer.

This is the host-side barrier, not `__syncthreads()`. In CUDA's terms it is the
`cudaDeviceSynchronize()` between two kernel launches, which is why `Lang.Compile.Lower` **refuses**
one inside a `parallel` thread:

```text
'synchronize' cannot appear inside a 'parallel' thread: it separates phases of a sequential
chain, and threads of one fork have no barrier between them
```

A barrier between siblings of one fork would need a synchronisation node in `ParM`, and `ParM` has
none — racy programs land in `wrong` by design rather than being ordered by a barrier. A
`synchronize` in a `for`, `if` or `while` body *is* accepted: those bodies are spliced into the chain
that encloses them, so their barriers end phases of that chain. `Lower.Site` is the three-way
distinction — `.file`, `.block`, `.thread` — and `ParProg.noSynchronizeInThread` is the same property
read off a finished program.

### The mechanism

`ParProg.phases` splits a flattened chain at every barrier and `ParProg.joinPhases` puts it back:

```text
flatten p   = [s₀ s₁ synchronize s₂ s₃ synchronize s₄]
phases      = [[s₀ s₁], [s₂ s₃], [s₄]]
planPhase   ↓          ↓         ↓
              par[…]     par[…]    s₄
joinPhases  = [par[…] synchronize par[…] synchronize s₄]
```

`ParProg.joinPhases_phases` proves `joinPhases (phases us) = us` for every chain, so the
decomposition loses nothing — which is why the barriers in the autoparallelized output are exactly
the ones that were written, and the printed result reads back as itself (`Test/Lang.lean`).

`canPar` and `canParSeg` also answer `false` for a barrier before they look at a footprint. They have
to: its footprints are empty, so Bernstein alone would group it with anything. That is what makes
`dependences` report a barrier as forcing order against every statement, and it is the one place the
construct shows up in the analysis besides `phases`.

### The proved route declines

`AutoPar.rewriteOk` requires `synchronizeFree p`, so `AutoPar.rewrite` returns a program with a
barrier unchanged and `parReport` falls back to `ParProg.autoPar` for it. Two reasons, both recorded
rather than fixed:

1. `emit pl = block (pl.map fun st => .par (st.map block))` wraps every stage in a `par`, so a
   barrier reaching the plan ends up inside a thread — a program `Lower` would then reject on
   re-read, which breaks the round trip the rewrite is supposed to preserve. This is the same missing
   singleton case as § *The two routes*.
2. The rewritten program leaves the register file untouched (`execPar (.par ss) ρ` restores `ρ` at
   the join) while the original chain does not, so composing the per-phase results needs the
   registers to agree at every barrier — a liveness side condition on the cut, in the shape of
   `cutOK`, that `rewrite_sound` does not currently state.

So the split is the usual one: the greedy route accepts the barrier and `wfB` checks the result per
program; the proved route refuses it and keeps `rewrite_sound` hypothesis-free.

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
children's register files at the join (`Lang/Core/Prog.lean`'s `par` case) under Bernstein on registers,
with per-thread renaming at emission. Registers admit renaming and memory cells do not — a `Loc` is
reached by a computed address, so the cell *is* its name.

**`emit` always emits a fork.** `emit pl = block (pl.map fun st => .par (st.map block))` has no
singleton case, so a program with nothing to parallelise comes back wrapped in a one-thread
`parallel { … }`. Harmless — same depth, same heap, `wfB` true, `rewrite_sound` unaffected — but it
is visible in `surface`, and changing it would mean reproving `stages_seqAll` and `emit_heap` around
a two-case `emit`. Recorded, not fixed.

`Test/AutoPar.lean` § *The two routes, side by side* pins every number above. Those gates are
expected to **fail** when the gate is weakened; that failure is the notification.
