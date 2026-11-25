# Running under a random schedule

`paralever run FILE` executes one order: every fork's children left to right, which is `runSeq`, the
canonical run. That order is one member of `step`'s successor set, and a reader watching it has no
way to see that the set has other members. `--run-again N` (`-ra N`) runs the program `N` times
choosing a successor at random each step, and groups the runs by the outcome they left.

```text
$ paralever run Examples/Language/matmul.prl -ra 10
10 runs under random schedules, 1 distinct outcome — every schedule agreed.

$ paralever run Examples/Language/race.prl -ra 10
10 runs under random schedules, 3 distinct outcomes — the schedule decides what this program computes.
```

The first line is the point of the flag. `par_seq_eq` says a well-formed program reaches exactly one
outcome under every schedule; the first report is that theorem being watched instead of read, and the
second is what the hypothesis excludes.

## Why the walk is trustworthy

The random choice is untrusted. What makes its answer a fact about the program is that the walk
records the `Schedule` it took, and `Search/RaceSearch.lean`'s `follow_sound` turns a schedule into a
`Reaches` proof:

```text
walk fuel seed c  ──►  (schedule, c')
                            │
      walk_follow:  follow c schedule = some c'
                            │
      follow_sound: Reaches c c'
```

`walk_reaches` (`Search/Interleave.lean`) is that composition. So every outcome the report lists is
an outcome of the semantics the theorems are about, not of a second executor written for the tool.
This is the same discipline as the race search: the search may return anything, and what it returns
is checked.

## The generator

Knuth's MMIX linear congruential generator, seeded by the run index. The low bits of an LCG are
poor, so `pick` takes the index from the high half, and `seedOf` passes the run index through two
rounds before the first choice so that consecutive seeds do not start the same way.

It is a seeded generator rather than `IO.rand` because a surprising outcome has to be reproducible:
the report names the seed of every run in a group, and re-running with that seed replays the
interleaving exactly. The same seed also gives the same answer on another machine, so a gate in
`Test/Tool.lean` can assert what twenty interleavings of `race.prl` find.

## What the report says

One group per distinct outcome, in the order the outcomes first appeared, each with the seeds that
produced it.

```text
outcome 1 — 2 runs (seeds 0 7)
x [1] @0  [7]

outcome 2 — 6 runs (seeds 1 3 4 6 8 9): wrong — this schedule caught a race

outcome 3 — 2 runs (seeds 2 5)
x [1] @0  [9]
```

Two runs count as the same outcome when they agree on **every cell of the arena and every register
the file names** — `Layout.bot` to `Layout.top`, and `Compiled.regs`. `ParSeqEq` quantifies over the
pair `(result, final heap)`, so comparing the heap alone would miss a program whose registers
disagree. `--buffer NAME` narrows what is *printed* and never what outcomes are compared on, so
`-ra 20 -b C` cannot report agreement that the rest of the heap does not have.

`wrong` is an outcome like any other: a schedule that reached it found a race, and it is listed with
its seeds rather than silently dropped.

## Limits

- **`--real-threads` does not combine with it.** A `Task` is scheduled by the Lean runtime, and
  `runTask_eq` makes its answer the canonical one, so there is no interleaving left for the tool to
  choose. The invocation is refused rather than ignored.
- **`print` output is left out.** A print belongs to a run and this report is about several.
- **A sample is not a proof.** Twenty agreeing runs are evidence; `check` decides, and `prove`
  proves. The flag exhibits the theorem, it does not establish it.
- **The step budget** is `2 * stepBound + 1024`. A run under an arbitrary schedule takes `stepBound`
  steps when control flow does not depend on a raced cell and may take more when it does, so the
  bound is doubled and padded. A run that exhausts it is reported as *still running when the step
  budget ran out* rather than counted as an outcome.
- **Cost** is one small-step interpretation per run, against `runSeq`'s one fold. Three runs of
  `Examples/Scale/matmul12.prl` take about 0.6 s, so the flag is usable on the corpus but it is not
  the way to execute a program.
