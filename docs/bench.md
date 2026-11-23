# The evaluation: corpora, reachability, and what the harness is allowed to measure

Rationale for the `Bench/` library and the `paralever-bench` executable. Code references this file as
`docs/bench.md`.

## What the evaluation was before this

Worth stating plainly, because it is the baseline every number here has to beat.

| | |
|---|---|
| labelled corpus | **7** hand-written MLIR pilots (`MLIR/Corpus.lean:37`), plus 2 custom-form twins |
| confusion matrix | `#guard confusion == (3, 0, 0, 4)` (`MLIR/Corpus.lean:96`) |
| scored against | `verdictExact`, the per-heap check — **not** `wfB` (`MLIR/Corpus.lean:83`) |
| precision gap | `#guard gap == []` (`MLIR/Corpus.lean:113`) |
| a second labelled corpus | `Test/Lang.lean:13` — 15 `.prl` files, one Boolean each, no matrix |
| end to end on real MLIR | 20 functions of LLVM's own `parallelize.mlir` → 11 read → **2 reach a verdict** (`docs/mlir-pretty.md:132`) |
| wall-clock harness | **none.** No `IO.monoMsNow` anywhere; every number in `docs/scale.md` is prose from `/usr/bin/time`, with no committed script |
| speedup | **1.66×** forked against unforked on an array heap, after the fork was found to be running on one thread (`docs/scale.md` § `--threads`); the earlier 13.15× was chain-shortening, not cores |
| SMT contribution | unquantified; `docs/smt-vc.md:138` is a two-row table on one program |

`gap == []` is the sharpest statement of the problem. The precision gap between "independent at
every heap" and "independent at this one" is what the project's own documentation is organised
around, and at seven pilots it is *invisible*, because the single pilot that would exercise it
(`indirect-yes`) happens to be genuinely racy. Seven is too few to measure anything.

## The corpora, and how much of each is reachable

Counted by reading the suites, before porting anything. A corpus whose size is discovered during
the work cannot be reported honestly.

### PolyBench/C 4.2.1 — 30 kernels

Thirty kernels across four categories (`Nussinov.orig.c` is a variant of `nussinov.c`, not a
thirty-first kernel). Every subscript is affine in the loop indices: that is what the suite is
*for*, so reachability is not the question here and loop depth is. Kernels carry 5 to 21 `for`
statements each, in nests two and three deep, at standard sizes of 1000 to 4000 per dimension —
which is the measurement that makes `docs/loops.md` a prerequisite rather than a nicety.

The split that matters is by dependence structure, and it is a prediction to be checked, not a
result:

| expected | kernels |
|---|---|
| **proved** — disjoint writes, shared reads | `gemm`, `2mm`, `3mm`, `gesummv`, `syrk`, `syr2k`, `symm`, `trmm`, `bicg`, `atax`, `mvt`, `doitgen`, `covariance`, `correlation` |
| **refused, soundly** — loop-carried | `jacobi-1d`, `jacobi-2d`, `seidel-2d`, `fdtd-2d`, `heat-3d`, `adi`, `lu`, `ludcmp`, `cholesky`, `durbin`, `trisolv`, `gramschmidt`, `floyd-warshall`, `nussinov`, `deriche` |

A kernel landing in neither column is the interesting case and gets its own row in the report.

### DataRaceBench — 76 of 204 reachable

The suite purpose-built for this matrix, and the source of the `-yes`/`-no` filename convention
`MLIR/Corpus.lean:6` already uses. Measured over the 204 C micro-benchmarks:

| | count | labels |
|---|---|---|
| total | 204 | 102 racy / 102 race-free |
| use an `omp (parallel) for` | 108 | |
| **reachable now** — no construct `ParM` lacks | **76** | **-yes 47 / -no 29** |
| …of those, carrying only a clause we may ignore (`num_threads`, `schedule`) | 12 | |
| a pattern we model differently (`reduction`, `collapse`) | 6 | -yes 2 / -no 4 |
| out of scope by construction — locks, atomics, `critical`, `ordered`, tasking, `sections`, `barrier`, `simd`, `target` | 122 | |

Two things follow, and both go in the report rather than being quietly absorbed.

**The 122 belong outside the denominator, with their count stated.** `ParM` has no lock, no atomic
and no task constructor, so a `-no` case whose race-freedom comes from a lock will read as racy.
That is not a false positive; it is a program the model does not describe. `docs/mlir.md:463` fixed
this methodology before the suite was ever cloned, and it is kept.

**The reachable subset is label-skewed, 47 racy to 29 race-free.** The full suite is balanced 102 to
102; the subset is not. A tool that refused every program would therefore score 47/76 — 62 % — on
the reachable subset and look respectable. So accuracy on this subset is not a headline number, and
the report gives the two columns separately: of the 47 racy, how many are caught; of the 29
race-free, how many are proved. Those are the numbers that cannot be gamed by refusing everything.

### NAS and Rodinia — a boundary, not a coverage figure

Rodinia is CUDA and NAS is Fortran or C with OpenMP. Neither has a path into either front end today.
These are reported as a reachability census with a reason per kernel, and as an out-of-scope count —
never as a coverage percentage.

## The six-cell verdict taxonomy

The harness classifies each kernel into one cell, against a *declared* label. Without a declared
label there is no matrix, only a list of outputs.

| cell | meaning | what it is for |
|---|---|---|
| **proved** | label race-free, the check accepts | maximise |
| **sound refusal** | label racy, a race is reported | maximise |
| **false refusal** | label race-free, refused anyway | reportable, attributed by cause |
| **false acceptance** | label racy, accepted | **fails the build** |
| **inconclusive** | `wfB` refuses, the bounded probe finds nothing in ≤ 512 heaps | the SMT route's target |
| **over the ceiling** | representable, but `decide` or `run` does not finish | what `docs/loops.md` drives to zero |
| **unreachable** | the front end cannot read it, or the construct is out of scope | reported with a reason each |

A false refusal is imprecision: it is a number to report and improve. A false acceptance is a
soundness bug in the hypothesis check, so a non-zero cell there fails the build rather than
appearing in a table. `MLIR/Corpus.lean:17` argues the false-negative cell is structurally empty via
`raceSites_nil_iff`; that argument has to survive the larger corpus or be corrected here.

### Both matrices, and the gap between them

Every kernel is scored **twice**: once against `wfB`, which answers for every heap, and once against
`verdictExact`, which answers for the heap the file declares. `MLIR/Corpus.lean` scores only the
second, which is why its `gap` is empty. The gap between the two columns is the precision result,
and it is the quantity both the nest certificate and the SMT route exist to shrink.

### Why a false refusal is attributed, not just counted

There are exactly **three** widening clauses in the footprint, and they reduce to **two** causes: a
computed address contributes every cell of its buffer (`.loadAt`, `.storeAt`), and a branch
contributes both arms (`.ifElse`) — `Lang/Core/Prog.lean:191`, with `ParProg.widenedBy` returning
exactly those two strings. So the attribution is determined by the implementation rather than
guessed, and every false refusal lands in one of five classes:

1. a computed address — `Examples/Language/scatter.prl`'s shape;
2. a branch — `Examples/Language/branch.prl`'s shape, and the `Inconclusive` witness;
3. genuinely racy — not a refusal to fix;
4. over the unrolling or `decide` ceiling — `docs/loops.md`'s target;
5. unreachable — the front end, or a construct out of scope.

## The harness measures the project's own code

The rule, and the reason the harness is small: **every number comes from a function that already
exists and is already gated.** `Bench/` orchestrates and reports; it re-implements nothing.

| what | reused from |
|---|---|
| reading either front end | `Tool/Run.lean:153` `loadAny` |
| the two-part verdict | `Lang/Verdict.lean` `verdictParts`, over `ParProg.verdictHere` / `verdictAnywhere` |
| the hypothesis, both ways | `ParProg.wfB`; `wellFormedB`; `sideSound` |
| why a refusal happened | `ParProg.widenedBy`, `refusedAt`, `probeCells`, `probeBudget` |
| a claim's outcome | `Lang/Verdict.lean` `claimHolds`, `claimParts` |
| MLIR rows | `MLIR/Lower.lean:620` `Lowered` — `.verdict`, `.verdictExact`, `.sites`, `.footprintIsExact`, `.exactValues`, `.agrees`, plus `unsupportedOps` and `roundTrips` |
| real-thread runs | `Lang/Core/Exec.lean` `runTask` / `runTaskSeq` |

`Bench/Matrix.lean` therefore *generalises* `MLIR/Corpus.lean`'s `detected`, `confusion`, `gap` and
`approximated` over an arbitrary corpus, and that module's existing gates then call the generic
version. Their pinned values — `(3, 0, 0, 4)`, `[]`, `["indirect-yes"]` — must come out byte
identical, which is the test that generalising changed no meaning. Two scoring functions that could
disagree is the failure this avoids.

## The command line

```
paralever-bench                     the corpus — both front ends — one job per core
paralever-bench --jobs 1            serial: the mode to quote a timing from
paralever-bench --prl | --mlir      one front end's entries only
paralever-bench --csv out.csv       a row per kernel, and out.csv.scale.csv for the curve
paralever-bench --markdown          the verdict table this file quotes
paralever-bench --scale             also the rolled-against-unrolled curve
paralever-bench --prove             the curve, with each proof written and elaborated
paralever-bench --ceiling-ms N      stop a curve after a row taking N ms (default 8000)
paralever-bench --max-unrolled N    never start an unrolled program over N points (default 65536)
paralever-bench FILE...             those files instead; a `-yes`/`-no` name carries its own label

paralever-bench chaos-depth         the crossover: `chaos.prl` swept over `d`, three ways
  --exec-threads N                    the matrix dimension `n` (`m` is `4n`)
  --exec-sizes a,b,c                  the values of `d`
  --exec-ceiling-ms N                 the grain gate; 0 is off
paralever-bench chaos               the same file swept over `n` instead, at a fixed `d`
paralever-bench chaos-regions       one run per kind of marked region, at one parameter
```

Exit code 1 when a row is a false acceptance, so the harness can gate a build; a false refusal is
imprecision and exits 0 with the number reported.

## The run

`paralever-bench --jobs 1`, over the nineteen `.prl` examples relabelled semantically and the nine
MLIR pilots (`Bench/Manifest.lean`). Reproduce with that command; the verdict columns are identical
at `--jobs 8`, which is the order-independence check for the fan-out.

```text
soundness      OK — no false acceptance
kernels        28
any heap       tp=7 fp=0 fn=0 tn=20 skipped=1
this heap      tp=5 fp=0 fn=0 tn=23
sensitivity    7/7 of the racy caught
specificity    20/20 of the race-free proved
precision gap  [scatter, stripe]
inconclusive   [(branch, 11)]
false refusals []
total measured 7 ms
```

| | `.prl` | MLIR | together |
|---|---|---|---|
| kernels | 19 | 9 | **28** |
| labelled racy | 3 | 4 | 7 |
| proved at every heap | 15 | 5 | 20 |
| sound refusals | 3 | 4 | 7 |
| false acceptances | 0 | 0 | **0** |
| false refusals | 0 | 0 | **0** |
| inconclusive | 1 (`branch`) | 0 | 1 |
| precision gap | 2 | 0 | 2 |

The nine MLIR pilots are scored here through `Tool.loadAny` — the path a user takes — where
`MLIR/Corpus.lean` scores them through `include_str`. Both read the same labels off the same
filenames, so the two cannot disagree about what a pilot is, and `Test/Bench.lean` gates that.

Four things to read out of it.

**The gap is non-empty, and it comes entirely from the `.prl` half.** `scatter` and `stripe` are
refused for every heap and accepted at the one their file declares — the first measured gap in the
project, where the nine MLIR pilots give an empty one. Both are attributed to the same cause, a
computed address contributing every cell of its buffer, which is `ParProg.widenedBy`'s own words.

**`branch` is inconclusive at exactly 11 probed heaps**, which is the value `Test/Heaps.lean:82`
pins independently. The harness agreeing with a gate it does not call is the evidence that it is
reading the same verdict the rest of the project reads.

**The false-refusal cell is empty, and that is a correction rather than a result.** `scatter` looked
like the obvious false refusal, and it is not one: `verdictAnywhere` *finds* a counterexample heap
for it, because two entries of `B` agreeing make two threads write one cell. So `wfB`'s refusal is
**sound** for the general question. What `scatter` exhibits is the gap, not an imprecision — and
booking it as a false refusal would have been a measurement error. This is why `Entry` carries two
labels: `racy` for "at some heap" and `racyHere` for "at the heap the file declares". Scoring the
exact check against the general label reported `fn = 2` until each matrix was given its own label.

**The corpus cannot time anything.** Every kernel checks in under a millisecond because every one is
small, and the total measured work over all 28 is 7 ms. Cost is a separate measurement, below.

## Verification cost: the same shape rolled and unrolled

`paralever-bench --prove` runs it. Two shapes at nine sizes each, in both representations, through
four stages:

| stage | what runs | whose code |
|---|---|---|
| read | parse and lower the `.prl` | `Lang.ofString` |
| verdict | the two-part verdict, as compiled code | `Lang.verdictParts` |
| write | the Lean module `paralever prove` writes | `Tool.proofFile` |
| **elaborate** | **that module, `wfB` decided by the kernel** | `lake env lean` |

The fourth stage is the one that matters and the reason the first three are not enough. `wfB` as
compiled code is a machine-word loop over footprints; `wfB` inside `by decide` is reduced by the
*kernel*, and that is the cost a `par_seq_eq` actually has. Measured on the corpus's own shapes the
first three stages are 0 ms everywhere, including at 10⁹ points — which says only that the compiled
checks are cheap, not that the proof is.

**The two representations are two texts, not one text compiled twice.** The rolled text is a
`for`/`parfor` nest; the unrolled text is the same iteration space written out, one `parallel` arm
per thread and one statement per point, which is what a user without rolling would have had to write
and what `Examples/Scale/matmul12.prl` is. A threshold inside the compiler would have been the wrong
instrument: the generated module re-reads the *file* while it elaborates, so both rows would have
measured the rolled route and both would have come back flat. That mistake was made first and caught
by the numbers being identical where they had no reason to be.

Measured on the machine `docs/scale.md` names (16 cores, Ubuntu 24.04, `--jobs 1`), elaborate times:

| shape | n | points | threads | rolled | unrolled |
|---|---|---|---|---|---|
| `elemwise` | 8 | 64 | 8 | — (below the threshold) | 1.87 s |
| `elemwise` | 12 | 144 | 12 | **0.85 s** | 6.40 s |
| `elemwise` | 20 | 400 | 20 | **0.85 s** | **49.4 s** |
| `elemwise` | 32 | 1 024 | 32 | **0.88 s** | over the ceiling |
| `elemwise` | 200 | 40 000 | 200 | **0.88 s** | over the ceiling |
| `elemwise` | 1000 | 10⁶ | 1 000 | **0.85 s** | over the ceiling |
| `gemm` | 8 | 512 | 8 | **0.89 s** | 6.15 s |
| `gemm` | 10 | 1 000 | 10 | **0.89 s** | **16.9 s** |
| `gemm` | 24 | 13 824 | 24 | **0.88 s** | over the ceiling |
| `gemm` | 100 | 10⁶ | 100 | **0.86 s** | over the ceiling |
| `gemm` | 1000 | 10⁹ | 1 000 | **0.89 s** | over the ceiling |

**The rolled curve is flat.** 0.85–0.89 s from 64 points to 10⁹, and ~0.84 s of that is `lean`
starting and importing `Lang.Report` — the proof itself is the remainder. This is the shape of a
certificate: what `decide` decides is a fixed number of subscript-map pairs, so the iteration space
does not enter the cost. `gemm` at n = 1000 is a billion points and 10⁶ threads, and it costs what
64 points cost.

**The unrolled curve is not.** 1.87 s at 64 points, 6.4 s at 144, 49.4 s at 400 — superlinear, and
past 400 points over an 8 s ceiling. At 400 points the two routes differ by **58×**, and that is the
largest size where a comparison can be made at all, which is itself the result: above it there is no
unrolled number to compare against.

Both ceilings are reported with the table and both are settable (`--ceiling-ms`, `--max-unrolled`),
because a ceiling is a property of the machine a run happened on and not of the method. They are
also not interchangeable: a time ceiling can only be tested once a row has returned, so it bounds
how many rows are attempted rather than how long one takes, and an unrolled 10⁹-point program does
not return.

The whole run — 28 kernels, 36 curve points, 24 of them elaborated by `lean` — is **98.8 s**.

### What is not measured here

The 19 s at a hundred threads recorded in `docs/mlir.md` and `Examples/Programs/MatMul.lean` is a
*different* term: a `ParM` program whose footprints `decide` computes by unfolding definitions,
rather than a `.prl` file's literal. It is not the unrolled column above and the two should not be
read as one curve. The numbers above replace it as the comparison for rolling, because they are the
same shape through the same front end at the same sizes.

## Timing lives outside the build

There is no timing primitive in the repository today, and that is deliberate: a wall clock inside
elaboration is not reproducible, and a slow machine must not fail CI. So `lake build` times nothing,
and `paralever-bench` — an executable — writes CSV and Markdown. This mirrors how every number in
`docs/scale.md` was obtained, with the difference that the script is committed this time.

**Benches run in parallel; a measurement does not.** The corpus is fanned out across cores, because
a row is an independent job: read, lower, decide, time. But the wall clock of a single kernel is
never itself measured under contention — the pool runs one kernel per core, each row records only
its own elapsed time, and the degree of parallelism in force is recorded beside it. A contended
number reported as a clean one is worse than no number.

## Stated in advance: the speedup curve is expected to be flat or negative

`--threads` is slower today: `reduce64` takes 23.93 s against 16.98 s single-threaded
(`docs/scale.md:194`). The cause is known and is in the interpreter, not the theorem — `ParM.seqAll`
grafts binds and `Regs = Reg → Int` builds closure chains, both quadratic, and `par_seq_eq`
quantifies over every `ρ` and every `σ` without inspecting either, so neither cost can weaken a
proved statement (`docs/scale.md:143`).

The deliverable is therefore that curve together with its cause, not a speedup claim. Writing this
down before the harness exists is the point: a measurement whose unfavourable outcome was predicted
in advance is evidence, and the same measurement suppressed after the fact is not.

### How it came out

Flat and negative, as predicted — and then not, once the cause was found, which was neither of the
two named above.

The harness is `paralever-bench --exec`, and the first curve it drew looked like a win: banded
matmul against the same program flattened reached 13.15× at n = 128. It was not a win. Running it
again at `LEAN_NUM_THREADS=1` gave the same numbers to within noise, and `/usr/bin/time -v` reported
99% CPU, so the whole figure was the fork shortening the interpreter's closure chains and none of it
was cores. Replacing the heap with an array (`Compile/ExecArr.lean`) removed the chains and with
them the apparent speedup: the fork then measured **0.61×**, slower than not forking at all.

The cause was in `execChilds`, and it was not the join and not `seqAll`. Spawn and wait sat in one
pass over `Childs`, so each `Task.spawn` was issued only when its own `Task.get` was about to block
and the children ran in sequence on the calling thread. Three controls separate that from every
other candidate: the same spawn-recurse-get shape over `Nat` reached 1,394% CPU, a spawned closure
carrying a 49,152-cell array reached 1,413%, and `execArr` itself inside hand-written tasks reached
1,381%. Only the match on the indexed family failed. Splitting the pass into `spawnChilds` and
`collectChilds` fixed it, with every proof in `Compile/Exec.lean` unchanged:

| C := A × B, 16 bands | before | after |
|---|---|---|
| `execTask`, function heap, n = 96 | 2,936 ms | 1,069 ms |
| `execArr`, array heap, n = 160 | 1,038 ms | 395 ms |
| fork against no fork, array heap | 0.61× | 1.66× |

So the prediction was right about the curve and wrong about its cause, and the cause it named was
the thing that stopped anyone looking further. The negative result stands as the reason the fix was
found.

## The crossover: a thousand lines of nothing in particular

The corpus above is kernels, each one a shape chosen because it has parallelism in it. That is the
favourable case, and it does not answer the question a reader asks next: on a long program that was
not written with threads in mind, does the pass win, and at what size?

`Bench/chaos.prl` is the unfavourable case. A thousand lines that do many unrelated
things in sequence — index arithmetic, a branch per cell, a four-point stencil, an odd-even sorting
network, serial folds that carry a dependence and so have nothing to find, and a few matrix
multiplies in the middle. Nothing in it is parallel. Its three `const` lines are its parameters, and
`Bench/Chaos.lean` rewrites only those three, so the program's *shape* is fixed across the sweep —
the same statements, the same stages, the same buffers — and only the work behind each line changes.
`d` is the contraction length of the matrix multiplies, which is what carries most of the work.

Three runs are compared: the file as written; `autoPar` over every statement in it; and `autoPar`
inside the `{ … } :: "name"` regions the file marks and nowhere else (`docs/autopar.md` §
*Regions*). All three leave the same heap, which every row checks by checksum against the proved
full-scan join, and `wfB` accepts both proposals at every point.

| `d` | instructions | as written | autopar, markers off | regions only |
|---|---|---|---|---|
| 32 | 63,234 | 3 ms | 19 ms — 0.15× | 5 ms — 0.60× |
| 64 | 100,098 | 5 ms | 20 ms — 0.25× | 6 ms — 0.83× |
| 128 | 173,826 | 9 ms | 22 ms — 0.40× | 8 ms — **1.12×** |
| 256 | 321,282 | 19 ms | 26 ms — 0.73× | 12 ms — 1.58× |
| 512 | 616,194 | 36 ms | 36 ms — **1.00×** | 21 ms — 1.71× |
| 1024 | 1,206,018 | 68 ms | 55 ms — 1.23× | 40 ms — 1.70× |
| 2048 | 2,385,666 | 142 ms | 91 ms — 1.56× | 73 ms — 1.94× |

`n = 8`, `m = 32`, sixteen cores, five runs per point with the median kept; planning is a compile
time cost and is in neither run.

Both curves cross, and the crossing is where the work behind a fork overtakes the cost of making
one. Forking everything puts 2,072 children in the program, most of them over the glue, where a
thread does a handful of operations and the spawn costs more than the work; it needs `d = 512`
before it breaks even. Forking only inside the marked regions puts 280 children in, each with
`2,072 / 280` times as much to do, and it breaks even at `d = 128` — four times earlier — and stays
ahead at every size after. At the top of the sweep the marked-region plan is 1.94× against 1.56×
for the same program with the markers ignored, from a seventh as many threads.

That is the whole argument for naming a region: the parallelism in a long program is concentrated,
and a pass that forks everywhere spends most of its forks where there was nothing to gain.

### Which regions pay

`chaos.prl` marks three kinds of region, and the file does not say which of them is worth a fork.
`paralever-bench chaos-regions` runs one configuration per kind, forking inside that kind and
nowhere else — same file, same parameter, same heap at the end:

| forked inside | regions | children | planning | run | against as written |
|---|---|---|---|---|---|
| nothing | 0 | 0 | — | 67 ms | 1.00× |
| `stencil` | 12 | 96 | 14 ms | 75 ms | 0.89× |
| `branch` | 17 | 136 | 12 ms | 76 ms | 0.88× |
| `matmul` | 6 | 48 | 226 ms | 39 ms | **1.71×** |
| all three | 35 | 280 | 254 ms | 39 ms | 1.71× |

At `n = 8`, `m = 32`, `d = 1024`. The matrix multiplies carry the whole result: forty-eight threads
over six regions give 1.71×, and adding the other 232 threads changes nothing. The stencil and the
branch sweeps are each a net loss — their cells are four reads and a store, so a thread finishes
before the spawn has paid for itself, and forking them costs about 12% either way.

So the interesting number is not how much of the program was parallelized but which part. A pass
with no way to be told where to look has to find that out by forking everything, which is the
0.15× row at the top of the sweep; a `keep` predicate over region names finds it by being asked.
