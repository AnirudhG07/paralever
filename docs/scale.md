# Scale — what each stage costs, measured

Generators: `Test/Stress.lean`, which gates every shape below at sizes that keep its elaboration
under a few seconds. The numbers here are the same generators at the sizes that hurt, run through
the command line rather than through `#eval`.

Every figure is wall clock from `/usr/bin/time` on one core of an AMD Ryzen 7 9700X, Lean
`v4.34.0`, the binary at `.lake/build/bin/paralever`. Lean compiles through C — 184 generated `.c`
files become one 118 MB native executable — so the constant factor is a compiled program's and
every cost recorded below is algorithmic. Four of them were defects and are fixed; two remain in the
interpreter and are explained rather than hidden.

## The corpus

| file | shape | lines |
|---|---|---|
| `chain1k`, `chain10k`, `chain50k` | *n* stores to distinct cells, no fork | 1,002 / 10,002 / 50,002 |
| `fork64`, `fork256`, `fork1024` | `parfor i in n { A[i] := i }` | 5 |
| `sh128` … `sh1024` | *n* threads, each reading one shared cell and writing its own | 7 |
| `nest10` | ten nested `parfor`s, 1,024 leaves | 23 |
| `barrier8` | two phases over 64 cells with a `synchronize` between | 55 |
| `arena16` | sixteen buffers declared, freed and reused | 126 |
| `matmul8`, `matmul16` | `C[i,j] := Σ A[i,k]·B[k,j]`, one thread per row | 16 |
| `reduce64` | 64 chunks of 64 additions into a register accumulator | 12 |

Long files are long in *statements*, not in text: `fork1024` is five lines that unroll to 1,024
threads, and `reduce64` is twelve lines that unroll to 4,096 steps. The two axes come apart, which
is why the measurements below vary one at a time.

The files themselves are not in the repository, because every one of them is one call away:

```lean
import Test.Stress
open Test.Stress

def main (args : List String) : IO Unit := do
  let dir := args.headD "."
  IO.FS.writeFile (dir ++ "/chain50k.prl") (chainSrc 50000)
  IO.FS.writeFile (dir ++ "/reduce64.prl") (reduceSrc 64 64)
  IO.FS.writeFile (dir ++ "/matmul16.prl") (matmulSrc 16)
```

`lake env lean --run` on that writes the three largest. The generators are the same ones the gates
in `Test/Stress.lean` use at small sizes, so a file measured here is a file whose answer is checked
there.

## Reading a file

| | lines | before | now |
|---|---|---|---|
| `chain1k.prl` | 1,002 | 0.23 s | 0.02 s |
| `c2000.prl` | 2,002 | 0.82 s | 0.03 s |
| `c4000.prl` | 4,002 | 3.40 s | 0.04 s |
| `c8000.prl` | 8,002 | 13.32 s | 0.05 s |
| `chain10k.prl` | 10,002 | 21.19 s | 0.06 s |
| `chain50k.prl` | 50,002 | not measured | 0.27 s |
| `matmul8.mlir` | 4,391 | 1.67 s | 0.11 s |
| `matmul12.mlir` | 14,451 | 20.54 s | 0.40 s |
| `matmul16.mlir` | 33,855 | 123.09 s | 1.35 s |

`before` is the same binary with the tokeniser and error-message fixes of § *Where the time went*
reverted — nothing else — measured the same way. `chain50k` was not measured there: the
8,000-statement point already cost 13.32 s and each doubling cost four times the last, so the
50,000-statement point is some ten minutes. Both readers are now linear or close to it: eight times
the `.prl` statements cost 2.5× the time, and 7.7× the MLIR lines cost 12× the time.

## Checking and running

`check` reads the file, computes the footprint and decides `wfB`. `run` additionally executes the
program and prints the heap.

| file | check | run |
|---|---|---|
| `chain10k` | 0.06 s | 0.08 s |
| `chain50k` | 0.27 s | 0.35 s |
| `fork1024` | 0.05 s | 0.49 s |
| `sh1024` | 0.13 s | 1.23 s |
| `nest10` | 0.02 s | 0.04 s |
| `barrier8` | 0.02 s | 0.05 s |
| `arena16` | 0.01 s | 0.03 s |
| `matmul8` | 0.04 s | 0.28 s |
| `matmul16` | 0.78 s | 8.98 s |
| `reduce64` | 1.70 s | 17.0 s |

The straight-line files are the cheap ones and the wide ones are not, in both commands. The reason
is the same in both: the independence check ranges over pairs of children, and the interpreter walks
a structure built per child.

## The proof the command line writes

`paralever prove Examples/Scale/matmul12.mlir -o Mm12Proof.lean` writes a module that re-reads the
14,451-line file while it elaborates and states `par_seq_eq` of what it finds. `lake env lean` on
that module takes **34.65 s**, against 78 s before the reader was fixed — elaboration pays the
reading cost twice, once to lower and once to quote, so halving the reader halved the proof.

## Where the time went

Four defects, every one found by measuring rather than by reading, all fixed.

**`Array Char → List Char` in the `.prl` tokeniser.** `slice` was
`String.ofList ((cs.toList.drop a).take (b - a))`, so every identifier and every number converted
the whole file to a list before taking its few characters. One pass over the file per token is a
quadratic in the file's length, and the table above is its shape: 2,000 → 4,000 → 8,000 statements
cost 0.82 → 3.40 → 13.32 s, almost exactly 4× a doubling. `Array.extract` makes it linear
(`Lang/Compile/Parse.lean`).

**Eager error messages in the MLIR reader.** `err` built a 48-character excerpt of the source —
again through `st.cs.toList` — at the point of failure. The grammar backtracks constantly, because a
`memref`'s shape is a run of `N x` groups whose end is only known by trying to read one more, so
*every* failed alternative paid for a message that was then discarded. The error now carries an
offset and a message, and `P.render` quotes the source once, for the failure that escaped
(`MLIR/Parse.lean`). That one change is the whole MLIR column above — 15× at 4,391 lines, 91× at
33,855 — and it is also why the `prove` figure moved.

**A race scan on programs with no race.** `paralever run` scanned for race sites unconditionally so
it could warn that a printed heap was one schedule's answer. But `wfB` accepting *is* the absence of
a race, by `par_seq_eq`, so the scan is only informative when `wfB` refuses. Guarding it
(`Tool/Run.lean`) took `run` on `sh1024` from 9.94 s to 1.23 s:

| threads | before | now |
|---|---|---|
| 256 | 0.23 s | 0.09 s |
| 512 | 1.42 s | 0.32 s |
| 1024 | 9.94 s | 1.23 s |

**Deduplicating a location list by appending to it.** `nubLocs` in
`Paralever/Search/Explain.lean` was `fun acc l => if acc.contains l then acc else acc ++ [l]` inside
a fold: quadratic twice over, once in the membership test and once in the append. `check` prints the
footprint, so the list is as long as the program's distinct locations, and a straight-line file is
where it bites:

| statements | before | now |
|---|---|---|
| 8,000 | 0.20 s | 0.05 s |
| 10,000 | 0.29 s | 0.06 s |
| 50,000 | 11.91 s | 0.27 s |

A `Std.HashSet` for membership with a reversed accumulator for order keeps first-mention order,
which the report depends on. Note the shape of that table: this cost is invisible below about
10,000 statements, which is why the stress corpus has a 50,000-statement file in it. On wide forks
it does not appear at all (`race` on `sh1024`: 8.91 s before, 9.17 s after, noise either way).

## What is still quadratic

Two costs in the interpreter, each isolated by holding the other axis fixed.

**The number of children of a fork.** With no register accumulator at all, so that the second cost
below cannot contribute:

| threads × 32 writes | run |
|---|---|
| 64 | 0.09 s |
| 128 | 0.24 s |
| 256 | 0.95 s |
| 512 | 3.77 s |

Four times the time for twice the threads. The cause is `ParM.seqAll`, which is
`bind (seqPair p (seqAll ps)) (fun r => .pure (r.1 :: r.2))`: `ParM.bind` grafts a continuation by
recursing over its first argument's whole structure, so the outer `bind` of child *i* walks children
*i* through *n* again. `run` without `--real-threads` goes through `execSeq`, whose `par` case is
`seqAll`, so this is on the default path.

**The number of times one thread updates a register.** `Regs = Reg → Int` and
`ρ.set r v = fun k => if k = r then v else ρ k`, so a loop that accumulates into `%acc` makes the
*m*-th read of it cost O(*m*). At 16 threads, varying only the loop length:

| per-thread length | run |
|---|---|
| 16 | 0.09 s |
| 32 | 0.24 s |
| 64 | 0.82 s |
| 128 | 3.21 s |

The same loop writing to memory instead of accumulating in a register is flat (0.02 s at every
length from 32 to 256). `reduce64`'s 17 s is these two multiplied together.

**But the register file is not the cost, and the shape above is what to read off this table.**
Measured directly, with the loop body isolated from `run`'s parsing and lowering
(`paralever-bench reg-vs-mem`), a register is *cheaper* than a cell and both are linear:

| n = 160,000 | register | memory |
|---|---|---|
| read-modify-write one location | 4 ms | 17 ms |
| write only, never read back | 3 ms | 8 ms |

What is quadratic in both is a **buried read**: reading a location that later writes to *other*
locations sit on top of. `ρ.set` and `σ.update` both prepend a closure frame, so a match walks the
frames until it hits the one it wants. Writing a location and reading it straight back hits the
first frame and is O(1); reading one that *n* unrelated writes have buried is O(*n*):

| n | `A[0]` read n times, after n writes | the same reads, nothing written |
|---|---|---|
| 4,000 | 62 ms | 0 ms |
| 8,000 | 246 ms | 0 ms |
| 16,000 | 881 ms | 1 ms |
| 32,000 | 3,718 ms | 1 ms |

Exactly four times the cost for twice the length. That is matrix multiply's shape: `A` and `B` are
never written, so every thread reads them from below all of its own stores to `C`. The register
accumulator in the table above is not what costs; the loop reading past its own writes is.

**The race search, on refused programs only.** `paralever race` is roughly cubic in the thread count
when the conflict is not immediate:

| threads | race |
|---|---|
| 128 | 0.04 s |
| 256 | 0.19 s |
| 512 | 1.20 s |
| 1024 | 9.17 s |

Eight times for twice the threads. A program whose first two threads already conflict costs 0.02 s
at any width, because `findWrongGuided` is aimed by the conflict locations phase 1 found — the curve
above is the price of *not* finding one, which is why the scan now runs only where `wfB` refused
(see above) and never on the accepted path.

**`--real-threads` was slower, and the reason was not the join.** `run --real-threads reduce64` took 23.93 s
against 16.98 s single-threaded, and this file used to attribute that to `joinAllStates` costing
O(*n*) per read after an *n*-way join. Measurement says otherwise: the fork was getting **no cores
at all**. `execChilds` spawned and waited in one pass over `Childs`, which put the `Task.spawn` and
its matching `Task.get` in a single branch of a match on an indexed family; the spawn was then not
issued until its own `get` was about to block, so the children ran one after another on the calling
thread. The evidence, taken on `Compile/ExecArr.lean`'s twin so the two shapes could be timed
against each other with nothing else changed:

| | one pass | two passes |
|---|---|---|
| 16 bands of a 160×160 matmul, forked | 988 ms | 401 ms |
| wall time from 1 to 32 children | flat (988 → 1 child, 1,010 → 32) | 988 → 401 → 452 |
| process CPU | 99% | ~290% |

The fix is in `Compile/Exec.lean`: `spawnChilds` returns a `TaskChilds` spine and `collectChilds`
walks it, so each spawn is a value the recursion *returns* and cannot be deferred past the join.
Nothing about the semantics changed — every proof in that file went through unaltered, and
`execTask_par` still holds by `rfl`. Banded matmul through `execTask` at n = 96 went from 2,936 ms
to 1,069 ms.

The two runs agree on the answer by `runTask_eq_runTaskSeq`, which is what makes the comparison a
measurement of speed and nothing else. Past the fix the fork wins, but only to about 2.4× on 16
cores; what now limits it is named under *What would fix the rest*.

## What would fix the rest

Both remaining quadratics are in the interpreter, not in the theorem: `par_seq_eq` quantifies over
every `ρ` and every `σ` and never inspects either, so neither cost can make a proved statement
weaker. Two directions, recorded here and not taken:

**`seqAll` with an accumulator.** The grafting is quadratic only because the recursive call's result
is bound again at every child; threading the list being built instead makes it one pass. It is the
cheaper of the two, but not free: a dozen theorems induct on the current shape —
`runSeq_seqAll_cons` and `runSeq_seqAll_append` in `AutoPar/Sound.lean`, `time_seqAll_cons` in
`Lib/Cost.lean`, `runSeq_seqAll` in `Theory/Sequentialize.lean` — so the accumulating version has to
be proved equal to this one and those proofs rewritten through it.

**An `Array`-backed heap — built, as a twin.** `State = Loc → Val` and `Regs = Reg → Int` are
*functions*, which is how two heaps are proved equal at all (`funext`, at four sites in
`Theory/WellFormedCanonical.lean` and `Compile/Exec.lean`) and how a fork's children share `σ`
without copying it. *Replacing* them would change `State.update`, `joinStates`,
`runTask_eq_runTaskSeq` and every `simp` lemma stated with `update_same`/`update_other`, so nothing
was replaced. `Compile/ExecArr.lean` instead runs the same `ParM` on an `Array Val` beside the
existing executor, and `Core/` and `Theory/` import nothing from `Compile/`, so the theory cannot
be touched by it — checked, not asserted: the diff against both directories is empty.

It removes the buried-read quadratic outright. Throughput is flat where the function heap's falls
away, and 12.3 M instructions run in 395 ms:

| n | instructions | array, forked | instructions/ms |
|---|---|---|---|
| 64 | 794,624 | 38 ms | 20,911 |
| 96 | 2,672,640 | 91 ms | 29,369 |
| 128 | 6,324,224 | 210 ms | 30,115 |
| 160 | 12,339,200 | 395 ms | 31,238 |
| 192 | 21,307,392 | 700 ms | 30,439 |

What is **not** proved is `execArr_eq_execTask`, which is what would make the twin usable for
anything but a benchmark. `AState.toState_joinArr` — that the array join is `joinAllStates`, with
no independence hypothesis — is proved; the executor-level statement is not, and no `sorry` stands
in for it. See `PLAN.md`.

**The remaining ceiling on the fork: about 2.4×.** At 16 bands of a 192×192 matmul the fork
saturates at width 8 (671 ms) and gets no better at 16 (690 ms) or 32 (744 ms), which is why
`defaultWidth` is 8. Two candidates, neither measured apart yet: the join is serial and costs one
`Val` comparison per cell per child on the calling thread, and every cell read allocates an
`Option Val` and refcounts a `Val` object shared across all the threads, so the reads contend on
cache lines the writes never touch.

**`seqAll` with an accumulator** remains untaken, for the reason given above it.
