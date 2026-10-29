# Examples

Everything demonstrable in the project, in one tree: Lean files, `.prl` source files and `.mlir`
source files side by side. The `.prl` and `.mlir` files are read and compiled **from inside Lean**,
while the Lean file elaborates — no command line is involved, and `by decide` sees the compiled
program rather than the reader.

Start with **[`Tour.lean`](Tour.lean)**: five claims on one program, each evaluated or proved.

```
Tour.lean          the whole project on one program — start here

Programs/          how do I prove my own algorithm equivalent?
Language/          how do I write and check a .prl file?
Mlir/              how do I bring a program in from MLIR?
Scale/             does any of this survive a 14,451-line file?
AutoPar/           what does the parallelizing pass actually do?
Races/             what does a failure look like?
Threads/           does any of this run on real threads?
```

Build any of it with `lake build Examples`. Open a file in an editor with Lean's infoview and the
`#eval`s print beside the code.

---

## `Programs/` — the method, on real algorithms

Every file follows the same chain, and the two links are independent: changing the algorithm does
not touch link 2, and changing the decomposition does not touch link 1.

```
pure function  ──①──►  seq  ──②──►  par
               ordinary        par_seq_eq,
               Lean proof      given WellFormed
```

| file | the program | what makes it interesting |
|---|---|---|
| `SharedReads.lean` | min and max of the same three cells | the case Bernstein admits and `∗`-disjointness refuses |
| `MapArray.lean` | `Out[i] := 2 * In[i]` | the smallest complete instance of the chain |
| `SumArray.lean` | chunked sum, uneven chunks | read-only, so independence is free at every plan |
| `RowSums.lean` | `Out[i] := Σⱼ A[i,j]` | written purely, then lifted by `Lib/Pure.lean` |
| `CompareSwap.lean` | independent compare-swap rounds | reads *and* writes the same cells, so the obligation is real |
| `MergeSort.lean` | recursive parallel mergesort | genuine divide and conquer; `par` inside every call |
| `MatMul.lean` | `C[i,j] := Σₖ A[i,k]·B[k,j]` | tasks share whole rows and columns; four keyings compared |
| `SortBatches.lean` | sort independent batches | pure chunks, so there is no footprint proof at all |
| `OpaqueAgents.lean` | two bodies never read | footprints *declared*; the theorem holds for every implementation |
| `Pipeline.lean` | sequential, loop, sequential, loop | what ordinary code actually looks like |

## `Language/` — the surface language

Twelve `.prl` files, and the Lean that reads them.

| file | |
|---|---|
| `Files.lean` | nine files read by `prl_file`, checked, run, with the reports pinned |
| `Writing.lean` | writing a program by hand, and repairing one the check refuses |
| `ControlFlow.lean` | `if` and bounded `while`, where the footprint becomes a bound |
| `Scatter.lean` | `A[B[i]]`: a computed address, and the three tiers of check |
| `NeuralNet.lean` | a two-layer net assembled from pre-verified kernels |
| `Input.lean` | a line of standard input uppercased in parallel, and where `input` is refused |
| `Stripe.lean` | `A[2*%p]` against `A[2*%q+1]`: the same program, proved for every in-range heap |
| `Functions.lean` | `def`: a matrix-vector product called from four threads, and a sorting network |
| `Equivalence.lean` | `assert`: two programs, and the theorem that they agree |

`stripe.prl` and `branch.prl` are the two files whose verdict has two different halves, which is why
the report prints two (`docs/general-heap.md`).

`stripe.prl` has two threads writing the even and the odd cells of one buffer with indices loaded
from memory, so `wfB` refuses it and the exact check answers for the declared heap. The general-heap
search then finds a heap where it is wrong: at `k[1] = -1` the `Int.toNat` clamp sends `2 * (-1) + 1`
onto `A[0]`, where `2 * 0` already is, so the *unrestricted* `par_seq_eq` is false and no tactic
could have discharged it. `Stripe.lean` writes the same program by hand, gates it against the file —
through `ParProg.dropPrints`, since the file ends in a `print` — and proves the statement that *is*
true: `par = seq` for every heap whose two indices are in range, the obligation `paralever vc` hands
to a solver, discharged by `grind` through `ArrRef.addr_ne` instead.

`branch.prl` is the other half of that story: two threads writing mirror-image cells of one `if`. The
footprint of a branch is the union of its arms, so `wfB` refuses; only one arm runs, so no heap
races. The search probes every value of the cell the condition is read from, finds nothing, and the
verdict is `Inconclusive` with both of its reasons named — the one shape where the gap is a branch
rather than an index.

`funcs.prl` is the language's `def`: one row of a matrix-vector product written once, called from a
`parfor` over four rows, and a scaling pass after the barrier. A call is written out where it stands
and every register the body names is renamed per call site, so the program `wfB` and `par_seq_eq`
see has no trace of a function in it — the same way it has no trace of the `for` loops once they are
unrolled (`docs/prl.md` § Functions). All four threads read every cell of `V`, which is the case
Bernstein's condition admits and disjointness would refuse.

`sortnet.prl` is the same feature at the other extreme: odd-even transposition sort on eight cells,
eight phases with a `synchronize` between them, and one `def` called 28 times. Both arms of its `if`
write both cells of the pair, so a comparator's footprint is its pair whichever way the comparison
goes, and `wfB` accepts at *every* heap — the theorem is about every input, not about the eight
values the file declares.

`equiv.prl` and `twofold.prl` are the language's `assert`, which states a different question from
every other file here: not whether one program's forks are safe, but whether *two programs* compute
the same thing. `equiv.prl` compares bubble sort against odd-even transposition sort, built from one
comparator `def` so the two sides differ in their schedule and in nothing else — 56 comparator steps
in a row against eight phases of up to four at a time. `twofold.prl` compares two *parallel* sums,
neither of them the sequential program: four threads over two cells each followed by a serial fold,
against a halving tree of three forks. Both leave the answer in `S` and both use `P` as scratch,
which they leave holding different things — so the claim names `S`, and `Equivalence.lean` gates
that comparing all of memory instead would reject the pair. The division of labour is the point:
`par_seq_eq` on each side disposes of the schedules, and what remains is two programs with no fork
in them (`docs/equivalence.md`).

The nine `prl_file` programs: `sum`, `matmul`, `stencil`, `pipeline`, `chain`, `control`, `arena`
are accepted; `race` is racy; `scatter` is the third verdict — refused syntactically, accepted at
its heap. The tenth, `input.prl`, reads the shell, so Lean cannot read it with `prl_file` and
`Input.lean` compiles it from text with the input supplied (`docs/prl.md` § Input):

```bash
echo "hello, world" | paralever run Examples/Language/input.prl
```

## `Mlir/` — the other front end

Seven hand-written pilots in MLIR generic form, named with the verdict each is expected to get in
DataRaceBench's `-yes`/`-no` convention, and two more in MLIR's *custom* form —
`pretty-doall-no.mlir` and `pretty-reduce-yes.mlir`, the syntax `mlir-opt` prints and people write.
`Files.lean` lowers one end to end and prints the whole corpus report. The exhaustive gates live in
`MLIR/Corpus.lean`, where each custom-form pilot is checked against its generic twin: same verdict,
same footprint, same values (`docs/mlir-pretty.md`).

## `Scale/` — one big file

`matmul12.prl` is the 12×12 matmul, twenty lines. `matmul12.mlir` is the same program as
`paralever to-mlir` emits it: **14,451 lines** of MLIR generic form, 1.0 MB, every one of the 12
threads unrolled. Reading it back gives the same verdict, the same footprint and the same heap as
the `.prl` it came from:

```bash
paralever Examples/Scale/matmul12.mlir          # wfB = true, 12 threads, 300 rounds — 0.9 s
paralever run Examples/Scale/matmul12.mlir      # the same heap the .prl run leaves — 3.4 s
```

Lean proves it too — `paralever ... --prove Big12.lean --check` writes the module and Lean accepts
it in 35 s — but no Lean module in this tree reads the pair, because every `lake build` would pay
that. `docs/scale.md` has the measurements, `docs/mlir.md` § *Scale* the MLIR-side table.

## `AutoPar/` — sequential in, parallel out

`Pass.lean` runs the pass on `Language/chain.prl` and evaluates **every step**: the units, the
dependence DAG, the critical-path bound, the plan, the emitted program, and the soundness theorem
that needs no hypothesis.

## `Races/` — what failure looks like

| file | |
|---|---|
| `Caught.lean` | two programs where the *conclusion* of the theorem is false, not just its hypothesis |
| `Report.lean` | reading a counterexample: the interleaving, and the heap the sequential run leaves |
| `Pointers.lean` | a stray index — rejected in three shapes, and **accepted** in one, because this is equivalence, not memory safety |

## `Threads/`

`RealThreads.lean` runs a `ParM` tree on real `Task`s, so what executes is the term the theorems
are about.
