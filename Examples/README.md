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

Nine `.prl` files, and the Lean that reads them.

| file | |
|---|---|
| `Files.lean` | all nine files read by `prl_file`, checked, run, with the reports pinned |
| `Writing.lean` | writing a program by hand, and repairing one the check refuses |
| `ControlFlow.lean` | `if` and bounded `while`, where the footprint becomes a bound |
| `Scatter.lean` | `A[B[i]]`: a computed address, and the three tiers of check |
| `NeuralNet.lean` | a two-layer net assembled from pre-verified kernels |

The nine programs: `sum`, `matmul`, `stencil`, `pipeline`, `chain`, `control`, `arena` are accepted;
`race` is racy; `scatter` is the third verdict — refused syntactically, accepted at its heap.

## `Mlir/` — the other front end

Seven hand-written pilots in MLIR generic form, named with the verdict each is expected to get in
DataRaceBench's `-yes`/`-no` convention. `Files.lean` lowers one end to end and prints the whole
corpus report. The exhaustive gates live in `MLIR/Corpus.lean`.

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
