# MLIR as the one front end

`MLIR/` reads MLIR generic form and produces a `Layout` and a `ParProg`, so a benchmark written in
C, C++ or Fortran can be given a race verdict without being translated by hand. Entry points:
`MLIR.parse`, `MLIR.lower`, `MLIR.Lowered.verdict`, and `MLIR.Corpus.summary`.

Hand-translating a benchmark suite is the dominant threat to validity for any claim measured on one,
because the translation is part of what is being measured and is itself unverified. This removes
that threat by making the translation mechanical, auditable, and — eventually — a theorem.

## The interface

Two stages, and only the second is ours.

```text
  C / C++         ──cgeist──┐
  Fortran         ──flang───┤
  a .mlir by hand ──────────┤──►  MLIR generic form  ──►  Layout × ParProg
  SCF→Affine pass ──────────┘            │                       │
                                      stage 1                 stage 2
                               off-the-shelf, a text      MLIR/, in Lean
                               format, not our problem
```

N languages against one converter, instead of one front end per language. Stage 1 is replaceable:
if `cgeist` is unavailable a hand-written `.mlir` feeds the same interface and nothing downstream
changes. Stage 2 is one artifact, so it is the only thing that has to be tested.

**Generic form, not each dialect's own assembly.** `--mlir-print-op-generic` prints every op the
same way —

```text
%0 = "affine.load"(%A, %i) {map = affine_map<(d0) -> (d0)>} : (memref<8xi32>, index) -> i32
```

— so one reader covers `affine`, `memref`, `arith` and `func`. The custom form
(`affine.for %i = 0 to 8 { … }`) needs a parser per dialect, which is what would make "one
converter" false. Affine maps are the only piece with their own grammar.

**Not LLVM IR.** It is below the level we can consume, for two separate reasons.

| | LLVM IR | MLIR affine/scf/memref |
|---|---|---|
| control flow | unstructured `br`, phi nodes | structured regions |
| representable in `ParM`? | no — `ParM` is inductive, so arbitrary jumps have no encoding at all (`CLAUDE.md` fact 4) | yes |
| affine maps | gone; a loop is a CFG | present, and they are what we need |

So consuming LLVM IR means writing a loop structurizer first, and going through it *destroys* the
information the lowering depends on.

## An affine map is a footprint function

This is the alignment the whole design rests on. `wfB_parFor_of_lists`
(`Paralever/Lang/Kernels.lean`) asks for each thread's read and write sets as two lists of `Loc`.
An `affine.store` already carries exactly that:

```text
  "affine.store"(%v, %A, %i, %j) {map = affine_map<(d0, d1) -> (d0, d1)>}

  map applied to (i, j)  ──►  subscript [i, j]
                         ──►  Layout.at "A" [i, j]  =  A.base + i·cols + j
                         ──►  wr (i, j) = [that cell]
```

No analysis, no inference: the map *is* the function. What remains of the obligation is index
arithmetic, which `lin_inj` and `lin_ne_of_ne` (`Paralever/Kernels/Grid.lean`) already discharge.

**Loops are unrolled at lowering time**, which is what makes the subscript a literal `Nat` rather
than an expression. The consequence that matters is `ParProg.footprintExact`: a literal address
keeps the footprint *exact*, and proportional to the number of accesses rather than to the size of
the array. `ArrRef.cells` materialises a list as long as the buffer, and `indepB` is quadratic in
list length, so an over-approximated footprint on a large array is not merely imprecise — it is
unevaluable.

Unrolling has a ceiling. `by decide` on `wfB (matmul n)` costs 6.6 s at `n = 8` and 19 s at
`n = 10` (`Examples/MatMul.lean`), and `native_decide` is prohibited (`Test/Sanity.lean`). So
roughly 100 threads is the limit for the unrolled route, and anything larger has to go through a
kernel lemma at symbolic `n` instead. All eleven `ParProg` kernels now have one, verified usable in
`Test/SymbolicKernels.lean`; emitting kernel *shapes* rather than unrolled `.par` lists is the next
step for the lowering, not something it does today.

## Values

MLIR's element types land in two places, and the split is forced by what is provable rather than by
convenience.

| MLIR | Paralever | exact? |
|---|---|---|
| `index`, `i1`, `i8`, `i16`, `i32`, `i64` | `Int` | yes, except that Paralever has no wrapping, so C's overflow is not modelled |
| `f16`, `f32`, `f64` | `Rat`, in `MLIR/Eval.lean` | yes, for the value written |
| `f16`, `f32`, `f64` | `Int`, in the lowered `ParProg` | no — each term truncates |

**Integer widths are discarded.** Paralever's arithmetic is unbounded, so `i32` addition is
`Int` addition. Where a C program would wrap, we do not, and that is a recorded divergence rather
than an approximation we claim is harmless.

**Floating point becomes `Rat`, not `Real`.** Two reasons, and the first is the one that matters.
Every finite IEEE value *is* `m · 2ᵉ`, so `Rat` represents every `f32` and `f64` value **exactly**;
it is a superset of the floats, not an approximation of them. What `Rat` does not model is IEEE
*rounding*, so the divergence between a reference run and a real C run is the accumulated rounding
error and nothing else — named, instead of hidden inside a value type. The second reason is that
`Real` is noncomputable: a `Real`-valued interpreter could state a corpus gate but never run one,
and running them is the point.

A decimal literal is read at its written value, so `0.5` is `1/2` and `4.2` is `21/5`. The nearest
`f64` to `4.2` is a *different* rational, so this already differs from what a C program holds, by
one rounding at parse time. That is the mathematically exact reading of the source, which is the
thing worth checking a translation against.

### Two paths, and why the verdict only needs one

```text
                     MLIR generic form
                            │
            ┌───────────────┴───────────────┐
            ▼                               ▼
      MLIR/Lower.lean                  MLIR/Eval.lean
      Layout × ParProg                 heap : Loc → Scalar
      over Int                         Int and Rat
            │                               │
            ▼                               ▼
      wfB, wellFormedB,                 the values
      raceSites, par_seq_eq
      THE VERDICT                       THE REFERENCE
```

**The verdict does not depend on any value.** `footprintOf` and `indepB` never inspect a `Val`, and
`raceSites` only threads the heap through. A `memref<8xf64>` occupies the same eight cells as a
`memref<8xi32>` and gets the same verdict. This is a property of the design, not a hope about the
workload: `Core/Access.lean`'s `Indep` is a statement about two sets of `Loc`.

**Values cannot reach an address except through `loadAt`/`storeAt`**, whose footprint is the whole
array whatever the index evaluates to (`ArrRef.addr_mem_cells`, which needs no hypothesis). So even
where the `Int` lowering computes the wrong number, it cannot compute the wrong *verdict*.

`MLIR/Eval.lean` evaluates a `par` in one canonical order, and what licenses that is `par_seq_eq`
itself: once the verdict says race-free, every schedule leaves the same heap, so the reference run
may take the sequential one. The project's own theorem is what makes the reference interpreter
allowed to be sequential.

Where `Int` gives up, it says so. `Lowered.exactValues` is `false` as soon as floating-point
arithmetic was evaluated in `Int`, and `Lowered.notes` lists each approximation: a rational
coefficient `q` multiplying `e` is emitted as `(q.num · e) / q.den`, which has the right magnitude
and truncates. On the `stencil-f64-no` pilot the reference run gives
`B = [7/4, 11/4, 15/4, 19/4, 23/4, 27/4]` and the `Int` lowering gives `[0, 2, 3, 4, 4, 6]`, while
both give the verdict `race-free`.

## Why in Lean

`MLIR.lower` is a Lean *function*, so the translation is an object we can state theorems about. The
target is **footprint preservation**: every memory access the MLIR program performs lies inside the
bound the produced `ParProg` reports. That converts the central threat to validity from "trust the
translator" into a proof obligation. A Python script emitting text could never get there — its
output can be checked on examples but never characterised.

This also follows the repo's standing preference for building converters and parsers as Lean
libraries in-repo rather than as scripts.

Not yet done. Until the preservation theorem exists, the translation is validated by **differential
execution** (below), which is the methodology the loop-dependence literature uses — instrument and
trace — except that `accesses` computes the trace exactly rather than sampling it.

**`lean-mlir` was evaluated and not used.** `opencompl/lean-mlir` is the right reference for the
discipline, but its own stated limits are exactly our requirement: it targets the LLVM dialect's
integer instructions, with memory operations, floating-point arithmetic and richer loop classes
listed as future work. `memref`/`affine` load, store and loops are the entirety of what we need. It
also carries its own toolchain pin and Mathlib dependency, against the dependency policy in
`CLAUDE.md`. Decision: borrow the AST shape and the parse-into-typed-terms discipline, write our
own reader. The scope justifies it — roughly forty op kinds, not general MLIR.

## What the lowering does

| MLIR | Paralever | note |
|---|---|---|
| `affine.for`, constant bounds | `block [...]` | unrolled; `step` honoured |
| `affine.parallel`, constant bounds | `.par [...]` | one thread per point of the index box, row-major |
| `affine.load` / `affine.store` + `map` | `.load r l` / `.store l e` | the map evaluates to a literal `Loc`; `footprintExact` stays true |
| `affine.apply` | folded to a literal | |
| `memref.load` / `memref.store`, constant index | `.load` / `.store` | preferred, because it keeps the footprint exact |
| `memref.load` / `memref.store`, computed index | `.loadAt` / `.storeAt` | footprint is the whole array; recorded in `notes` |
| `memref.global`, `memref.alloc`, `memref.alloca` | a `Buf` in the `Layout` | shape from the memref type |
| `memref.get_global` | binds a name to that buffer | |
| a `func.func`'s memref block arguments | a `Buf` each | these are the arrays the benchmark was handed |
| `arith.constant` | a compile-time `Scalar` | `.flt` for a decimal literal |
| `addi`/`subi`/`muli`/`divsi`/`divui`/`maxsi`/`minsi` | `AExp`, folded when both sides are known | |
| `addf`/`subf`/`mulf`/`divf`/`maxnumf`/`minnumf` | the same, over `Int`; exact over `Rat` in `Eval` | marks `exactValues := false` |
| `index_cast`, `extsi`, `trunci`, `sitofp`, `fptosi`, … | the value, unchanged or truncated | Paralever has no widths to convert between |
| `affine.yield`, `func.return`, `memref.dealloc` | nothing | |

`Layout.of` places the buffers in consecutive ranges, so array disjointness is discharged once by
the allocator (`alloc_pairwise`) rather than once per pair. Every subscript is range-checked against
its own buffer, because `Layout.at` is total — without the check, an out-of-range subscript would
silently name a cell of the next buffer.

## What it refuses, and why

Each of these produces a named error rather than a plausible-looking lowering. The list of op names
a file contains that no rule handles is `MLIR.unsupportedOps`, and that list *is* the expressiveness
taxonomy a corpus report needs: what is missing gets counted rather than discovered one benchmark at
a time.

| refused | why |
|---|---|
| multi-block regions, successor lists | unstructured control flow; `ParM` is inductive, so arbitrary jumps have no encoding (`CLAUDE.md` fact 4) |
| `scf.if`, `affine.if` | `ParProg.ifElse` tests `c.eval ρ != 0`, and `AExp` has no comparison operator, so a condition from `arith.cmpi` has nowhere to go |
| `omp.parallel`, `omp.wsloop` | not read yet; `affine.parallel` is the marker the lowering uses |
| `func.call` | no interprocedural handling; this is also why `lower` refuses to pick among several functions |
| dynamic memref dimensions (`?`) | no `Nat` for the shape |
| memref layout maps, memory spaces | strides other than row-major are not modelled |
| `affine_set` (integer sets) | the `affine.if` case, one level down |
| hexadecimal float literals | the written decimal value is the thing we read exactly |
| non-memref function parameters | a scalar parameter has no caller to supply it |
| a computed subscript on a multi-dimensional memref | would need `i·stride + j` as an `AExp`, and `ArrRef.addr` takes one index |

Two smaller limits worth stating. A `memref.global`'s `initial_value` is read into `Buf.init`, which
is `List Int`, so **initial data for a floating-point buffer must be integral** — a cell of such a
buffer starts as an integral rational. And `MLIR.render` drops the type suffix on an integer
attribute (`42 : i32` prints as `42`), so it is the reader's inverse for round-trip checking, not a
printer whose output `mlir-opt` would accept.

## Differential execution

The two runs are compared cell by cell: `Lowered.progCells` against `Lowered.refCells`. It is a
test of the *lowering* only where the comparison has a right answer, and the cases divide cleanly:

| program | the two runs | what a disagreement means |
|---|---|---|
| race-free, integral | must agree | a disagreement is a lowering bug |
| race-free, floating point | disagree by the `Int` truncation | the divergence `notes` already named |
| racy | may disagree | a second, independent witness of the race |

That last row is worth drawing out, because it is the anti-vacuity obligation discharged through
MLIR. On `reduction-yes` the reference run takes the canonical schedule and reaches `sum = 36`; the
threaded `ParProg` run reaches something else. The program the verdict rejects really does depend on
its schedule.

The converse case is on the same corpus: `antidep-yes` is racy and *both* runs give
`A = [1, 1, 1, 1, 1, 1, 1, 0]`, because every schedule reads a `0` and writes a `1` at this heap.
So agreement is not evidence of race-freedom, which is the same point `docs/race-search.md` makes
about a read-after-write race leaving the heap unchanged.

## The corpus

Seven hand-written pilots in `MLIR/corpus/`, with the label in the filename as DataRaceBench carries
it (`-yes` means a race is expected). Hand-written on purpose: it decouples the reader, the lowering
and the reference interpreter from any external toolchain, so all three can be gated before
Polygeist is built. `MLIR/Corpus.lean` holds them as `#guard`s, so a regression fails the build
rather than a report.

| pilot | pattern | label | verdict | note |
|---|---|---|---|---|
| `doall-no` | `C[i] := A[i] + B[i]` | race-free | race-free | two globals and an alloc |
| `antidep-yes` | `A[i] := A[i+1] + 1` | racy | racy | WAR; 6 sites |
| `reduction-yes` | `sum += A[i]`, no clause | racy | racy | WAW and RAW on one cell; 7 sites |
| `reduction-split-no` | disjoint partials, then a sequential fold | race-free | race-free | `sum = 36`, both runs |
| `stencil-f64-no` | `B[i] := 0.5A[i] + 0.25A[i+1] + 0.25A[i+2]` | race-free | race-free | windows overlap, writes do not; `f64` |
| `nested-2d-no` | `C[i,j] := 2·A[i,j]` over 3×4 | race-free | race-free | a two-dimensional index space |
| `indirect-yes` | `A[Idx[i]] := i` | racy | racy | the only over-approximated footprint |

Measured, `MLIR.Corpus.summary`:

```text
expressible    7/7
unsupported    []
confusion      tp=3 fp=0 fn=0 tn=4
precision gap  []
over-approx    [indirect-yes]
round trip     true
```

Two readings. The absence of false negatives is not luck: `raceSites_nil_iff` makes the scan
*complete* for the obligation, so an empty site list is the race-freedom proof and a false negative
would be a bug in `raceSites` rather than a tuning matter. And the `stencil-f64-no` row is the
Bernstein case: neighbouring threads share two of three read cells, which separating conjunction
rejects outright and `Indep` accepts without a clause, because it constrains writes only.

`indirect-yes` is scored correctly for a weaker reason than the others, and the report says so.
Paralever's footprint for a computed subscript is the whole array, so the threads are rejected
whatever `Idx` holds — the real program *is* racy, but a race-free indirect access would be rejected
too. That is the precision cost of an over-approximation, and `approximated` names the entry that
pays it.

## Status, and what is next

Done: the reader (`Ast`, `Parse`, `Affine`), the lowering (`Lower`), the ℚ reference interpreter
(`Eval`), the labelled corpus with its gates (`Corpus`), and the eleven symbolic kernel obligations
the lowering will eventually emit against.

Next, in order:

1. **Kernel shapes instead of unrolled `.par` lists.** The lowering emits one thread per index
   point, which hits the ~100-thread ceiling. Going through `wfB_parFor_of_lists` at symbolic `n`
   removes the ceiling, and is the only route to PolyBench sizes.
2. **Real `mlir-opt` output.** The pilots are hand-written, and `mlir-opt` prints a superset of
   their attributes. The reader ignores unknown attributes, which is the right behaviour, but
   feeding genuine Polygeist output is untested. Build Polygeist, run `cgeist` over DataRaceBench's
   96 C files, feed the generic form through.
3. **`scf.if` and `affine.if`.** These need a comparison operator in `AExp`, which is a change to
   the language, not to the front end — so it wants its own design note.
4. **The footprint-preservation theorem for `lower`.** The reason the converter is a Lean function
   at all.
5. **`flang`,** for DataRaceBench's 166 Fortran files, which the same interface reaches for free.

Excluded by design, not pending: locks, `critical`, `atomic`, `ordered` and barriers are not
modelled, so a DataRaceBench `-no` case whose race-freedom comes from a lock will read as racy.
Those belong outside the denominator with their count reported, not booked as false positives.
