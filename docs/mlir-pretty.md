# Pretty form — reading the MLIR people actually write

Code: `MLIR/Pretty.lean`. The generic-form reader it sits beside is `MLIR/Parse.lean`; what both
feed is `MLIR/Lower.lean`, unchanged. Rationale for the front end as a whole: `docs/mlir.md`.

## The problem, measured

`docs/mlir.md` § *The interface* takes generic form (`--mlir-print-op-generic`) because it is one
grammar for every dialect. That is true and it is still the reason there is one reader. It is also
not what anybody writes. Every `.mlir` file in `llvm/llvm-project`, in Polygeist's tests, in an
IREE sample or in a bug report is in *custom* (pretty) form, and a generic-form reader stops at the
first operation:

```console
$ paralever to-prl mlir/test/Dialect/Affine/canonicalize.mlir
expected a quoted string (offset 464, near: func.func @compose_affine_maps_1dto2d_no_symbols)
```

Translating one form to the other is `mlir-opt --mlir-print-op-generic`, so before this module the
project could read a file from outside only on a machine with an MLIR build — which is the one
dependency `CLAUDE.md` § *Dependencies* rules out.

## The decision

**A second reader, not a second anything else.** `MLIR/Pretty.lean` parses custom assembly and
produces `Op`, the same generic AST. Every pretty construct is *desugared* to the operation MLIR's
own generic printer would have produced, so `Lower`, `Eval`, `Emit` and `Corpus` do not learn that
pretty form exists.

The alternative — a `PrettyOp` AST with its own lowering — was rejected on the usual ground: it
doubles the number of places a verdict can come from, and a verdict is the thing this project is
for. Desugaring keeps exactly one path from syntax to `ParProg`.

```text
  pretty .mlir ──► Pretty.parse ──┐
                                  ├──► List Op ──► Lower ──► Layout × ParProg
 generic .mlir ──► Parse.parse ───┘       ▲
                                          └── Emit prints this, never pretty form
```

`MLIR.parseAny` chooses the reader by looking at the first operation: a `"` starts generic form, a
bare identifier starts pretty form. Nothing else distinguishes them, and a file may mix the two —
an unregistered op inside a pretty file is written generically (`"test.foo"(%v) : (f32) -> ()`),
which the pretty reader hands to `Parse.parseOp` where it stands.

## The desugaring table

| pretty | generic |
|---|---|
| `module { … }` | `"builtin.module"() ({ … })` |
| `func.func @f(%a: memref<4xi64>) { … }` | `"func.func"() ({ ^bb0(%a: memref<4xi64>): … }) {sym_name = "f", function_type = …}` |
| `return` | `"func.return"() : () -> ()` |
| `affine.for %i = 0 to 8 step 2 { … }` | `"affine.for"() ({ ^bb0(%i: index): … }) {lowerBoundMap = affine_map<() -> (0)>, upperBoundMap = affine_map<() -> (8)>, step = 2 : index}` |
| `affine.parallel (%i, %j) = (0, 0) to (4, 8) { … }` | `"affine.parallel"() ({ … }) {lowerBoundsMap = …, upperBoundsMap = …, steps = [1, 1]}` |
| `affine.load %A[%i, %j + 1] : memref<4x8xi64>` | `"affine.load"(%A, %i, %j) {map = affine_map<(d0, d1) -> (d0, d1 + 1)>} : (memref<4x8xi64>, index, index) -> i64` |
| `affine.store %v, %A[%i] : memref<4xi64>` | `"affine.store"(%v, %A, %i) {map = affine_map<(d0) -> (d0)>}` |
| `affine.apply #map(%i)` | `"affine.apply"(%i) {map = affine_map<(d0) -> (d0 + 1)>}` |
| `memref.alloc() : memref<6xi64>` | `"memref.alloc"() : () -> memref<6xi64>` |
| `memref.global "private" @A : memref<3xi64> = dense<[1, 2, 3]>` | `"memref.global"() {sym_name = "A", type = memref<3xi64>, initial_value = dense<[1, 2, 3]> : tensor<3xi64>}` |
| `arith.constant 7 : i64` | `"arith.constant"() {value = 7 : i64} : () -> i64` |
| `arith.addi %a, %b : i64` | `"arith.addi"(%a, %b) : (i64, i64) -> i64` |
| `%0 = arith.cmpi slt, %a, %b : i64` | `"arith.cmpi"(%a, %b) {predicate = "slt"} : (i64, i64) -> i1` |

Two of those rows carry the whole translation. **An index list becomes a map.** MLIR's pretty form
writes the affine expression inline, `%A[%i, %j + 1]`, where generic form carries a `map` attribute
and a flat operand list; the reader parses each subscript as an `AffExp` and collects the SSA
values it mentions, in order of first use, as the map's dimensions. So the operands are
`memref :: values` and the map is over `d0 … dₙ₋₁`, which is exactly the shape
`Lower.subscript` already consumes. **A region argument is a loop index.** `affine.for %i` becomes
a region whose entry block takes `%i : index`, because that is where `lowerIters` looks.

Map aliases are substituted on use: a top-level `#map = affine_map<(d0) -> (d0 + 1)>` is kept in a
table and `#map(%i)` reads as the map itself. An alias is a file-local abbreviation with no meaning
of its own, so there is nothing to carry into `Op`.

## What it refuses, and why

Each of these is a named error with the offset, never a plausible-looking lowering. They divide into
two kinds, and the division is the point: a *vocabulary* gap is a gap, and a *representability*
refusal is permanent.

| refused | kind |
|---|---|
| an op whose custom syntax is not in the table, named: `pretty form of 'tensor.empty' is not in the vocabulary` | vocabulary; write that one generically, or add a row |
| `affine.for … iter_args(%acc = %init)` | representability: a loop-carried value is a reduction, which is the dependence `wfB` exists to refuse |
| `affine.parallel … reduce ("addf")` | representability, same reason |
| `^bb1:` | representability: unstructured control flow, `CLAUDE.md` fact 4 |

Two things are deliberately **not** refused by the reader, because the lowering is the right place
to refuse them. A loop bound that is an operand or a `max` of maps parses, and desugars to the
operands and maps generic form would carry; `Lower` then says
`affine.for needs constant lowerBound and upperBound maps`, because it unrolls and needs the trip
count. And an operation whose result nobody names — `affine.load %m[%i] : memref<?xf32>`, which
occurs in MLIR's own tests — is read as an operation with no results and lowered as the read it is:
a load with no reader still has a footprint, and the footprint is what a verdict is about.

### What the reader keeps verbatim

Three things are carried through as the text they are written as rather than refused, so that a file
*mentioning* one still reads and it is the lowering that declines:

| written | read as | refused by |
|---|---|---|
| `memref<?xf32>`, `memref<8xf32, strided<[1], offset: ?>>`, `memref<8xi32, 1>` | `MTy.other "memref<…>"` | `Lower`: a parameter has to be a memref with a static shape |
| `vector<64xf32>`, `complex<f32>` as a memref's element | `MTy.other "vector<64xf32>"` | `Lower.scalarElt`: one cell holds one scalar |
| `#llvm.fastmath<none>` and any other dialect attribute | `MAttr.raw "#llvm.fastmath<none>"` | nothing reads it; it prints back unchanged |

A bare `#map` in an attribute position is the exception: it stays an **error**, because a rule that
read an unresolved alias as the identity map would misread the file rather than refuse it.

### One thing that is modelled conservatively, not refused

`memref.alloc` inside a loop is one buffer, not one per iteration, because `Layout` places buffers
once and has no run-time allocator (`docs/layout.md` § *Lifetimes*). MLIR's own
`-affine-parallelize` turns `affine.for { %m = memref.alloc() … }` into an `affine.parallel`, which
is sound there because each iteration allocates its own. Read here, the same loop written as
`affine.parallel` has every thread writing one shared buffer, so the verdict is **racy** where MLIR
is right that it is not. That is the conservative direction — a refusal, not a false acceptance —
and it is the only place in the front end where the two models disagree about a program's meaning.

## One function out of twenty

A real test file holds many functions — `mlir/test/Dialect/Affine/parallelize.mlir` holds twenty —
and `Lower.entryOf` refuses to choose among several unless one is called `main`, because
`func.call` is not supported. `paralever --func NAME` names the one to lower, and buffer collection
follows the same choice: module-level `memref.global`s, then the declarations inside the function
selected. Without it, a twenty-function file fails on the layout before any verdict is reached,
because twenty functions declare twenty `%0`s.

## Measured, on MLIR's own test input

`mlir/test/Dialect/Affine/parallelize.mlir` is the input to `-affine-parallelize`, the pass
Paralever is a certifying replacement for, and it is the hardest sensible target: twenty functions
written to exercise that pass's edge cases. `paralever funcs` reads it function by function:

| | |
|---|---|
| functions | 20 |
| **read** by `MLIR/Pretty.lean` | **11** |
| refused by the reader | 9 — seven `iter_args` reductions, one `memref.reinterpret_cast`, one `index.constant`/`tensor.empty` |
| of the 11 read: **a verdict** | **2** — `non_affine_load`, `local_alloc` |
| refused by the lowering, named | 7 — `arith.cmpf`, `unknown`, four dynamic-`memref` parameters, one `index` parameter |
| over the unrolling ceiling | 2 — `max_nested_1` (4096×4096) and `explicit_parallel` (1×123×194) do not finish in 120 s |

The one to look at is `non_affine_load`: a hundred iterations of `memref.load %0[%i]` with a
non-affine subscript.

```console
$ paralever --func non_affine_load parallelize.mlir
parallelize.mlir
  memory    v0[100] @0  (100 cells)
  reads     {v0[0], v0[1], v0[2], v0[3], v0[4], v0[5], v0[6], v0[7], v0[8], v0[9], … +90 more}
  writes    {}
  threads   1
  rounds    100 parallel, 100 sequential
  verdict   independent — par = seq under every schedule (wfB = true)

PROVED. Bernstein holds at every fork, so par_seq_eq applies: every schedule of this
program leaves the heap its sequential reading leaves.
```

`-affine-parallelize` **declines** that loop — the file's own `CHECK` line expects `affine.for` to
survive — because the pass cannot analyse a non-affine access. Bernstein accepts it, because the
loop only reads, and reads never conflict. On the pass's own test input, in the pass's own syntax,
the comparison is a precision gain and not a loss, and it comes with `par_seq_eq` attached.

## What is not claimed

Pretty form goes **in** and never comes out: `MLIR.emitText` prints generic form only, which is
what `mlir-opt` reads and what `docs/mlir.md` § *Generic form out* describes. So there is no
`parse ∘ render = id` claim on this path. What is gated instead is that the desugaring lands in the
generic language: `Parse.parse (render (Pretty.parse s)) = Pretty.parse s`, as a `#guard` on every
pretty pilot — the reader's image is readable by the reader this project already trusts.

-- ref: MLIR LangRef, *Operations* (custom assembly format); the Affine dialect's own documentation
for `affine.for`, `affine.parallel`, `affine.load` and `affine.store`; `mlir-opt
--mlir-print-op-generic`, which is the function this module inverts.
