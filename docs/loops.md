# Rolled loop nests: a certificate instead of an unrolling

Rationale for `Lang/Core/Loop.lean` and `ParProg`'s `loop` constructor. Code references this file as
`docs/loops.md`.

## The complaint this answers

Every loop in the project is unrolled. `parFor n body = .par ((List.range n).map body)`
(`Lang/Core/Kernels.lean:27`); `for` and `parfor` are written out at `Lang/Compile/Lower.lean:518`;
`affine.for` becomes a sequential `block` of its iterations and `affine.parallel` a `.par` of them
(`MLIR/Lower.lean:589`). So a program's `ParProg` is proportional to its iteration space, and the
independence check is proportional to its square.

That ceiling has been measured. `Examples/Programs/MatMul.lean:267` records `by decide` on `wfB` at
n = 2, 4, 6, 8, 10:

| threads | 4 | 16 | 36 | 64 | 100 |
|---|---|---|---|---|---|
| `by decide` | <1 s | 0.8 s | 2.0 s | 6.6 s | **19 s** |

A hundred threads is nineteen seconds, and `native_decide` is prohibited (`Test/Sanity.lean:8`), so
there is no escape by changing the evaluator. PolyBench's standard sizes are 1000–4000 per
dimension, which is 10⁶ threads for a two-level nest: six orders of magnitude past the measurement
above. The repository has said so twice already — `docs/mlir.md:450` calls kernel shapes "the only
route to PolyBench sizes", and `docs/prl.md:414` pairs rolled loops with a call node as future work.

The fix is not a faster `decide`. It is to stop deciding a proposition about N^d threads and start
deciding one about the handful of affine maps the nest declares. That is PolCert's packaging (Li,
Liang, Feng, TASE 2024): one generic theorem, plus a per-instance decidable validator.

## What already exists, and is not rebuilt

Most of the theory is done. This is worth stating precisely, because it bounds the work.

| already proved | where |
|---|---|
| the loop metatheorem, **polymorphic in the index type** `{κ τ : Type} (idxs : List κ)`, with *separate* read and write bounds `Pr Pw : κ → Loc → Prop` | `Paralever/Lib/Loop.lean:107` |
| why reads and writes are bounded separately — "iterations may share reads freely… what lets a loop like matmul go through at all" | `Paralever/Lib/Loop.lean:9` |
| the two-level index set and its one structural fact | `gridIdx`, `gridIdx_nodup`, `Paralever/Kernels/Grid.lean:58,80` |
| row-major linearisation, injective | `lin`, `lin_lt`, `lin_inj`, `lin_div`, `lin_mod`, `Paralever/Kernels/Grid.lean:101` |
| d-dimensional affine map evaluation | `AffMap.apply (args : List Int)`, `MLIR/Affine.lean:51` |
| symbolic footprint bounds | `Within`/`ReadsWithin`/`WritesWithin`/`FootprintWithin`, `Paralever/Theory/Intervals.lean` |
| size-free discharge of `wfB` | `wfB_parFor_of_lists` and eleven DSL kernels, `Lang/Core/Kernels.lean:203,248` |

So the metatheorem needs no change. What is missing is the d-dimensional index box, a decidable
certificate, and an AST node to hang them on.

## Four questions answered before any of it was written

Each was a scratch experiment that could have stopped the design.

**1. Can a nest carry a `ParProg` body while `ParProg` carries the nest?** Yes, as a `mutual`
inductive. Three encodings were tried:

| encoding | verdict |
|---|---|
| `structure Nest (β : Type)` with `loop : Nest ParProg → ParProg` | **rejected.** Structural recursion through `n.body` is not inferred: `sizeOf n.body < 1 + sizeOf n` is left as a goal. |
| `mutual inductive ParProg … inductive LoopNest` | **chosen.** Accepted by the kernel; `Repr`, `Inhabited` and `ToExpr` all derive. |
| the fields inlined into a six-argument `loop` constructor | works, but spends the named fields that make the nest readable. |

The mutual form also matches how the file is already written: every fold over the AST is a `mutual`
pair (`footprintOf`/`footprintsOf`, `wfB`/`wfAllB`, `execPar`/`execParAll`), so a nest adds a third
companion rather than a new idiom. `ParProg` derives only `Repr, Inhabited` — it has no
`DecidableEq`, and does not need one.

**2. Does the metatheorem instantiate at `κ := List Int`?** Yes, and freely: `parEach`'s index type
is an unconstrained `α : Type` (`Paralever/Kernels/Assign.lean:29`), so there is nothing to satisfy.
The work is the box's one structural fact, which is proved:

```lean
def boxIdx : List (List Int) → List (List Int)
  | []         => [[]]
  | vs :: rest => vs.flatMap (fun v => (boxIdx rest).map (fun p => v :: p))

theorem boxIdx_nodup : ∀ lvls, (∀ vs ∈ lvls, vs.Nodup) → (boxIdx lvls).Nodup
```

A level contributes its own list of values, so `(lo, hi, step)` is handled by generating them
(`levelVals`) and never appears in an induction. The proof is `gridIdx_nodup`'s template — nested
induction, `List.nodup_append`, `List.flatMap_cons` — and uses no Mathlib.

**3. Is the certificate decidable at PolyBench sizes?** Yes. The gemm access set at N = 1000 —
`C[i,j]` written, `A[i,k]` and `B[k,j]` read — closes by `decide` in under a second, Lean's own
startup included, and the goal never mentions an index. Measured against 19 s for a hundred
*unrolled* threads, the check is now independent of N, as intended: its input is three accesses and
a two-number stride vector, not 10⁶ children.

The d-dimensional injectivity the certificate rests on is proved, again by `Grid.lean`'s template
(`Nat` points, `omega`, `Nat.mul_le_mul_right`, no Mathlib):

```lean
def linBox : List Nat → List Nat → Nat          -- p₀·|n₁…| + p₁·|n₂…| + ⋯
theorem linBox_lt  : InBox ns ps → linBox ns ps < prodN ns
theorem linBox_inj : InBox ns ps → InBox ns qs → linBox ns ps = linBox ns qs → ps = qs
```

`lin`/`lin_lt`/`lin_inj` are the two-level corollaries, and `linBox [h,w] [i,j] = lin w i j` is
gated pointwise so `Kernels/Grid.lean` keeps its current proofs.

**4. How much of the published corpora is reachable?** Recorded in `docs/bench.md`, because it is a
fact about the evaluation rather than about loops.

## The design

As built, in `Lang/Core/Loop.lean`. One leaf constructor, and **no mutual inductive**:

```lean
inductive NestStmt where
  | rd : Reg → AffAccess → NestStmt      -- `%r := A[aff(p)]`
  | wr : AffAccess → AExp → NestStmt     -- `A[aff(p)] := e`
  | st : Reg → AExp → NestStmt           -- `%r := e`, pure

structure LoopNest where
  ivs      : List Reg        -- one induction register per level, outermost first
  sizes    : List Nat        -- trip count per level; the box is ∏ sizes
  lo       : List Int        -- first value per level (0 when normalized)
  step     : List Int        -- stride per level (1 when normalized)
  parDepth : Nat             -- how many leading levels are forked
  body     : List NestStmt

inductive ParProg where
  | …
  | loop : LoopNest → ParProg
```

```text
                       loop
                         │
      ┌───────┬────────┬─┴──┬───────┬──────────┐
     ivs    sizes     lo   step  parDepth    body
   [%i,%j] [1000,   [0,0] [1,1]     2      [rd %10 A[i,k],
            1000]                           rd %11 B[k,j],
                                            wr C[i,j] …]
```

Three decisions, each of which the earlier sketch had the other way.

**The accesses are computed, not declared.** The sketch gave `LoopNest` its own `reads` and
`writes` fields, "declared as `Paralever/Lib/OpaqueOp.lean` declares the footprint of a body it
never reads". That is the wrong parallel: `OpaqueOp`'s own discipline is that the footprint is a
*theorem* (`opaqueOp_accesses`), not an annotation, because the body is an ordinary pure function.
A nest's body is ordinary data too, so `LoopNest.reads = readsOf n.body` and
`LoopNest.writes = writesOf n.body` are projections of the body, and `wfB`'s nest case cannot be
satisfied by a declaration that the body contradicts. There is nothing to check against the body,
because there is nothing separate to check.

The cost is that the body is **straight-line**: no `if`, no inner `ParProg`. A reduction over the
sequential levels is still expressible — that is gemm — but a conditional inside a nest is refused.
`Paralever/Lib/Block.lean` takes the same restriction for the same reason.

**The body is not a `ParProg`, so the constructor is a leaf.** Stage 0 found that
`structure Nest (β)` with the body *inside* the record defeats structural recursion. With the body
a `List NestStmt`, `LoopNest` contains no `ParProg` at all, so `| loop : LoopNest → ParProg` is as
ordinary as `| synchronize`: `execPar` recurses into nothing, and all twenty-seven exhaustive
matches on `ParProg` gain a leaf case rather than a recursive one.

**`sizes`, with `lo` and `step` beside them, rather than `ranges : List (Int × Int × Int)`.** The
certificate is over `List Nat` coordinates — `AffAccess.addr` and `linBox` both are — so the trip
count is the primary datum and the induction register's *value* at coordinate `c` is
`lo + step * c` (`ivVal`). Nothing in `nestIndepB` reads `lo` or `step`, so a non-normalized nest
checks identically to a normalized one; this is MLIR's affine normalization, kept as data instead
of applied as a rewrite.

### Semantics: fork the prefix, iterate the suffix

```lean
LoopNest.thread  n ρ u = n.inner u n.innerBox ρ         -- one thread: every inner point, in order
LoopNest.threads n ρ   = n.outerBox.map (n.thread ρ)    -- one child per forked coordinate
execPar (.loop n) ρ    = ParM.bind (ParM.parAll (n.threads ρ)) (fun _ => .pure ρ)
execSeq (.loop n) ρ    = ParM.bind (ParM.seqAll (n.threads ρ)) (fun _ => .pure ρ)
```

`outerBox = boxNat (sizes.take parDepth)` and `innerBox = boxNat (sizes.drop parDepth)`, so the
point the body runs at is `u ++ p` and `List.take_append_drop` is what makes it a point of the
whole box (`inBox_whole`). The two interpreters differ in `parAll` versus `seqAll` over the **same**
list of children, which is why `execPar_runSeq_all`'s nest case is one rewrite with
`runSeq_parAll_eq_seqAll` and nothing else.

Registers are thread-private here as everywhere: the fork hands each thread the parent's file and
discards what it leaves, so `execPar (.loop n) ρ` returns `ρ`.

### What the constructor cost

| | |
|---|---|
| `mutualInduction` call sites, each gaining one `?_` and one case | 11 — 7 in `Lang/Core/Prog.lean`, 2 in `AutoParSound.lean`, 1 each in `Cost.lean` and `AutoPar/Chain.lean` |
| exhaustive matches on `ParProg` gaining a leaf case | 18, across 10 files |
| new proofs the constructor *forced* | `wellFormed_threads`, `wellFormed_seqAll`, `accesses_threads_sub`, and the nest half of `agree_run_all` |

`hloop` was added **last** to `ParProg.mutualInduction`, exactly as `hprint` was, so every existing
call site's goals kept their original order and the new goal is the final bullet.

The one that was not anticipated is `agree_run_all` in `Lang/Core/AutoParSound.lean`: two register
files agreeing on a set `R` must leave the same heap. A nest has no sub-statement, so the induction
cannot be delegated to a sub-term — it runs over the body, then over the inner points, then over
the threads, carrying one invariant at all three levels (equal heaps, files agreeing on `R`). A
register written *inside* the body may lie outside `R`, which is harmless: anything the body goes
on to read is in `regsOfNest` and therefore in `R`.

### One forked point is no fork at all

`nestIndepB` begins `prodN (sizes.take d) ≤ 1 || …`. At `parDepth = 0` the nest forks a single
thread, so Bernstein has nothing to say, and `inBox_unique_of_prodN_le_one` discharges the
soundness obligation vacuously: `u ≠ v` with both in a one-point box is a contradiction.

This clause is load-bearing rather than cosmetic. A *sequential* `affine.for` — most of PolyBench,
and every reduction's inner loop — lowers to `.loop` with `parDepth = 0`, and without the clause it
would be refused for carrying a dependence it is entitled to carry: a loop-carried write is not
row-major in zero forked levels. `Test/Loop.lean` gates `A[i+1] := A[i] + 1` both ways — refused at
`d = 1`, accepted at `d = 0` — on the same nest.

### The certificate

As built, in `Paralever/Theory/Nest.lean`. An access is one cell per iteration at an affine function
of the induction variables, so `mapsDisjoint_sound`'s conclusion is an inequality of addresses
rather than a `Disjoint` of lists:

```lean
structure AffAccess where
  base   : Loc          -- the buffer's base address
  size   : Nat          -- cells in the buffer, so an access can be confined to it
  coeffs : List Nat     -- one coefficient per loop level, outermost first
  off    : Nat          -- the constant term

def mapsDisjoint (sizes : List Nat) (d : Nat) (a b : AffAccess) : Bool
def nestIndepB   (sizes : List Nat) (d : Nat) (reads writes : List AffAccess) : Bool

theorem mapsDisjoint_sound (ha : a.inBounds sizes = true) (hb : b.inBounds sizes = true)
    (h : mapsDisjoint sizes d a b = true) :
    ∀ u v p q, InBox (sizes.take d) u → InBox (sizes.take d) v → u ≠ v →
      InBox sizes (u ++ p) → InBox sizes (v ++ q) → a.addr (u ++ p) ≠ b.addr (v ++ q)
```

### `d` — how many levels are forked

A nest forks its `d` outermost levels and runs the rest inside each thread, so a point of the box is
`u ++ p` with `u` the forked coordinates and `p` the sequential ones. Bernstein's question is asked
about `u` alone: two threads differ in `u`, and each one runs every `p`.

Without this, gemm is unreachable. `C[i,j]` over the box `(i,j,k)` is written by a thousand
iterations of `k`, so it is **not** injective on the whole box — and it does not need to be, because
those thousand iterations all belong to one thread. What it must be is injective in `(i,j)`.

The whole-box formulation could not express that at all: `C[i,j]`'s coefficients are not the stride
vector of `(i,j,k)` and never will be.

#### Injective in the forked levels, *scaled*

The clause that decides it is `outerInjective sizes d a`, and it is one condition rather than two
because a thread does not need to own a *single* cell — it needs to own a *block* no other thread
reaches into. Write `S` for how far the sequential levels can move an address:

```text
S  =  innerSpan sizes d a  =  1 + dotN (a.coeffs.drop d) (maxPoint (sizes.drop d))
```

The clause is then: the forked levels' coefficients are the forked box's row-major strides, *times
`S`*.

```text
a.coeffs.take d  ==  (strides (sizes.take d)).map (· * S)
```

The address a point `u ++ p` reaches is `base + off + S · linBox (sizes.take d) u + t` with
`t < S` — thread `u` owns the `S` consecutive cells starting at `S · linBox u`, and `t` chooses one
of them. Two threads are two blocks, so `linBox_inj` finishes it (`addr_outer`, `mul_add_inj`).

Two very different shapes fall out of the one clause, and both are shapes PolyBench is made of:

| nest | write | `S` | why it is accepted |
|---|---|---|---|
| `parfor i { for j { … } }` | `A[i]` | `1` | the write does not mention `j`, so thread `i` owns one cell |
| `parfor i { for j { … } }` | `C[i,j]` | `N` | thread `i` owns `C[i, 0..N)`, and thread `i+1` owns the next `N` |
| `parfor i,j { for k { … } }` | `C[i,j]` | `1` | gemm at `d = 2`: `k` is a reduction inside the thread |
| `parfor i { for j,k { … } }` | `C[i,j]` | `N` | gemm at `d = 1`: the same nest, one level forked |

The second row is the one the first formulation of this clause got wrong. It required the
coefficients to be **zero** over the sequential levels — which is `S = 1` — and so refused
`parfor i { for j { C[i,j] := A[i,j] + B[i,j] } }`, the single most common perfectly-nested shape
there is. The scaled reading accepts it and accepts gemm at `d = 1` as a bonus, at no cost in
soundness: `S = 1` is the old clause exactly, so nothing that was accepted before is accepted for a
new reason.

What the clause still refuses is a genuine race. `A[i,k] := …` with `(i,j)` forked has
`coeffs.take 2 = [N, 0]` against a required `[N·N, N]`, and two threads differing only in `j` would
indeed write one cell. `Test/Nest.lean` gates that refusal beside the four acceptances, and
`#guard !outerInjective [N,N,N] 1 { Cij with coeffs := [1,1,0] }` gates that the scaling is
load-bearing rather than decoration.

`nestIndepB` takes the two declaration lists directly rather than a `LoopNest`, so the certificate
and its soundness are provable before the AST carries a nest at all — which is the order they were
built in. `nestIndepB_ww` and `nestIndepB_wr` deliver the two halves in exactly the shape
`parAll_par_seq_eq_of_indexed_rw` consumes as `hww` and `hwr`.

#### `grind`, not `omega`

Every arithmetic step in the module closes with `grind`. The reason is mechanical: `Loc` is an
`abbrev` for `Nat`, and `omega` does not unfold it when it decides which subterms are integer atoms.
So `a.base` is opaque to `omega`, and a goal as small as `a.base ≤ a.base + a.off` comes back as
"no usable constraints found" — with the field typed `Nat` instead, the same goal closes. Destructuring
the record does not help, because the bound variable keeps the `Loc` type. `ArrRef.loc_mem` is the
same wall and already uses `grind`.

`wfB` gains `| .loop n => nestIndepB n && wfB n.body`. Cost is O((#reads + #writes)²) and
independent of the bounds. `nestIndepB` checks write-versus-write and write-versus-read only; there
is no read-versus-read clause, because `Indep` has none (`docs/access.md`). That omission is what
lets gemm through: `A`'s row and `B`'s column are read by a whole row and column of iterations, and
the overlap is never examined.

### The clause that was rejected, and why

The first draft of `mapsDisjoint` accepted two accesses on one buffer when they had the same
coefficients and *different* constant offsets — "the cells differ, so the iterations cannot
collide". That is unsound, and the experiment caught it: it accepted `A[i] := A[i-1] + 1`.

The error is the quantifier. Distinct offsets establish that iteration `p`'s write misses iteration
`p`'s *own* read. Bernstein asks about `p` and `q` with `p ≠ q`, and for a unit stride every offset
gap is realised by some such pair — `q = p + 1` for a gap of one, which is exactly a loop-carried
dependence. So the clause is gone, and what remains is:

* the two accesses lie in **different buffers**; or
* they are the **same** access, and that access is injective on the box — the read-modify-write of
  one cell by its own iteration, which Bernstein permits and which `A[i] := A[i] + 1` needs.

`A[i] := A[i-1] + 1` is therefore **refused**, which joins the four existing encodings of the same
program (`Examples/Programs/MapArray.lean:59`, `Test/AutoParAlgo.lean:82`, `Test/Stress.lean:181`,
`Test/DependenceDistance.lean:33`) as the project's standing anti-vacuity witness.

### The second clause that was rejected: a skipped self-pair

The write-versus-write loop was first written `writes.all (fun w => writes.all (fun w' =>
w == w' || mapsDisjoint sizes w w'))`. The `w == w' ||` reads as a tautology guard and is the
opposite: in a parallel nest two *distinct* iterations both perform the same write, so `(W, W)` is
the pair that matters most, and skipping it accepted a write that collides with itself. The guard is
gone, and `mapsDisjoint sizes W W` reduces to `isRowMajor sizes W` — which is exactly the injectivity
a collision would have to violate.

This is the same error as `shiftedApart`, one level up: both quantified over the wrong pair. The
witness is `Test/Nest.lean`'s `collide`, whose coefficients ignore the outer index, so `(0,0)` and
`(1,0)` address one cell.

### What the certificate decides, measured

`Test/Nest.lean` elaborates in **0.59 s**, and that includes `by decide`s of `nestIndepB` over a box
of 10⁶ points and, for gemm, one of 10⁹. The same shapes written out instead cost 49.4 s at four
hundred points and are past an 8 s ceiling above that (`docs/bench.md` § Verification cost). The box
is never enumerated: the cost is in the number of
*declarations*, and at `N = 1000` the arithmetic is on three-element coefficient lists.

| shape | box | verdict | why |
|---|---|---|---|
| `C[i,j] := A[i,j] + B[i,j]` | 1000² | accepted | three disjoint buffers |
| `A[i,j] := A[i,j] + 1` | 1000² | accepted | the same access, row-major ⇒ injective |
| a read shared by a whole row | 1000² | accepted | there is no read-versus-read clause |
| `A[i+1] := A[i] + 1` | 1000 | refused | one buffer, distinct offsets — loop-carried |
| a write ignoring the outer index | 4×4 | refused | the self-pair, not injective |
| gemm, `(i,j)` forked | 1000³ | accepted | `C` outer-injective; `A`, `B` other buffers |
| gemm, `(i,j,k)` forked | 1000³ | refused | 1000 threads writing one cell |
| `A[i,k] := …`, `(i,j)` forked | 1000³ | refused | the write mentions a sequential level |
| a write escaping its buffer | 4×4 | refused | `boundsOK`, checked rather than assumed |
| `B[j,i] := …`, column-major | 4×4 | **refused, imprecisely** | injective, but not the stride vector |

The last row is the module's only false refusal, and it is gated so the count is measured rather
than claimed: a column-major write is injective on the box, so the unrestricted statement is true
and `isRowMajor` still declines it. Widening `mapsDisjoint` from "is the stride vector" to "is a
permutation of it" would close it; that is a change to the validator, not to the theorem.

`Test/Loop.lean` then gates the *constructor* in **0.99 s**: three `par_seq_eq` instances through
`by decide` on the certificate (one of them gemm's, over 10⁹ points), a 4×4 nest run on real
threads with its heap checked cell by cell, the induction registers carrying `lo + step * c`, and
the loop-carried nest refused at `d = 1` and accepted at `d = 0`.

The two gemm rows are the same nest with the same declarations; the forked depth is the only thing
that differs. Refusing `d = 3` is the right answer rather than a limitation — gemm's `k` loop is a
reduction, and MLIR's `isLoopParallel` declines it too — and accepting `d = 2` is what the whole-box
formulation could not do.

## The footprint a rolled nest reports

`Footprint` is `⟨List Loc, List Loc⟩` — concrete cell lists — and `wfB (.par ss)` decides
`indepAllB` on them. `Paralever/Theory/Intervals.lean` is the symbolic layer, but it is `Prop`-valued
and so not decidable. A rolled nest therefore cannot report a concrete footprint without
enumerating the N^d cells whose enumeration this whole file exists to avoid.

The resolution needs no new footprint type, because of where `footprintOf` is consulted:

* `wfB (.loop n)` **does not consult it**. A nest at the top level or in a `seq` chain — PolyBench's
  shape — is decided symbolically, at a cost independent of N. This is the case that matters.
* `footprintOf (.loop n)` falls back to each access's **span**: the cells from its base through
  `base + off + dotN coeffs (maxPoint sizes)`, the furthest the box can reach. This is the same kind
  of bound `.loadAt` and `.storeAt` already return through `ArrRef.cells`
  (`Lang/Core/Prog.lean:191`), so a nest *inside* a `parallel` block is no more approximate than a
  computed address already is.

`AffAccess.span` has to be the span rather than the declared buffer, and that is not a stylistic
choice. `execPar_accesses_sub` carries **no hypotheses** — it holds at every register file and every
heap — so the bound may not depend on `inBounds`, which `wfB` checks but `footprintOf` never sees.
`dotN_le_maxPoint` bounds the offset at every point of the box with nothing assumed, so
`addr_mem_span` is unconditional. Using `[base, base + size)` instead would have been a bound that
holds only for accesses the certificate accepted, which is precisely the wrong quantifier order.

`footprintExact (.loop _)` is `false`, because an empty box runs nothing while the span is still
non-empty.

So `parallel { nest, nest }` over large buffers is refused, and refused for a reason the refusal
taxonomy already names: an over-approximated footprint from a computed address. A symbolic
`Footprint` would fix it and is deliberately out of scope here.

## Rolling: how a front end builds a nest

Both front ends face the same problem and solve it the same way. A subscript has to be read
*symbolically* — as coefficients over the loop coordinates — where the unrolled route reads it as a
literal address, because the unrolled route is handed constant indices and the rolled one is not.

Everything after that symbolic reading is shared, and lives in `Lang/Core/Roll.lean`:

```text
                 .prl Exp            MLIR AffExp under an AffMap
                     │                           │
                 linOf (Lower)             linearOf (MLIR/Lower)
                     └─────────────┬─────────────┘
                                   ▼
                              Roll.Lin          off + Σ coeffs[k]·c_k, over Int
                                   │
                            Roll.rowMajor       one Lin per axis, against the shape's strides
                                   │
                           Roll.affAccess?      Int → Nat, or a refusal
                                   ▼
                            Nest.AffAccess
```

`Lin` is over `Int` while `AffAccess`'s coefficients are `Nat`, and the gap is deliberate: `A[n-1-i]`
is a perfectly good affine subscript this representation cannot hold, so it is **refused at the last
step** rather than wrapped silently into the wrong cell.

### A refusal is a fallback, not an error

Every step of the recognizer returns `Option`, and `none` means *this loop is unrolled* — the route
that was always there. So a shape the recognizer does not read costs precision at large sizes and
nothing at all at small ones. `Test/Roll.lean` gates each refusal with its cause, because "not
rolled" is otherwise invisible and a recognizer that refused everything would pass unnoticed:

| refused | why |
|---|---|
| `A[%r] := 1` | a computed subscript is heap-dependent — `scatter.prl`'s shape |
| `for i { parfor j { … } }` | `parDepth` is a *prefix*, so a fork under a sequential level is not one nest |
| `if` or `parallel` in the body | `NestStmt` has no branch for an access to hide behind |
| `for i { for j in i { … } }` | the sizes are folded before the loop variables are bound, so a non-rectangular nest does not fold |
| a named inner `parfor` | a nest has nowhere to carry a label; the outermost level's survives |

### `.prl`: `for` and `parfor`, unchanged in the source

No new surface syntax, and no new token spent. `for i in n { … }` and `parfor i in n { … }` already
*mean* a nest; above `Roll.maxUnroll` points they now compile to one. `parDepth` is read off the
leading run of `parfor` levels, so `parfor i { parfor j { for k { … } } }` is `d = 2` and needs no
`fork` keyword.

One thing changes inside `Env`. A loop variable is a compile-time constant on the unrolled route
(`consts`), and in a rolled nest it cannot be: it must be a *coordinate* in a subscript and a
*register* in a value. So `Env.ivRegs` holds the enclosing rolled nests' induction registers,
`Env.aexp` resolves a loop variable to that register, and `Env.fold` refuses it with a position —
which is what forces every subscript through the affine recognizer instead of through `Env.place`.
The registers come from `freshRegBase`, one past every occurrence in the file, so a nest's induction
variable cannot collide with the program's own `%7`.

### MLIR: `affine.for` is `d = 0`, `affine.parallel` forks

The one bit the two ops differ in is `parDepth`, and that is the whole translation. An
`affine.parallel` with *m* induced dimensions contributes *m* forked levels; an `affine.for`
contributes one sequential level. `peelAffine` walks the perfect nest collecting them, and the
innermost body is read op by op: `affine.load` and `affine.store` become the nest's accesses, and
**every other op goes through `lowerOp` unchanged** and must emit no statement. That is how
`arith.mulf`, the casts and `arith.constant` are reused rather than re-read — a pure arith op already
binds an `SVal` and emits nothing, so "emits nothing" is exactly the test for "this is arithmetic".

`lo` and `step` are kept as MLIR writes them, so a non-normalized `affine.for %i = 2 to 20 step 3`
is read without normalizing it: the subscripts are over the *coordinate* either way, and `lo`/`step`
only decide what the induction register holds.

**The non-constant-bound refusal stands**, and the plan was wrong to expect otherwise.
`LoopNest.sizes` is `List Nat`, so a trip count must be a literal. Rolling removes the *cost* of a
large trip count, not the need for it to be known — a symbolic trip count is a different and larger
change.

### The nest, out

`MLIR/Emit.lean` writes a nest back as `affine.parallel` over its forked prefix wrapping one
`affine.for` per sequential level. The subscript maps are reconstructed by dividing the flat
coefficients by the memref's row-major strides, outermost axis first (`splitAxes`); the division is
exact, since `Σ strides[j] · axis[j]` is the flat form it came from, so the reader's own `rowMajor`
recovers the access that was declared. `emitRoundTrips` compares memory, footprint, verdict and
heap — and passes for both a forked and a sequential nest (`Test/Roll.lean`).

A level whose induction register the body *reads as a value* gets an `arith.index_cast`, because
MLIR types a loop index `index` and a cell `i64`; a level that is only ever subscripted with gets
nothing.

### What rolling does not make cheap

Rolling makes `wfB` free. It does not make **running** the program free, and two places in the
report were running it.

`ParProg.verdictHere` calls `raceSites (execPar s ρ)`, which builds the whole `ParM` tree — 10⁹
nodes for a 1000³ gemm. But `wfB` accepting already settles that half **by theorem**:
`wfB_wellFormed` holds at every heap and the declared heap is one of them, so `raceSites` would
return `[]`. `verdictParts` now tests `wfB` first and emits the `every heap` line without a run. The
printed text is unchanged for every program; what changes is that the run does not happen.

The `rounds` line is a genuine *measurement* — `time` walks the program — and it is the one figure
in `checkReport` not proportional to the text. Above `roundsCeiling` it states `stepBound`'s closed
form and says it did not run, rather than hanging.

With both, a 1000×1000×1000 gemm written as four lines of `.prl` reports in **0.88 s**:

```text
  memory    A[1000, 1000] @0, B[1000, 1000] @1000000, C[1000, 1000] @2000000  (3000000 cells)
  threads   1000000
  rounds    not run — 4001000000 steps, over the ceiling of 10000000
  verdict   every heap  Proved: Yes — wfB accepts: the threads' footprints are pairwise independent
```

And `paralever prove` on the same file writes a Lean module whose

```lean
theorem big_par_seq_eq (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar src.prog ρ) (ParProg.execSeq src.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ
```

typechecks in **0.96 s**, `lean` startup included. The `decide` reduces `nestIndepB` over three
subscript maps; it never sees the box.

The curve, rather than the one point, is in `docs/bench.md` § Verification cost: the same shape
written both ways, at nine sizes, with `paralever prove` run and `lean` run on what it wrote. The
rolled side is **flat at 0.85–0.89 s from 64 points to 10⁹** — of which ~0.84 s is `lean` starting
and importing, so the proof itself is the remainder. The unrolled side is 1.87 s at 64 points,
6.4 s at 144 and **49.4 s at 400**, and past 400 points there is no number to compare against. At
the largest size where both can be measured the two differ by **58×**.

The 19 s at a hundred threads in `Examples/Programs/MatMul.lean` is a *different* term — a `ParM`
program whose footprints `decide` computes by unfolding definitions rather than a `.prl` file's
literal — so it is not that curve's unrolled column and the two should not be read as one. The
measurement above replaces it as rolling's comparison point, because it is the same shape through
the same front end at the same sizes.

### Where `toPrl` is still lossy

`Lang/Compile/Print.lean` writes a `.loop` in the Lean form's vocabulary, which `.prl` cannot read
back, so `roundTrips` does not cover a rolled nest. Printing one as `for`/`parfor` needs the inverse
of `rowMajor` — a subscript per axis from the flat coefficients, the same decomposition
`MLIR/Emit.lean` performs — and is not done. Named here rather than hidden: the MLIR direction round
trips and the `.prl` direction does not.

## Rolled is additive, never a replacement

A `maxUnroll` threshold decides which path a loop takes: below it, `for` and `parfor` are unrolled
exactly as they are today; above it, they lower to `.loop`. Nothing that currently elaborates
changes, which is the point — every pinned `#guard`, `#guard_msgs` and `by decide` in `Examples/`
and `Test/`, the twenty gates of `MLIR/Corpus.lean`, the twenty-two web snippets and the deck's
facets all keep their present values, and that they do is the test that the new path is additive.

The threshold is `128` points and is gated from both sides on one text with one number changed
(`Test/Roll.lean`): 128 points unroll, 129 roll. `Examples/Language/rolled.prl` is the first corpus
entry carried rolled, and it scores `proved` at every heap with the bench matrices otherwise
unmoved — which is the measurement that the new route is additive rather than the claim. The
twenty-eight-kernel run and the cost curve beside it are in `docs/bench.md`.

## Refused, not handled

* **Non-affine and heap-dependent subscripts.** `A[B[i]]` has no affine map, so no certificate.
  `Examples/Language/scatter.prl` stays the witness; the escape route is the injectivity hypothesis
  named at `docs/block-ir.md:143`, and it is not taken here.
* **A σ-dependent predicate.** `parAll_par_seq_eq_of_indexed_rw`'s bounds do not mention the heap,
  so a nest whose footprint depends on heap contents is outside it. Lifting the theorem, plus a
  frame argument that index cells are never written, is recorded as future work and not promised.
* **Unbounded loops.** `ParM` is inductive; `whileAtMost` remains the only `while`.
* **Tiling, skewing, any schedule search.** Paralever validates a parallelization; it does not look
  for one beyond `autoPar`'s greedy pass.
