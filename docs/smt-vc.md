# Verification conditions for an SMT solver

Code: `Lang/Smt/Ast.lean` (S-expressions), `Lang/Smt/Vc.lean` (the symbolic footprint and the
query), `Lang/Smt/Solve.lean` (running a solver and reading its answer). The command is
`paralever vc` — see `docs/cli.md`.

## What this is for

`wfB` computes a footprint from the syntax alone, so a computed address contributes *every* cell of
its buffer (`docs/block-ir.md`). Two threads that provably touch different cells of one buffer are
therefore refused, and `Examples/Language/scatter.prl` is the standing example. The exact check
closes the gap for one heap by running every schedule, which answers a different question — the
equivalence *at that heap*, not the theorem.

A verification condition closes it symbolically. The address a thread touches is an expression; the
obligation is that two threads' expressions never denote one cell; an SMT solver decides that for
the linear-integer fragment the language emits. The result is a third verdict path:

```text
                      concrete cells          computed cells
   wfB  (Lean, decide)   exact            ──►  every cell of the buffer   (over-approximate)
   vc   (SMT)            exact            ──►  the expression itself      (exact, if decidable)
   run  (interpreter)    this heap only        this heap only
```

## The solver is never shown a theorem of ours

This is the load-bearing property, and it is structural rather than fortunate. `Paralever/Lib/Loop.lean`
already proves the metatheorem for an indexed loop:

```lean
theorem parAll_par_seq_eq_of_indexed_rw (idxs : List κ) (body : κ → ParM τ)
    (Pr Pw : κ → Loc → Prop) (hnodup : idxs.Nodup) (hwf : …) (hbodyR : …) (hbodyW : …)
    (hww : ∀ i j, i ∈ idxs → j ∈ idxs → i ≠ j → ∀ l, Pw i l → Pw j l → False)
    (hwr : ∀ i j, i ∈ idxs → j ∈ idxs → i ≠ j → ∀ l, Pw i l → Pr j l → False) (σ) :
    ParSeqEq (ParM.parAll (idxs.map body)) (ParM.seqAll (idxs.map body)) σ
```

`hww` and `hwr` **are** the verification condition. Every other hypothesis is discharged already:
`hnodup` by `decide` on a literal thread list, `hwf` and the two confinement hypotheses by
`Lib/Block.lean`'s footprint lemma. So the solver fills a hole whose consumer is a Lean theorem, and
`par_seq_eq`, `wellFormed_canonical`, `runSeq_frame` and everything else in `Core/` and `Theory/`
stay on this side of the boundary. They cannot be the reason a query fails, because they are not in
the query.

What the solver must know is finite and closed:

| It needs | Where it comes from | How it is written |
|---|---|---|
| each buffer's base and length | `Layout` — already literals | folded into the term as numerals |
| what an address *is* | `ArrRef.addr a i = a.base + i.toNat % max a.len 1` | `(+ base (mod (ite (< i 0) 0 i) len))` |
| the index expression | `AExp`, eleven constructors (`Lib/Block.lean`) | one case each, below |
| which values are unknown | a `load` is the only source | `(declare-const uN Int)` |

Nothing else. `AExp` has exactly eleven constructors, so the list of things an encoder can meet is
closed rather than open-ended.

## The encoding, case by case

Lean's `/` on `Int` is **Euclidean** (`(-7)/2 = -4`, `7/(-2) = -3`, `(-7)/(-2) = 4`), which is also
SMT-LIB's `div`, so division needs no sign gymnastics — only the division-by-zero convention, which
Lean fixes at `0` and SMT-LIB leaves uninterpreted.

| `AExp` | SMT-LIB |
|---|---|
| `lit n` (`n < 0`) | `n` / `(- n)` |
| `add`, `sub`, `mul` | `+`, `-`, `*` |
| `min a b`, `max a b` | `(ite (<= a b) a b)`, `(ite (<= a b) b a)` |
| `div a b` | `(ite (= b 0) 0 (div a b))` |
| `lt a b`, `eq a b` | `(ite (< a b) 1 0)`, `(ite (= a b) 1 0)` |
| `not a` | `(ite (= a 0) 1 0)` |

`mul` whose operands are both non-literal is the only case that leaves the linear fragment; the
emitter detects it and declares `QF_NIA` instead of `QF_LIA`, saying so in the file's header rather
than downgrading silently.

### The wrap is semantics, not an artifact

`ArrRef.addr` reduces its index modulo the buffer's length, which is what confines a computed access
to its buffer with no hypothesis (`addr_mem_cells`, and the reason slicing needed no change in
`Core/`). The encoding reproduces the `mod` exactly, so no in-range premise is added: a collision
the wrap alone makes possible is a collision the interpreter makes too.

**That faithfulness has a measured consequence.** The index is `i.toNat`, so *every* negative index
is the buffer's first cell. A solver asked about two computed indices therefore answers `sat` with
both of them negative, every time, in preference to any more interesting model — and the answer is
correct. So a program whose computed index is not visibly nonnegative aliases at `base`, and that
is a fact about the language rather than about the query. `paralever vc --assume nonneg` is how a
reader asks the other question; it asserts `(>= uN 0)` for each unknown, which **weakens the claim**,
so the report names the assumption on its first line.

## From a program to a query

Registers are not memory, so they are substituted away. Walking one thread carries a map from
register to symbolic value, and the only thing that cannot be determined is a value read from the
heap:

```text
   %p := 2 * 1         ─►  env[p] = lit 2 * lit 1          a literal, after substitution
   %i := idx[t]        ─►  env[i] = opaque 0               a load: the one unknown
   dst[%i] := 1        ─►  writes += at dst (opaque 0)
```

A `Sym` is `AExp` with `reg` replaced by `opaque : Nat`: the type records that substitution has
happened. A register never assigned is a fresh unknown rather than zero, which keeps the query's
answer valid for every register file, as `wfB`'s is.

Each `parallel` block becomes one query. For threads *i* < *j*, the conflict condition is the
disjunction of `a = b` over the three Bernstein cross-products — W×W, W×R and R×W — and the fork is
independent exactly when that disjunction is **unsat**:

```text
   (assert (or (= addr_w0 addr_w1) (= addr_w0 addr_r1) … ))
   (check-sat)        unsat ─► independent        sat ─► a model, and a candidate race
```

Pairs where both addresses are concrete are decided here, not sent: that is `disjointB`'s job and it
is already exact. Only a pair with at least one computed address reaches the solver, which keeps a
twelve-thread query small and makes the division of labour legible — `wfB` owns concrete cells, the
solver owns computed ones.

## Trust, which is asymmetric

**`sat` costs nothing, and it is not a race.** The model assigns a value to each unknown, and
`Sym.evalWith` substitutes it back into the symbolic addresses to recompute the collision *in Lean*
(`Smt.witness`), so the two cells the report names are named on our own arithmetic. But an
assignment is not a run: nothing says any reachable heap holds those values, so a `sat` is the
obligation **failing**, reported as `inconclusive`, never as `RACY`. Only a real interleaving earns
that word, and `paralever race` is what looks for one. Turning a model into an interleaving needs a
heap witness and is not done; `Search/RaceSearch.lean`'s `findWrongGuided` is where it would go.

**`unsat` is not a Lean proof.** An external solver's refutation is not checked by Lean's kernel, so
a verdict obtained this way is reported as *discharged by* the solver it came from, naming the
solver and its version, and never as `PROVED`. Three futures, in increasing cost: keep the label;
reconstruct the refutation from a proof certificate (Alethe, lean-smt); or use `unsat` as a filter
that says a Lean proof exists before one is attempted. The label is what is implemented.

## What it gains, measured

`Examples/Language/stripe.prl` is the file this exists for: two threads write the even and the odd
cells of one eight-cell buffer, with both indices loaded from memory.

| | answer |
|---|---|
| `paralever stripe.prl` | `this heap` proved; `any heap` **RACE found** at `k[1] = -1` |
| `paralever vc stripe.prl --solve --assume nonneg` | *independent* — unsat, for every heap satisfying the hypothesis |

`wfB` cannot do better, because both threads' syntactic footprint is all of `A`. The solver's work
is one line of arithmetic — `2k` is never `2m+1` — and z3 5.3.1 answers in under 10 ms.

The hypothesis is the whole of it, and the first row is how that became visible: without
`--assume nonneg` the claim is false, and the general-heap search of `docs/general-heap.md` now finds
the counterexample in Lean, by changing one cell. So this file measures what a solver buys *under a
stated hypothesis* — not what it buys over Lean, which on the unrestricted statement is nothing,
because the unrestricted statement does not hold.

Two further measurements, both from `Test/Smt.lean`, bound what the solver is actually for:

* **An unrolled `parfor` needs no solver.** `parfor t in 4 { %p := t ; s[%p] := 65 }` has `wfB =
  false`, and `obligations` returns `independent`: `t` is a literal after unrolling, so `Sym.fold`
  reduces the index and `SAddr.norm` turns the computed address into the cell it names. Most of the
  over-approximation gap closes in Lean, and the solver sees only the residue.
* **`scatter.prl` stays `sat`.** The indices are loaded and nothing in the text constrains them, so
  the obligation is genuinely satisfiable — see the boundary below.

## Lean closes the same arithmetic

The queries this emitter writes are linear integer arithmetic over a handful of unknowns, and that
is a fragment `grind` decides. Measured on the three shapes the pilots produce, with the in-range
facts in hand:

| obligation | closed by |
|---|---|
| `2 * a % 8 ≠ (2 * b + 1) % 8` over `Nat` — `stripe.prl` | `grind` |
| the same over `Int` under `0 ≤ u`, through `ArrRef.addr` | `grind` |
| `A.addr u ≠ A.addr v` from `0 ≤ u, v < 3`, `u ≠ v` — the scatter shape | `grind` |
| the `stripe` shape with no bound on the unknowns | fails, correctly — the clamp aliases |

So the two lemmas live in `Paralever/Lib/ArrRef.lean` rather than in a solver's answer:
`ArrRef.addr_ne` and its contrapositive `ArrRef.eq_of_addr_eq`, distinct in-range indices addressing
distinct cells. Both go through `grind`, and both need the wrap rewritten away first — a bare
`grind [ArrRef.addr]` stops at `max a.len 1` with the two clamp branches open, which is the same
branch z3 reported as its model. `omega` cannot finish either: at the rewritten goal it drops
`i ≠ j` and reports no usable constraints.

`Examples/Language/Stripe.lean` is that carried through on the file the VC path exists for: the
program written by hand, gated against `stripe.prl`, and `par = seq` proved for *every* heap whose
two indices are cells of `A`'s halves — the statement `--solve --assume nonneg` was being asked for,
with no solver in it. The same module records why the hypothesis cannot be dropped: at `k = [-1,-1]`
the clamp sends `2 * (-1)` and `2 * (-1) + 1` both to `A[0]`, `wellFormedB` is `false`, and the
unrestricted `par_seq_eq` is not unproved but **false**. z3's `sat` was right — and
`ParProg.verdictAnywhere` now finds the same heap without a solver, at the smaller witness
`k[1] = -1`, which the report prints as the `any heap` half of the verdict
(`docs/general-heap.md`).

What that leaves the solver is the shapes `grind` does not close — several unknowns under an
invariant, or nonlinear products — and what it leaves open is the bridge. `Lib/Loop.lean`'s
`parAll_wellformed_of_indexed_rw` and `parAll_par_seq_eq_of_indexed_rw` take σ-*independent*
footprint predicates (`Pr Pw : κ → Loc → Prop`, with the `∀ σ` inside `hbodyR`/`hbodyW`), so an
address that depends on the heap cannot be bounded by them. Carrying `addr_ne` through to
`par_seq_eq` needs a theorem with σ-dependent predicates plus a frame argument that the index cells
are never written — new work, not an instantiation.

## Boundaries

**A heap-dependent index stays heap-dependent.** In `scatter.prl` the index is loaded, so the
unknowns are unconstrained and the query is satisfiable — correctly, because nothing in the program
text makes `idx` injective. What improves over `paralever check` is the form of the answer: the
report names the assignment that collides (`dst[0]` when `u0 = u1 = 0`) and what each unknown is
(`u0  the value read from idx[0]`), so the missing hypothesis is visible rather than inferred.
Adding `(assert (distinct u0 u1 u2))` to the emitted file by hand makes z3 answer `unsat`, which is
the right answer and the right amount of honesty about where it came from. `--assume` states only
`nonneg` today; an invariant over several unknowns has to be written into the file, and the
placeholder block the emitter leaves is where it goes.

**A `sat` is not replayed.** The collision is recomputed in Lean, which certifies the arithmetic but
not the reachability: a model satisfying the stated assumptions need not correspond to any heap the
program can be run on. Turning a model into an interleaving is the remaining half.

**A branch is over-approximated, as in `footprintOf`.** `ifElse` contributes both branches'
footprints, and a register either branch assigns becomes a fresh unknown afterwards. Path conditions
would be more precise and are not encoded. A fork whose threads contain a branch is marked
`Vc.approx`, and the consequence is reported rather than hidden: two threads sharing a known cell
is a *race* when the footprint was computed and only `inconclusive` when it was widened, because
the two accesses may be branches that never both run. The flag is per fork, so a branch elsewhere
in the program does not weaken a fork that has none.

**A nested fork contributes to its parent and is also queried on its own**, matching `footprintsOf`
and `wfB` respectively. Register updates inside a `parallel` block are private and discarded, which
is `execPar`'s own rule for `.par`, so a nested fork perturbs no substitution.

## Why not replace `wfB`

`wfB` is decided by the kernel, needs no external program, and is what `paralever prove` emits a
theorem about. The VC path needs a solver on the machine and yields a labelled verdict. They answer
the same question at different precisions and different levels of trust, so the tool runs `wfB`
first and offers the VC for what `wfB` refuses. -- ref: Barrett et al., *CSLib* (arXiv 2602.04846)
§ Boole, for the same obligation-generation architecture at a much larger scale.
