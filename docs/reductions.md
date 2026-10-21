# Reductions: `Σ`-shaped loops with a pure accumulator

Rationale for `Paralever/Lib/Reduce.lean`. Code references this file as `docs/reductions.md`.

## The pattern, and why it deserves a combinator

`Kernels/MapArray.lean` collapsed the elementwise case — `Out[i] := f(In[i])` — from ~30 proof lines
to one. The *other* pervasive shape is a reduction:

```
for each p in parallel:
    acc := init
    for k in [0, m):  acc := combine(acc, <locations determined by p and k>)
    Out[p] := acc
```

Matmul is this (`C[i,j] = Σ_k A[i,k]·B[k,j]`), as is every dot product, row sum, norm, histogram bucket,
and `argmin`. Before this file, `Examples/Programs/MatMul.lean` spent most of its length on two footprint inductions over
the fuel parameter that are *entirely mechanical*: same `Val` case splits, same `ReadsWithin.union` chains, same shape any other
reduction would reproduce verbatim.

## The one structural fact that makes reductions easy

**The accumulator lives in a pure value, not in the heap.** In `dotStep`, `acc : Int` is an ordinary
Lean term threaded through the recursion; it is never a memory cell. Consequence:

> the entire inner loop contributes **reads only — zero writes**.

That is the whole reason reductions parallelize so cleanly, and it is worth stating because the
"obvious" alternative — accumulating into `Out[p]` with a read-modify-write per step — would produce
`m` writes per iteration instead of one, and would need its own frame reasoning to show those writes
don't escape. Keeping the accumulator pure means the write set of one whole reduction is a *single
location*, and `Indep` only ever checks writes.

So the independence obligation for `N` parallel reductions decomposes into exactly two facts, both
arithmetic:

1. `dst` is injective on `[0,N)` — distinct outputs are distinct cells (write/write);
2. no `dst p` satisfies the read predicate — outputs are disjoint from inputs (write/read).

Read/read overlap is *unconstrained*, which is essential: every cell in a row of matmul reads the
same row of `A`. This is the Bernstein-not-`∗` point (`docs/access.md`) in its sharpest form.

## What the user supplies

`reduceArray_par_seq_eq` takes, per iteration body:

| hypothesis | meaning | typical proof |
|---|---|---|
| `hwf` | the body is well-formed | `trivial` (no `par` inside a body) |
| `hreads` | the body's reads satisfy `Pr` | one `omega`/`grind` on index arithmetic |
| `hnowrite` | the body writes nothing | `rfl` when the accumulator is pure |
| `hdstinj` | `dst` injective on `[0,N)` | `omega` |
| `hdstout` | `¬ Pr (dst p)` | `omega` |

and nothing else. The fuel-induction that used to be written per example is discharged once here
(`reduceFold_readsWithin`, `reduceFold_no_writes`).

Note that `hreads`/`hnowrite` are stated `∀ σ'`, not for one fixed state. A reduction body reads
addresses computed from indices, not from values it read, so its footprint genuinely does not depend
on the state — and quantifying that way means the caller never has to reconcile "measured from `σ`"
against "measured from `(runSeq … σ).2`" as the fold threads state through.

## Scope and limits

**Static index-to-address maps only.** The body may read any locations it likes *as a function of the
indices* `p` and `k`. It may not choose addresses from values it has read — `A[B[k]]` is out of
scope, because then `hreads` cannot be a fact about arithmetic. This is the same data-dependent-
footprint boundary `docs/opaque-ops.md` hits, earmarked for `Logic/` (DCSL-lite).

**One output cell per iteration.** A reduction writing several cells needs `Pw` as a predicate rather
than a single `dst`; `Lib/Loop.lean`'s `parAll_par_seq_eq_of_indexed_rw` remains the escape
hatch for that, and this file is a specialization of it, not a replacement.

**No cross-iteration combination.** This parallelizes `N` *independent* reductions. It does not
parallelize one reduction internally (tree reduction over `k`), which would need the combining
operation to be associative — a genuinely different theorem, and a natural next step.

## Why a specialization rather than a new primitive

`reduceArray_par_seq_eq` is proved *through* `parAll_par_seq_eq_of_indexed_rw` with
`Pr := fun _ => Pr` and `Pw := fun p l => l = dst p`. Nothing new is axiomatized and no `Core/`
induction gains a case — the same reason `mapArray` is a specialization and the same reason N-ary
parallelism is derived from binary `par` rather than given a constructor
(`docs/program-model.md`).

## References

- Blom, Darabi, Huisman, Safari, *Correct Program Parallelisations*, STTT 23(5) 2021 — per-block
  contracts and **iteration contracts encoding data dependences**, which is precisely the
  `hreads`/`hnowrite`/`hdstinj` triple above; their result (sequential correctness implies
  parallelised correctness, given those contracts) is this theorem's shape. `papers.md` §2.2 records
  that their work is tool-supported but *not* mechanized in a proof assistant — the gap this file
  narrows.
- Bocchino, Adve et al., *A Type and Effect System for Deterministic Parallel Java*, OOPSLA 2009 §2
  — `commutes`/reduction effects over disjoint regions.
- Li, Liang, Feng, *Verified Validation for Affine Scheduling*, TASE 2024 — Bernstein's conditions
  mechanized generically; the write/write and write/read checks above are its two non-vacuous cases.

Full list in [`../papers.md`](../papers.md).
