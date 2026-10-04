# The pure ↔ `ParM` bridge

Rationale for `Paralever/Lib/Pure.lean`. Code references this file as `docs/pure-bridge.md`.

## The question

A user's algorithm is naturally a **pure function of the heap**: "look at these cells, fold them
together." Nobody wants to write a reduction as a tree of `.read` nodes. But `ParM` is exactly what
makes the memory accesses *visible as data* (`docs/program-model.md`), and visibility is the whole
mechanism — a pure `Int → Int` has no footprint, so there is nothing for `accesses` to find and
nothing to prove disjoint.

So the conversion is unavoidable. The question is whether it is **trustworthy**:

> If I rewrite my pure algorithm as a `ParM` program, how do I know the rewrite preserves meaning?

`Examples/SumArray.lean` answers this by hand, and that answer is the model for this file:

```lean
def sumRangePure (σ : State) : List Loc → Int        -- the algorithm
def sumRange : List Loc → ParM Int                   -- the ParM conversion
theorem sumRange_eq_sumRangePure :                   -- the conversion is faithful
    (runSeq (sumRange locs) σ).1 = sumRangePure σ locs
```

That third declaration is the load-bearing one, and before this file it was written per example. Here
it is proved once.

## The split: *what* to combine vs. *where* to read

The conversion becomes mechanical once the algorithm is separated into two independent pieces:

| piece | type | nature |
|---|---|---|
| **what to combine** | `f : List Val → α → α` | pure, arbitrary, never inspected |
| **where to read** | `locs : Nat → List Loc` | the layout — arithmetic only |

`readsCombine locs f k acc` is then "read `locs k`, fold the values into `acc`", and the pure
specification `foldPure σ locs f` is the same thing with `σ` applied directly instead of read. The
bridge theorem says they agree:

```lean
theorem reduceFold_eq_foldPure (locs) (f) (σ) : ∀ fuel k acc,
    (runSeq (reduceFold (readsCombine locs f) fuel k acc) σ).1 = foldPure σ locs f fuel k acc
```

`locs k` is a **list**, not a single location, so one step may read several cells — matmul's step
reads one from `A` and one from `B`. `readAll` (from `Lib/OpaqueOp.lean`, reused rather than
duplicated) does the reading, and its footprint `⟨R, []⟩` and lookup `runSeq (readAll R) σ = (R.map σ, σ)`
are already proved there.

## Why this collapses the proof obligation

`reduceArray_par_seq_eq` (`docs/reductions.md`) takes five hypotheses. For a `readsCombine` body,
three of them are *generic facts about the shape* and are discharged here once and for all:

| hypothesis | for a general body | for `readsCombine` |
|---|---|---|
| `hwf` | per-example | `readsCombine_wellformed` |
| `hreads` | fuel induction + `Val` case splits | `readsCombine_readsWithin` — one list membership |
| `hnowrite` | per-example | `readsCombine_no_writes` — the accumulator is pure |
| `hdstinj` | `omega` | `omega` |
| `hdstout` | `omega` | `omega` |

`reduceArrayPure_par_seq_eq` therefore asks the caller for **three arithmetic facts and nothing
else** — where the reads land, that outputs are distinct, that outputs avoid the read region. No
footprint induction and no `Val` analysis survives at the call site. `Examples/PureToParM.lean` is
the worked instance (row sums), and its two `rfl` checks confirm the generated program computes the
right values, not merely a well-typed term.

## What this does and does not automate

**Does:** the footprint reasoning, the faithfulness proof, and the independence assembly, for any
fold whose read locations are a function of the indices.

**Does not:** write `locs` for you. The layout — which cell is `A[i,j]` — remains a human decision,
and deliberately so: it is a data-structure choice, not a proof obligation, and it is precisely the
choice that turns undecidable alias analysis into `omega` (`docs/reductions.md` on the polyhedral
bargain).

**Does not:** inspect the user's Lean term. `f` is passed as a function, not parsed. A genuine
source-to-source elaborator — take a pure Lean definition over arrays, *read its syntax*, emit the
`ParM` version plus the faithfulness proof — is a further step, and the natural next milestone. The
combinator approach here gets the same guarantees without any reflection, which is why it comes
first.

**Does not:** cover data-dependent reads. `locs` may depend on the indices `p`, `k`, never on values
already read, so `A[B[k]]` stays out of scope — the same boundary as `docs/opaque-ops.md` and
`docs/reductions.md`, earmarked for `Logic/`.

## Relationship to `SumArray.lean`

`sumRange` folds over an arbitrary `List Loc` with `foldr`; `reduceFold` folds over a `Nat` index
range with fuel. Neither subsumes the other, and `SumArray.lean` is kept as-is: it is the
self-contained pedagogical statement of *why* a faithfulness theorem is needed, with the induction
visible. This file is the reusable version for the index-range shape, which is the one every
reduction example actually has.

## References

- Blom, Darabi, Huisman, Safari, *Correct Program Parallelisations*, STTT 23(5) 2021 — the main
  result is that **functional correctness of the sequential program implies correctness of the
  parallelised program**, given per-block contracts. That implication is only usable if one has the
  sequential program *and* a link to the parallel one; `reduceFold_eq_foldPure` is that link,
  mechanized. `papers.md` §2.2 notes their work is tool-supported but not proof-assistant
  mechanized.
- Bocchino, Adve et al., *A Type and Effect System for Deterministic Parallel Java*, OOPSLA 2009 —
  the effect-annotation discipline the `locs`/`f` split mirrors: effects are declared structurally,
  the computation itself is unconstrained.
- Xia et al., *Interaction Trees*, POPL 2020 — the freer representation that makes a `ParM` program
  interpretable in several ways at once, hence both `runSeq` (meaning) and `accesses` (footprint)
  over one term.

Full list in [`../papers.md`](../papers.md).
