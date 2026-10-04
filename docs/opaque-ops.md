# Opaque operations: parallelism whose bodies we never read

Rationale for `Paralever/Lib/OpaqueOp.lean`. Code references this file as `docs/opaque-ops.md`.

## The problem

Every example so far builds its program out of `.read`/`.write` and then proves a footprint bound by
an induction mirroring the program's own recursion (`MatMul.dotStep_readswithin` is the template).
That works, but it presumes two things:

1. the computation **is** a `ParM` term we can induct over, and
2. the induction is tractable.

Neither holds for "I have two agents doing complicated disjoint things." The body may be a solver, a
learned model, a library call, or simply 400 lines whose footprint induction nobody wants to write.
The user's claim is not about the body at all — it is *"this one touches these locations, that one
touches those, and they don't overlap."*

## Three tiers of trust

The question "can the user just assert independence?" has three different answers, and keeping them
distinct matters because they are not equally sound.

| Tier | Mechanism | What is assumed |
|---|---|---|
| 0 | `Indep`/`WellFormed` as a theorem *hypothesis* (`Independent.mk`) | nothing — it is a conditional |
| 1 | `opaqueOp R W f` — declare the footprint, **derive** it | nothing — the footprint is proved |
| 2 | `axiom myFn_footprint : FootprintWithin (accesses myFn σ) P` | the annotation, untested |

Tier 0 already worked before this file existed: `par_seq_eq` takes `WellFormed (parPair p q) σ` as a
hypothesis, so a user can parameterize over it and push the obligation to the call site.
`Lib/Notation.lean`'s `Independent` is a structure precisely so it can be built field by field when no
smart constructor fits. Nothing false is assumed; the theorem is just conditional.

Tier 2 is the DPJ model — the programmer writes region annotations and a *separate* mechanism checks
them (DPJ: a type system; here: nothing yet, so an `axiom`). Sound exactly when the annotation is
true, which Lean cannot know. Property tests (`Plausible`) are the honest mitigation: you cannot
prove the annotation, but you can falsify it on random states.

**Tier 1 is this file, and it is the one worth having**, because it needs no axiom.

## Why Tier 1 needs no axiom

The move is to stop modelling the body and model only its *interface*. An operation that reads
locations `R` and writes locations `W` has a net effect on the heap that is some function from `R`'s
values to `W`'s values. So represent it as exactly that:

```lean
def opaqueOp (R W : List Loc) (f : List Val → List Val) : ParM Unit :=
  ParM.bind (readAll R) (fun vs => writeAll (W.zip (f vs)))
```

`f` is an ordinary pure Lean function — universally quantified, never inspected, arbitrarily complex.
And now the footprint is not an annotation to be trusted but a theorem:

```lean
theorem opaqueOp_accesses (R W) (f) (σ) :
    (accesses (opaqueOp R W f) σ).reads = R ∧
    ∀ l ∈ (accesses (opaqueOp R W f) σ).writes, l ∈ W
```

The complexity has been quarantined somewhere it cannot matter. This is the same reason
`parMap_par_seq_eq` is unconditional: **pure functions have no footprint**, so the hard part of the
program is irrelevant to the independence obligation rather than hidden from it.

Independence between two opaque ops is then pure list reasoning on `R`/`W` that never mentions `f`
(`opaqueOp_indep`), and `Independent.of_declared_footprint` packages the whole thing.

### Reads are exact, writes are an over-approximation

`reads = R` on the nose; writes only `⊆ W`, because `W.zip (f vs)` truncates when `f` returns fewer
values than `W` has slots. This asymmetry is deliberate and is the *sound* direction: a footprint
that claims more writes than occur can only make `Indep` harder to prove, never easier. Over-
approximating effects is the standard soundness condition for effect systems (DPJ §3), and matching
it here means a user who declares `W` too large gets a weaker theorem rather than a wrong one.

### Why the coarse grain is sound

`opaqueOp` fixes one schedule shape — all of `R` read, then all of `W` written — whereas the real
computation presumably interleaves. That does not weaken the theorem, for Reynolds' reason: races go
to an absorbing `wrong`, so **the choice of atomic grain is irrelevant** for programs the theorem
applies to (FSTTCS 2004; `docs/semantics.md` for how `wrong` is wired here). Independence is a
property of the *location sets*, and those are identical at any grain. A conflicting pair conflicts
in the coarse model too, so race detection is not blunted either.

What the coarse grain *does* lose is intermediate states: `opaqueOp` says nothing about what the heap
looks like partway through. Since `ParSeqEq` quantifies over reachable `(result, final-state)` pairs
only, that is not information the theorem needs.

## Limits

**Static footprints only.** `R` and `W` are fixed lists. A computation whose touched locations depend
on values it reads — indirect indexing `A[B[i]]`, pointer chasing, a work-stealing queue — has no
static `R`/`W`, and over-approximating to "the whole array" usually destroys the disjointness the
user wanted. This is the Tier-2 case `CLAUDE.md` earmarks `Logic/` (DCSL-lite) for, and it is not
solved by this file.

**Footprint must be known, even if the body is not.** `opaqueOp` buys ignorance of *how* the
computation works, never of *where* it reaches. A user who cannot name `R` and `W` has nothing to
declare, and no abstraction here will help.

## Why not the alternatives

**A new `ParM` constructor for opaque effects** (`| op : List Loc → List Loc → (…) → ParM α`) would
give exact declared writes instead of `⊆`, but costs an extra case in *every* induction in `Core/`
and `Theory/` — `accesses`, `runSeq`, `WellFormed`, `step`, and all of `wellFormed_canonical`. The
derived encoding above needs none of that and is strictly cheaper. Rejected on cost, and the same
reasoning that removed `iter` (`docs/program-model.md`) applies.

**`axiom` per function** is Tier 2 and remains available for the case where the user insists on
keeping the real `ParM` term. It is a trusted annotation, so it is documented as such rather than
dressed up as a proof.

## References

- Bocchino, Adve et al., *A Type and Effect System for Deterministic Parallel Java*, OOPSLA 2009
  §2–3 — region-based read/write declarations, effect over-approximation, and the non-interference
  soundness theorem. `papers.md` §2.1 records the decision: "If our DSL carries footprint
  annotations, this is the design to copy."
- Reynolds, *Toward a Grainless Semantics for Shared-Variable Concurrency*, FSTTCS 2004 — races as
  absorbing `wrong`, hence grain-irrelevance; why the coarse read-then-write shape is sound.
- Brookes, *A Semantics for Concurrent Separation Logic*, CONCUR'04 §5–7 — the decomposition lemma
  the whole `ParSeqEq` result rests on.

Full list in [`../papers.md`](../papers.md).
