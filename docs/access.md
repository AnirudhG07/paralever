# Footprints, independence, and `accesses`

Rationale for `Paralever/Core/Access.lean`.

## Bernstein, not `∗` — restated precisely

Independence of two footprints `(r₁,w₁)` and `(r₂,w₂)`:

```
w₁ ∩ w₂ = ∅   ∧   w₁ ∩ r₂ = ∅   ∧   w₂ ∩ r₁ = ∅
```

`r₁ ∩ r₂ = ∅` is deliberately **absent**. Matmul writes disjoint `C[i,j]` per iteration but reads
overlapping rows/columns of `A`/`B`; naive `∗`-disjointness rejects it, Bernstein accepts it.
`Label.conflicts` (`Core/Semantics.lean`) already encodes the single-step version of this: same
location, at least one write.

## `accesses` is a reference interpreter, not the operational semantics

`accesses p σ` must answer "what would `p` touch, run in isolation from `σ`" — this is the
*hypothesis* the metatheorem is about (theory.md §9). It is deliberately **not** derived from
`step`/`Reaches`, for two reasons:

1. `step` is nondeterministic (a `List` of successors); footprints need a single answer to state
   `Indep` against.
2. Computing "the actual outcome of a `par` node" requires *some* real values to feed its
   continuation — you cannot get a Bernstein footprint out of possible-worlds alone.

So `accesses` fixes a canonical **left-to-right sequential unfolding** as the reference execution
(mirroring `seqPair`), and records every location touched along it:

```lean
accesses : ParM α → State → Footprint
accesses (.par p q k) σ =
  let (a, σ₁) := runSeq p σ
  let (b, σ₂) := runSeq q σ₁
  accesses p σ ∪ accesses q σ₁ ∪ accesses (k (a,b)) σ₂
```

Note the asymmetry: `p`'s footprint is measured from `σ` (true isolation), `q`'s from `σ₁` (after
`p`'s reference effects). This is not a compromise we're stuck with — it disappears exactly when
`Indep` holds. If `p`'s writes lie outside `q`'s reads, `σ₁` and `σ` agree everywhere `q` looks, so
`accesses q σ₁ = accesses q σ` (a lemma to prove, used by `Theory/Decomposition.lean`). Independent
programs get true isolation; the asymmetry only shows up for programs the theorem doesn't apply to
anyway.

**Why this is total.** With `iter` gone, every `ParM` value is a finite tree, so `accesses` and its
helper `runSeq` are ordinary structural recursions — into `p`, into `q`, and into the continuation
applied to a concretely computed value (the same recursion-through-a-continuation pattern already
used by `bind`). No partiality, no fuel, no `Option`.

**What `accesses` is not claimed to be, yet.** That `accesses`'s footprint bounds every actual
`step`/`Reaches` execution is not built into the definition — it is `Theory/Decomposition.lean`'s
job to prove, under `Indep`, that the reference run and the real interleaved run agree. `Access.lean`
only defines the oracle and the Bernstein predicate on it.

## One trace feeds footprint, work, and span

A flat access log gives footprint and total operation count ("work") for free. It does **not**
give span (longest dependency chain) — that needs the `par`-branch structure preserved, since span
is `max` at a fork rather than `Σ`. Not built yet (cost is not on the critical path — see
`papers.md` §8, calf/decalf), but the representation is chosen so it can be added as another fold
over the same recursion shape rather than a rewrite: a `Trace` tree (`step : Label → Trace → Trace`,
`fork : Trace → Trace → Trace`) alongside `accesses`, with `footprint`/`work`/`span` as three folds
over it.

**Corrected claim from discussion:** parallel programs do not have *fewer total operations* than
their sequential counterpart — chunked sum still performs `n` additions either way. Work is
schedule-invariant (often equal, sometimes higher with combine overhead); **span** is what shrinks
with more threads. Do not conflate the two.
