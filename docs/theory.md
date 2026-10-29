# The theory behind Paralever

Written to be read start to finish, assuming no background in separation logic. Each section ends
with **→ In our code**, tying the idea to a file. Questions to test yourself are marked **Q**.

Papers with links: [`../papers.md`](../papers.md).

---

## 0. The problem

You have a sequential program:

```
sum = 0
for i in 0..n:  sum += A[i]
```

and a parallel one: split `A` into `k` chunks, sum each chunk on its own thread, add the partials.

Everyone *believes* these agree. We want a machine-checked proof — and not one proof per program,
but **one theorem** that covers all such pairs, leaving a small, per-program side condition.

Two things make this hard.

**(1) Interleaving explosion.** With `k` threads of `m` steps each, the number of interleavings is
astronomically large. Any proof that reasons about "all the ways this could interleave" directly is
dead on arrival. The whole game is to *avoid* reasoning about interleavings.

**(2) Stating it at all.** "Same output" needs a semantics precise enough to compare a
nondeterministic program with a deterministic one.

The literature's answer to (1), in one line:

> If the threads don't interfere, then **every** interleaving gives the same answer as the
> sequential order. So prove non-interference once, and interleaving stops mattering.

Everything below is machinery for making "don't interfere" precise and proving that implication.

---

## 1. Hoare logic — the starting point

A **Hoare triple** `{P} C {Q}` reads: *if `P` holds before running `C`, and `C` terminates, then
`Q` holds after.* `P` is the precondition, `Q` the postcondition.

```
{x = 5}  x := x + 1  {x = 6}
```

Rules compose. Sequencing:

```
{P} C₁ {R}    {R} C₂ {Q}
─────────────────────────
     {P} C₁; C₂ {Q}
```

This is *compositional*: to verify `C₁; C₂` you verify each piece separately and glue. That
property is what we want for `∥`, and it is exactly what naive approaches lose.

**Why plain Hoare logic fails for the heap.** With pointers, `{x = 5} [p] := 7 {x = 5}` is only
valid if `p` doesn't point at `x`. Every proof drowns in "and these pointers are different"
side conditions. This is the **frame problem**.

**Q1.** Why is `{P} C₁ {R}, {R} C₂ {Q} ⊢ {P} C₁;C₂ {Q}` insufficient for `C₁ ∥ C₂`? What can `C₂`
do that breaks the reasoning for `C₁`?

**Ans:** Consider `{x = 5} [p] := 5 {x = 5}, {x = 5} [p] := 8 {x = 5}`, now if `C₁` and `C₂` run in parallel, they can both write to the same location pointed by `p`(which is `x`), for `C₁` it is fine, but `C₂` will change the value of `x` to 8. If `C₂` runs first, then `C₁` will read the value of `x` as 8, which is not equal to 5. Hence it is insufficient for `C₁ ∥ C₂`.

---

## 2. Separation logic — ownership as the fix

Separation logic (Reynolds, O'Hearn, Ishtiaq, ~2001) adds one connective.

- `l ↦ v` — "the heap consists of *exactly* one cell, at address `l`, holding `v`." Note
  **exactly**: this is an assertion of ownership, not just a fact.
- `P ∗ Q` — **separating conjunction**: the heap splits into two *disjoint* pieces, one satisfying
  `P`, the other `Q`.

So `l₁ ↦ 3 ∗ l₂ ↦ 4` says: two cells, and **`l₁ ≠ l₂` is implied**, not assumed. Disjointness is
baked into the connective instead of being a side condition.

The payoff is the **frame rule**:

```
      {P} C {Q}
────────────────────────   (C doesn't modify variables free in R)
{P ∗ R} C {Q ∗ R}
```

*If `C` works with only `P`'s worth of heap, then any extra heap `R` is untouched.* You verify `C`
against the smallest heap it needs — its **footprint** — and the rest comes free. This is local
reasoning.

**Q2.** Why is `l ↦ v` "exactly one cell" rather than "at least this cell"? What breaks in the
frame rule if you weaken it?

**→ In our code.** We don't need the full logic to state the theorem, but the *idea* — footprints,
and disjointness as part of the structure — is everything. Tier 2 (`Logic/Rules.lean`) states Hoare
triples directly against `Reaches` and frames with `∧` over `Core/Access.lean`'s footprints. It does
not instantiate a `BI`: § 8 explains why `∗` is the wrong connective for a project whose
independence relation permits shared reads.

---

## 3. Concurrent separation logic — the rule that is our theorem

O'Hearn (CONCUR'04) noticed the frame rule's idea applies to parallelism. If two threads own
*disjoint* heaps, they cannot interfere:

```
{P₁} C₁ {Q₁}    {P₂} C₂ {Q₂}
──────────────────────────────
 {P₁ ∗ P₂}  C₁ ∥ C₂  {Q₁ ∗ Q₂}
```

**This is the whole idea of the project.** Read it carefully:

- The premises are about `C₁` and `C₂` *in isolation*. No interleaving appears anywhere.
- The `∗` in `P₁ ∗ P₂` is the price: you must split your heap before you fork.
- The conclusion recombines the results.

Verifying a parallel program becomes: verify each thread alone, then exhibit a heap split. The
interleaving explosion never happens.

O'Hearn calls the underlying principle the **Ownership Hypothesis**: *a program component only
accesses cells it currently owns.*

**How this connects to our code — by derivation, not by a separate proof.** Paralever never proves
this rule's soundness on its own terms. It proves `par_seq_eq` (§5, §9) as the primitive fact, and
the Hoare-triple layer (`Logic/Rules.lean`) is a thin derivation *on top of* that fact, not an
independent verification standing next to it. Concretely, `Triple.par`'s proof body is one call to
`wellFormed_canonical`: given `{P} C {Q}` and `{P'} C' {Q'}` valid against the real `Reaches`
relation, and `WellFormed (parPair C C') σ` (Bernstein independence checked at *every* nesting
level, not only the outermost `par` — §9's counterexample is exactly why the outermost check alone
would be unsound), `wellFormed_canonical` says the only state `parPair C C' σ` can ever reach is the
canonical `runSeq` value, which *is* "run `C` fully, then run `C'`" — so the two triples compose
directly. One detail worth flagging: the frame side condition here is stated with `Local`/`Disjoint`
predicates over locations, not a separating `∗` (a BI's `∗` is *exclusive*
heap-split, strictly narrower than `Indep` — see §8 — so using it here would silently reintroduce
the very restriction Bernstein exists to lift). The upshot: "did we prove CSL sound" is the wrong
question to ask about this codebase — soundness here is a *corollary* of `par_seq_eq`, checked once,
not a second theorem independently re-derived and then found to agree with the first.

### Shared resources, and why the equality stops there

CSL is not only the disjoint rule. It also has resource declarations and critical regions,

```
resource r in C                    with r when b do C                    R_r
```

with the **critical-region rule**

```
        {(P ∗ R_r) ∧ b}  C  {Q ∗ R_r}
        ─────────────────────────────────
        {P}  with r when b do C  {Q}
```

Between regions the invariant `R_r` is owned by *no* thread; entering acquires it, and the body must
restore it before release. That mechanism is ownership **transfer**, and it is how CSL verifies
genuinely shared state — the disjoint rule governs what each thread owns privately, `R_r` governs
what they hand back and forth.

**In that fragment our theorem is not merely unproved — it is false.** Two threads communicating
through a resource-protected cell:

```text
C₁ = with r do x := x + 1          C₂ = with r do y := x

   parallel  C₁ ∥ C₂                    sequential  C₁ ; C₂
       ┌──────┴──────┐
     x:=x+1       y:=x                     x:=x+1 ──► y:=x
       └──────┬──────┘
      y ∈ {pre, post}                      y = post, always
```

The parallel composition admits two outcomes, the sequential one admits one, so the outcome *sets*
differ and `ParSeqEq` fails. CSL verifies both programs — each satisfies its triple — because
soundness never asserts that the two compositions agree.

This is the answer to "why did everyone prove soundness and not equality". For *their* language
equality is false, so soundness is the strongest statement available. Equality becomes a theorem
only once ownership transfer is removed, and isolating that fragment was not their goal.

We have the mechanised half of the counterexample: `Examples/Races/Caught.lean`'s
`DetectedRace.not_parSeqEq` proves `¬ ParSeqEq` the moment two children share a written cell, and
`OrderDependent.not_parSeqEq` does it with *both* sides terminating normally. So the restriction is
not a modelling convenience — it marks where the theorem stops holding.

Two further points fix the boundary precisely. First, a critical region is not even expressible
here: `read` and `write` are separate `step`s, so a test-and-set is two steps on one cell,
`racingAll` fires, and the program goes to `wrong` — the language has no atomicity from which to
build a lock. Second, adding an `atomic`/`cas` constructor would make such programs *expressible*
without making the equality true for them; the domain of `par_seq_eq` is intrinsically the
no-transfer fragment. -- ref: O'Hearn CONCUR'04 §3 (`docs/papers/`); `Logic/Rules.lean` header

**Q3.** Why can't you just take `P₁ ∧ P₂` (ordinary conjunction) instead of `P₁ ∗ P₂`? Give a
program where the rule with `∧` would be unsound.

---

## 4. What a data race is, and why it's the enemy

A **data race**: two threads access the same location concurrently, and at least one access is a
write.

- write/write — final value depends on order.
- read/write — the reader sees old or new depending on order.
- **read/read is fine.** Both see the same value. This asymmetry matters enormously later.

**Race-freedom ⇒ determinism** is the informal engine of the whole field. If threads never race,
each one sees the same values it would see running alone, so it behaves the same, so the result is
the same — for *every* interleaving, including the sequential one.

Making that rigorous is exactly what the rest of this document is about.

**→ In our code.** `Label.conflicts` in `Core/Semantics.lean` is literally this definition: same
location, at least one write. `racing` lifts it to sets of concurrent next-actions.

**Q4.** Why is read/read not a race? Now: two threads both do `x := x + 1` on a shared `x`. Is
that a race under this definition? What does the program do?

---

## 5. Brookes' semantics — where the real theorem lives

O'Hearn stated the rule. Brookes (CONCUR'04, same conference) proved it sound, and his proof
contains the result we actually want.

**Setup.** A program's meaning is a set of **traces** — sequences of state transitions
`(σ₀, σ₀'), (σ₁, σ₁'), …`. The gaps between `σᵢ'` and `σᵢ₊₁` are where *other threads* act. This is
how a thread's meaning can be defined without knowing its environment.

**Races are catastrophic.** A racy step produces a distinguished error, and error is *absorbing* —
once wrong, always wrong. This is a modelling decision, not a technicality (§6 explains why).

**The Parallel Decomposition Lemma** (Brookes §5–7) is the heart:

> If a trace of `C₁ ∥ C₂` runs from a state split as `σ₁ ∗ σ₂`, and the components' footprints stay
> separate, then that trace is an **interleaving** of a trace of `C₁` from `σ₁` and a trace of `C₂`
> from `σ₂`, and the final states recombine as `σ₁' ∗ σ₂'`.

Unpack the consequence. Any parallel execution *factors* into two independent solo executions. The
interleaving contributed nothing. So **every** interleaving yields the same result — in particular
the fully sequential one, `C₁; C₂`.

That last step — from "factors" to "`C₁ ∥ C₂` = `C₁; C₂`" — is one short corollary that **Brookes
never writes down.** Vafeiadis mechanizes the soundness proof but also doesn't state it. DPJ states
it but only on paper for a Java-like language. PolCert states it only for affine loop nests.

**That missing corollary, stated generically and mechanized, is this project.**

### 5b. The actual proof, piece by piece

The abstract lemma is one paragraph; the mechanization is not, because "the trace factors" has to
be rebuilt from a real step relation with no trace model to appeal to. Four pieces, each doing one
job. (This subsection describes what is actually proved in `Theory/WellFormedCanonical.lean` — read
it alongside `docs/decomposition.md`, which is the file-level rationale this summarizes.)

**Piece 1 — locality.** If two states agree everywhere outside a set `F`, and a program's footprint
avoids `F` entirely, running it from either state gives the same answer *and* the same footprint.
Proved once (`accesses_runSeq_locality`) and specialized to the case that matters:
`accesses_runSeq_isolated` — under `Indep`, `q`'s canonical run from `σ₁ := (runSeq p σ).snd` (the
state *after* `p`'s reference execution) agrees exactly with `q`'s run from the original `σ`. This
is the "asymmetry that vanishes under `Indep`" from `access.md` — now a proved fact, not an
assertion.

**Piece 2 — join-point decomposition.** Take a real, step-by-step execution of `.par p q k` from
`σ`. At every point along it, exactly one of three things is true: it's still inside the `par` node
(one or both branches mid-run), it has passed through the join into `k`'s continuation, or it has
crashed to `wrong`. `par_dichotomy` proves this trichotomy holds at every step (though since the
N-ary migration it is no longer on the proof path — uniqueness goes through
`runSeq_invariant_chain`). It pins down *that*
a join or a crash happens and rules out anything else — not yet *which* values the join lands on.

**Piece 3 — the single-step canonical invariant.** This is where the real difficulty lives, and
where the first attempt at this proof failed. The natural-looking approach — show that *every*
reachable configuration, at arbitrary depth, stays inside the original top-level footprint — runs
into a three-way mutual induction with no clean base case, because the "reached a join point" case
needs the theorem's own uniqueness direction as an ingredient to even state.

The unlock is a different question: *why does the theorem need `WellFormed` at all?* `step`'s racing
check is re-evaluated **fresh at every single step**, not once at the top. So a real step that
doesn't crash is automatically race-free *at that instant* — for free, at any nesting depth,
`WellFormed` or not. Independence is needed only for a narrower fact: when the *right* branch of a
`.par` node moves before the left one finishes, its real starting state is the raw joint state at
that moment, not the canonical reference point `σ₁` the whole theorem is stated against — and only
`Indep` guarantees that replaying the step against `σ₁` gives the identical result. `step_combined`
proves exactly this one-step fact — a real step never changes what `runSeq` would have computed, and
never lets a location outside the original footprint leak into the result — by induction on
whichever program actually moved. The hard case (right branch moves first) replays that step against
`σ₁` via `step_locality` (piece 1's operational twin), then needs the *footprint* half of its own
conclusion, one level down through the induction hypothesis, to pin the replayed state down exactly
rather than merely "agrees outside some set." That circularity inside a single step — needing the
containment fact to prove the containment fact — is why `step_combined` is one combined statement
(value invariance *and* footprint containment, together), not two lemmas proved back to back.

**Piece 4 — chaining.** A real execution is a chain of steps, not one step. Iterating
`step_combined` along the whole chain needs `WellFormed` to survive every intermediate step, so
`step_combined` can be invoked again at each one — that survival fact is `WellFormed_preserved`
(subject reduction: `WellFormed` is stable under one real step, whichever branch moved, at any
nesting depth). Composing `step_combined` with `WellFormed_preserved` along a whole `Reaches` chain
(`runSeq_invariant_chain`/`subset_chain`) gives both directions of `wellFormed_canonical` at once:
*uniqueness* (any real, non-crashing execution's value matches the canonical `runSeq` value — the →
direction), and the containment fact needed to justify the *existence* witness for the ← direction,
which explicitly constructs the schedule "run `p` to completion, then run `q`, then step into `k`"
and uses `reaches_par_left`/`reaches_par_right` to show that schedule is legal precisely because `p`
and `q` are independent.

Put together: **piece 2 says a join must happen; pieces 3 and 4 say which value it lands on, and
that no real schedule can do better or worse than the canonical left-to-right one.** That is the
entire content of Brookes' lemma, rebuilt from a step relation instead of a trace model.

**→ In our code.** `Theory/Decomposition.lean` then `Theory/WellFormedCanonical.lean` then
`Theory/Sequentialize.lean`. This is where essentially all the difficulty is; everything else is
bookkeeping.

**Q5.** The decomposition lemma assumes the footprints "stay separate". But whether they stay
separate can depend on values read, which can depend on the interleaving. Isn't that circular?
(This is the key subtlety — §9.)

---

## 6. Why races become an absorbing error

Reynolds (*Toward a Grainless Semantics*, FSTTCS 2004) asks: what is the atomic unit of execution?
Is `x := x + 1` one step or three (read, add, write)? Different answers give different interleavings
and different semantics.

His answer: if racy programs are *catastrophic* — mapped to an absorbing `wrong` — then for
race-free programs **the choice of grain doesn't matter**. All grains agree.

This is a great bargain. We pick whatever granularity is convenient, and the theorem stays honest,
because the hypothesis *excludes* racy programs rather than quietly assuming they behave.

**→ In our code.** `Conf.wrong` in `Core/Semantics.lean`, terminal and absorbing. `step` at a `par`
node checks `racing (nextAccs p) (nextAccs q)` and aborts. `Safe c := ¬ Reaches c .wrong`.

---

## 7. Vafeiadis' operational reformulation — the version to imitate

Brookes' trace model is heavy (domain theory, trace closure conditions). Vafeiadis (*CSL and
Operational Semantics*, MFPS 2011) redoes it with:

- an ordinary small-step operational semantics,
- **safety defined by induction on a step budget**: `safe 0 C σ Q` always; `safe (n+1) C σ Q` means
  *doesn't abort now*, *doesn't race now*, and every step lands in `safe n`,
- soundness by induction on that budget.

No traces, no domain theory. ~1500 lines of Coq (`vafeiadis/cslsound`). The restriction to no
ownership transfer (no locks handing off resources) is called **DCSL** — Disjoint CSL — and is
exactly our scope.

**Where our proof diverges from his literal recipe.** We inherit the *style* — an ordinary
small-step relation, no traces, no domain theory — but not the literal safety-by-step-budget
induction. `wellFormed_canonical` (§5b) instead proves a *uniqueness* statement directly: the value
any real execution reaches is provably the canonical `runSeq` value, established via join-point
decomposition and a chained single-step invariant, with no artificial fuel parameter threaded
through the proof at all. Both techniques prove the same *kind* of fact — operationally, without
appeal to trace-closure conditions — but they are not the same induction. Worth knowing before you
go read `cslsound` expecting a line-for-line match.

**→ In our code.** `Core/Semantics.lean`'s `step`/`Reaches`/`Safe` follow this shape. The abort
condition — compare the *next actions* of each thread — is his.

---

## 8. Bernstein's conditions — independence done right

Bernstein (1966) gave the criterion for reordering two statements. Write `R(S)` for the locations
`S` reads, `W(S)` for those it writes. `S₁` and `S₂` may run in either order (or concurrently) iff

```
W(S₁) ∩ W(S₂) = ∅        no write/write conflict
W(S₁) ∩ R(S₂) = ∅        no write→read conflict
W(S₂) ∩ R(S₁) = ∅        no read→write conflict
```

**Note what is absent: `R(S₁) ∩ R(S₂) = ∅`.** Shared reads are fine.

This is strictly weaker than `∗`-disjointness, and the difference is not academic. Matrix multiply:

```
for i, j in parallel:
    C[i][j] = Σₖ A[i][k] * B[k][j]
```

Each iteration writes only `C[i][j]` — disjoint. But iteration `(i,j)` reads *all* of row `i` of
`A` and column `j` of `B`, and iteration `(i,j')` reads that same row `i`. Reads overlap massively.

**Naive `∗`-disjointness rejects matmul. Bernstein accepts it.** Same for stencils, and for any
reduction where threads read shared data.

So we take Bernstein as the independence predicate:

```lean
Indep (r₁,w₁) (r₂,w₂) := w₁∩w₂ = ∅ ∧ w₁∩r₂ = ∅ ∧ w₂∩r₁ = ∅
```

Separation logic recovers this with **fractional / read permissions** (`DFrac`): a read-only
permission can be split and shared, a write permission cannot. Same idea, different packaging.

### Why there is no BI instance here

The project briefly depended on iris-lean to find out whether a bunched-implications instance was
worth having. The spike answered the question it was built for and the dependency was then removed,
so the finding is recorded here rather than in a module.

What the spike established, in order. Instantiating `BI` at a heap-predicate model costs nothing:
iris-lean ships a fully proved non-step-indexed instance for exactly this shape of model, with
`▷ := id` and a discrete COFE, so the step-indexing burden that was the stated risk never
materialized. But the `∗` that instance provides is *exclusive* separation — `P ∗ Q` means the state
splits into disjoint-domain sub-heaps — and the whole content of this section is that `Indep` is
weaker than that. So the imported connective is not the one the theorems are about, and the
assertion carrier it is defined over (a partial map) is a different type from `Core.State` (total),
which would need a restriction or an embedding before a triple could even be stated.

Two conclusions follow. First, `Logic/Rules.lean` frames with `∧` over `Local`/`Disjoint` predicates
on locations, and the parallel rule it proves is therefore *fully general* — shared reads included —
rather than waiting on a `∗` that would have narrowed it. Second, a BI buys notation and proof-mode
tactics for an assertion type no theorem in this tree uses, which is not worth a dependency. If
read-sharing is ever wanted inside a separating conjunction, the construction to build is a
fractional-permission `∗` over `Core.State`, and nothing available supplies it off the shelf.

**→ In our code.** `Core/Access.lean` (M2). Already visible in `Label.conflicts`: same location and
*at least one write* — read/read never conflicts. `Examples/Programs/MatMul.lean` is this exact matmul
mechanized: `Theory/Intervals.lean`'s `indep_of_read_write_confined` takes *separate* read/write
confinement predicates per side and checks only write/write and write/read cross terms, never
read/read — so the independence proof for `#parallel_for (n*n), cellCompute` is two `grind` calls on
where `A`/`B`/`C` live in memory (`[0,n²)`, `[n²,2n²)`, `[2n²,3n²)`), with **zero** reasoning about
which rows or columns actually overlap. That the proof doesn't need to know is the point: `Indep`
was never checking read/read in the first place, so there was never anything to reason about there.

**Q6.** Write a two-iteration loop that satisfies all three Bernstein conditions but where the
iterations still cannot be swapped. (Hint: think about what "location" means for control flow, or
about aliasing.)

---

## 9. The circularity, and how it resolves

Here is the subtlety from Q5, stated sharply.

We want the hypothesis "the threads' footprints are independent". But a thread's footprint is
determined by its execution — which values it reads determine which branch it takes, hence which
locations it touches next. And inside `p ∥ q`, the values `p` reads could have been written by `q`.

So: the *hypothesis* is defined in terms of solo executions, but the *conclusion* is about an
interleaved execution in which those solo executions may not occur.

**The resolution is the decomposition lemma itself**, by induction on the interleaved run,
maintaining the invariant:

> at every point, the heap restricted to `p`'s footprint agrees with what `p`'s solo run would see.

Base case: trivial. Inductive step: the next action is either `p`'s or `q`'s. If `q`'s, it writes
only into `q`'s footprint, which by independence is disjoint from `p`'s reads — so `p`'s view is
unchanged and the invariant survives. Symmetrically for `p`.

This is precisely Brookes' `σ₁ ∗ σ₂` splitting. **The invariant is the proof.** Everything else is
plumbing.

**Named precisely** (§5b spells out the full mechanization): this invariant *is* `step_combined`'s
conclusion, re-established one real step at a time by `WellFormed_preserved`, and chained across a
whole execution by `runSeq_invariant_chain`. What the "why does the theorem need `WellFormed` at
all" question in §5b adds to the picture above: independence isn't needed to keep *every* step
honest — a real step that doesn't crash is automatically race-free at that instant, unconditionally.
It's needed only at the one place a real schedule can legitimately disagree with the canonical
left-to-right one: replaying a step against a *different* state than the reference execution
assumed, which is exactly what happens when the right branch of a `par` node moves first.

**→ In our code.** `Theory/Decomposition.lean` sets up the general `runSeq`/`WellFormed`-through-
`bind` facts; the invariant itself, and the induction that maintains it, is
`Theory/WellFormedCanonical.lean`'s `step_combined`/`WellFormed_preserved` pair (§5b).

---

## 10. Alternatives worth knowing

Independence is not the only route to "parallel = sequential". Know these so you can say why we
didn't take them.

### Movers / reduction (Lipton 1975, CIVL ESOP'26)

Instead of *disjointness*, use **commutativity**. An action is a **right mover** if it commutes
forward past any other thread's action; a **left mover** if backward. A block `R*·A·L*` can be
treated as atomic, which lets you replace `∥` with `;`.

Strictly more general — it admits shared state where operations commute (e.g. two threads
incrementing a counter atomically). Harder soundness proof. **Our fallback if Bernstein excludes
programs we care about.**

### Confluence (LVars, Kuper & Newton 2013)

Allow shared state but constrain *how* it changes: writes must be inflationary in a lattice, reads
are "threshold" reads that block until enough information arrives. Determinism then follows from
**strong local confluence + Newman's lemma** — a diamond argument on the step relation.

The most Lean/Mathlib-friendly technique in the list, and our fallback if the footprint route gets
painful.

### Algebra (third homomorphism theorem, BMF, SyDPaCC)

For *pure* code there's no heap, so no races, and the result is pure algebra: a chunked reduction
equals a fold iff the operator is **associative**. Commutativity is needed *only* if the schedule
may reorder elements — get that distinction right.

This is genuinely simpler and it's why plain-Lean-plus-`Task` gets you a real library with no
concurrency theory. Its hard limit is that it cannot express mutable shared state — no in-place
sort, no imperative loop parallelization.

**Q7.** Chunked reduce with `k` threads, each folding a contiguous chunk left-to-right, then
combining partials in order. Do you need commutativity? What if the runtime is work-stealing and
combines partials as they finish?

---

## 11. Where this gets used: compilers

- **DPJ** (Bocchino et al., OOPSLA'09) — a *type and effect system*. Region annotations give
  read/write sets; the soundness theorem is exactly "non-interfering effects ⇒ either order gives
  the same values, effects, and heap". Our goal, as a type system, on paper only.
- **Polyhedral / PolCert** (TASE'24) — Bernstein for affine loop nests, **mechanized in Coq**.
  Architecture worth copying: prove a generic theorem once, then a *decidable validator* checks
  each program.
- **OpenMP / VerCors / VeyMont** — `#pragma omp parallel for` is **trusted and unchecked**, which
  is why it's a bug factory. Blom et al. (STTT'21) have our architecture — sequential correctness
  plus dependence contracts ⇒ parallel correctness — but no proof assistant.

**→ In our code.** `Lib/Loop.lean` gives OpenMP-shaped syntax (`#parallel_for n, body`,
`#parallel[ p, q, ... ]`) that elaborates to `ParM.parAll` **plus a proof obligation** —
`parAll_wellformed_of_indexed_rw`, the PolCert-shaped validator: supply a per-iteration footprint
bound and one pairwise-disjointness fact, get `WellFormed`/`ParSeqEq` for the whole loop, any size,
with no per-loop induction to write. Same notation as OpenMP, but nothing is trusted — and the loop
this project's own anti-vacuity discipline requires (`Examples/Programs/MapArray.lean`'s `incFromPrev`,
`A[i] := A[i-1] + 1`) is checked to genuinely fail the obligation, not just asserted to.

---

## 12. Where Paralever sits

| concept | paper | our code |
|---|---|---|
| ownership / footprint | O'Hearn CONCUR'04 | `Core/Access.lean` |
| race = same loc, one write | folklore; Vafeiadis MFPS'11 | `Label.conflicts` |
| races ↦ absorbing error | Reynolds FSTTCS'04 | `Conf.wrong`, `Safe` |
| small-step, no traces (style only — see §7) | Vafeiadis MFPS'11 | `step`, `Reaches` |
| independence = Bernstein | Bernstein 1966; DPJ | `Indep` |
| decomposition lemma | Brookes CONCUR'04 §5–7 | `Theory/WellFormedCanonical.lean` |
| **the missing corollary** | *nobody* | `Theory/Sequentialize.lean` |
| generic Bernstein-from-footprints (this project's own layer) | — | `Theory/Intervals.lean` |
| checked pragmas | Blom STTT'21 (unmechanized) | `Lib/Loop.lean` |
| free case: no shared state at all | — | `Kernels/ParMap.lean` |

The theorem splits in two, mirroring the literature:

```lean
-- metatheorem: race-free ⇒ sequentializable          (Brookes' decomposition)
par_eq_seq : Safe (.run (parPair p q) σ) →
  (Reaches (.run (parPair p q) σ) (.run (.pure r) σ') ↔
   Reaches (.run (seqPair p q) σ) (.run (.pure r) σ'))

-- discharge path: independence ⇒ race-free           (CSL soundness)
indep_safe : Indep (accesses p σ) (accesses q σ) → Safe (.run (parPair p q) σ)
```

Bernstein is then *one sufficient condition* for safety, not part of the metatheorem — so Tier-1
footprints, the Tier-2 ownership logic, and any future criterion (movers, confluence) all target
the same obligation.

## Final verdict

We use the `ParM`/`WellFormed` interleaving model, not the `Task`-based model, as the source of
truth for correctness, because it is the only one of the two that proves anything about
*interference*: it is our mechanization of Brookes' Parallel Decomposition Lemma (*A Semantics for
Concurrent Separation Logic*, CONCUR'04 — §5), in Vafeiadis' operational *style* (*CSL and
Operational Semantics*, MFPS'11 — small-step, no traces) but via our own join-point-decomposition-
plus-chaining proof technique rather than his literal step-budget induction (§5b, §7), and it holds
for *every* schedule, not one measured run. The
final lemma is `par_seq_eq`/`parAll_par_seq_eq` (`Theory/Sequentialize.lean`): `ParSeqEq (parPair p
q) (seqPair p q) σ` whenever `WellFormed (parPair p q) σ` — and the condition actually discharged
per program is `WellFormed` itself, i.e. Bernstein's independence (`w₁∩w₂ = w₁∩r₂ = w₂∩r₁ = ∅`,
shared reads always allowed) checked at *every* `par` node in the term, not only the outermost one
(§9's counterexample is exactly why the outermost check alone is unsound). The `Task` model
(`Compile/TaskFacts.lean`) is kept as a deliberately weaker, complementary check: it proves the
compiled program computes the right *value* by direct computation, and — checked empirically, not
by Lean's proof, since `Task`'s real concurrency is invisible to the type theory — that the spawned
work's wall-clock windows genuinely overlap; it says nothing about interference because `Task` is
`rfl`-trivial in the logic and has no way to represent a race in the first place.

---

## 13. Glossary

| term | meaning |
|---|---|
| **footprint** | the locations a program reads / writes |
| **frame rule** | verify against the footprint; untouched heap comes free |
| **`∗` (separating conj.)** | heap splits into disjoint pieces |
| **ownership hypothesis** | a component only touches what it owns |
| **data race** | concurrent same-location access, ≥1 write |
| **absorbing `wrong`** | error state you can never leave; makes grain irrelevant |
| **decomposition lemma** | a parallel trace factors into independent solo traces |
| **Bernstein's conditions** | W∩W = W∩R = R∩W = ∅ (note: *not* R∩R) |
| **DCSL** | CSL without ownership transfer — our scope |
| **mover** | an action that commutes past other threads' actions |
| **confluence** | different reduction orders reconverge |
| **adequacy** | the logic's judgments say something true about real executions |

---

## 14. Reading order

1. O'Hearn, *Resources, Concurrency and Local Reasoning* — the rule.
2. Brookes, *A Semantics for CSL*, §5–7 — the decomposition lemma. **Read properly.**
3. Apt & Olderog, disjoint parallelism chapter — the cleanest statement of our target.
4. Vafeiadis, *CSL and Operational Semantics* + the Coq — the method we imitate.

Then by need: DPJ and PolCert (§11), Lipton and LVars (§10), Gibbons and SyDPaCC (§10).

---

## Answers to check yourself against

**Q1.** `C₂` can write a location `C₁`'s proof depends on, mid-execution. Sequential composition
only needs `R` to hold at the boundary; parallel composition needs `C₁`'s reasoning to survive
arbitrary interference at *every* point.

**Q2.** With "at least", two assertions could both claim the same cell, so `P ∗ Q` would no longer
imply disjointness and the frame rule would let `C` silently modify `R`'s cells.

**Q3.** `∧` doesn't force disjointness. Take `C₁ = [l] := 1`, `C₂ = [l] := 2`, `P₁ = P₂ = l ↦ 0`,
`Q₁ = l ↦ 1`, `Q₂ = l ↦ 2`. Both premises hold, but `Q₁ ∧ Q₂` is `l ↦ 1 ∧ l ↦ 2` — false. `∗`
blocks this because `l ↦ 0 ∗ l ↦ 0` is unsatisfiable.

**Q4.** Read/read: neither changes anything, so both orders give identical results. `x := x + 1`
twice **is** a race, because it compiles to read-then-write; you can lose an update. Note this only
shows up at a *fine* grain — which is Reynolds' point in §6.

**Q5.** Not circular, but the crux — see §9. The invariant "the heap restricted to `p`'s footprint
matches `p`'s solo view" is maintained inductively, and independence is exactly what makes the
inductive step go through.

**Q6.** Aliasing: if `R`/`W` are *syntactic* names, `A[i]` and `A[j]` look distinct but may be the
same location when `i = j`. Bernstein is about *actual* locations — which is exactly why our
footprints are dynamic rather than syntactic.

**Q7.** Contiguous chunks combined in order need only **associativity** — the element order is
preserved. Work-stealing that combines partials as they finish reorders them, so it additionally
needs **commutativity**. This distinction is a good early Lean lemma.
