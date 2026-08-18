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
and disjointness as part of the structure — is everything. Tier 2 (`Logic/`) instantiates
iris-lean's `BI` at `State → Prop` to get `∗` and a proof mode.

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

**→ In our code.** `Theory/Decomposition.lean` then `Theory/Sequentialize.lean`. This is where
essentially all the difficulty is; everything else is bookkeeping.

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

**→ In our code.** `Core/Access.lean` (M2). Already visible in `Label.conflicts`: same location and
*at least one write* — read/read never conflicts.

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

**→ In our code.** This is `Theory/Decomposition.lean`. When you start it, write the invariant
first and the induction second.

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

**→ In our code.** `Pragma/` gives OpenMP-shaped syntax that elaborates to `parFor` **plus a proof
obligation**. Same notation, but nothing is trusted. That gap — mechanized, with a real proof
assistant — is the paper.

---

## 12. Where Paralever sits

| concept | paper | our code |
|---|---|---|
| ownership / footprint | O'Hearn CONCUR'04 | `Core/Access.lean` |
| race = same loc, one write | folklore; Vafeiadis MFPS'11 | `Label.conflicts` |
| races ↦ absorbing error | Reynolds FSTTCS'04 | `Conf.wrong`, `Safe` |
| small-step + fuel-indexed safety | Vafeiadis MFPS'11 | `step`, `Reaches` |
| independence = Bernstein | Bernstein 1966; DPJ | `Indep` |
| decomposition lemma | Brookes CONCUR'04 §5–7 | `Theory/Decomposition.lean` |
| **the missing corollary** | *nobody* | `Theory/Sequentialize.lean` |
| checked pragmas | Blom STTT'21 (unmechanized) | `Pragma/` |

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
