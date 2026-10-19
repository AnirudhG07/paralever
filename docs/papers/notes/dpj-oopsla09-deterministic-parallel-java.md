# A Type and Effect System for Deterministic Parallel Java
Robert L. Bocchino Jr., Vikram S. Adve, Danny Dig, Sarita V. Adve, Stephen Heumann, Rakesh Komuravelli, Jeffrey Overbey, Patrick Simmons, Hyojin Sung, Mohsen Vakilian · OOPSLA 2009 · `dpj-oopsla09-deterministic-parallel-java.pdf`

## One-line thesis
A modular, compile-time region-and-effect type system (region path lists, index-parameterized arrays, subarrays/partitions, commutativity annotations) can statically guarantee that a parallel Java program has deterministic semantics, by checking that every pair of concurrently-executed expressions has noninterfering effects.

## The setting

**Language.** Java extended with regions and effects, called *Deterministic Parallel Java* (DPJ). Parallelism is structured, not unstructured threads: two constructs only (§2, "Expressing parallelism"):

- `cobegin { s1; ...; sn }` — "executes each statement in its body as a parallel task"
- `foreach (int i in lo, hi) { ... }` — parallel loop over an array index range

Both are fork–join with an implicit join; §6.4 describes `cobegin` as "an unspecified order, with an implicit join at the end of the execution." The implementation maps these to `ForkJoinTask` (§7).

**Judgment form.** A *type and effect system*, not a program logic. The core judgment (Fig. 12(e)) is

```text
Γ ⊳ e : T, E          "e has type T and effect E in Γ"
```

Effects are read/write sets over regions plus an invocation effect (Fig. 11):

```text
Effects   E   ∅ | reads R | writes R | E ∪ E |
              invokes C.m with E
```

The whole discipline rests on two auxiliary relations, both *binary on syntactic objects, not on programs*:

```text
Γ ⊳ R # R'        disjointness of RPLs          (Fig. 22)
Γ ⊳ E # E'        noninterference of effects    (Fig. 23)
```

**Memory model / atomic grain.** NOT FOUND IN PDF as an explicit memory-model statement. The paper's position is that the question is dissolved rather than answered: §1 claims programmers "do not have to reason about notoriously subtle and difficult issues such as data races, deadlocks, and memory models." There is no weak-memory model, no explicit sequential-consistency assumption, and no atomic grain discussed. The dynamic semantics (§6.2) is a **large-step (big-step) sequential** evaluation relation

```text
(e, dΓ, H) → (o, H', dE)
```

where `dΓ` is a dynamic environment, `H` a heap, `o` the result reference, and `dE` the dynamic effect. §6.2: "We write the evaluation rules in large-step semantics notation."

**Terminating programs only?** Not stated as a restriction, but the semantics is big-step, so it only relates terminating evaluations; divergence is simply not in the relation. The paper does not discuss this.

**Crucial scoping fact (§6, simplification list, p. 10).** The formalized calculus has *no parallelism at all*:

> "We have chosen to make Core DPJ a sequential language, in order to focus on our mechanisms for expressing effects and noninterference. In Section 6.4, we discuss how to extend the formalism to model the `cobegin` and `foreach` constructs of DPJ." (§6, p. 10)

Core DPJ is further simplified (§6, items 1–4): expression-based, no statements or control flow; classes and objects but **no inheritance**; region names declared at global scope, one region parameter per class, one formal parameter per method; array indices are natural number literals.

## Main results, stated

### The region/effect machinery

**RPLs (§3.1).** An RPL is a colon-separated list beginning with `Root`, e.g. `Root:A:B`; `R1 ≤ R2` means `R1` is under `R2` (i.e. `R2` is a prefix). §3.1: "The set of all regions partitions the heap, i.e., each memory location lies in exactly one region. The regions are arranged in a tree with a special region `Root` as the root node." Partially specified RPLs use `*` (§3.2) to denote *sets* of regions, enabling "distinctions from the left" (differ in some place before any `*`) and "distinctions from the right" (differ in the nth place from the right, no `*` in the first n places from the right).

**Disjointness of RPLs (Fig. 22, Appendix C.2).** Verbatim:

```text
                          r ≠ r'    Γ ⊳ R ≤ R_f : r    Γ ⊳ R' ≤ R_f : r'
(DISJOINT-LEFT-NAME)      ───────────────────────────────────────────────
                                            Γ ⊳ R # R'

                          i ≠ i'    Γ ⊳ R ≤ R_f : [i]  Γ ⊳ R' ≤ R_f : [i']
(DISJOINT-LEFT-INDEX)     ────────────────────────────────────────────────
                                            Γ ⊳ R # R'

                               Γ ⊳ R ≤ R_f : r    Γ ⊳ R' ≤ R_f : [i]
(DISJOINT-LEFT-NAME-INDEX)     ──────────────────────────────────────
                                            Γ ⊳ R # R'

                                        r ≠ r'
(DISJOINT-RIGHT-NAME)                ──────────────────
                                     Γ ⊳ R : r # R' : r'

                                        i ≠ i'
(DISJOINT-RIGHT-INDEX)              ────────────────────────
                                    Γ ⊳ R : [i] # R' : [i']

(DISJOINT-RIGHT-NAME-INDEX)         ────────────────────────
                                     Γ ⊳ R : r # R' : [i]

                                       Γ ⊳ R # R'
(DISJOINT-NAME)                     ───────────────────
                                    Γ ⊳ R : r # R' : r

                                       Γ ⊳ R # R'
(DISJOINT-INDEX)                    ─────────────────────
                                    Γ ⊳ R : [i] # R' : [i]
```

Fig. 22 caption: "Rules for disjointness of RPLs. The disjointness relation is symmetric (obvious rule omitted)."

**Noninterference of effects (Fig. 23, Appendix C.3).** This is the Bernstein-shaped condition. Verbatim:

```text
(NI-READ)                  ───────────────────────────
                           Γ ⊳ reads R # reads R'

                                    Γ ⊳ R # R'
(NI-READ-WRITE)            ───────────────────────────
                           Γ ⊳ reads R # writes R'

                                    Γ ⊳ R # R'
(NI-WRITE)                 ───────────────────────────
                           Γ ⊳ writes R # writes R'

                                     Γ ⊳ E # E'
(NI-INVOKES-1)             ─────────────────────────────────
                           Γ ⊳ invokes C.m with E # E'

                              m commuteswith m' ∈ def(C)
(NI-INVOKES-2)   ────────────────────────────────────────────────────────
                 Γ ⊳ invokes C.m with E # invokes C.m' with E'

(NI-EMPTY)                        ───────────
                                  Γ ⊳ ∅ # E

                           Γ ⊳ E # E''    Γ ⊳ E' # E''
(NI-UNION)                 ──────────────────────────────
                             Γ ⊳ E ∪ E' # E''
```

Fig. 23 caption: "The noninterference relation on effects. Noninterference is symmetric (obvious rule omitted)."

Note `(NI-READ)` has **no premise**: any two reads are noninterfering regardless of region.

The paper's own prose summary (§6.3, "Noninterference"):

> "The rules express four basic facts: (1) reads commute with reads; (2) writes commute with reads or writes if the regions are disjoint; (3) invocations commute with other effects if the underlying effects are disjoint; and (4) two invocations commute if the methods are declared to commute, regardless of interference between the underlying effects." (§6.3)

### Theorem 1 (Preservation), Appendix C.1

Verbatim:

```text
Theorem 1 (Preservation). For a well-typed program, if
Γ ⊳ e : T, E and H ⊳ dΓ ≤ Γ and (e, dΓ, H) → (o, H', dE),
then (a) ⊳H'; and (b) H' ⊳ dT ≤ dΓ(T), where H' ⊳ o : dT;
and (c) H' ⊳ dE; and (d) H' ⊳ dE ⊆ dΓ(E).
```

§6.3 gloss: "if we type an expression `e` in environment Γ, and we evaluate `e` in dynamic environment `dΓ`, where `dΓ` instantiates Γ, then (a) the evaluation takes a valid heap to a valid heap; (b) the static type of `e` bounds the dynamic type of the value `o` that results from the evaluation; and (c) the static effect of `e` bounds the dynamic effect that results from the evaluation."

Supporting definitions: Definition 1 (valid dynamic environments), Definition 2 (valid heaps), Definition 3 (instantiation of static environments), Definition 4 (set interpretation of dynamic RPLs), Definition 5 (region of a field or array cell), Proposition 1 (disjointness of region sets: `H ⊳ dR # dR'` implies `S(dR,H) ∩ S(dR',H) = ∅`), Proposition 2 (distinctness of disjoint regions).

### Theorem 2 (Soundness of noninterference), Appendix C.3 — the main result

Verbatim:

```text
Theorem 2 (Soundness of noninterference). If Γ ⊳ e : T, E
and Γ ⊳ e' : T', E' and Γ ⊳ E # E' and H ⊳ dΓ ≤
Γ and (e, dΓ, H) → (o, H', dE) and (e', dΓ, H') →
(o', H'', dE'), then there exists H''' such that (e', dΓ, H) →
(o', H''', dE') and (e, dΓ, H''') → (o, H'', dE).
```

§6.3 gloss: "Theorem 2 expresses the main soundness property of Core DPJ, which is that the execution order of noninterfering expressions does not matter. It states that in a well-typed program, if `e` and `e'` are expressions with types `T` and `T'` and effects `E` and `E'`, and `E` and `E'` are noninterfering, then either order of evaluating `e` and `e'` produces the same values `o` and `o'`, the same effects `dE` and `dE'`, and the same final heap `H`."

**Read the statement carefully: both sides of Theorem 2 are *sequential* compositions.** The left side is "run `e` then `e'`"; the right side is "run `e'` then `e`". It is a sequential-reordering / commutativity theorem, not a parallel-vs-sequential theorem. There is no parallel step relation and no schedule anywhere in it.

### §6.4 — the parallel claim, asserted not proved

This is where parallelism enters, and it enters informally:

> "We can easily simulate `cobegin` by adding a parallel composition operator `e|e'`, which says to execute `e` and `e'` in the same environment, in an unspecified order, with an implicit join at the end of the execution. We can simulate `foreach` by allowing an induction variable `i` to appear in expressions inside the scope of a `foreach`, mapping `i` to `n` over the index range of the `foreach`, and evaluating all `e_n` in unspecified order. In both cases we can extend the static typing rules to say that for any pair of expressions `e` and `e'` as to which the order of execution is unspecified, then the effects of `e` and `e'` must be noninterfering." (§6.4)

> "It follows directly from Theorem 2 that parallel composition of noninterfering expressions produces the same result as sequential composition of those expressions. This guarantees determinism of execution regardless of the order of parallel execution. **The formalization of this property is straightforward, and we omit it from our technical report.**" (§6.4, emphasis added)

So the parallel-equals-sequential statement is made in one English sentence, is derived informally from Theorem 2, and is explicitly **not formalized anywhere** — not in the paper, not in the technical report.

Note also what "unspecified order" means in §6.4: the simulated parallel operator `e|e'` is interleaving-free. It executes `e` and `e'` *in some order*, atomically, not interleaved at a fine grain. There is no real nondeterministic small-step relation in which two threads interleave their individual reads and writes.

## Proof technique

Chain of three groups, all in Appendix C and in full only in the technical report [10] (§6.3: "We provide further explanation and a full proof in our technical report [10]"):

1. **Type and effect preservation (§C.1).** Theorem 1: static types and effects bound dynamic types and effects. This is the bridge that lets the static noninterference relation imply anything dynamic.
2. **Disjointness (§C.2).** Definition 4 gives a *set interpretation* `S(dR, H)` of a dynamic RPL as a set of fully-specified RPLs; Definition 5 maps every field and array cell to a region. Proposition 1: syntactically disjoint RPLs denote disjoint region sets. Proposition 2: disjoint fully-specified regions are distinct locations (`o ≠ o'` or `f ≠ f'`). This is the step that turns the syntactic `#` relation into actual memory-location disjointness.
3. **Noninterference (§C.3).** Theorem 2.

Justification of Theorem 2, in the paper's own words (§6.3):

> "The claim is true for dynamic effects from the commutativity of reads, the disjointness results of Section C.2, and the assumed correctness of the commutativity specifications for methods. The claim is true for static effects by the type and effect preservation property above. See [10] for the formal proof."

What the induction goes over: **NOT FOUND IN PDF.** The paper states only the three-part structure above and the theorem statements; the actual inductive argument is deferred entirely to [10], which is not included.

Note the explicit assumption: `commuteswith` is *unchecked*. §5: "The commutativity property itself is not checked by the compiler; we must rely on other forms of checking ... Our effect system does guarantee deterministic results for an application using a commutative operation, **assuming that the operation declared commutative is indeed commutative**."

## Side condition on parallel composition

Exactly `Γ ⊳ E # E'` — the noninterference relation of Fig. 23 — between the static effects of the two branches. §6.4: "for any pair of expressions `e` and `e'` as to which the order of execution is unspecified, then the effects of `e` and `e'` must be noninterfering."

Unfolded, this is **precisely Bernstein's condition**, as the rules show:

- `writes R # writes R'` requires `R # R'` — write/write disjointness (`w₁ ∩ w₂ = ∅`)
- `reads R # writes R'` requires `R # R'` — read/write disjointness, both directions by symmetry (`r₁ ∩ w₂ = w₁ ∩ r₂ = ∅`)
- `reads R # reads R'` has **no premise at all** — read/read sharing is unconditionally allowed

**Is read/read sharing allowed? Yes, explicitly and unconditionally.** `(NI-READ)` is an axiom. §1 states the design goal in these terms: "the compiler can then check ... that all pairs of memory accesses either commute with each other (e.g., they are both reads, or they access disjoint parts of the heap) or are properly synchronized." §6.3 lists it first: "(1) reads commute with reads."

The paper's worked example makes the overlapping-reads point directly (§3.2, Fig. 5): a tree computation where each node writes only its own `force` field but follows a `link` pointer to read some *other* node's `mass`. §3.3:

> "Note how our effect system is able to prove that the updates to different subtrees are distinct, even though (1) non-tree edges exist in the graph; and (2) those edges are followed to do possibly overlapping reads." (§3.3)

**Fractional / read permissions?** No. Permissions do not appear; the mechanism is region naming plus a tree-structured region hierarchy. Boyland's fractional permissions [13] appear only in related work (§8, "Unique References"). There is no ownership *transfer*: regions are static names fixed by the type, and §6 notes the heap-region assignment is a partition fixed by declarations.

The example check (§2, "Proving determinism") shows how the side condition is discharged in practice:

> "Second, check that the parallelism in lines 8–13 is safe. It is, because the effect of line 10 is `reads Links writes L`; the effect of line 12 is `reads Links writes R`; and `Links`, `L`, and `R` are distinct names. Notice that this analysis is entirely intraprocedural." (§2)

Note that the two branches here *share* a read of `Links` — allowed by `(NI-READ)`.

## Shared state / resources

**Shared mutable state between concurrent tasks is not supported** at the read/write level — that is the whole point of the discipline. Two parallel branches may share *reads* of mutable state freely, but any location written by one branch must be untouched by the other.

There are no resource invariants, no locks, no CAS, no ghost state. There is no synchronization construct in the language at all. §1: "Programmers do not have to reason about notoriously subtle and difficult issues such as data races, deadlocks, and memory models."

The one escape hatch is **commutativity annotations** (§5), which permit genuinely interfering concurrent access at the read/write level, provided the operations commute at a logical level:

```text
class IntSet<region P> {
    void add(int x) writes P { ... }
    add commuteswith add;
}
```

§5: "classes may contain declarations of the form `m commuteswith m'`, where `m` and `m'` are method names, indicating that any pair of invocations of the named methods may be safely done in parallel, regardless of the read and write effects of the methods. In effect, the `commuteswith` annotation says that (1) the two invocations are atomic with respect to each other, i.e., the result will be as if one occurred and then the other; and (2) either order of invocation produces the same result."

The accompanying `invokes C.m with E` effect (Fig. 11) records that an invocation happened with underlying effect `E`, so the checker can simultaneously disregard interference between two `add`s and still verify no *other* code interferes with `writes R`. Rules `(NI-INVOKES-1)` and `(NI-INVOKES-2)` above.

This is an *assumption*, not a verified mechanism: the compiler does not check commutativity (§5, quoted above). It is an atomicity-plus-commutativity axiom discharged by the programmer.

The structural mechanisms that make disjoint *writable* state expressible are:

- **Index-parameterized arrays** (§4.1, Insight 1): "We can define a special array type with the restriction that an object reference value `o` assigned to cell `n` ... has a runtime type that is parameterized by `n`."
- **Subarrays and `DPJPartition`** (§4.2): a `DPJArray` is a view into a contiguous segment; `DPJPartition` is "an indexed collection of `DPJArray` objects, all of which point into mutually disjoint segments of the original array." Used for in-place parallel quicksort (Fig. 9). Notably the `get` method "uses a type cast to generate a `DPJArray` of type `this:[i]:*` ... The type cast is not sound within the type system, but it is hidden from the user code in such a way that all well-typed uses of `DPJPartition` are noninterfering" (§4.2) — i.e. `DPJPartition` is trusted library code, not type-checked code.

## What it does NOT claim

**Does it prove an equality/equivalence between a parallel program and a sequential one?** It *claims* one and does *not* prove it. Precisely:

- The **claim** is made twice. Contribution 3 (§1): DPJ "guarantees semantic equivalence between a DPJ program and its obvious sequential Java version." And §6.4: "It follows directly from Theorem 2 that parallel composition of noninterfering expressions produces the same result as sequential composition of those expressions."
- The **proved theorem** (Theorem 2) is a *sequential reordering* result: given `e;e'` runs from `H` to `H''`, there is an `H'''` such that `e';e` also runs from `H` to `H''` with the same results. Both sides are sequential; neither side involves a parallel operator, a schedule, or an interleaving.
- §6.4 explicitly declines to formalize the parallel claim: "The formalization of this property is straightforward, and we omit it from our technical report."

So the honest summary is: **DPJ proves sequential commutativity of noninterfering expressions, and asserts (without formalizing) the corollary that parallel composition agrees with sequential composition.**

Further, Core DPJ — the only thing formalized — has **no parallel constructs** (§6: "We have chosen to make Core DPJ a sequential language"). There is no parallel operational semantics, no schedule, no interleaving, no notion of a step, no race state, no `wrong` or abort outcome, and no fine-grained atomic grain anywhere in the formal development. `cobegin`/`foreach` exist only in the implemented language, which is not formalized.

Other non-claims and limitations:

- Core DPJ omits inheritance, statements and control flow, class-scoped region names, multiple region/formal parameters, and integer-valued array indices (§6, simplifications 1–4). Effect variables, present in full DPJ, are deferred: "we leave the discussion of effect variables to future work" (§2).
- Commutativity is assumed, not checked (§5).
- `DPJPartition.get` relies on a cast that "is not sound within the type system" (§4.2).
- Disjointness constraint violations produce only a **warning**, not an error: §2, "If the disjointness constraints are violated, the compiler issues a warning."
- No-annotation code defaults to "reads and writes the entire heap" (§2), so unannotated code cannot be parallelized but remains type-correct.
- Interoperation with raw Java threads is guaranteed only under phase separation: §7, "the DPJ portions will be guaranteed deterministic if the explicitly threaded and DPJ portions are separate phases that do not run concurrently."
- Nothing about termination, deadlock-freedom (there is no synchronization to deadlock on), or liveness.
- Vector parallelism is out of scope (§7.2).
- Does not handle nondeterministic algorithms; §1 lists this as future work.

## Mechanized?

**No.** There is no mechanization anywhere. A grep of the full text for "Coq", "Isabelle", "mechanized", "machine-checked", "theorem prover", "proof assistant" returns nothing; the only hits for "formaliz*" are to the pen-and-paper formalization of Core DPJ (§6) and to the sentence in §6.4 omitting the parallel formalization.

What exists, precisely:

- **In the paper:** §6 and Appendix A–C — Core DPJ syntax (Fig. 11), type judgments (Fig. 12), dynamic syntax (Fig. 13), static rules (Figs. 16–20), evaluation rules (Fig. 21), disjointness (Fig. 22), noninterference (Fig. 23), Definitions 1–5, Propositions 1–2, Theorems 1–2 — **statements only**, no proofs.
- **In a technical report, on paper:** reference [10], "R. L. Bocchino and V. S. Adve. Formal definition and proof of soundness for Core DPJ. Technical Report UIUCDCS-R-2008-2980, U. Illinois, 2008," available via `http://dpj.cs.uiuc.edu` (ref [1]). §6.3: "We provide further explanation and a full proof in our technical report [10]." The TR is not included in this PDF, so its contents cannot be verified here.
- **Nowhere:** the par-equals-seq property, by the authors' own statement (§6.4).

A prototype compiler exists (an extension of Sun's `javac`, §7) with a `ForkJoinTask`-based runtime, and an annotation-inference Eclipse plugin DPJIZER [49] (§7.4) — these are implementations, not proofs.

## Quotable lines

- "We have chosen to make Core DPJ a sequential language, in order to focus on our mechanisms for expressing effects and noninterference." — §6, p. 10
- "It follows directly from Theorem 2 that parallel composition of noninterfering expressions produces the same result as sequential composition of those expressions. ... The formalization of this property is straightforward, and we omit it from our technical report." — §6.4
- "guarantees semantic equivalence between a DPJ program and its obvious sequential Java version" — §1, contribution 3
- "The rules express four basic facts: (1) reads commute with reads; (2) writes commute with reads or writes if the regions are disjoint; (3) invocations commute with other effects if the underlying effects are disjoint; and (4) two invocations commute if the methods are declared to commute." — §6.3
- "Note how our effect system is able to prove that the updates to different subtrees are distinct, even though (1) non-tree edges exist in the graph; and (2) those edges are followed to do possibly overlapping reads." — §3.3
- "The commutativity property itself is not checked by the compiler; we must rely on other forms of checking ... to ensure that methods declared to be commutative are really commutative." — §5
- "Kendo [36] and DMP [21] use runtime mechanisms to guarantee equivalence to some (arbitrary) serial interleaving of tasks; however, that interleaving is not necessarily obvious from the program text, as it is in DPJ." — §8, Runtime Checks

## Relevance to a parallel-equals-sequential equivalence theorem

- **DPJ's side condition is literally the Bernstein condition, with read/read sharing as an axiom.** Fig. 23's `(NI-READ)` has no premise, while `(NI-WRITE)` and `(NI-READ-WRITE)` both demand `R # R'`. A project whose independence predicate is `w₁∩w₂ = w₁∩r₂ = w₂∩r₁ = ∅` with shared reads permitted has adopted the same hypothesis DPJ adopts; the difference lies entirely in what is concluded from it and how. DPJ reaches the condition through a *static region approximation* (RPLs, Prop. 1 and 2 convert syntactic disjointness to location disjointness) rather than through concrete read/write footprints.

- **The gap DPJ leaves open is exactly the parallel-equals-sequential theorem.** What DPJ proves (Theorem 2) is that two *sequential* orders of two noninterfering expressions agree. What it asserts and does not formalize (§6.4) is that parallel composition agrees with sequential composition. The step from "either sequential order gives the same heap" to "every schedule of a genuinely interleaving parallel semantics gives the same heap" is the step DPJ skipped, and it is not obviously "straightforward": DPJ's `e|e'` executes the two branches atomically in one order or the other, so Theorem 2 covers it directly, but a real small-step interleaving semantics admits schedules that are not any sequential order of the two branches.

- **DPJ has no race state and no notion of schedule, so it cannot state anti-vacuity.** There is no `wrong`, no abort, no fault; a program that violates the side condition is simply rejected by the type checker, and nothing is said about its runtime behaviour. A development with an absorbing `wrong` outcome and an explicit nondeterministic step relation can say what *fails* when independence fails, which DPJ structurally cannot. Conversely, DPJ's effect system is the mature answer to the *inference* question — how a programmer states footprints modularly and intraprocedurally (§2: "this analysis is entirely intraprocedural") — which a footprint-based equivalence theorem still has to solve separately.

- **Commutativity annotations mark the boundary of a purely footprint-based result.** §5's `commuteswith` exists precisely because Bernstein independence rejects programs that are nonetheless deterministic (concurrent sets, reductions, connected components). DPJ handles these by an unchecked axiom. Any project resting on footprint disjointness alone inherits the same expressiveness limit and must either accept it or add a logical-commutativity layer — and DPJ's experience data says this is rare in practice: only 2 commutativity annotations across 5615 SLOC of six benchmarks (Table 3).

- **Empirical context (one line):** six programs — parallel merge sort, Monte Carlo and IDEA encryption from Java Grande, Barnes-Hut force computation, k-means from STAMP, and a collision-detection tree — totalling 5615 SLOC, required 600 changed lines (10.7%), 143 region declarations, 898 RPL arguments, 269 effect summaries and 2 commutativity annotations (Table 3), with speedups on 24 cores close to or beating hand-written Java threads versions (Table 2, Fig. 15).
