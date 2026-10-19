# Reading notes: eight papers on concurrency, separation logic and parallelisation

One note per paper, same template throughout (`One-line thesis` / `The setting` / `Main results,
stated` / `Proof technique` / `Side condition on parallel composition` / `Shared state / resources`
/ `What it does NOT claim` / `Mechanized?` / `Quotable lines` / `Relevance to a
parallel-equals-sequential equivalence theorem`). Every claim in every note is traceable to a
section, figure, rule name, theorem number or page of the PDF it is about; anything that could not
be verified from the PDF is marked `NOT FOUND IN PDF` rather than guessed.

Three of the PDFs are not the edition their filename suggests, and the notes say so in their header
lines: `ohearn-concur04-…` is the TCS 375 (2007) journal version, `brookes-concur04-…` is the long
TCS/Reynolds-Festschrift version (80pp, not the 19-page CONCUR paper), and `reloc-2021-…` is *ReLoC
Reloaded* in LMCS 17(3), not a conference paper. Section numbers in each note are that PDF's.

---

## The papers

**O'Hearn, *Resources, Concurrency and Local Reasoning*** —
[`ohearn-concur04-resources-concurrency-local-reasoning.md`](./ohearn-concur04-resources-concurrency-local-reasoning.md).
The paper that put `∗` into Hoare's TTPP / Owicki–Gries rules for conditional critical regions. It
is explicitly a *fluency* paper — "very much about fluency with the logic … rather than its
metatheory" (§1) — with the soundness theorem delegated to Brookes. The note reproduces the full
rule set verbatim (disjoint concurrency, resource declaration, N-ary parallel, critical region,
auxiliary-variable elimination, frame, small axioms, assertion semantics, precision) and
reconstructs both worked derivations step by step: the pointer-transferring buffer of §7.1 (four
steps: region rule for `put`, region rule for `get`, parallel rule, resource-declaration rule,
concluding `{emp} prog {RI_buf}`) and the toy memory manager of §8 with its `alloc`/`dealloc`
interface specs. Also the Reynolds counterexample of §11 in full, both derivations, and the "False
Conjecture" that restricting only the region rule's precondition to be precise does *not* restore
soundness. Nothing in the paper relates two programs; §12 names shared read access to heap cells as
an open limitation.

**Brookes, *A semantics for concurrent separation logic*** —
[`brookes-concur04-semantics-for-csl.md`](./brookes-concur04-semantics-for-csl.md).
The denotational action-trace semantics that makes CSL sound. Two findings dominate. First, his
interference predicate is *literally* Bernstein's condition: `λ1 ♯ λ2 ⇔ free(λ1) ∩ writes(λ2) ≠ {} ∨
writes(λ1) ∩ free(λ2) ≠ {}`, with "Notice that we do not regard two concurrent reads as a disaster"
(§4.4) — and `abort` is a left zero for trace concatenation, i.e. an absorbing error. Second,
**Theorem 21 (Parallel Decomposition) is a per-computation projection, not a set-level equality**:
it quantifies over *one* interleaved trace `α ∈ α1‖α2`, *one* heap partition `h = h1·h2` and *one*
local computation, and produces one local computation of each component, with no converse direction
and no statement about `[[c1‖c2]]` as a set. The Appendix proves it by induction on the lengths of
`α1` and `α2`. The note also records "local enabling" (Figure 2) in full, the Definition 24 notion
of validity, and §14's admission that the *logic* cannot prove `{z ↦ 1} x:=[z] ‖ y:=[z] {x = y = 1
∧ z ↦ 1}` although the *semantics* handles it correctly — "here is a place where the semantics is
ahead of the logic". Example 5 of §4.6 does exhibit a genuine trace-set equality between a parallel
and a sequential program, but under explicit mutual exclusion, not independence, and as an example
rather than a theorem.

**Reynolds, *Toward a Grainless Semantics for Shared-Variable Concurrency*** —
[`reynolds-fsttcs04-grainless-semantics.md`](./reynolds-fsttcs04-grainless-semantics.md).
The source for "races ↦ absorbing `wrong`", and for why. Operations have *duration*: `start(σ)`
removes the operation's footprint from the available state and `fin(σ')` returns it, so two
overlapping operations touching the same location make the second `start` go `wrong`. `Exec`
collapses everything once `wrong` is reachable (`Wrong ∪ S = Wrong`). The motivation is the "grain
of time" problem — §1 enumerates four plausible atomic grains for `x := x × x ‖ x := x + 1`, each
giving a different outcome set, and concludes "there is no default level of atomicity that is
natural for both user and implementor". Crucially, **Reynolds's `wrong` is strictly more aggressive
than Bernstein: overlapping *reads* of the same location also go wrong**, and §6 lists relaxing
this ("passivity") as future work. The paper has no numbered theorems and no proofs; the two
asserted properties (totality/lock-totality, `impossible` never arises) are stated without them.

**Vafeiadis, *Concurrent separation logic and operational semantics*** —
[`vafeiadis-mfps11-csl-and-operational-semantics.md`](./vafeiadis-mfps11-csl-and-operational-semantics.md).
CSL soundness against a *standard* small-step semantics, no instrumented semantics, no erasure
theorem. The meaning of a triple is the step-indexed `safe_n(C, s, h, J, Q)` (Definition 3.1), where
`n` is a well-foundedness device — "The number of steps merely ensures the definition is
structurally decreasing" — not a bound on the program, since validity quantifies over all `n`. The
race/fault state is `abort`, and §5's `RaceDetect` rule is Bernstein again: `(accesses(C1,s) ∩
writes(C2,s)) ∪ (accesses(C2,s) ∩ writes(C1,s)) ≠ ∅ ⟹ (C1‖C2, (s,h)) → abort`. Theorem 4.5 is
soundness; the component lemmas (Par 4.9, Frame 4.10, Share 4.11) are each proved by induction on
`n`. Precision is needed *only* for the conjunction rule, and §6 shows plainly that base CSL cannot
verify `{10 ↦ −} x := [10] ‖ y := [10] {10 ↦ −}` without adding fractional permissions. Fully
machine-checked in Isabelle/HOL (§1 fn.1, §5, §6); the RGSep extension of §7 is on paper.

**Blom, Darabi, Huisman, Safari, *Correct program parallelisations*** —
[`blom-sttt21-correct-program-parallelisations.md`](./blom-sttt21-correct-program-parallelisations.md).
The closest related work. Iteration contracts in permission-based separation logic; the derived
`b-linearise` rule (Fig. 18) converts a triple about a parallel program `P` into a triple about its
block-level-linearised form `blin(P)`, under the side condition `∀(i^b, j^{b′}) ∈ ℑ^P_⊥. (RC_P →
rc_b(i) ⋆ rc_{b′}(j))` over incomparable iteration pairs — "they are disjoint or they are read
accesses". Read/read sharing is allowed, but via Boyland fractions, not a footprint-set condition.
The whole-program result is **one-directional and existential**: §6.2, "for each program execution
there exists a corresponding b-linearised execution with the same functional behaviour … if all
independent iterations are non-conflicting". The converse — every terminal state of `blin(P)` is
reachable by `P` — is never stated. Racy executions *block* in the instrumented semantics; there is
no absorbing `wrong` and no theorem about programs violating the condition. All metatheory is
"Proof sketch 1…7" on paper; the mechanization is the VerCors tool (→ Viper → Silicon → Z3), not a
proof assistant.

**Gäher et al., *Simuliris*** — [`gaeher-popl22-simuliris.md`](./gaeher-popl22-simuliris.md).
Relational, and deliberately so: a coinductive simulation `{P} e_t ⪯ e_s {Φ}` whose adequacy
theorem gives fair termination-preserving contextual refinement of an optimized target against a
source. Notable for running on **Iris^light — "Iris without the step-indexing"**, with the
step-index fixed to 0 and the later modality dropped, justified because "With all invariants being
statically determined upfront, there is—for now—no need for step-indexing" (§8). Three reasons it
cannot express par≡seq, in increasing force: the relation is one-sided (`∀b_t ∃b_s`, refinement not
equality); the model's source-step case requires `|T_t| = |T_s|`, "a one-to-one mapping between
threads in the source and target programs", which a `par p q` vs `p; q` pair violates at the first
fork; and §9 concedes the class outright — "Simuliris cannot be used to show, for example, that it
is sound to replace a sequential program with a more efficient, concurrent implementation which
uses spinlocks to synchronize." Races-as-UB has the *opposite* polarity here: a racy source licenses
any target behaviour, and the optimizer actively mines that assumption. All results mechanized in
Coq; no Lean port mentioned.

**Frumin, Krebbers, Birkedal, *ReLoC Reloaded*** —
[`reloc-2021-mechanized-relational-logic.md`](./reloc-2021-mechanized-relational-logic.md).
Also relational: `e ≾ e' : τ` as a first-class Iris proposition, sound for contextual refinement.
The key limitation for outcome-set purposes is in the *definition* of the observable — contextual
refinement is termination preservation under contexts, with resulting values and final states
existentially quantified and unrelated, and the paper says this is deliberate: "contextual
refinement only takes termination into account, and does not require the resulting values v and v'
to be equal. Demanding the equality on the resulting values would make contextual refinement too
strong" (p. 9:9). So even `≃ctx` never asserts two programs reach the same (result, final-state)
pairs. There is **no disjointness side condition at all**: `REL-FORK` is simply `∆ ⊨ e₁ ≾ e₂ : unit
⟹ ∆ ⊨ fork{e₁} ≾ fork{e₂} : unit`, and interference is controlled by a *temporal* discipline
(invariants may be opened only across a single atomic left-hand step, because left-hand scheduling
is demonic) rather than by footprints. No case study relates a concurrent program to a sequential
one — the "coarse-grained" side is always still concurrent, instrumented with a lock, so that the
refinement expresses linearizability. ~10 300 lines of Coq; no Lean port mentioned.

**Bocchino et al., *A Type and Effect System for Deterministic Parallel Java*** —
[`dpj-oopsla09-deterministic-parallel-java.md`](./dpj-oopsla09-deterministic-parallel-java.md).
A region-and-effect type system (region path lists, index-parameterized arrays, partitions,
`cobegin`/`foreach`) whose noninterference judgment `Γ ⊳ E # E'` (Fig. 23) **is** Bernstein, with
`(NI-READ)` an axiom carrying no premise — read/read sharing allowed unconditionally. DPJ *claims*
par≡seq twice (§1 contribution 3: "guarantees semantic equivalence between a DPJ program and its
obvious sequential Java version"; §6.4: "parallel composition of noninterfering expressions produces
the same result as sequential composition") but what it *proves* (Theorem 2, Appendix C.3) relates
two **sequential** compositions in opposite orders — no parallel operator, no schedule, no
interleaving — and §6.4 then declines to close the gap: "The formalization of this property is
straightforward, and we omit it from our technical report." §6 states outright, "We have chosen to
make Core DPJ a sequential language." Nothing is mechanized; the only proofs live in tech report
UIUCDCS-R-2008-2980, on paper. Violating programs are rejected by the type checker; there is no
race state and no `wrong`, so DPJ structurally cannot state an anti-vacuity result.

---

## Comparison

| paper | judgment arity | side condition for `∥` | read/read sharing | shared state mechanism | proves par≡seq? | mechanized? |
|---|---|---|---|---|---|---|
| **O'Hearn** CONCUR'04 / TCS'07 | unary (Hoare triple `{P}C{Q}`) | `∗` on preconditions + syntactic variable non-interference ("no variable free in `Pi` or `Qi` is changed in `Cj` when `j ≠ i`") | **no** on the heap (`∗` is strict disjointness); §12 names it a limitation | resource invariants `RI_r` + conditional critical regions; semaphores encoded as CCRs; auxiliary variables | **no** — nothing relates two programs | no |
| **Brookes** CONCUR'04 / TCS'07 | unary (`Γ ⊢ {p}c{q}`), over a denotational trace semantics with a separate `[[c]] = [[c']]` equivalence | logic: `∗` + `(free(c1) ∩ writes(c2)) ∪ (free(c2) ∩ writes(c1)) ⊆ owned(Γ)`. semantics: `λ1 ♯ λ2 ⇔ free∩writes ≠ ∅` either way | **semantics yes** ("we do not regard two concurrent reads as a disaster"); **logic no** — §14 gives an unprovable-but-valid read-shared formula | resource contexts `Γ : r(X) : R` + CCRs, nested; ownership transfer in the local-enabling `acq`/`rel` clauses | **no theorem**; one worked trace-set equality (§4.6 Ex.5) under explicit mutual exclusion. Thm 21 is a per-computation projection, one-directional | no |
| **Reynolds** FSTTCS'04 | none (pure semantics; trace sets + `Exec`) | **none** — composition is unconditional fair merge; interference is detected at execution time | **no** — overlapping *reads* also go `wrong`; "passivity" is future work (§6) | locks only (`try`/`acq`/`rel` over a lock set `κ`); **no resource invariants, no state transfer** | **no** — no theorems at all; only an observational-equivalence remark between two *sequential* commands (§6) | no |
| **Vafeiadis** MFPS'11 | unary (`J ⊢ {P}C{Q}`, meaning via step-indexed `safe_n`) | `∗` on preconditions + `fv(J,Pi,Ci,Qi) ∩ wr(Cj) = ∅` both ways. Operationally, `RaceDetect` aborts on `(accesses ∩ writes)` either way | **no** in base CSL; **yes** with the §6 fractional-permission extension (`10 ↦^0.5 −`) | single invariant `J` + `atomic C` (§2–4); multiple resources `Γ` + CCRs (§5); rely/guarantee in §7 (RGSep) | **no** — every judgment mentions one command | **yes**, Isabelle/HOL (CSL, multi-resource, permissions); RGSep on paper |
| **Blom et al.** STTT 2021 | unary (`{P} S {Q}` in permission-based SL); `b-linearise` relates `P` to `blin(P)` but is still a unary rule | `∀(i^b, j^{b′}) ∈ ℑ^P_⊥. (RC_P → rc_b(i) ⋆ rc_{b′}(j))` — "disjoint or they are read accesses" | **yes**, via Boyland fractions in `(0,1)` | fractional permissions; `send`/`receive` ghost statements inside `Vec` blocks (none inside `Par`) | **partly, one-directional**: "for each program execution there exists a corresponding b-linearised execution with the same functional behaviour" (§6.2). The converse is never stated | **no proof assistant** — "Proof sketch 1…7" on paper; VerCors → Viper → Z3 is the tool |
| **Gäher et al.** POPL'22 | **relational** (`{P} e_t ⪯ e_s {Φ}`, coinductive simulation) | model-level, not a rule: `∗`-disjoint resources **plus** `\|T_t\| = \|T_s\|` (one-to-one thread mapping). No `par` rule exists | **yes**, via fractional permissions (`exploit_frac(Rd(q)) = q`) | Iris ghost state: `heapbij`, `LOC-ESCAPE`, `EXPLOIT-*`/`RELEASE-EXPLOIT`; races-as-UB exploited as an *assumption* | **no**, and §9 concedes the class: cannot show "it is sound to replace a sequential program with a more efficient, concurrent implementation" | **yes**, Coq on Iris^light (Iris with step-index fixed to 0). No Lean port |
| **Frumin et al.** LMCS 2021 | **relational** (`∆ ⊨ e₁ ≾ e₂ : τ`, one-sided refinement; equivalence = both directions) | **none** — `REL-FORK` requires only that the two bodies are related at `unit`; threads may share arbitrary mutable state | **yes**, and read/write and write/write sharing too; controlled by atomicity + invariants, not disjointness | Iris invariants + higher-order ghost state + a ghost thread pool (`i ⤇ e`, `↦ₛ`); locks, prophecy variables | **no** — and contextual refinement's final states are existentially quantified and unrelated, so even `≃ctx` is weaker than outcome-set equality | **yes**, ~10 300 lines of Coq on Iris. No Lean port |
| **Bocchino et al.** OOPSLA'09 | unary (type-and-effect judgment `Γ; ε ⊢ e : T, E`) | `Γ ⊳ E # E'` (Fig. 23): write/write and read/write require region disjointness; **`(NI-READ)` has no premise** | **yes, unconditionally** — `(NI-READ)` is an axiom; §3.3's worked example has disjoint writes with "possibly overlapping reads" | regions (RPLs), region parameters, index-parameterized arrays, partitions; **no transfer** — regions are static names. `commuteswith` is unchecked | **claimed, not proved**: §1 and §6.4 assert semantic equivalence with the sequential version; Theorem 2 relates two *sequential* orders, and §6.4 omits the parallel formalization | **no** — no proof assistant anywhere; Theorems 1–2 stated in the paper, proofs only in TR UIUCDCS-R-2008-2980, on paper |

---

## How to read the table

- **"Judgment arity"** is the crux. Five of the eight systems are unary: they specify one program.
  Two (Simuliris, ReLoC) are relational but one-sided (refinement), and neither relates a parallel
  program to a sequential one — Simuliris because its model demands equal thread counts, ReLoC
  because its observable discards final states. DPJ is unary and *claims* a par≡seq equivalence it
  does not prove.
- **Three different objects are called "the independence condition"** and they are not the same.
  `∗` (O'Hearn, Brookes's logic, Vafeiadis's base CSL) forbids read sharing. Fractional permissions
  (Blom, Simuliris, Vafeiadis §6) recover read sharing by splitting ownership. A Bernstein footprint
  condition (`w₁∩w₂ = w₁∩r₂ = w₂∩r₁ = ∅`) recovers it by comparing *sets*. Brookes's `λ1 ♯ λ2`,
  Vafeiadis's `RaceDetect` and DPJ's `Γ ⊳ E # E'` are the three places the Bernstein shape appears
  verbatim — but in the first two it is the *definition of a race in the semantics*, and in the
  third it is a *typing side condition*; in none of the three is it the hypothesis of an equality of
  outcome sets.
- **"Races go to an absorbing error" means different things.** Reynolds's `wrong` (`Wrong ∪ S =
  Wrong`) and Brookes's `abort` (a left zero for concatenation) *exclude* racy programs from
  consideration. Simuliris's UB does the opposite — it is an assumption the optimizer exploits to
  gain ownership. Blom's racy executions merely block. DPJ has no race state at all.
