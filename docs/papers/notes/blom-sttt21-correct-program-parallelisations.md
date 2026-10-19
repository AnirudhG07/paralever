# Correct program parallelisations
S. Blom, S. Darabi, M. Huisman, M. Safari · International Journal on Software Tools for Technology Transfer (STTT), Special Issue: MeTRID, 2021 (accepted 10 December 2020) · `blom-sttt21-correct-program-parallelisations.pdf`

> Extended version of Darabi, Blom, Huisman, NFM 2017 [12]; the basic-block rules are rephrased
> from Blom, Darabi, Huisman, FASE 2015 [5] (stated in Sect. 1, "This paper is an extended
> version of our paper presented at NFM 2017 [12]. In addition, it contains (1) a rephrasing of
> the verification rules for parallel and vectorised loops, presented at FASE 2015 [5] ... and (2)
> an algorithm that encodes a commonly used subset of OpenMP into PPL.").

## One-line thesis
If a user annotates each basic block of a deterministic-parallel program with an *iteration
contract*, and one discharges the side condition that all iteration pairs which are not ordered
sequentially have non-conflicting heap accesses, then verifying the **block-level linearised**
(sequentialised) variant of the program against the global contract suffices to conclude data-race
freedom and functional correctness of the *parallel* program.

## The setting

**Language.** Not a real language but an intermediate representation, **PPL** ("Parallel
Programming Language"), Sect. 3.1, Fig. 8:

```text
Parallel Programming Language:

  P    ::= P ‖ P | P ⊕ P | P ⨟ P |
           Par(N) S | S
  S    ::= s;S | skip
  s    ::= assg | if (b) {S} else {S} | while (b) {S} | Vec(N) V
  V    ::= b ⇒ assg;V | skip
  assg ::= v := e | gv := e | v := mem(e) | mem(e) := v |
           [e] := e
  b    ::= b ∧ b | ¬b | e = e | e ≤ e | …
  e    ::= v | gv | N | e + e | e − e | [e] | …
  v    ::= thread local variables
  gv   ::= program global variables
  N    ::= integer constants
```

Three *basic* blocks — parallel `Par(N) S`, vectorised `Vec(N) V`, sequential `S` — and three
binary composition operators: parallel `‖`, fusion `⊕`, sequential `⨟` (Sect. 3.1). Precedence
`⊕ > ‖ > ⨟` (Sect. 4.2). Fusion operands must be parallel basic blocks with the *same*
parallelisation level (extra well-formedness condition, Sect. 3.1). Each basic block has a
read-only `tid ∈ [0..N)`.

Sect. 4 gives an encoding (Fig. 15) of a subset of OpenMP (`omp parallel`, `omp for`, `omp simd`,
`omp for simd`, `omp sections`, `omp single`; relevant clauses `simdlen(M)`, `schedule(static)`,
`nowait`; grammar Fig. 14) into PPL. `nowait` + `schedule(static)` on two `omp for`s ⇒ `⊕`;
`nowait` alone ⇒ `‖`; otherwise `⨟` (Sect. 4.2).

**Memory model.** "For simplicity, but without loss of generality, threads have access to a single
shared array which we refer to as heap. We assume all memory locations in the heap are allocated
initially." (Sect. 3.1). Three domains (Sect. 3.2): `h ∈ SharedMem = Loc → Val` (heap), `γ ∈ Store
= VarName → Val` (program store, constant within a block, holds globals), `σ ∈ PrivateMem =
VarName → Val` (per-thread private memory).

**Atomic grain / consistency.** Interleaving semantics at the granularity of single assignments and
single `mem` reads/writes; **sequential consistency is implicit** — the paper never discusses a
weak memory model. `Par` interleaves freely ("To allow all possible interleavings of the threads in
the block's thread pool, each thread has its own local state LS, which can be executed
independently", Sect. 3.2); `ParC` "non-deterministically evaluates one of its block states"
(Sect. 3.2). `Vec` runs in **lock-step**: "all threads execute the same instruction, no thread can
proceed to the next instruction until all are done, meaning that they all share the same program
counter", implemented via auxiliary set `E ⊆ [0..N)` and rule `Vec Sync` (Sect. 3.2, Fig. 12).

**Semantics shape.** Small-step operational semantics in three layers (Sect. 3.2):
`→_p ⊆ (BlockState × Store × SharedMem)²` (Fig. 11), auxiliary `→_s ⊆ (LocalState ×
SharedMem)²` (Fig. 12), `→_assg ⊆ (PrivateMem × S × SharedMem) × (PrivateMem × SharedMem)`
(Fig. 13). There is **no `wrong`/fault state in the base semantics**; instead an *instrumented*
semantics is layered on (Sect. 6.2) in which transitions carry a heap mask and "If a transition
cannot satisfy its premises, it **blocks**" — i.e. racy steps are *stuck*, not absorbing-error.

A separate **denotational trace semantics** is introduced in Sect. 5.3.1 only for the soundness
argument: "The denotational semantics that is defined in this section is equivalent to the
operational semantics as defined in Sect. 3, but the proof is omitted from the paper."

**Terminating programs only?** Yes, in the sense that only finite executions are considered.
Definition 9: "An execution of a program P is a finite sequence of state transitions `Init(P), γ, h
→*_p Done, γ, h'`." Hoare triples are read as **partial correctness**: "if the precondition P holds
in a state s, and if execution of statement S from state s terminates in a state s′, then the
postcondition Q holds in this state s′" (Sect. 5.3). `while` is in the syntax (Fig. 8), so
nonterminating programs are expressible but are simply outside the set of executions reasoned
about.

**Judgment form.** A **unary Hoare triple** `{P} S {Q}` in permission-based separation logic with
fractional permissions (Sect. 2.2, Sect. 5.3), plus one derived program-transformation rule
(`b-linearise`, Fig. 18) whose premise mentions a *transformed* program `blin(P)`. Assertions
(Sect. 2.2):

```text
F ::= b | Perm(e₁, e₂) | b ? F : F | F ⋆ F | ★_{i∈I} F(i)
b ::= true | false | e₁ == e₂ | e₁ ≤ e₂ | ¬b | b₁ ∧ b₂ | …
e ::= v | n | [e] | e₁ + e₂ | e₁ − e₂ | …
```

Permissions are Boyland fractions [9]: "any fraction in the interval (0, 1) denotes a read
permission, while 1 denotes a write permission" (Sect. 2.2). Semantics (Fig. 6) is a hybrid of
implicit dynamic frames [25] and fractional-permission separation logic: `σ, h, π ⊨ F` iff
`(σ, h, π₀ ⊨ F ⇓ π′) ∧ (π′ ≤ π)`, with memory masks `π : Loc → Frac` (Sect. 2.2).

## Main results, stated

### Fig. 16 — proof rule **ParBlock** (Sect. 5.2)

```text
          ∀i ∈ [0..N). {rc(i) ⋆ P(i)} S(i) {rc(i) ⋆ Q(i)}
  ──────────────────────────────────────────────────────────────────── [ParBlock]
   { ★_{i=0}^{N−1} rc(i) ⋆ P(i) } Par(N) S { ★_{i=0}^{N−1} rc(i) ⋆ Q(i) }
```

where `S(i)` is the body of the i-th iteration. Commentary (Sect. 5.2): "As the threads execute
completely independently, there is no permission transfer, and the resource pre- and postcondition
coincide. Notice further that soundness of this rule implies that all threads in a parallel block
must be independent, because otherwise the universal separating conjunction would not be
satisfiable."

### Fig. 17 — proof rule **VecBlock** (Sect. 5.2)

```text
        ∀i ∈ [0..N). {rc_pre(i) ⋆ P(i)} S(i) {rc_post(i) ⋆ Q(i)}
  ──────────────────────────────────────────────────────────────────────────────── [VecBlock]
   { ★_{i=0}^{N−1} rc_pre(i) ⋆ P(i) } Vec(N) V { ★_{i=0}^{N−1} rc_post(i) ⋆ Q(i) }
```

"It is similar in spirit to the **ParBlock** rule, but does not require the resource pre- and
postcondition to be the same." (Sect. 5.2)

### Eq. (1) — **send** / **receive** ghost statements (Sect. 5.2)

```text
  ───────────────────────────── [send]
   {P} send P to L, d {true}
                                                    (1)
  ───────────────────────────────── [receive]
   {true} receive P from L, d {P}
```

Usable only under the syntactic criterion (i) "send and receive annotations always come in pairs"
and the two proof obligations

```text
(ii)  ∀j ∈ [0..N). b_r(j)  ⟹  j ≥ d ∧ b_s(j − d)            (2)

(iii) ∀j ∈ [d..N). φ(j − d)  ⟹  ψ(j)                        (3)
```

(Sect. 5.2). `d` is the "distance of dependence": `send` at label `L_s` in iteration `i` transfers
to label `L_r` in iteration `i + d`.

### Denotational semantics used in the soundness proof (Sect. 5.3.1)

```text
Definition 5   ⟦Par(N)S⟧  = Interleave^{j=1..N} Concat^K_{i=1} ⟦S^j_i⟧

Definition 6   ⟦Vec(N)S⟧  = Interleave^{j=1..N} SynchConcat^K_{i=1} ⟦S^j_i⟧

Definition 7 (sequential execution trace)
               ⟦Par(N)S⟧^Seq = Concat^N_{j=1} Concat^K_{i=1} ⟦S^j_i⟧
               ⟦Vec(N)S⟧^Seq = Concat^N_{j=1} SynchConcat^K_{i=1} ⟦S^j_i⟧

Definition 8 (instrumented sequentialised execution traces)
   ⟦Par(N)S⟧^Seq_Spec = Concat^N_{j=1} ( Assert rc(j) ⋆ P(j) ++
                                          Concat^K_{i=1} ⟦S^j_i⟧ ++
                                          Assert rc(j) ⋆ Q(j) )

   ⟦Vec(N)S⟧^Seq_Spec = Concat^N_{j=1} ( Assert rc(j) ⋆ P(j) ++
                                          SynchConcat^K_{i=1} ⟦S^j_i⟧ ++
                                          Assert rc(j) ⋆ Q(j) )
```

"where Assert checks the pre- and postcondition before and after each iteration. If the asserted
property φ holds, Assert φ behaves as a skip; otherwise, it aborts (i.e. there is no execution).
Note that the sequential execution trace is in happens-before order." (Sect. 5.3.1)

Supporting definitions: Def. 2 (execution trace = finite sequence of statement instances); Def. 3
plain concatenation `C₁ ++ C₂ = {c₁·c₂ | c₁ ∈ C₁ ∧ c₂ ∈ C₂}`; Def. 4 synchronised concatenation
`C₁ # C₂ = {c₁·b·c₂ | …}` inserting a barrier `b`; `Interleave` defined with a happens-before order
`<` maintaining program order (PO) and synchronisation order (SO).

### Theorem 1 (Sect. 5.3.2) — verbatim

```text
Theorem 1  All execution traces in ⟦Par(N) S⟧ and ⟦Par(N) S⟧^Seq_Spec are
           functionally equivalent only if all contracts hold.
```

(The "only if" is as printed in the PDF, p. 15, col. 2. The surrounding prose says what is
actually proved: "We prove that every execution trace in ⟦Par(N) S⟧ is functionally equivalent to
the single execution trace ⟦Par(N) S⟧^Seq_Spec **if all contracts hold**, by showing that any
execution trace can be reordered until it is the sequential execution order.")

### Theorem 2 (Sect. 5.3.2) — verbatim

```text
Theorem 2  All execution traces in ⟦Vec(N) S⟧ and ⟦Vec(N) S⟧^Seq_Spec are
           functionally equivalent.
```

Note immediately after Theorem 1: "As a corollary of Theorem 1, we can also conclude that all
executions in ⟦Par(N) S⟧ are data-race-free."

### Fig. 18 — proof rule **b-linearise** (Sect. 6.1)

```text
 ( ∀(i^b, j^{b′}) ∈ ℑ^P_⊥. (RC_P → rc_b(i) ⋆ rc_{b′}(j)) )    {RC_P ⋆ P_P} blin(P) {RC_P ⋆ Q_P}
 ───────────────────────────────────────────────────────────────────────────────────────────── [b−linearise]
                             {RC_P ⋆ P_P} P {RC_P ⋆ Q_P}
```

with (Sect. 6.1)

```text
ℑ^P_⊥ = { (i^{b₁}, j^{b₂}) | i^{b₁}, j^{b₂} ∈ I_P ∧ b₁ ≠ b₂ ∧ i^{b₁} ⊀_e j^{b₂} ∧ j^{b₂} ⊀_e i^{b₁} }

∀i^b, j^{b′} ∈ I_P. i^b ≺_e j^{b′} ⇔ (b ≺ b′) ∨ ((b ≺_⊕ b′) ∧ (i = j))

            ⎧ ∅,                     if P ∈ {Par(N) S, S}
G(P, δ)  =  ⎨ G,                     if P = P′ δ P″ = •
            ⎩ G ∪ (B_{P′} × B_{P″}), otherwise          where G = G(P′, δ) ∪ G(P″, δ)

≺ = G(P, ⨟)      ≺_⊕ = G(P, ⊕)
```

`blin : P → P_⨟` is "a program transformation which substitutes all non-sequential compositions by
a sequential composition" (Sect. 6.1).

### Lemmas and Theorem 3 (Sect. 6.2) — verbatim

```text
Definition 10 (Instrumented Execution). An instrumented execution of a program P is a
   finite sequence of state transitions Init(P, π), γ, h →*_{p,i} Done(π), γ, h′ where the
   set of all instrumented executions of P is written as IE_P.

Lemma 1  Assuming that (1). ∀(i^b, j^{b′}) ∈ ℑ^P_⊥. RC_P → rc_b(i) ⋆ rc_{b′}(j) and
   (2). ∀b ∈ B_P. {★_{i∈[0..N_b)} rc_b(i)} P_b {★_{i∈[0..N_b)} rc_b(i)} are valid for a
   program P (i.e. every basic block in P respects its iteration contract), for any
   execution E of the program P, there exists a corresponding instrumented execution.

Lemma 2  All instrumented executions of a program P are data-race-free.

Definition 11 (Normalised Execution). An instrumented execution labelled by L is
   normalised if the labels of its transitions are in non-decreasing order.

Lemma 3  For each instrumented execution of a program P, there exists a normalised
   execution such that they both end in the same terminal state.

Lemma 4  For each normalised execution of a program P, there exists a b-linearised
   execution blin(P), such that they both end in the same terminal state.

Definition 12 (Validity of Hoare Triple). The Hoare triple {RC_P ⋆ P_P} P {RC_P ⋆ Q_P}
   is valid if for any execution E (i.e. Init(P), γ, h →*_p Done, γ, h′) if γ, h, π ⊨
   RC_P ⋆ P_P is valid in the initial state of E, then γ, h′, π ⊨ RC_P ⋆ Q_P is valid in
   its terminal state.

Theorem 3  The rule b-linearise is sound.

Proposition 1  A verified program is data-race-free.
```

The proof obligation shape for the **composition** side condition in prose (Sect. 6): "by proving
that all the heap accesses of all iterations which are not ordered sequentially are non-conflicting
(i.e. they are disjoint or they are read accesses)."

### Fig. 19 — instrumented operational rules (Sect. 6.2)

```text
                       π₁ + π₂ ≤ π
  ───────────────────────────────────────────────────────────────────── [Init ParC]
   Init(P₁‖P₂, π), γ, h →_{p,i} ParC(Init(P₁, π₁), Init(P₂, π₂), π), γ, h

  ───────────────────────────────────────────────────────────── [ParC Done]
   ParC(Done(π₁), Done(π₂), π), γ, h →_{p,i} Done(π), γ, h

          l = E⟦e⟧_σ     π(l) > 0
  ──────────────────────────────────────────────── [rdsh]
   σ, v := mem(e), h, π →_{assg,i} σ[v := h(l)], h, π

          l = E⟦e⟧_σ     π(l) = 1
  ──────────────────────────────────────────────── [wrsh]
   σ, mem(e) := v, h, π →_{assg,i} σ, h[l := v], π
```

### Sect. 6.3 — strengthened side condition when resource pre/post differ

```text
∀(i^b, j^{b′}) ∈ ℑ^P_⊥. ( RC_P → rc_pre,b(i)  ⋆ rc_pre,b′(j)  ∧
                                  rc_pre,b(i)  ⋆ rc_post,b′(j) ∧
                                  rc_post,b(i) ⋆ rc_pre,b′(j)  ∧
                                  rc_post,b(i) ⋆ rc_post,b′(j) )
```

This is claimed sound **only for a single resource transfer**. For multiple transfers: "we need to
define the *intermediate maximal resource contract* for an intermediate statement S … Absence of
conflicts is then defined as a check over all intermediate resource contracts. **It is future work
to define this formally.**" (Sect. 6.3)

## Proof technique

Two separate arguments.

**(a) Basic blocks (Sect. 5.3), Theorems 1 and 2.** A *denotational* trace semantics is defined
(Defs. 1–8) for non-nested blocks with K guarded statements, and the proof is a **reordering /
adjacent-transposition argument**: "Functional equivalence of the two traces is shown by
transforming the computations in one trace into the computations in the other trace by swapping
adjacent independent execution steps." (Sect. 5.3). Proof sketch 1 is an induction on the length of
the matched prefix: assume the first `n` steps agree with the sequential trace; `t_{n+1}` must occur
somewhere later in the given trace; since the sequential trace is in happens-before order, all of
`t_{n+1}`'s predecessors are already in the prefix, so every intermediate step is independent of
`t_{n+1}` and can be swapped past it; repeat. The second half of Proof sketch 1 is a separate
induction over the `N` iterations showing `P₀ ⋆ … ⋆ P_N` is consumed into `Q₀ ⋆ … ⋆ Q_N`. For
`Vec` (Theorem 2) "swapping past barriers is never necessary" because `SynchConcat` inserts
barriers.

**(b) Block composition (Sect. 6.2), Theorem 3.** A chain of four lemmas over the *operational*
semantics:

1. **Lemma 1** — from the two assumptions (non-conflicting incomparable iteration pairs + every
   block respects its iteration contract), every execution `E` can be decorated with heap masks,
   yielding a corresponding instrumented execution. Proof is by assigning `π ≤ 1` initially and
   splitting at each `Init ParC`/`Init Par`/`Init Vec`.
2. **Lemma 2** — instrumented executions are data-race-free. Proof by contradiction on permission
   arithmetic: a write needs `π₁(e) = 1`, a concurrent access needs `π₂(e) > 0`, and permissions
   only descend from a common ancestor thread so `π₁(e) + π₂(e) ≤ π_z(e) ≤ 1`.
3. **Lemma 3** — *normalisation*: an adjacent-transposition argument again, this time on labelled
   instrumented transitions, using Lemma 2 to argue that any two swapped accesses to a shared
   location must both be reads, hence the swap preserves functionality and the terminal state.
4. **Lemma 4** — a state map `M : BlockState → BlockState` (given explicitly in Proof sketch 5)
   carries a normalised execution to an execution of `blin(P)` with the same terminal state.

Theorem 3 then composes: from the `b-linearise` premises, Lemma 1 gives an instrumented execution
`IE`; Lemmas 3 and 4 give a `blin(P)` execution `E′` with the same terminal state; the triple for
`blin(P)` plus soundness of the underlying program logic (cited as [5]) transfers the postcondition
back to `IE`.

**Key lemma:** Lemma 3 (normalisation by commuting non-conflicting adjacent transitions) is the
load-bearing step; everything else is bookkeeping around it. The induction in both (a) and (b) is
over the **position in a finite execution trace**, not over program syntax.

## Side condition on parallel composition

Two distinct side conditions, at two levels.

**Inside a parallel basic block** — implicit in `ParBlock` (Fig. 16): the precondition of the whole
block is `★_{i=0}^{N−1} rc(i) ⋆ P(i)`, the **universal separating conjunction** over all `N`
iterations. Verbatim justification (Sect. 5.2):

> "As the threads execute completely independently, there is no permission transfer, and the
> resource pre- and postcondition coincide. Notice further that soundness of this rule implies that
> all threads in a parallel block must be independent, because otherwise the universal separating
> conjunction would not be satisfiable."

**Between composed blocks** — the left premise of `b-linearise` (Fig. 18), verbatim:

```text
∀(i^b, j^{b′}) ∈ ℑ^P_⊥. ( RC_P → rc_b(i) ⋆ rc_{b′}(j) )
```

and in prose (Sect. 6):

> "by proving that all the heap accesses of all iterations which are not ordered sequentially are
> non-conflicting (i.e. **they are disjoint or they are read accesses**)."

**Is read/read sharing allowed? Yes**, and it is essential. It is obtained not by a Bernstein-style
set condition but by **fractional permissions**: "any fraction in the interval (0, 1) denotes a read
permission, while 1 denotes a write permission. Permissions can be split and combined, but
soundness of the logic ensures that for every memory location the total sum of permissions over all
threads to access this location does not exceed 1" (Sect. 2.2). So `rc_b(i) ⋆ rc_{b′}(j)` is
satisfiable when both ask only for `read` on the same cell, but not when either asks for `write`.
Example 9's contract `requires Perm(c[tid], write) ** Perm(a[tid], read)` is exactly this:
disjoint writes to `c`, shared reads of `a`. Lemma 3's proof turns on it: "from Lemma 2 we know
that this is data-race-free, thus any accesses of t₁ and t₂ to a shared heap location must be
reads."

**Fractional/read permissions used? Yes** — Boyland fractions [9], Sect. 2.2, with the `read`
keyword as sugar for "an arbitrary read permission" and `write` for 1.

**Ownership transfer?**
- *Across `‖` / `⊕` composition and inside `Par`*: **no**, by design (quote above).
- *Inside a `Vec` block*: **yes**, via `send`/`receive` ghost statements at the implicit per-
  instruction barriers, with distance-`d` inter-iteration dependence (Sect. 5.2, Eq. 1–3). "The
  rules for the send and receive ghost statements are similar in spirit to the rules that are
  typically used for permission transfer upon lock acquiring and release (see e.g. [15]). In
  particular, send is used to give up resources that the receive acquires."
- *With differing `rc_pre`/`rc_post` across composed blocks*: Sect. 6.3 strengthens the b-linearise
  premise to the four-way conjunction above; sound only for a single transfer, the general case is
  explicitly future work.

## Shared state / resources

Yes, there is shared mutable state: a single shared heap `h : Loc → Val`, with every location
preallocated (Sect. 3.1). Access is governed by **fractional permissions** (memory masks
`π : Loc → Frac`), not by resource invariants.

Mechanisms present:
- **Permission splitting at fork.** In the instrumented semantics, `Init ParC` (Fig. 19) carries the
  premise `π₁ + π₂ ≤ π`, and in general "there are `n ≥ 2` heap masks `π₁, …, πₙ`, one for each newly
  initialised state such that `Σⁿᵢ πᵢ ≤ π`" (Sect. 6.2). `ParC Done` collects back to `π`.
- **Access checks.** `rdsh` requires `π(l) > 0`; `wrsh` requires `π(l) = 1` (Fig. 19).
- **`send`/`receive` ghost transfer inside vectorised blocks** (rule set Eq. 1 above) — the only
  genuine ownership-transfer mechanism in the paper.

Mechanisms **absent**: no locks, no CAS, no atomics, no resource invariants, no ghost state beyond
`send`/`receive`. Atomics are listed as future work (Sect. 10): "We also plan to identify the subset
of atomic operations that can be combined with our technique that allows verification of the widely
used reduction operations." No concurrent abstract predicates (CAP/iCAP is only discussed as
related work, Sect. 9, ref. [13,14]).

## What it does NOT claim

**Does it prove an equality or equivalence between a parallel program and a sequential one?
Partly — and strictly less than a two-sided outcome-set equality.** Be precise about three separate
things:

1. **Theorem 1 / Theorem 2 are *per-block* trace statements, not whole-program ones.** They relate
   `⟦Par(N) S⟧` (a *set* of interleaved traces of one basic block) to `⟦Par(N) S⟧^Seq_Spec` (**a
   single** instrumented sequentialised trace), and only "functionally equivalent", i.e. agreeing
   on the computed values/terminal state — not an equality of trace sets, and not a statement about
   composed programs.

2. **At the whole-program level the result is one-directional and existential.** Sect. 6.2 states
   exactly what is proved: "we show that for each program execution there exists a corresponding
   b-linearised execution with the same functional behaviour (i.e. they end in the same terminal
   state if they start in the same initial state) if all independent iterations are
   non-conflicting." Lemma 3 and Lemma 4 are both of the form "for each X there exists a Y ending in
   the same terminal state". **The converse direction — that every terminal state of `blin(P)` is
   reachable by `P` — is never stated or proved.** So this is a (conditional, one-sided) refinement
   `P ⊑ blin(P)` on terminal states, not `P ≡ blin(P)`.

3. **The whole thing is conditional on *verified contracts*.** Lemma 1 (and hence Theorem 3) assumes
   (1) all incomparable iteration pairs are non-conflicting *as derivable from `RC_P`*, and (2) every
   basic block provably respects its iteration contract. Nothing is claimed about programs lacking
   such annotations. There is no "if the condition fails then the program goes `wrong`" direction;
   failing executions simply **block** in the instrumented semantics, and no theorem characterises
   programs that violate the condition.

Also not claimed:
- No relational / contextual-refinement judgment, no simulation relation between two programs as a
  first-class object. The only "two-program" object is the derived rule `b-linearise`, which relates
  a triple about `P` to a triple about `blin(P)` — syntactically, within a unary logic.
- Nothing about nonterminating executions (Def. 9 fixes executions to be finite, ending in `Done`).
- Nothing about weak memory.
- The equivalence of the denotational trace semantics (Sect. 5.3.1) to the operational semantics of
  Sect. 3 is **asserted and the proof omitted**: "but the proof is omitted from the paper."
- Sect. 5.3.1 formalises **non-nested blocks** only: "We develop our formalisation for non-nested
  blocks with K guarded statements."
- The resource-transfer extension (Sect. 6.3) for *multiple* transfers within a block is explicitly
  "future work to define this formally."
- They do **not** synthesise parallel code: "Unlike them, we do not generate any parallel program.
  Instead we prove that parallelisation annotations can safely be applied" (Sect. 9).

## Mechanized?

**Not in a proof assistant.** The words "Coq", "Isabelle", "mechanised/mechanized" do not appear
anywhere in the PDF. All metatheory (Theorems 1–3, Lemmas 1–4, Proposition 1) is on paper and
presented as *proof sketches* — labelled literally "Proof sketch 1" … "Proof sketch 7".

What *is* implemented is the **verification technique**, in the **VerCors** program verifier
(Sect. 7, Fig. 20; tool at `https://github.com/utwente-fmt/vercors`, footnote 4). Pipeline:
annotated OpenCL / OpenMP / PVL / Java → VerCors transformations → Viper's intermediate language
Silver → Silicon → Z3 (Fig. 20). Concretely implemented (Sect. 7.1–7.2):
- basic blocks and `send`/`receive` encoded as Viper method contracts (`basic_block`,
  `block_body`, `send_s_to_r`, `receive_r_from_s`);
- "a function to compute the set `ℑ^P_⊥`", and "the program transformation `blin`, resulting in a
  Viper program called `blin_program()`";
- the first proof obligation emitted as `indep_iteration(b,b′,i,j)` lemma stubs with
  `requires RC_P; ensures rc_b(i) ⋆ rc_{b′}(j);`.

Steps 2 and 3 (OpenMP→PPL encoding, and PPL→Viper checking) are stated to be "fully automatic, the
user only has to provide the specifications" (Sect. 7). Sect. 8 reports the OpenMP example of
Fig. 2 verified in **25 seconds**; the examples of Figs. 21 and 22 are "successfully verified by
VerCors". No benchmark table or broader evaluation is given.

So: **tool-supported, not machine-checked metatheory.**

## Quotable lines

- "it is sufficient to establish functional correctness on a linearised version of the original
  program to conclude functional correctness of the parallel program." — Abstract
- "by proving that all the heap accesses of all iterations which are not ordered sequentially are
  non-conflicting (i.e. they are disjoint or they are read accesses)." — Sect. 6, opening paragraph
  (p. 16)
- "we show that for each program execution there exists a corresponding b-linearised execution with
  the same functional behaviour (i.e. they end in the same terminal state if they start in the same
  initial state) if all independent iterations are non-conflicting." — Sect. 6.2 (p. 17)
- "As the threads execute completely independently, there is no permission transfer, and the
  resource pre- and postcondition coincide." — Sect. 5.2, on **ParBlock** (p. 13)
- "we prove that parallelisation annotations can safely be applied and the parallelised program is
  functionally correct and exhibits the same behaviour as its sequential counterpart." — Sect. 9,
  Related work (p. 21)
- "The denotational semantics that is defined in this section is equivalent to the operational
  semantics as defined in Sect. 3, but the proof is omitted from the paper." — Sect. 5.3.1 (p. 14)
- "If a transition cannot satisfy its premises, it blocks." — Sect. 6.2, on the instrumented
  semantics (p. 17)

## Relevance to a parallel-equals-sequential equivalence theorem

- **The side condition has the same *shape* as Bernstein's but is expressed as permission
  disjointness, not as a set condition on footprints.** The paper's condition is
  `RC_P → rc_b(i) ⋆ rc_{b′}(j)` with `⋆` over fractional permissions, which admits read/read sharing
  (fractions in `(0,1)` split) while forbidding write/write and write/read overlap. The word
  **"Bernstein" never appears** — `NOT FOUND IN PDF`. A footprint-set formulation
  (`w₁∩w₂ = w₁∩r₂ = w₂∩r₁ = ∅`) is a different encoding of the same intent; the permission encoding
  buys compositionality with an existing separation logic, at the cost of needing the fraction
  algebra and of making the condition a *provability* obligation rather than a decidable set
  equation.

- **The reordering argument transfers, and is the reusable core.** Proof sketch 1 (basic blocks) and
  Proof sketch 4 / Lemma 3 (composition) are both "commute adjacent independent transitions until
  the trace is in sequential order". Any mechanised `par p q ≈ p ⨟ q` proof will need the same
  bubble-sort normalisation argument, and will need the analogue of Lemma 2 (the swapped pair
  touches a shared location only via reads) as its justification for each swap. Note that both of
  Blom et al.'s inductions go over **positions in a finite execution trace**, not over program
  syntax — relevant where a syntax-directed induction is wanted instead.

- **Where it must differ: direction and unconditionality.** Blom et al. prove only
  `∀ execution of P. ∃ execution of blin(P). same terminal state`, and only *under the assumption
  that the contracts have been verified*. An outcome-set *equality* needs the missing converse
  (every sequential terminal state is parallel-reachable — easy here, since the sequential order is
  one particular interleaving, but it is not stated as a theorem), and an unconditional statement
  quantified over all schedules rather than one predicated on discharged annotations.

- **Where it must differ: racy programs are stuck, not `wrong`.** The instrumented semantics blocks
  on a permission violation (Sect. 6.2), and no theorem says anything about programs whose
  independence condition fails — there is no anti-vacuity counterpart. An absorbing `wrong` state
  plus a result in both directions (equality on independent programs, `wrong` on racy ones) is a
  strictly stronger specification than anything in this paper.

- **Mechanisation gap is real.** Theorems 1–3 are proof sketches; the asserted operational↔
  denotational agreement is unproved in the paper; the multi-transfer case of Sect. 6.3 is open. A
  machine-checked statement of even the one-directional result would already be new relative to
  this paper.
