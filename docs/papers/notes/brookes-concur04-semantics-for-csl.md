# A semantics for concurrent separation logic
Stephen Brookes (Carnegie Mellon) · CONCUR 2004 (LNCS 3170, pp16–34); **the PDF supplied is the long journal/Festschrift version** (80pp, *Theoretical Computer Science* 375(1-3), the Reynolds Festschrift volume — see §15: "I am especially pleased that this paper will appear as part of the Reynolds Festschrift") · `brookes-concur04-semantics-for-csl.pdf`

> The PDF itself carries no venue line on its title page; the venue above is reconstructed from §15 and from O'Hearn's bibliography entry [12] ("Theoretical Computer Science, this Volume. Preliminary version appeared in Proceedings of the 15th CONCUR (2004), LNCS 3170, pp16-34."). Section/theorem numbers below are this PDF's.

## One-line thesis
A denotational action-trace semantics in which race conditions are detected and treated as catastrophic, together with a *local* enabling relation that executes a trace in the heap portion a process owns, suffices to prove concurrent separation logic sound and to prove that every provable program is race-free.

## The setting

**Language** (§2):

```text
c ::= skip | i:=e | c1 ; c2 | c1‖c2 |
      i:=[e] | [e]:=e' | i:=cons E | dispose e |
      if b then c1 else c2 | while b do c | local i = e in c |
      resource r in c | with r when b do c
```

Unlike O'Hearn, Brookes allows **nested resource declarations and nested parallel compositions** (§1: "We reformulate O'Hearn's rules in a more general manner, allowing nested resource declarations and nested parallel compositions"). Expressions are pure: "expressions do not contain notations, such as `cons` and `[−]`, whose semantics refers to the heap, and they do not cause side-effects" (§2). One syntactic constraint: a region for `r` may not contain another region for `r` (§2).

**State** (§4.1): "A state σ comprises a store s, a heap h, and a finite set A of resource names." An initial state is `(s,h,{})`, abbreviated `(s,h)`.

**Atomic grain** (§4.5, §4.6): deliberately fine, and expressions are *not* atomic. "We do not assume that expression evaluation is atomic, because we want to design a semantics for commands that permits analysis of race conditions, and we do not want to make unrealistic assumptions about granularity" (§4.5). "(So we do not assume that assignments are atomic.)" (§4.6). Individual reads/writes to one identifier or address *are* indivisible — and §14 flags this as a residual idealization.

**Terminating programs only?** No. Traces may be infinite and fairness is built in: "we also want to be able to use our semantics to establish race-freedom properties, so that we also need to include infinite traces. Consequently it makes sense to build fairness directly into our model" (§4.1 fn.1). `[[while b do c]] = ([[b]]true [[c]])* [[b]]false ∪ ([[b]]true [[c]])ω`.

**Judgment form** (§8.1): a resource-sensitive partial correctness formula

```text
Γ ⊢ {p}c{q}
```

where Γ is a resource context `r1(X1) : R1, ..., rk(Xk) : Rk` associating each resource name with a protection list `Xi` and a **precise** resource invariant `Ri`. So: a **unary** Hoare triple indexed by a resource context. Underneath it sits a denotational semantics `[[c]] ⊆ Tr` (a set of action traces) and a *semantic* equivalence `[[c]] = [[c']]` (§5).

### Actions and the trace model (§4.2–§4.4)

```text
Definition 4
An action has one of the following forms:
  • δ, an idle step
  • i=v, a read of identifier i
  • i:=v, a write to i
  • [l]=v, a lookup of address l
  • [l]:=v, an update to address l
  • alloc(l, L), an allocation, where l is an address and L is a finite list of values
  • disp(l), a disposal of address l
  • acq(r), where r is a resource name
  • rel(r), where r is a resource name
  • try(r), where r is a resource name
  • abort, an error stop
```

Read/write sets of actions (§4.3):

```text
writes(i:=v) = {i}              reads(i=v) = {i}
writes([l]:=v) = {l}            reads([l]=v) = {l}
writes(disp(l)) = {l}           reads(disp(l)) = {l}
writes(λ) = {} otherwise        reads(λ) = {} otherwise
free(λ) = reads(λ) ∪ writes(λ)
```

Allocation addresses are deliberately excluded from the write-set: "we do not include addresses l,...,l+n in the write-set of `alloc(l,[v0,...,vn])`, because these addresses will be assumed to be fresh" (§4.3).

Trace semantics of commands (§4.6, Definition 5):

```text
[[skip]] = {δ}
[[i:=e]] = {ρ i:=v | (ρ,v) ∈ [[e]]}
[[i:=[e]]] = {ρ [v]=v' i:=v' | (ρ,v) ∈ [[e]]}
[[i:=cons E]] = {ρ alloc(l,L) i:=l | (ρ,L) ∈ [[E]]}
[[[e]:=e']] = {ρ ρ' [v]:=v' | (ρ,v) ∈ [[e]] & (ρ',v') ∈ [[e']]}
[[dispose(e)]] = {ρ disp(l) | (ρ,l) ∈ [[e]]}
[[c1 ; c2]] = [[c1]] [[c2]] = {α1α2 | α1 ∈ [[c1]] & α2 ∈ [[c2]]}
[[if b then c1 else c2]] = [[b]]true [[c1]] ∪ [[b]]false [[c2]]
[[while b do c]] = ([[b]]true [[c]])* [[b]]false ∪ ([[b]]true [[c]])ω
[[c1‖c2]] = [[c1]]‖[[c2]]
[[local i = e in c]] = {ρ(α\i) | (ρ,v) ∈ [[e]] & α ∈ [[c]][i:v]}
[[with r when b do c]] = wait* enter ∪ waitω
      where wait = acq(r) [[b]]false rel(r) ∪ {try(r)}
      and enter = acq(r) [[b]]true [[c]] rel(r)
[[resource r in c]] = {α\r | α ∈ [[c]]r}
```

## Main results, stated

### The interference (race) relation — this is the paper's Bernstein condition

§4.4, verbatim:

```text
We want to detect race conditions caused by an attempt to write to an
identifier or address being used concurrently: we will treat such a possibility
as a catastrophe. We will write λ1 ♯ λ2, pronounced λ1 interferes with λ2, to
indicate when this happens:

   λ1 ♯ λ2  ⇔  free(λ1) ∩ writes(λ2) ≠ {}  ∨  writes(λ1) ∩ free(λ2) ≠ {}.

Notice that we do not regard two concurrent reads as a disaster.
```

Expanding `free = reads ∪ writes`, this is exactly `(r1∪w1)∩w2 ≠ ∅ ∨ w1∩(r2∪w2) ≠ ∅`, i.e. Bernstein's condition negated: non-interference is `w1∩w2 = w1∩r2 = w2∩r1 = ∅`.

### Mutex fairmerge, and the absorbing error (§4.4)

```text
         α1 A1‖A2 ε = {α1 | (A1,A2) --α1--> ·}
         ε A1‖A2 α2 = {α2 | (A2,A1) --α2--> ·}
 (λ1α1) A1‖A2 (λ2α2) = {abort | λ1 ♯ λ2}
                     ∪ {λ1β | (A1,A2) --λ1--> (A1',A2) & β ∈ α1 A1'‖A2 (λ2α2)}
                     ∪ {λ2β | (A2,A1) --λ2--> (A2',A1) & β ∈ (λ1α1) A1‖A2' α2}
```

with `abort` a left zero for concatenation: "We assume that abort behaves like a left-zero for concatenation, so that `α abort β = α abort`, for all traces α and β" (§4.4). That is the absorbing-error discipline.

Resource enabling (§4.4):

```text
(A1,A2) --try(r)--> (A1,A2)
(A1,A2) --acq(r)--> (A1 ∪ {r}, A2)   if r ∉ A1 ∪ A2
(A1,A2) --rel(r)--> (A1 − {r}, A2)   if r ∈ A1
(A1,A2) --λ-->      (A1,A2)          if λ is not a resource action
```

### The proof rules (§8.3), verbatim — the ones that matter

```text
• Parallel
                      Γ ⊢ {p1}c1{q1}   Γ ⊢ {p2}c2{q2}
                        Γ ⊢ {p1 ∗ p2}c1‖c2{q1 ∗ q2}
 if   free(p1,q1) ∩ writes(c2) = free(p2,q2) ∩ writes(c1) = {}
 and (free(c1) ∩ writes(c2)) ∪ (free(c2) ∩ writes(c1)) ⊆ owned(Γ)

• Local Resource
                          Γ, r(X) : R ⊢ {p}c{q}
                    Γ ⊢ {p ∗ R}resource r in c{q ∗ R}
 if r ∉ dom(Γ), X ∩ owned(Γ) = {}, free(R) ∩ owned(Γ) = {},
 and R is precise.

• Region
                           Γ ⊢ {(p ∗ R) ∧ b}c{q ∗ R}
                   Γ, r(X) : R ⊢ {p}with r when b do c{q}
 if r ∉ dom(Γ), X ∩ owned(Γ) = {}, free(R) ∩ owned(Γ) = {}, R is
 precise, and free(p,q) ∩ X = {}

• Frame
                                 Γ ⊢ {p}c{q}
                              Γ ⊢ {p ∗ I}c{q ∗ I}
 if free(I) ∩ writes(c) = {} and free(I) ∩ owned(Γ) = {}

• Conjunction
                       Γ ⊢ {p1}c{q1}    Γ ⊢ {p2}c{q2}
                           Γ ⊢ {p1 ∧ p2}c{q1 ∧ q2}

• Auxiliary
                                Γ ⊢ {p}c{q}
                               Γ ⊢ {p}c\X{q}
 if X is auxiliary for c, and X ∩ free(p,q) = {}.

• Expansion
                                   Γ ⊢ {p}c{q}
                                  Γ, Γ' ⊢ {p}c{q}
 if writes(c) ∩ free(Γ') = {}, free(c) ∩ owned(Γ') = {}, Γ ⊥ Γ', and
 free(p,c,q) ∩ owned(Γ') = {}

• Contraction
                                  Γ, Γ' ⊢ {p}c{q}
                                   Γ ⊢ {p}c{q}
 if res(c) ⊆ dom(Γ) and Γ ⊥ Γ'
```

(Also Skip, Assignment, Lookup, Allocation, Update, Disposal, Sequential, Conditional, Loop, Local variable, Renaming variable, Renaming resource, Consequence, Existential, Disjunction — all with `owned(Γ)`-disjointness side conditions.)

Unlike O'Hearn, Brookes **keeps the Conjunction rule** and rules out the Reynolds counterexample by requiring precision in Region/Local Resource.

### Local enabling (§10.1) — "local enabling" defined

A local state `(s,h,A)` is *consistent with Γ* if `dom(s) ∩ owned(Γ) = owned(Γ⌐A)`, where `Γ⌐A` is the part of Γ for resources in A. The local enabling relation `(s,h,A) --λ-->Γ (s',h',A')` (Figure 2) differs from the global one `==λ=>` (Figure 1) in four places:

```text
• (s,h,A) --i:=v-->Γ ([s | i : v], h, A) iff i ∈ dom(s) − free(Γ\A)
• (s,h,A) --i:=v-->Γ abort iff i ∉ dom(s) or i ∈ free(Γ\A)
• (s,h,A) --acq(r)-->Γ,r(X):R (s·s', h·h', A ∪ {r}) iff
  r ∉ A, h ⊥ h', dom(s') = X and (s·s', h') ⊨ R
• (s,h,A) --rel(r)-->Γ,r(X):R (s\X, h − h', A − {r}) iff
  r ∈ A, h' ⊆ h, and (s,h') ⊨ R
• (s,h,A) --rel(r)-->Γ,r(X):R abort iff ∀h' ⊆ h. ¬(s,h') ⊨ R
```

Brookes's own gloss (§10.1): "We use the error state `abort` to handle runtime errors such as races or an attempt to use an identifier or heap address not locally owned, or an attempt to release a resource in a state for which no sub-heap satisfies the corresponding invariant." And: "each time the program acquires a resource it claims ownership of exactly the store and heap needed to satisfy the relevant invariant, and on releasing a resource it relinquishes ownership of the store and heap determined by the invariant." Precision is what makes this deterministic: "since resource invariants are precise there will be, for a given global store s'' ⊇ s at most one heap h' such that (s'',h') ⊨ R, and hence at most one local transition from (s,h,A) involving the action acq(r) consistent with this global state."

Crucially (§10.1 last paragraph): "Note that this notion of local computation makes sense for arbitrary traces, not just for sequential traces." The *global* enabling `==α=>` is by definition interference-free ("By definition, every trace participating in this kind of enabling is sequential", §4.3) — local enabling is what allows gaps at resource actions.

### Validity (§11, Definition 24)

```text
Definition 24
The formula Γ ⊢ {p}c{q} is valid if for all traces α of c, all local states
(s,h) such that dom(s) ⊇ free(c,Γ) − owned(Γ), and all σ', if (s,h) ⊨ p and
(s,h) --α-->Γ σ' then σ' ⊨ q.
```

"Since `abort` does not satisfy q validity implies freedom from race conditions. Furthermore, this notion of validity involves all traces of c, not just the sequential traces and not just the finite traces" (§11).

Informal version first proposed (§8.2, Proposal 12): "A formula Γ ⊢ {p}c{q} is valid iff every finite interactive computation of c, from a state satisfying p ∗ inv(Γ) with initial values for free(c), in an environment that respects Γ, is error-free, respects Γ, and ends in a state satisfying q ∗ inv(Γ)."

### Supporting lemmas (§10.2)

```text
Lemma 13 (Empty Context Lemma)
Let α be a finite trace, let {r1,...,rn} be the set of resource names occurring
in actions of α, and let Γ0 be the resource context r1 : emp, ..., rn : emp.
Then
            (s,h,A) ==α=> σ'   if and only if   (s,h,A) --α-->Γ0 σ'.

Theorem 14 (Respect for resources)
If α ∈ [[c]] and (s,h,A) --α-->Γ (s',h',A'), then dom(s') = dom(s) and A = A'.

Theorem 17 (Agreement)
Let α ∈ [[c]] and suppose that s1 agrees with s2 on free(c,Γ).
  • If (s1,h) --α-->Γ abort, then (s2,h) --α-->Γ abort.
  • If (s1,h) --α-->Γ (s1',h') then there is a store s2' such that
    (s2,h) --α-->Γ (s2',h') and s1' agrees with s2' on free(c,Γ).
If α ∈ [[c]] and (s,h) --α-->Γ (s',h') then s' agrees with s except on writes(c).

Theorem 19 (Frame)
Let α ∈ [[c]] and suppose h1 ⊥ h2 and h = h1·h2.
  • If (s,h) --α-->Γ abort then (s,h1) --α-->Γ abort.
  • If (s,h) --α-->Γ (s',h') then either (s,h1) --α-->Γ abort, or there is a heap h1'
    such that h1' ⊥ h2, h' = h1'·h2, and (s,h1) --α-->Γ (s',h1').
```

### ⭐ Theorem 21 (Parallel Decomposition) — §10.2, verbatim

```text
Theorem 21 (Parallel Decomposition)
Suppose (free(c1) ∩ writes(c2)) ∪ (writes(c1) ∩ free(c2)) ⊆ owned(Γ) and
α ∈ α1‖α2, where α1 ∈ [[c1]] and α2 ∈ [[c2]]. Suppose h1 ⊥ h2 and h = h1·h2.

  • If (s,h) --α-->Γ abort then
    (s\writes(α2), h1) --α1-->Γ abort  or  (s\writes(α1), h2) --α2-->Γ abort.

  • If (s,h) --α-->Γ (s',h') then
    (s\writes(α2), h1) --α1-->Γ abort  or  (s\writes(α1), h2) --α2-->Γ abort,
    or there are disjoint heaps h1' ⊥ h2' such that h' = h1'·h2' and
      – (s\writes(α2), h1) --α1-->Γ (s'\writes(α2), h1')
      – (s\writes(α1), h2) --α2-->Γ (s'\writes(α1), h2')
```

**It is a per-computation projection, not a set-level equality of trace sets.** Every quantifier is over *one* interleaved trace `α ∈ α1‖α2`, *one* chosen heap partition `h = h1·h2`, and *one* local computation; the conclusion produces *one* local computation of each component. It says nothing about the trace set `[[c1‖c2]]` as a whole, and it has no converse direction (nothing recombines component computations into an interleaved one). Brookes's own informal statement (§1) matches: "When `c1‖c2` is a race-free program, every interleaved computation of `c1‖c2` can be decomposed into 'local' computations of the constituent processes `c1` and `c2` which are interference-free except for interactions with protected resources."

The more general Appendix version, from which Theorem 21 follows by `A = {}`:

```text
Lemma 4 (Parallel Decomposition for traces)
Assume (free(α1) ∩ writes(α2)) ∪ (writes(α1) ∩ free(α2)) ⊆ owned(Γ) and
α ∈ α1 A1‖A2 α2. Suppose h1 ⊥ h2, A1 ⊥ A2, and h = h1·h2, A = A1·A2.
Let s1 = s\writes(α2)\owned(Γ) ∪ s⌐owned(Γ⌐A1),
and s2 = s\writes(α1)\owned(Γ) ∪ s⌐owned(Γ⌐A2).
  • If (s,h,A) --α-->Γ abort then either (s1,h1,A1) --α1-->Γ abort,
    or (s2,h2,A2) --α2-->Γ abort.
  • If (s,h,A) --α-->Γ (s',h',A') then either (s1,h1,A1) --α1-->Γ abort,
    or (s2,h2,A2) --α2-->Γ abort, or there are disjoint heaps h1', h2', and
    disjoint resource sets A1', A2', such that h' = h1'·h2', A' = A1'·A2',
    (s1,h1,A1) --α1-->Γ (s1',h1',A1'), and (s2,h2,A2) --α2-->Γ (s2',h2',A2'),
    where s1' = (s'\writes(α2)\owned(Γ)) ∪ (s'⌐owned(Γ⌐A1'))
    and s2' = (s'\writes(α1)\owned(Γ)) ∪ (s'⌐owned(Γ⌐A2')).
Proof: By induction on the lengths of α1 and α2.
```

Note the hypothesis of Lemma 4 is on **traces** `α1, α2` (dynamic footprints), while Theorem 21 / Corollary 5 state it on **commands** `c1, c2` (static footprints).

### Other main theorems

```text
Theorem 22 (Local Resource Lemma)
Let β ∈ [[c]]r and suppose h1 ⊥ h2 and (s,h2) ⊢ R.
  • If (s,h1·h2) --β\r-->Γ abort then (s\X,h1) --β-->Γ,r(X):R abort.
  • If (s,h1·h2) --β\r-->Γ (s',h') then either (s\X,h1) --β-->Γ,r(X):R abort, or
    there are heaps h1' ⊥ h2' such that h' = h1'·h2', (s',h2') ⊨ R, and
    (s\X,h1) --β-->Γ,r(X):R (s'\X,h1').

Theorem 23 (Local Variable Lemma)
Let β ∈ [[c]][i:v] and i ∉ owned(Γ).
  • If (s,h) --β\i-->Γ abort then ([s | i : v],h) --β-->Γ abort.
  • If (s,h) --β\i-->Γ (s',h') then either ([s | i : v],h) --β-->Γ abort, or there is a
    value v' such that ([s | i : v],h) --β-->Γ ([s' | i : v'],h').

Theorem 25 (Soundness)
Every provable formula Γ ⊢ {p}c{q} is valid.

Lemma 26 (Connection Property)
Let (s,h,A) be a global state and suppose h = h1·h2 with (s,h2) ⊨ inv(Γ\A).
  • If (s,h,A) ==λ=> abort then (s↓A,h1,A) --λ-->Γ abort.
  • If (s,h,A) ==λ=> (s',h',A') then either (s↓A,h1,A) --λ-->Γ abort, or there
    are heaps h1' ⊥ h2' such that h' = h1'·h2', (s',h2') ⊨ inv(Γ\A'), and
    (s↓A,h1,A) --λ-->Γ (s'↓A',h1',A')

Theorem 28 (Valid implies race-free)
If Γ ⊢ {p}c{q} is valid and well formed, then c is race-free from every state
satisfying p ∗ inv(Γ). In fact, for all states σ, σ' and all traces α ∈ [[c]], if
σ ⊨ p ∗ inv(Γ) and σ ==α=> σ' then σ' ⊨ q ∗ inv(Γ).

Corollary 29
If ⊢ {p}c{q} is provable then for all σ, σ' such that σ ⊨ p and all traces
α ∈ [[c]], if σ ==α=> σ' then σ' ⊨ q. Hence c is race-free from every state
satisfying p.
```

### ⭐ A genuine par-equals-seq *example* (§4.6, Example 5)

Not a theorem, but an explicit trace-set *equality* between a parallel and a sequential program, derived from the semantics:

```text
[[resource r in (with r do x:=x + 1 ‖ with r do x:=x + 1)]]
     = {αβ | α, β ∈ [[x:=x + 1]]}
     = [[x:=x + 1; x:=x + 1]].
```

"The parallel assignments to x here are protected by r, and the overall effect is the same as that of two consecutive increments." The side condition making this work is **explicit mutual exclusion**, not independence. Related semantic equivalences are given in §5 (associativity and commutativity of `‖`, `[[skip‖c]] = [[c‖skip]] = [[c]]`, loop unrolling), all of which are equalities of trace sets under Definition 6: "Commands c and c' are said to be semantically equivalent if `[[c]] = [[c']]`."

## Proof technique

Soundness (Theorem 25) is proved **rule by rule**, closing under "induction on the length of the derivation" (§12). Each rule's case shows: well-formed premisses + side conditions + valid premisses ⇒ valid conclusion.

The key lemma is **Theorem 21 (Parallel Decomposition)**, built on **Theorem 19 (Frame)**. The Parallel rule case (§12) runs: given `(s,h) ⊨ p1 ∗ p2` split as `h = h1·h2`, take any `α ∈ [[c1‖c2]]` with `(s,h) --α-->Γ σ'`, pick `α1 ∈ [[c1]]`, `α2 ∈ [[c2]]` with `α ∈ α1‖α2`; if `σ' = abort`, Parallel Decomposition forces one component to abort, contradicting validity of the premisses; otherwise it supplies `h1' ⊥ h2'` with `h' = h1'·h2'` and component computations satisfying `q1`, `q2`, hence `(s',h') ⊨ q1 ∗ q2`.

**The induction in Parallel Decomposition itself goes over the lengths of the two component traces** (Appendix, Lemma 4: "Proof: By induction on the lengths of α1 and α2"), with base case "when one of the traces is empty", discharged by the Frame Property. There is **no step budget / fuel**: traces may be infinite, and the infinite case is handled by the convention that an infinite trace can only lead to `abort` (via a finite prefix), never to a proper state (§4.3, §11).

Theorem 28 (race-freedom) goes the other way, from the *global* enabling relation to the *local* one, via Lemma 26 (Connection Property), proved by "Case analysis using the definitions of the two enabling relations" and extended to traces "by induction on the length of α".

## Side condition on parallel composition

**In the logic** (§8.3, Parallel rule) — verbatim:

```text
 if   free(p1,q1) ∩ writes(c2) = free(p2,q2) ∩ writes(c1) = {}
 and (free(c1) ∩ writes(c2)) ∪ (free(c2) ∩ writes(c1)) ⊆ owned(Γ)
```

plus the implicit semantic demand carried by `∗` in `{p1 ∗ p2}`: the preconditions must hold on *disjoint* subheaps.

The second clause is **Bernstein-shaped on identifiers** (free∩writes in both directions, modulo resource protection): two commands may both *read* the same unprotected identifier, since `free(c1) ∩ free(c2)` is unconstrained when neither writes it. So for the **store**, read/read sharing is allowed by the logic.

**In the semantics** (§4.4): read/read sharing is allowed everywhere, store and heap alike — "Notice that we do not regard two concurrent reads as a disaster."

**But in the logic, read/read sharing on the HEAP is not expressible.** §14, verbatim and decisive:

> "The trace semantics was designed to detect races. We did not include a pair of concurrent reads as a race, since this kind of passive interaction is usually regarded as benign. However, the use of separating conjunction in the **Parallel** rule requires that the processes in a provable program operate on disjoint portions of the heap, even if part of the heap is treated as 'read-only' by all processes and could safely be shared without racing. For example, there is no way to prove the obviously valid formula
>
> ⊢ {z ↦ 1}x:=[z]‖y:=[z]{x = y = 1 ∧ z ↦ 1},
>
> since the logic requires both processes to 'need' to own the heap cell denoted by z, separately. **Nevertheless, the trace semantics handles this issue (and this example) correctly, so here is a place where the semantics is ahead of the logic.**"

**Fractional permissions: not used.** §14 names them only as a possible future fix: "Another possibility might be to try to adapt Boyland's ideas on fractional permissions [6], perhaps by designing a semantics in which partial permissions are attached to resource actions and managed in an appropriate manner upon resource acquisition and release, instead of all-or-nothing transfer."

**Ownership transfer: yes**, and it is formalized by the `acq(r)` / `rel(r)` clauses of local enabling (Figure 2), not by the Parallel rule.

## Shared state / resources

Yes — **resource invariants + conditional critical regions**, as in O'Hearn, but generalized to nested resource blocks and formalized as a resource context Γ. The mechanism:

- Mutual exclusion is enforced in the *semantics*, by the resource enabling relation in mutex fairmerge (§4.4), which only permits `acq(r)` when `r ∉ A1 ∪ A2`.
- Ownership transfer is enforced in the *local enabling* relation (Figure 2): `acq(r)` adds exactly the subheap satisfying `R` (unique by precision), `rel(r)` removes exactly one, and aborts if no subheap satisfies `R`.
- The logic rule is **Region** (above). A protection list `X` of identifiers travels with the resource: on acquire `dom(s') = X` is added to the store, on release `s\X` removes it.

**No CAS, no locks as first-class values, no ghost state beyond auxiliary variables** (Auxiliary rule, §8.3). Precision is required for soundness; §14 shows the alternative *supported + intuitionistic* "parsimonious ownership policy" with modified Region and Resource rules.

## What it does NOT claim

- **It proves no theorem relating a parallel program to its sequential counterpart.** Nothing in the paper's results relates two different programs. The logic's judgments are unary (`Γ ⊢ {p}c{q}`). The *semantics* does define a relation between two programs — semantic equivalence `[[c]] = [[c']]` (Definition 6, §5) — and §4.6 Example 5 exhibits one par≡seq instance, `[[resource r in (with r do x:=x+1 ‖ with r do x:=x+1)]] = [[x:=x+1; x:=x+1]]`. But that is a worked example, there is no general theorem of that shape, and its side condition is explicit mutual exclusion, not independence of footprints.
- **Parallel Decomposition is one-directional and per-computation.** It projects an interleaved computation into component computations. It does not reconstitute, and it is not an equality of trace sets.
- **The logic cannot prove read-shared programs** — §14's `{z ↦ 1}x:=[z]‖y:=[z]{…}` is stated to be valid but unprovable.
- **Not fully abstract.** §14: "The trace semantics presented here makes distinctions between programs based on the order in which they perform actions, and hence fails to be fully abstract for partial correctness." e.g. `x:=1; y:=1` and `y:=1; x:=1` have different trace sets but satisfy the same partial correctness formulas in all contexts.
- **Granularity is not abstracted away.** §14: "our repertoire of actions assumes that reads and writes to individual variables and heap addresses are executable indivisibly. But the partial correctness properties of a race-free program should not depend on whether assignments, or reads and writes to a variable, are atomic [43]." Reynolds's grainless semantics is cited as an alternative aim, left as future work.
- **Partial correctness only; no total correctness, no deadlock-freedom.** §14 sketches an acquisition-order extension for both, as future work.
- **Soundness is conditional on precise (or supported+intuitionistic) invariants**, and the Reynolds formula `r : true ⊢ {emp ∨ one}with r do skip{emp}` is "derivable if we allow the Region rule as before but without insisting that the resource invariant be precise. This formula is not valid" (§14).

## Mechanized?
**No.** `NOT FOUND IN PDF` — grep for Coq, Isabelle, HOL, "mechanized", "machine-checked", "theorem prover", "proof assistant" returns nothing. The entire development (semantics, all lemmas, the soundness theorem, the Appendix proof of Parallel Decomposition) is pen-and-paper.

## Quotable lines

- "λ1 ♯ λ2 ⇔ free(λ1) ∩ writes(λ2) ≠ {} ∨ writes(λ1) ∩ free(λ2) ≠ {}. Notice that we do not regard two concurrent reads as a disaster." — §4.4
- "the use of separating conjunction in the Parallel rule requires that the processes in a provable program operate on disjoint portions of the heap, even if part of the heap is treated as 'read-only' by all processes and could safely be shared without racing ... here is a place where the semantics is ahead of the logic." — §14
- "When c1‖c2 is a race-free program, every interleaved computation of c1‖c2 can be decomposed into 'local' computations of the constituent processes c1 and c2 which are interference-free except for interactions with protected resources." — §1
- "We do not assume that expression evaluation is atomic, because we want to design a semantics for commands that permits analysis of race conditions, and we do not want to make unrealistic assumptions about granularity." — §4.5
- "the partial correctness properties of a race-free program should not depend on whether assignments, or reads and writes to a variable, are atomic." — §14
- "Our semantics models a potential race condition as catastrophic, since we want to prove the absence of races." — §1
- "[[resource r in (with r do x:=x + 1‖with r do x:=x + 1)]] = [[x:=x + 1; x:=x + 1]]" — §4.6, Example 5

## Relevance to a parallel-equals-sequential equivalence theorem

- **Brookes's race predicate IS Bernstein**, at the level of single actions: `λ1 ♯ λ2 ⇔ free(λ1)∩writes(λ2) ≠ ∅ ∨ writes(λ1)∩free(λ2) ≠ ∅`, with concurrent reads explicitly benign. A project using Bernstein independence as the *hypothesis of an equivalence* is using the same condition Brookes uses as the *definition of a race in the semantics* — the citation is exact, and the difference is where the condition sits (hypothesis vs. error trigger).
- **The Parallel Decomposition Lemma is the half that already exists and the half that does not.** It projects one interleaved computation into two component computations under a footprint side condition. A par≡seq outcome-set equality needs (i) the projection, (ii) a *recombination* into the sequential computation, and (iii) set-level equality in both directions — none of which Theorem 21 provides. It is the natural lemma to cite as prior art for the forward direction.
- **The logic is strictly weaker than its own semantics on read sharing**, and Brookes says so in §14 with the unprovable-but-valid formula `{z ↦ 1}x:=[z]‖y:=[z]{x = y = 1 ∧ z ↦ 1}`. A theorem whose independence condition permits read/read overlap lands exactly in the gap Brookes identifies, on the semantics side of it.
- **Absorbing `wrong` has a direct antecedent here**: `abort` is a left zero for trace concatenation (§4.4), races produce `abort` inside mutex fairmerge, and validity's "`abort` does not satisfy q" is what turns partial correctness into race-freedom (§11, Theorem 28). But Brookes's grain is *not* abstracted away (§14 concedes individual reads/writes are assumed indivisible, and points at Reynolds for the fix), so grain-independence is not something to claim from this paper.
