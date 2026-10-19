# Concurrent separation logic and operational semantics
Viktor Vafeiadis (Max Planck Institute for Software Systems, MPI-SWS, Germany) · MFPS 2011 (published in *Electronic Notes in Theoretical Computer Science*) · `vafeiadis-mfps11-csl-and-operational-semantics.pdf`

## One-line thesis
CSL's soundness can be proved directly against a *standard* small-step operational semantics, by defining the meaning of a triple through a step-indexed `safe_n` predicate, with no intermediate instrumented/ownership semantics and no erasure theorem — and the proof is short enough to be machine-checked in Isabelle/HOL and to extend to permissions, RGSep and CAP.

## The setting

**Language** (§2):

```text
E ::= x | n | E + E | E − E | ...
B ::= B ∧ B | ¬B | E = E | E ≤ E | ...
C ::= skip | x := E | x := [E] | [E] := E | x := alloc(E) | dispose(E)
    | C1 ; C2 | C1‖C2 | if B then C1 else C2 | while B do C | atomic C
```

§5 replaces `atomic C` with O'Hearn/Brookes's CCRs: `resource r in C | with r when B do C | within r do C`, where `within r do C` is "a partially executed CCR: one that has acquired the lock, tested the condition, and still has to execute C."

**State** (§2):

```text
s ∈ Stack = VarName → Val      stacks (interpretations for variables)
h ∈ Heap  = Loc ⇀fin Val       heaps (dynamically allocated memory)
σ ∈ State = Stack × Heap       program states
```

**Memory model / grain.** Sequentially consistent interleaving — "Parallel composition interleaves executions of its two components, while atomic commands execute their body, C, in one transition" (§2). The grain is the individual transition of Figure 1: a read, a write, an allocation, a disposal, an assignment. No weak memory.

**Terminating programs only?** No. `while B do C` is present and `safe_n` is defined for all `n`, so partial correctness over possibly non-terminating programs. A footnote flags a gap in the §2 version: "Normally, in addition to **Atom**, there should be another rule for infinite executions for the body of atomic blocks. For simplicity, we omit such a rule. In §5, we will present a different semantics that does not involve →* and does not suffer from this problem" (§2 fn.2).

**Judgment form.** A **unary** Hoare triple with a resource invariant: `J ⊢ {P} C {Q}` (§2), generalized in §5 to `Γ ⊢ {P} C {Q}` with Γ a map from resource names to invariants. Validity `J ⊨ {P} C {Q}` is defined via `safe_n` (§3).

### The step relation (§2, Figure 1) — verbatim

```text
                                      C, σ →* skip, σ'
 (skip; C2), σ → C2, σ          (Seq1)  ─────────────────────── (Atom)
                                        (atomic C), σ → skip, σ'
      C1, σ → C1', σ'
 ─────────────────────────────  (Seq2)       C1, σ → C1', σ'
  (C1; C2), σ → (C1'; C2), σ'           ───────────────────────── (Par1)
                                         (C1‖C2), σ → (C1'‖C2), σ'
      C1, σ → abort
 ─────────────────────────      (SeqA)       C2, σ → C2', σ'
  (C1; C2), σ → abort                   ───────────────────────── (Par2)
                                         (C1‖C2), σ → (C1‖C2'), σ'
    σ = (s,h)   [[B]](s)
 ──────────────────────────────── (If1)  ──────────────────────── (Par3)
 (if B then C1 else C2), σ → C1, σ        (skip‖skip), σ → skip, σ

    σ = (s,h)   ¬[[B]](s)                      C1, σ → abort
 ──────────────────────────────── (If2)  ──────────────────────── (ParA1)
 (if B then C1 else C2), σ → C2, σ         (C1‖C2), σ → abort

      C, σ →* abort                            C2, σ → abort
 ─────────────────────────── (AtomA)     ──────────────────────── (ParA2)
   atomic C, σ → abort                     (C1‖C2), σ → abort

 (while B do C), σ → (if B then (C; while B do C) else skip), σ   (Loop)

(Assign) x := E, (s,h) → skip, (s[x := [[E]](s)], h)
(Read)   x := [E], (s,h) → skip, (s[x := v], h)              if h([[E]](s)) = v
(ReadA)  x := [E], (s,h) → abort                             if [[E]](s) ∉ dom(h)
(Wri)    [E]:=E', (s,h) → skip, (s, h[[[E]](s) := [[E']](s)]) if [[E]](s) ∈ dom(h)
(WriA)   [E]:=E', (s,h) → abort                              if [[E]](s) ∉ dom(h)
(All)    x := alloc(E), (s,h) → skip, (s[x := ℓ], h[ℓ := [[E]](s)])  where ℓ ∉ dom(h)
(Free)   dispose(E), (s,h) → skip, (s, h[[[E]](s) := ⊥])     if [[E]](s) ∈ dom(h)
(FreeA)  dispose(E), (s,h) → abort                           if [[E]](s) ∉ dom(h)
```

**The race / fault state is `abort`.** There is a single improper configuration `abort`, reached by dereferencing or disposing an unallocated address, and (in §5) by the explicit race-detection rule. Note `(ParA1)`/`(ParA2)`: `abort` propagates out of a parallel composition, so it is absorbing at the top level.

### The race-detection rule (§5, Figure 3) — this is Bernstein

```text
   (accesses(C1,s) ∩ writes(C2,s)) ∪ (accesses(C2,s) ∩ writes(C1,s)) ≠ ∅
  ──────────────────────────────────────────────────────────────────────── (RaceDetect)
                        (C1‖C2, (s,h)) → abort
```

"To show absence of data races, we have added a rule (RaceDetect) that aborts whenever a data race is observed. Here, the functions `accesses(C,s)` and `writes(C,s)` return the set of heap locations accessed or modified by C respectively. Their formal definitions can be found in [18]" (§5). Since `accesses ⊇ writes`, expanding gives `(r1∪w1)∩w2 ∪ (r2∪w2)∩w1 ≠ ∅`, i.e. a race is the negation of `w1∩w2 = w1∩r2 = w2∩r1 = ∅`. **Concurrent reads do not abort.** The formal definitions of `accesses`/`writes` are *not in this PDF* — they are in the Isabelle development [18].

Also in Figure 3, the lock-holding side conditions:

```text
      (C1,σ) → (C1',σ')                          (C2,σ) → (C2',σ')
 locked(C1') ∩ locked(C2) = ∅              locked(C1) ∩ locked(C2') = ∅
 ───────────────────────────── (Par1)      ───────────────────────────── (Par2)
  (C1‖C2, σ) → (C1'‖C2, σ')                 (C1‖C2, σ) → (C1‖C2', σ')

(Res1)  resource r in C, σ → resource r in C', σ'   if C, σ → C', σ'
(Res2)  resource r in skip, σ → skip, σ
(With1) with r when B do C, σ → within r do C, σ    if σ = (s,h) and [[B]](s)
(With2) within r do C, σ → within r do C', σ'       if C, σ → C', σ'
(With3) within r do skip, σ → skip, σ
(ResA)  resource r in C, σ → abort                  if C, σ → abort
(WithA) within r do C, σ → abort                    if C, σ → abort
```

## Main results, stated

### The proof rules (§2, Figure 2) — verbatim

```text
 J ⊢ {P} skip {P}                          (Skip)

        x ∉ fv(J)
 ──────────────────────────                (Assign)
 J ⊢ {[E/x]P} x := E {P}

        x ∉ fv(E, E', J)
 ─────────────────────────────────────────  (Read)
 J ⊢ {E ↦ E'} x := [E] {E ↦ E' ∧ x = E'}

 J ⊢ {E ↦ −} [E] := E' {E ↦ E'}            (Write)

        x ∉ fv(E, J)
 ─────────────────────────────             (Alloc)
 J ⊢ {emp} x:=alloc(E) {x ↦ E}

 J ⊢ {E ↦ −} dispose(E) {emp}              (Free)

 J ⊢ {P} C1 {Q}   J ⊢ {Q} C2 {R}
 ────────────────────────────────          (Seq)
      J ⊢ {P} C1; C2 {R}

   J ⊢ {P ∧ B} C1 {Q}   J ⊢ {P ∧ ¬B} C2 {Q}
 ──────────────────────────────────────────  (If)
   J ⊢ {P} if B then C1 else C2 {Q}

       J ⊢ {P ∧ B} C {P}
 ────────────────────────────────           (While)
 J ⊢ {P} while B do C {P ∧ ¬B}

   emp ⊢ {P ∗ J} C {Q ∗ J}
 ──────────────────────────                 (Atom)
  J ⊢ {P} atomic C {Q}

 J ⊢ {P1} C1 {Q1}
 J ⊢ {P2} C2 {Q2}
 fv(J, P1, C1, Q1) ∩ wr(C2) = ∅
 fv(J, P2, C2, Q2) ∩ wr(C1) = ∅
 ─────────────────────────────────          (Par)
 J ⊢ {P1 ∗ P2} C1‖C2 {Q1 ∗ Q2}

    J ∗ R ⊢ {P} C {Q}
 ─────────────────────────                  (Share)
 J ⊢ {P ∗ R} C {Q ∗ R}

 J ⊢ {P} C {Q}   fv(R) ∩ wr(C) = ∅
 ───────────────────────────────────        (Frame)
    J ⊢ {P ∗ R} C {Q ∗ R}

 J ⊢ {P} C {Q}   P' ⇒ P   Q ⇒ Q'
 ────────────────────────────────           (Conseq)
      J ⊢ {P'} C {Q'}

 J ⊢ {P1} C {Q1}   J ⊢ {P2} C {Q2}
 ──────────────────────────────────         (Disj)
 J ⊢ {P1 ∨ P2} C {Q1 ∨ Q2}

 J ⊢ {P} C {Q}    x ∉ fv(C)
 ───────────────────────────                (Ex)
 J ⊢ {∃x. P} C {∃x. Q}

 J ⊢ {P1} C {Q1}   J ⊢ {P2} C {Q2}   J precise
 ─────────────────────────────────────────────  (Conj)
      J ⊢ {P1 ∧ P2} C {Q1 ∧ Q2}
```

§5's two extra rules for CCRs:

```text
      Γ, r : J ⊢ {P} C {Q}                   Γ ⊢ {(P ∗ J) ∧ B} C {Q ∗ J}
 ─────────────────────────────────    ────────────────────────────────────────────
 Γ ⊢ {P ∗ J} resource r in C {Q ∗ J}   Γ, r : J ⊢ {P} with r when B do C {Q}
```

Key design point stated in §2: "Most presentations require precise J's in all judgments. This, however, is unnecessary: only **Conj** needs precision."

### The semantics of a triple (§3) — THE central definition

```text
Definition 3.1 (Configuration Safety)
safe_0(C, s, h, J, Q) holds always.
safe_{n+1}(C, s, h, J, Q) holds if and only if
(i)   if C = skip, then s,h ⊨ Q; and
(ii)  for all h_J and h_F, if s,h_J ⊨ J and (h ⊎ h_J ⊎ h_F) is defined, then
      C, (s, h ⊎ h_J ⊎ h_F) ↛ abort; and
(iii) for all C', h_J, h_F, h' and s', if s,h_J ⊨ J, and (h ⊎ h_J ⊎ h_F) is defined,
      and C, (s, h ⊎ h_J ⊎ h_F) → C', (s', h'), then there exist h'' and h'_J such that
      h' = h'' ⊎ h'_J ⊎ h_F and s',h'_J ⊨ J and safe_n(C', s', h'', J, Q).

Definition 3.2 J ⊨ {P} C {Q} if and only if for all n, s, and h, if s,h ⊨ P,
then safe_n(C, s, h, J, Q).
```

Roles of the three heaps (§3): `h` is "the part of the heap that is 'owned' by the command"; `h_J` is "the part of the heap that is shared among threads, and must hence satisfy the resource invariant"; `h_F` "represents the remaining part of the heap owned by the rest of the system."

```text
Definition 2.1  An assertion, P, is precise iff for all h1, h2, h1', and h2', if
def(h1 ⊎ h2) and h1 ⊎ h2 = h1' ⊎ h2' and s,h1 ⊨ P and s,h1' ⊨ P, then h1 = h1'.
```

The §5 version, extended for multiple resources and used to get data-race freedom:

```text
Definition 5.1  safe_0(C, s, h, Γ, Q) holds always.
safe_{n+1}(C, s, h, Γ, Q) if and only if
(i)   if C = skip, then s,h ⊨ Q; and
(ii)  for all h_F, if (h ⊎ h_F) is defined, then C, (s, h ⊎ h_F) ↛ abort; and
(iii) accesses(C, s) ⊆ dom(h); and
(iv)  for all C', h_Γ, h_F, s', h', L', if s,h_Γ ⊨ ⊛_{r ∈ locked(C')\locked(C)} Γ(r), and
      (C, (s, h ⊎ h_Γ ⊎ h_F), L) → (C', (s', h'), L'), then there exist h'' and h'_Γ such
      that h' = h'' ⊎ h'_Γ ⊎ h_F and s',h'_Γ ⊨ ⊛_{r ∈ locked(C)\locked(C')} Γ(r)
      and safe_n(C', s', h'', Γ, Q).

Definition 5.2  Γ ⊨ {P} C {Q} if and only if for all n, s, h, if s,h ⊨ P then
safe_n(C, L, s, h, Γ, Q).
```

Clause (iii) is the race-freedom hook: "the new conjunct `accesses(C,s) ⊆ dom(h)` is included so that we can show that safe programs do not have any data races" (§5).

### Theorems and lemmas

```text
Proposition 4.1  If C,(s,h) → C',(s',h'), then fv(C') ⊆ fv(C), wr(C') ⊆ wr(C),
and [s ∼ s']_{wr(C)̄}.

Proposition 4.2
(i)   If [s ∼ s']_{fv(E)}, then [[E]](s) = [[E]](s').
(ii)  If [s ∼ s']_{fv(B)}, then [[B]](s) = [[B]](s').
(iii) If [s ∼ s']_{fv(P)}, then s,h ⊨ P if and only if s',h ⊨ P.
(iv)  If [s ∼ s']_{fv(C)} and C,s → abort, then C,s' → abort.
(v)   If X ⊇ fv(C) and [s ∼ s']_X and C,s → C1,s1, then there exist s1' such
      that C,s' → C1',s1' and [s1 ∼ s1']_X.

Lemma 4.3  If safe_n(C,s,h,J,Q) and m ≤ n, then safe_m(C,s,h,J,Q).

Lemma 4.4  If safe_n(C,s,h,J,Q) and [s ∼ s']_{fv(C,J,Q)}, then safe_n(C,s',h,J,Q).

Theorem 4.5 (CSL Soundness)  If J ⊢ {P} C {Q}, then J ⊨ {P} C {Q}.

Lemma 4.6  For all n,s,h,J, and Q, if s,h ⊨ Q, then safe_n(skip,s,h,J,Q).

Lemma 4.7  If ∀n. safe_n(C,s,h,emp,Q) and def(h ⊎ h_F), then
(i)  ¬(C,(s, h ⊎ h_F) →* abort); and
(ii) if, moreover, C,(s, h ⊎ h_F) →* skip,(s',h'), then there exists h'' such that
     h' = h'' ⊎ h_F and s',h'' ⊨ Q.

Lemma 4.8  If emp ⊨ {P ∗ J} C {Q ∗ J}, then J ⊨ {P} atomic C {Q}.

Lemma 4.9  If safe_n(C1,s,h1,J,Q1), safe_n(C2,s,h2,J,Q1), h1 ⊎ h2 is defined,
fv(J,C1,Q1) ∩ wr(C2) = ∅, and fv(J,C2,Q2) ∩ wr(C1) = ∅, then
safe_n(C1‖C2, s, h1 ⊎ h2, J, Q1 ∗ Q2).

Lemma 4.10  If safe_n(C,s,h,J,Q), fv(R) ∩ wr(C) = ∅, h ⊎ h_R is defined, and
s,h_R ⊨ R, then safe_n(C, s, h ⊎ h_R, J, Q ∗ R).

Lemma 4.11  If safe_n(C,s,h,J ∗ R,Q), h ⊎ h_R is defined, and s,h_R ⊨ R,
then safe_n(C, s, h ⊎ h_R, J, Q ∗ R).

Lemma 5.3  If safe_n(C,s,h,(Γ, r : R),Q) and C is well-formed and fv(R) ∩ wr(C) = ∅,
then
(i)  if r ∉ locked(C), then for all h_R, if dom(h) ∩ dom(h_R) = ∅ and s,h_R ⊨ R,
     then safe_n(resource r in C, s, h ⊎ h_R, Γ, Q ∗ R); and
(ii) if r ∈ locked(C), then safe_n(resource r in C, s, h, Γ, Q ∗ R).

Lemma 5.4  If safe_n(C,s,h,Γ,Q ∗ R) and within r do C is well-formed, then
safe_n(within r do C, s, h, (Γ, r : R), Q).
```

**Data race freedom is not stated as a numbered theorem in this PDF.** §5's title is "Multiple Resources & Data Race Freedom" and §1 promises to "prove CSL's data race freedom result", but the DRF conclusion appears only as the informal consequence of Definition 5.1 clause (ii) ("`C,(s, h ⊎ h_F) ↛ abort`") together with the `RaceDetect` rule making every race abort. The formal statement is `NOT FOUND IN PDF` as a displayed theorem; it is in the Isabelle development [18].

Also `NOT FOUND IN PDF`: the formal definitions of `accesses(C,s)` and `writes(C,s)` (deferred to [18]), and the proofs of Lemmas 5.3 and 5.4 (deferred to [18]).

## Proof technique

**Rule-by-rule semantic soundness, then rule induction.** §4: "Our proof strategy is to prove that each proof rule is a sound implication if we replace all the ⊢ by ⊨. Then, the theorem follows by a straightforward rule induction."

**Yes, there is a step budget — and it is the whole point of the technique.** `safe_n` is indexed by a number of execution steps, and §3 says exactly what it is for: "The number of steps merely ensures the definition is structurally decreasing." So `n` is a *well-foundedness device for the definition*, not a bound on the program. Validity quantifies over all `n` (Definition 3.2), so no execution is truncated.

Each component lemma is then proved **by induction on `n`**:
- Lemma 4.9 (Par): "By induction on n", with the inductive hypothesis quantified over all `C1, h1, C2, h2`. Cases Par1 / Par2 (symmetric) / Par3.
- Lemma 4.10 (Frame): "By induction on n. The base case is trivial."
- Lemma 4.11 (Share): "By induction on n."
- Lemma 4.3 (downward closure in n): "(This is proved by induction on m.)"
- Lemma 4.7 (atomic bodies): "proved by an induction on the length of the →* traces".

The `safe_n` formulation is deliberately pre-inductive: "A nice aspect of Definition 3.1 is that the straightforward lemmas about safety of compound commands are usually already inductive, thereby rendering the otherwise most challenging part of soundness proofs trivial. The only exception is Lemma 5.3 about the resource declaration rule ... which was arguably the most intellectually challenging part of the proof" (§3).

**Where precision is needed (and only there).** §4, Conj case: the two uses of `safe_n(C,s,h,J,Q_i)` give splittings `h' = h¹ ⊎ h¹_J` and `h' = h² ⊎ h²_J`, "but, in general, we do not know that `h¹ = h²` which would allow us to complete the proof. Since, however, J must be precise, then (from Definition 2.1) `h¹_J = h²_J`, and since ⊎ is cancellative, we also have `h¹ = h²`."

**The `h_F` quantification replaces safety monotonicity and the frame property.** §3: "In condition (ii), `h_F` essentially plays the role of 'safety monotonicity' ... Similarly, in condition (iii), `h_F` plays the role of the 'frame property'." And: "if the operational semantics satisfies the safety monotonicity and frame properties (which it does in our case), we can drop the `h_F` quantification. ... Having the quantification, however, is crucial for some of the CSL extensions (see §6)."

**`abort` is not strictly required.** §3: "we do not strictly require an abort semantics to prove the soundness of CSL: if we drop condition (ii) from Definition 3.1, we can still prove the soundness of CSL without ever referring to an abort semantics. In contrast, proofs relying on the safety monotonicity and frame properties heavily depend on an abort semantics (e.g., [3,4,5,6,9,10])."

## Side condition on parallel composition

Verbatim (§2, Figure 2):

```text
 J ⊢ {P1} C1 {Q1}
 J ⊢ {P2} C2 {Q2}
 fv(J, P1, C1, Q1) ∩ wr(C2) = ∅
 fv(J, P2, C2, Q2) ∩ wr(C1) = ∅
 ─────────────────────────────────          (Par)
 J ⊢ {P1 ∗ P2} C1‖C2 {Q1 ∗ Q2}
```

Vafeiadis's gloss (§2): "**Par** allows us to compose two threads in parallel if and only if their preconditions describe disjoint parts of the heap. This prevents data races on memory locations. The side-conditions ensure that there are also no data races on program variables—here, `fv` returns the set of free variables of a command or an assertion, whereas `wr(C)` returns the set of variables being assigned to by the command C."

Note the variable side conditions are **Bernstein-shaped on the stack** (`fv ∩ wr`, both directions), so two threads may both read the same variable. The heap condition, carried by `∗`, is **strict disjointness** — no read/read sharing.

**Read/read sharing in base CSL: NO; with the §6 permissions extension: YES.** §6 is explicit:

> "Permissions [2,1] are an extension to the standard heap model that enables read-sharing between parallel threads. Consider, for example, the Hoare triple: `{10 ↦ −} x := [10] ‖ y := [10] {10 ↦ −}`. Standard CSL cannot verify that the program satisfies its specification because to read from [10] both threads must know that the cell is allocated (i.e., have `10 ↦ −` as a precondition), but the assertion `10 ↦ − ∗ 10 ↦ −` (required by the parallel composition rule) is unsatisfiable. With permissions, one can instead split `10 ↦ −` into two half permissions, `(10 ↦^0.5 −) ∗ (10 ↦^0.5 −)`, and give one to each thread."

The permission rule:

```text
       x ∉ fv(E, E', E'', J)
 ────────────────────────────────────────────  (Read2)
 J ⊢ {E ↦^E' E''} x := [E] {E ↦^E' E'' ∧ x = E''}
```

Permission models (§6): "sets, K, with a distinguished element, ⊤ ∈ K, called full permission, and a commutative and associative partial operator, ⊕", satisfying `∀k ∈ K. ¬def(⊤ ⊕ k)` and `∀k ∈ K \ {⊤}. ∃k' ∈ K. k ⊕ k' = ⊤`. Fractional permissions are the instance `K = (0,1]`, `⊕` = addition, `⊤ = 1`.

Why the soundness definition survives unchanged (§6): "The check in the safe definition that `h_F` does not change by transitions ensures that programs update the values only of heap locations they have full permission to, but allows threads to access any memory they partially own." And: "The soundness proof carries over to permission-heaps with no difficulty."

**Ownership transfer: yes**, via `Atom` / the CCR rule, where `J` is moved into the local heap for the duration of the region. §2's reading of a triple: "the command 'owns' the state described by its precondition ... In contrast, the state described by J can be changed by other concurrently executing threads."

## Shared state / resources

Yes. Two mechanisms, both resource-invariant based:

- **§2–4: a single global invariant `J` + `atomic C`.** The rule is `Atom`: `emp ⊢ {P ∗ J} C {Q ∗ J} / J ⊢ {P} atomic C {Q}`. `Share` lets you move local state into the invariant at any point: `J ∗ R ⊢ {P} C {Q} / J ⊢ {P ∗ R} C {Q ∗ R}`.
- **§5: multiple named resources `Γ : r ↦ J`, with CCRs.** Rules as quoted above. Mutual exclusion is enforced operationally by the `locked(·)` side conditions on `Par1`/`Par2`.

No CAS, no ghost state in the Iris sense. §7 extends to **RGSep**, replacing the invariant with a rely/guarantee pair:

```text
Definition 7.1  safeRG_0(C, s, h_L, h_S, R, G, Q) holds always.
safeRG_{n+1}(C, s, h_L, h_S, R, G, Q) if and only if
(i)   if C = skip, then s,(h_L,h_S) ⊨ Q; and
(ii)  for all h_F, C,(s, h_L ⊎ h_S ⊎ h_F) ↛ abort; and
(iii) whenever C,(s, h_L ⊎ h_S ⊎ h_F) → C',(s',h'), then there exist h'_L and h'_S such
      that h' = h'_L ⊎ h'_S ⊎ h_F and s,(h_S,h'_S) ⊨ G and safeRG_n(C',s',h'_L,h'_S,R,G,Q);
(iv)  whenever s,(h_S,h'_S) ⊨ R and def(h_L ⊎ h'_S), then safeRG_n(C,s,h_L,h'_S,R,G,Q).

Definition 7.2  R; G ⊨RGSep {P} C {Q} if and only if for all s, h_L, h_S, and n,
if s,(h_L,h_S) ⊨ P, then safeRG_n(C, s, h_L, h_S, R, G, Q).
```

"Note that the RGSep definitions use exactly the same operational semantics for commands as the CSL definitions: we did not have to come up with a new special semantics" (§7).

## What it does NOT claim

- **It proves no equality or equivalence between a parallel program and a sequential one.** Nothing in the paper relates two different programs. Every judgment (`J ⊢ {P} C {Q}`, `J ⊨ {P} C {Q}`, `safe_n(C, …)`, `R;G ⊨RGSep {P} C {Q}`) mentions exactly one command. What it proves instead is Theorem 4.5: every derivable triple is valid, where validity = (no abort) ∧ (invariant maintained) ∧ (postcondition on termination), relative to the step-indexed `safe_n`.
- **It is explicitly a soundness-proof paper, not a logic paper.** The rules are O'Hearn's/Brookes's; the contribution is the semantics of judgments and the proof method. §8: "The paper has presented a concise soundness proof of CSL and related program logics that does not involve any intermediate instrumented semantics."
- **No completeness.** Not discussed anywhere.
- **No liveness; partial correctness only.** §8: "So far, however, we have used this style of semantic definitions to justify the correctness only of program logics about partial correctness. It is quite possible to extend these definitions in order to capture certain kinds of liveness properties."
- **No numbered data-race-freedom theorem** in this PDF (see above); the result is asserted in §1/§5 and realized by `RaceDetect` + Definition 5.1(ii)–(iii), with the formal content in the Isabelle files.
- **The §2 semantics has a known gap for diverging atomic bodies**, admitted in fn.2 and repaired only by moving to the §5 CCR semantics.
- **Draconian variable side conditions.** §2 fn.3: "For simplicity, we impose draconian variable side-conditions. In effect, only heap cells may be shared among threads, as J cannot mention any updateable variables."
- **No granularity-independence claim.** The grain is fixed by Figure 1; nothing says results are independent of it (contrast Reynolds).

## Mechanized?
**Yes — Isabelle/HOL.** §1: "Our definition is concise and results in a relatively simple soundness proof, which we have formalised in Isabelle/HOL." Footnote 1: "The proof scripts are available at http://www.mpi-sws.org/~viktor/cslsound [18]."

What is mechanized, per the paper's own statements:
- The §2–§4 soundness proof (Theorem 4.5) for the `atomic`-block version.
- The §5 multi-resource / CCR version: "The proof of soundness proceeds as before and **has been fully formalised in Isabelle/HOL**. See [18] for details." This covers Lemmas 5.3 and 5.4, whose proofs are *only* in [18], plus "local variable declarations as well as the auxiliary variable elimination rule as in Brookes's original proof [3]."
- §6 permissions: "The soundness proof carries over to permission-heaps with no difficulty. See the **machine-checked proof** [18] for details."
- The claim that the `h_F` quantification can be dropped when the semantics satisfies safety monotonicity and the frame property: "(See [18] for a proof.)"
- The definitions of `accesses(C,s)` and `writes(C,s)`.

What is **on paper only**: §7 RGSep — the soundness proof there is only described ("The soundness proof goes through in pretty much the same way as in §4 and in [17]"), with no mechanization claim.

## Quotable lines

- "(accesses(C1,s) ∩ writes(C2,s)) ∪ (accesses(C2,s) ∩ writes(C1,s)) ≠ ∅ ⟹ (C1‖C2, (s,h)) → abort" — §5, Figure 3 (RaceDetect)
- "The number of steps merely ensures the definition is structurally decreasing." — §3
- "Par allows us to compose two threads in parallel if and only if their preconditions describe disjoint parts of the heap. This prevents data races on memory locations." — §2
- "Permissions are an extension to the standard heap model that enables read-sharing between parallel threads." — §6
- "we do not strictly require an abort semantics to prove the soundness of CSL: if we drop condition (ii) from Definition 3.1, we can still prove the soundness of CSL without ever referring to an abort semantics." — §3
- "We have shown that inventing elaborate semantics is unnecessary and have argued that it is also harmful because it obscures the soundness argument." — §8
- "the soundness of any particular instance of the logic ... tells us nothing about how verified programs behave when executed by the hardware. ... This is why our proof is instead based on a concrete semantics." — §8

## Relevance to a parallel-equals-sequential equivalence theorem

- **`RaceDetect` is literally the Bernstein condition as an abort trigger**, on a standard small-step relation, with reads allowed to overlap. A project whose races go to an absorbing `wrong` under the same condition is reusing Vafeiadis's operational device; the difference is that he uses it to make CSL's *unary* safety claim non-vacuous, while an equivalence theorem uses it to carve out the programs for which the equality holds.
- **The step-indexed `safe_n` is a template for a Lean development, but it is unary.** `safe_n(C, s, h, J, Q)` relates a program to a postcondition, never to another program, and `n` is a well-foundedness device ("merely ensures the definition is structurally decreasing"), not a schedule bound. An outcome-set equality over a nondeterministic step relation needs induction over the *reduction derivation* on both sides, which this predicate does not provide.
- **Read/read sharing costs Vafeiadis an extension.** §6 shows plainly that `{10 ↦ −} x := [10] ‖ y := [10] {10 ↦ −}` is unprovable in base CSL and needs fractional permissions and a permission-heap model to recover. A footprint-based Bernstein condition gets the same program for free, with no permission algebra — that contrast (`∗` + fractions vs. footprint sets) is the cleanest way to state the technical difference.
- **Soundness-of-CSL and par≡seq answer different questions on the same semantics.** Theorem 4.5 says a provable program is safe and meets its spec; it says nothing about which *other* program computes the same thing. Both can be stated over Figure 1's `→` relation, so they are complementary results about one model rather than competing ones.
