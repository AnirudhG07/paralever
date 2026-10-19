# Simuliris: A Separation Logic Framework for Verifying Concurrent Program Optimizations
Lennard Gäher, Michael Sammler, Simon Spies, Ralf Jung, Hoang-Hai Dang, Robbert Krebbers, Jeehoon Kang, Derek Dreyer · POPL 2022 (Proc. ACM Program. Lang. 6, POPL, Article 28) · `gaeher-popl22-simuliris.pdf`

## One-line thesis
A language-generic, *non*-step-indexed separation logic housing a coinductive relational simulation `{P} e_t ⪯ e_s {Φ}`, whose adequacy theorem yields **fair termination-preserving contextual refinement** of an optimized (target) program against an original (source) program, and whose proof rules let the optimizer *exploit* undefined behavior of data races to gain ownership of escaped locations.

## The setting

**Language.** SimuLang (§2, Fig. 2 p. 28:6): an expression-based language with ML-style references, **fork-based concurrency**, function pointers, and `while` loops. There is no `par` construct; concurrency is `fork{e}`. Grammar (Fig. 2, §2):

```text
Expr ∋ e ::= v | x | let x := e₁ in e₂ | e₁ + e₂ | call e₁ e₂ | fork{e}
           | ref(e) | !e | e₁ ← e₂ | free(e) | if e₁ then e₂ else e₃ | while e₁ do e₂ od | …
Val  ∋ v ::= z : Z | b : B | ℓ : Loc | f : FnName | () | …
Prog ∋ ρ ::= (f x ≜ e), ρ | ∅
Ectx ∋ K ::= • | let x := K in e₂ | e₁ + K | K + v | call e₁ K | call K v
           | ref(K) | !K | e₁ ← K | K ← v | free(K) | if K then e₂ else e₃ | …
```

A whole program is a *list of mutually recursive function declarations*; SimuLang has no λ-terms ("post-closure-conversion"). Evaluation order is right-to-left. Local `let`-bound variables are immutable; mutable stack variables are modelled with `ref(·)` (§2, p. 28:6).

**Memory model.** The memory model of λRust / RustBelt (§3.1). Two access kinds: **non-atomic** (`x ← y`, `!x`) and **sequentially consistent atomic** (`x ←sc y`, `!sc x`). There are no relaxed accesses: "SimuLang provides a memory model with sequentially consistent and non-atomic accesses" (§9). The operational semantics is extended with a **data-race detector** that "raises UB if two threads access the same location at the same time, where at least one access is a store and at least one access is non-atomic" (§3.1, p. 28:13). So the atomic grain is *not* irrelevant here: the grain is exactly a single per-thread reduction step, and simultaneity at that grain is what the race detector checks.

**Termination.** Terminating programs only? **No** — this is the opposite. Non-terminating programs are first-class and the whole point: the behaviour set includes a divergence token `ω`, and the correctness condition is *fair termination preservation*. Loops may diverge (`while-coind` works "without any knowledge of … whether it even terminates", §2.4).

**Operational semantics** (§4.1, Fig. 11 p. 28:17):

```text
T ∈ TPool ≜ List(Expr)                 (K[fork{e}], σ) →ρ (K[()], σ, [e])
σ ∈ State ≜ Loc ⇀fin MemCell
Beh ∋ b ::= V(v) | ω | ⊤                      (T(π), σ) →ρ (e′, σ′, e_f)
                                     ────────────────────────────────────
                                     (T, σ) →ρ,tp (T[π ↦ e′] ++ e_f, σ′)
```

i.e. a **nondeterministic small-step thread-pool relation** `→tp` picking an arbitrary thread. Initial configuration `I ≜ ([call main ()], ∅)`.

**Judgment form.** Relational, in the style of Relational Hoare Logic [Benton 2004] (§2, p. 28:5):

```text
{P} e_t ⪯ e_s {v_t, v_s. Φ v_t v_s}
```

"under precondition 𝑃, the source expression 𝑒𝑠 simulates the target expression 𝑒𝑡 such that both terminate in values related by postcondition 𝛷, or both diverge" (§2, p. 28:6). Later generalized to a postcondition on *expressions*, `{Φ e_t e_s} e_t ⪯ e_s {e_t′, e_s′. Φ e_t′ e_s′}`, to support `while-paco` (§2.4). The simulation is also indexed by a thread id once data-race exploitation enters: `e_t ⪯π e_s` (§3.2).

## Main results, stated

There are no numbered *definitions* in this paper; the simulation relation is given in **Figure 12** (unnumbered, §5.1). The numbered results are 4.1, 4.2, 4.3 (a "Statement"), 5.1, 5.2 — that is all.

### The simulation relation (§5.1, Fig. 12, p. 28:19) — verbatim

```text
sim e_t e_s Φ = ∀σ_t, σ_s, ρ_t, ρ_s. S(ρ_t, σ_t, ρ_s, σ_s) ∗ safe(ρ_s, e_s, σ_s) −∗ |⇛
  ( Base case: ∃e_s′, σ_s′. (e_s, σ_s) →ρ_s * (e_s′, σ_s′) ∗ S(ρ_t, σ_t, ρ_s, σ_s′) ∗ Φ e_t e_s′ ) ∨
  ( Step case: reducible(ρ_t, e_t, σ_t) ∗ ∀e_t′, σ_t′, T_t. (e_t, σ_t) →ρ_t (e_t′, σ_t′, T_t) −∗ |⇛
      ( Source stutter: T_t = [] ∗ S(ρ_t, σ_t′, ρ_s, σ_s) ∗ sim e_t′ e_s Φ ) ∨
      ( Source step:    ∃e_s′, e_s′′, σ_s′, σ_s′′, T_s. (e_s, σ_s) →ρ_s * (e_s′, σ_s′) ∗ (e_s′, σ_s′) →ρ_s (e_s′′, σ_s′′, T_s) ∗
                        S(ρ_t, σ_t′, ρ_s, σ_s′′) ∗ sim e_t′ e_s′′ Φ ∗ |T_t| = |T_s| ∗
                        ✱_{(e_t′′′, e_s′′′) ∈ zip(T_t, T_s)} sim e_t′′′ e_s′′′ V ) )
```

and

```text
{P} e_t ⪯ e_s {Φ} ≜ □(P −∗ sim e_t e_s Φ)
```

with `sim ≜ νG. μL. simbody(G, L)` — a **mixed (nested greatest-then-least) fixed point**; the red (coinductive) occurrences become `G`, the blue (source-stutter) occurrence becomes `L`. "The resulting definition satisfies sim = simbody(sim, sim), but it is neither the greatest nor the least fixed-point—it is in between." (§5.1, p. 28:21)

### Behaviours and refinement (§4.1, p. 28:17–18) — verbatim

```text
B(ρ) ≜ { V(v)  | I has a finite →ρ,tp execution where the main thread returns v }
     ∪ { ω     | I has a fair, infinite →ρ,tp execution }
     ∪ { ⊤     | I can via →ρ,tp reach a configuration which is stuck }

V(v_t) ⊑beh V(v_s) if O(v_t, v_s)       ω ⊑beh ω        b ⊑beh ⊤

ρ_t ⊑prog ρ_s ≜ ∀b_t ∈ B(ρ_t). ∃b_s ∈ B(ρ_s). b_t ⊑beh b_s

e_t ⊑ctx e_s ≜ ∀ρ, f, x, C. (FreeVars(C[e_t]) ∪ FreeVars(C[e_s]) ⊆ {x}) ∧ wf(C) ∧
                 (∀(f′ x′ ≜ e′) ∈ ρ. FreeVars(e′) ⊆ {x′} ∧ wf(e′)) ⇒
                 (f x ≜ C[e_t], ρ) ⊑prog (f x ≜ C[e_s], ρ)
```

Fairness is **weak fairness** [Lehmann et al. 1981]: "an infinite execution of a thread pool is fair if every thread which is eventually always enabled does always eventually take a step", with `enabled(ρ, σ, T, π) ≜ ∃e, e′, σ′. T(π) = e ∧ (e, σ) →ρ (e′, σ′)` (§4.1, p. 28:17).

### The logical relation (§4.2, p. 28:18) — verbatim

```text
e_t ≤log e_s ≜ ∀γ : FreeVars(e_t) ∪ FreeVars(e_s) → Val × Val.
  {exploit π ∅ ∗ ∀x, v_t, v_s. γ(x) = (v_t, v_s) ⇒ V v_t v_s}
     γ_tgt(e_t) ⪯ γ_src(e_s)
  {v_t′, v_s′. exploit π ∅ ∗ V v_t′ v_s′}
```

### Numbered theorems

```text
Theorem 4.1 (Fundamental Theorem). Let e be a well-formed expression. Then e ≤log e.

Theorem 4.2 (Contextual closure). Assume e_t ≤log e_s and wf(C). Then C[e_t] ≤log C[e_s].

Statement 4.3 (Adequacy). If e_t ≤log e_s, then e_t ⊑ctx e_s.

Lemma 5.1 (Whole-program adequacy). If S(ρ_t, ∅, ρ_s, ∅) ∗ ρ_t ≤prog ρ_s, then ρ_t ⊑prog ρ_s.

Theorem 5.2 (Adequacy, Statement 4.3). If e_t ≤log e_s, then e_t ⊑ctx e_s.
```

with the whole-program logical relation (§5.2, p. 28:21):

```text
ρ_t ≤prog ρ_s ≜ ∀(f x ≜ e_s) ∈ ρ_s. ∃(f x ≜ e_t) ∈ ρ_t. ∀v_t, v_s. {V v_t v_s} e_t[v_t/x] ⪯ e_s[v_s/x] {V}
```

### Core proof rules (§2, Fig. 3, p. 28:7) — verbatim

```text
Language-independent rules:

  SOURCE-FOCUS
  {P} e_s {v_s. Ψ v_s}^src     ∀v_s. {Ψ v_s} e_t ⪯ K_s[v_s] {Φ}
  ────────────────────────────────────────────────────────────
                 {P} e_t ⪯ K_s[e_s] {Φ}

  SIM-FRAME
          {P} e_t ⪯ e_s {Φ}
  ───────────────────────────────────────────
  {P ∗ R} e_t ⪯ e_s {v_t, v_s. Φ v_t v_s ∗ R}

  SIM-CALL
  {V v_t v_s} call f v_t ⪯ call f v_s {v_t′, v_s′. V v_t′ v_s′}

  SIM-BIND
  {P} e_t ⪯ e_s {v_t, v_s. Ψ v_t v_s}    ∀v_t, v_s. {Ψ v_t v_s} K_t[v_t] ⪯ K_s[v_s] {Φ}
  ──────────────────────────────────────────────────────────────────────────────────
                        {P} K_t[e_t] ⪯ K_s[e_s] {Φ}

  SIM-VALUE
  {Φ v_t v_s} v_t ⪯ v_s {Φ}

SimuLang rules:

  SOURCE-ALLOC                                          TARGET-ALLOC
  {True} ref(v_s) {v_s′. ∃ℓ_s. v_s′ = ℓ_s ∗ ℓ_s ↦src v_s}^src   {True} ref(v_t) {v_t′. ∃ℓ_t. v_t′ = ℓ_t ∗ ℓ_t ↦tgt v_t}^tgt

  SOURCE-PURE                                 TARGET-PURE
  e_s →*pure e_s′    {P} e_t ⪯ e_s′ {Φ}       e_t →*pure e_t′    {P} e_t′ ⪯ e_s {Φ}
  ───────────────────────────────────         ───────────────────────────────────
          {P} e_t ⪯ e_s {Φ}                            {P} e_t ⪯ e_s {Φ}

  SOURCE-LOAD                                           TARGET-LOAD
  {ℓ_s ↦src v_s} !ℓ_s {v_s′. v_s′ = v_s ∗ ℓ_s ↦src v_s}^src     {ℓ_t ↦tgt v_t} !ℓ_t {v_t′. v_t′ = v_t ∗ ℓ_t ↦tgt v_t}^tgt

  SOURCE-STORE                                          TARGET-STORE
  {ℓ_s ↦src _} ℓ_s ← v_s {v_s′. v_s′ = () ∗ ℓ_s ↦src v_s}^src   {ℓ_t ↦tgt _} ℓ_t ← v_t {v_t′. v_t′ = () ∗ ℓ_t ↦tgt v_t}^tgt
```

### Value relation (§2.2, Fig. 4, p. 28:9)

```text
V z_t z_s ≜ z_t = z_s                 (value-int)
V b_t b_s ≜ b_t = b_s                 (value-bool)
V ℓ_t ℓ_s ≜ ℓ_t ↔h ℓ_s                (value-loc)
V f_s f_t ≜ f_s = f_t                 (value-fnptr)
V (v_t, w_t) (v_s, w_s) ≜ V v_t v_s ∗ V w_t w_s   (value-pair)
```

"Values of different kinds (e.g., integers and locations) are not related." (Fig. 4 caption)

### Escaping and UB-exploitation rules

```text
LOC-ESCAPE
                     {ℓ_t ↔h ℓ_s ∗ P} e_t ⪯ e_s {Φ}
  ──────────────────────────────────────────────────────────────────
  {ℓ_t ↦tgt v_t ∗ ℓ_s ↦src v_s ∗ V v_t v_s ∗ P} e_t ⪯ e_s {Φ}

SIM-LOAD-ESCAPED
  {ℓ_t ↔h ℓ_s} !ℓ_t ⪯ !ℓ_s {v_t, v_s. V v_t v_s}        (§2.2; later weakened to SIM-LOAD-NA)

SIM-SRC-SAFE                                     SAFE-DIV-INT-NONZERO
  e_s ⇝ Q      {Q ∗ P} e_t ⪯ e_s {Φ}             v/w ⇝ ∃z₁, z₂ : Z. v = z₁ ∧ w = z₂ ∧ z₂ ≠ 0
  ────────────────────────────────
      {P} e_t ⪯ e_s {Φ}                          (§2.3, Fig. 5)

with   e_s ⇝ Q ≜ □(∀ρ_s, σ_s. safe(ρ_s, e_s, σ_s) ⇒ Q)        (§5.1)
```

Data-race exploitation rules (§3.2, Fig. 8, p. 28:14) — verbatim:

```text
EXPLOIT-STORE
        C(ℓ_s) = ⊥      e_s →*? K[ℓ_s ← v₀]
  ∀v_t, v_s. {ℓ_s ↦src v_s ∗ ℓ_t ↦tgt v_t ∗ V v_t v_s ∗ exploit π (C, ℓ_s ↦ Wr) ∗ P} e_t ⪯π e_s {Φ}
  ───────────────────────────────────────────────────────────────────────────────────────────────
                     {ℓ_t ↔h ℓ_s ∗ exploit π C ∗ P} e_t ⪯π e_s {Φ}

EXPLOIT-LOAD
        C(ℓ_s) = ⊥      e_s →*? K[!ℓ_s]
  ∀v_t, v_s, q. {ℓ_s ↦^q src v_s ∗ ℓ_t ↦^q tgt v_t ∗ V v_t v_s ∗ exploit π (C, ℓ_s ↦ Rd(q)) ∗ P} e_t ⪯π e_s {Φ}
  ───────────────────────────────────────────────────────────────────────────────────────────────────────────
                     {ℓ_t ↔h ℓ_s ∗ exploit π C ∗ P} e_t ⪯π e_s {Φ}

RELEASE-EXPLOIT
  C(ℓ_s) = c    q = exploit_frac(c)    {exploit π (C \ ℓ_s) ∗ P} e_t ⪯π e_s {Φ}
  ──────────────────────────────────────────────────────────────────────────────────────────
  {ℓ_s ↦^q src v_s ∗ ℓ_t ↦^q tgt v_t ∗ V v_t v_s ∗ ℓ_t ↔h ℓ_s ∗ exploit π C ∗ P} e_t ⪯π e_s {Φ}

  exploit_frac(Rd(q)) ≜ q         exploit_frac(Wr) ≜ 1
```

Revised rules (§3.2, Fig. 9, p. 28:15) — verbatim:

```text
SIM-LOAD-SC
  {C(ℓ_s) = ⊥ ∗ ℓ_t ↔h ℓ_s ∗ exploit π C} !sc ℓ_t ⪯π !sc ℓ_s {v_t, v_s. V v_t v_s ∗ exploit π C}

SIM-LOAD-NA
  {C(ℓ_s) = ⊥ ∗ ℓ_t ↔h ℓ_s ∗ exploit π C} !ℓ_t ⪯π !ℓ_s {v_t, v_s. V v_t v_s ∗ exploit π C}

SIM-STORE-SC
  {ℓ_t ↔h ℓ_s ∗ V v_t v_s ∗ exploit π ∅} ℓ_t ←sc v_t ⪯π ℓ_s ←sc v_s {v_t′, v_s′. v_t′ = () ∗ v_s′ = () ∗ exploit π ∅}

SIM-CALL-REVISED
  {V v_t v_s ∗ exploit π ∅} call f v_t ⪯π call f v_s {v_t′, v_s′. V v_t′ v_s′ ∗ exploit π ∅}
```

### Loop rules (§2.4, p. 28:11)

```text
WHILE-COIND
  {I} c_t ⪯ c_s {v_t, v_s. V v_t v_s ∗ ((v_s = true ∗ J) ∨ (v_s ≠ true ∗ Q))}      {J} e_t ⪯ e_s {I}
  ──────────────────────────────────────────────────────────────────────────────────────────────
              {I} while c_t do e_t od ⪯ while c_s do e_s od {Q}

WHILE-PACO
  W_t = while c_t do e_t od     W_s = while c_s do e_s od
  {I} if c_t then e_t; W_t else () ⪯ if c_s then e_s; W_s else () {e_t′, e_s′. Φ e_t′ e_s′ ∨ (e_t′ = W_t ∗ e_s′ = W_s ∗ I)}
  ────────────────────────────────────────────────────────────────────────────────────────────────────────────────────
                            {I} W_t ⪯ W_s {e_t′, e_s′. Φ e_t′ e_s′}
```

### Verified case studies

- §2.1 removing a load from a local unescaped location: `{True} let y := ref(42) in 42 ⪯ let y := ref(42) in !y {v_t, v_s. v_t = v_s}`.
- §2.2 moving a load across an unknown call `call f 23`, and across a call that is *passed* the pointer.
- §2.3 exploiting division-by-zero UB to remove a conditional.
- §2.4 Fig. 6 loop-invariant code motion for a load; Fig. 7 replacing repeated addition by primitive multiplication, `{z₁ ≥ 0} z₁ ∗ z₂ ⪯ (loop) {v_t, v_s. v_t = v_s}`.
- §3.2 store-to-load forwarding across an atomic load, `{x_t ↔h x_s ∗ y_t ↔h y_s ∗ exploit π ∅} x_t ← 42; !sc y_t; 42 ⪯π x_s ← 42; !sc y_s; !x_s {v_t, v_s. v_t = v_s ∗ exploit π ∅}`.
- §3.3 Fig. 10, the motivating loop-hoisting optimization from §1 (hoisting two non-atomic loads out of a possibly-diverging loop).
- §7 Stacked Borrows: "We verify correctness not only of the original paper's optimizations, but also of a new loop hoisting optimization" (Fig. 14a/14b), for a **new concurrent version** of Stacked Borrows with SC accesses, in which loads with an invalid tag return `poison` (deferred UB) rather than immediately triggering UB.
- §8: "We have verified all reorderings established by this prior work that involve only the accesses supported by our system and at least one non-atomic access", plus one new one: "moving a non-atomic load before a sequentially consistent load".

## Proof technique

Goal-directed, following Fig. 13 (§5.2, p. 28:21) backwards: `e_t ≤log e_s` → (Theorem 4.2 contextual closure + Theorem 4.1 fundamental theorem) → `ρ_t ≤prog ρ_s` → (**Lemma 5.1**, the language-independent heart) → `ρ_t ⊑prog ρ_s` → `e_t ⊑ctx e_s` (Theorem 5.2, language-specific).

**Key lemma: Lemma 5.1 (Whole-program adequacy).** Its proof sketch (p. 28:21–22) has two steps:

1. Show the **open** simulation (which may skip matching `call f` on both sides, `SIM-CALL`) implies a **closed** simulation. "This proof ties the big recursive knot over all the mutually recursive function definitions in the source and target programs. It essentially 'inlines' the simulation of the calls that were skipped." Open simulations are cited to Kang et al. 2015 and Hur et al. 2012.
2. Show the closed simulation implies whole-program refinement, in three cases matching the three constructors of `B(ρ)`:
   - **(1) Undefined Behavior.** "the target will never be stuck, because all the expressions it can reach are reducible" — from `reducible(ρ_t, e_t, σ_t)` in the step case.
   - **(2) Result Value.** From the postcondition: if the target terminates, the source terminates in a value and both are related by `V`, hence by `O`.
   - **(3) Fair Divergence.** "by far the most challenging case… the heart of the intuitive argument can still be recovered (**with a coinduction and three nested inductions**)". The details are explicitly omitted from the paper for space (footnote 19).

**What the induction goes over.** There is no step budget / fuel. The step-index is fixed at 0 (Iris^light). Instead, the finiteness that makes termination preservation work comes from the **least fixed point `μL` nested inside the greatest fixed point `νG`**: "The least fixed-point on the inside ensures that we can stutter the source, but we can only do so finitely often, which will be crucial for the adequacy proof of fair termination preservation" (§5.1, p. 28:21). The `νG` part gives "a language-independent parametric coinduction principle, from which language-specific rules such as `while-paco` can be derived".

**Soundness of the UB-exploitation rules (§6).** The state interpretation carries a heap bijection between escaped source and target locations:

```text
heapbij(H) ≜ ∃L. bijauth(L) ∗ ✱_{(ℓ_t, ℓ_s) ∈ L} ∃q_h, v_t, v_s. H(ℓ_s, q_h) ∗ V v_t v_s ∗ ℓ_t ↦^{q_h} tgt v_t ∗ ℓ_s ↦^{q_h} src v_s

H_C(ℓ_s, q_h) ≜ 1 = q_h + Σ_π { exploit_frac(c)  if C_π(ℓ_s) = c ; 0 otherwise }

exploit_wf(ρ_s, σ_s, T_s, C) ≜ ∀π, ℓ_s, c. C_π(ℓ_s) = c ⇒
    ∃K, e, v. pool_safe(ρ_s, T_s[π ↦ e], σ_s) ∧ e →*? K[c = Wr ? ℓ_s ← v : !ℓ_s]

e_s →*? e_s′ ≜ ∀ρ_s, σ_s. safe(ρ_s, e_s, σ_s) ⇒ ∃σ_s′. (e_s, σ_s) →ρ_s * (e_s′, σ_s′)

S(…, ρ_s, σ_s, T_s) ≜ … ∗ ∃C. exploitauth(C) ∗ exploit_wf(ρ_s, σ_s, T_s, C) ∗ heapbij(H_C)
```

The argument is: ownership can be stolen out of `heapbij` only if any *other* thread's access that would have needed it can be shown to **race** — "we can only remove ownership from heapbij if we prove that each access expecting this ownership to be in heapbij has a data race and thus need not be considered" (§6). `exploit_wf` "keeps track of alternative interleavings where thread π is 'paused' while the other source threads step along with the target. Since all interleavings must be data-race free, demonstrating a race in one of these alternative interleavings is sufficient."

## Side condition on parallel composition

**There is no `par` rule and no `sim-fork` proof rule anywhere in the paper body.** `NOT FOUND IN PDF` for a syntactic parallel-composition inference rule. Concurrency is `fork{e}`, and the composition condition is baked into the *model*, in the source-step case of Fig. 12:

```text
|T_t| = |T_s| ∗ ✱_{(e_t′′′, e_s′′′) ∈ zip(T_t, T_s)} sim e_t′′′ e_s′′′ V
```

The paper's own gloss (§5.1, "Concurrency", p. 28:22), quoted exactly:

> "Our simulation relation enforces a one-to-one mapping between threads in the source and target programs: for each thread forked in the target, there must be a matching thread simulating it in the source. This is restrictive, but sufficient for the vast majority of compiler optimizations—and it is crucial to our proof of fair termination preservation."

and

> "Note how in the source step case, we use a separating conjunction to concisely express that the simulation proofs of the forked-off threads, and of the original thread, are all based on disjoint resources. This ensures that the simulation of one thread does not interfere with the resources required by another thread."

So the side condition for composing two threads is the ordinary separation-logic one — **disjoint resources, via `∗`** — plus a *structural* condition peculiar to the relational setting: the source step must fork exactly as many threads as the target step (`|T_t| = |T_s|`), and the forked threads' postcondition is the value relation `V`.

**Is read/read sharing allowed?** Yes, but via **fractional permissions**, not via a Bernstein-style set-disjointness condition. `EXPLOIT-LOAD` hands out `ℓ_s ↦^q src v_s ∗ ℓ_t ↦^q tgt v_t` for "some fraction q" (Boyland 2003; Bornat et al. 2005), and `exploit_frac(Rd(q)) ≜ q` while `exploit_frac(Wr) ≜ 1`. The paper: "The rule for exploiting loads EXPLOIT-LOAD is similar to EXPLOIT-STORE except that it does not provide full ownership but only *fractional ownership* with some fraction q. This gives us permission to introduce extra loads in the target program, but we cannot introduce extra stores as that would require full ownership" (§3.2, p. 28:14). The fractions are forced to sum to 1 across all threads by `H_C` (§6).

**Is there ownership transfer?** Yes. `LOC-ESCAPE` transfers `ℓ_t ↦tgt v_t ∗ ℓ_s ↦src v_s` into the shared `heapbij` in exchange for the duplicable knowledge `ℓ_t ↔h ℓ_s`. `EXPLOIT-STORE`/`EXPLOIT-LOAD` transfer ownership *out* of `heapbij` into the thread, and `RELEASE-EXPLOIT` transfers it back. `SIM-STORE-SC` forces `exploit π ∅`, i.e. all exploited ownership must be returned before an atomic store — because an atomic store is the only synchronization that could let another thread avoid a race (§3.2, p. 28:15).

## Shared state / resources

Yes — shared mutable state between threads is supported, by two layered mechanisms:

1. **A heap bijection as a single global invariant** (`heapbij(H)`, §6), part of the state interpretation `S`. It holds ownership of every *escaped* location pair and maintains that they store `V`-related values. "each thread can use this ownership to justify executing a step, but it has to give it back at the end of the instruction and cannot keep the ownership between instructions" (§6). The `ℓ_t ↔h ℓ_s` assertion "represents knowledge, not exclusive ownership, and as such it is freely duplicable" (§2.2).
2. **Iris ghost state**, including authoritative ghost state `bijauth(L)` and `exploitauth(C)`, and fractional points-to. "Simuliris is based on Iris, and as such inherits its flexible notion of ghost state, which forms the foundation for all our ownership reasoning" (§1.1).

Crucially, there are **no impredicative Iris invariants** and **no user-definable invariants**: "Simuliris only requires a single global invariant (namely, that escaped pointers point to related values in the source and target heaps). With all invariants being statically determined upfront, there is—for now—no need for step-indexing in Simuliris." (§8)

There are no locks or CAS in SimuLang. Synchronization is only via SC atomic load/store, and the model is **non-blocking**: "we use a non-blocking concurrency model, which means that there are no synchronization operations that halt the execution of one thread (in a good way) until another thread makes progress" (§4.1).

## What it does NOT claim

- **It does not prove any equality or equivalence.** The top-level result is a **one-directional refinement**, `e_t ⊑ctx e_s`: every behaviour of the *target* (optimized) program is matched by some behaviour of the *source* (original) program (`ρ_t ⊑prog ρ_s ≜ ∀b_t ∈ B(ρ_t). ∃b_s ∈ B(ρ_s). b_t ⊑beh b_s`). The other direction is never claimed. The paper is explicit that nondeterminism makes the two different: "the optimized program might have a subset of the possible results of the original program" (footnote 2, §1).
- **It does not relate a parallel program to a sequential one.** Both sides of `⪯` are programs in the same concurrent language, and the simulation *requires* them to fork the same number of threads at every matching step (`|T_t| = |T_s|`). A par-vs-seq pair violates that structurally. §9 states the limit directly: "Simuliris cannot be used to show, for example, that it is sound to replace a sequential program with a more efficient, concurrent implementation which uses spinlocks to synchronize."
- **It does not expose fairness into the logic.** "This assumption is not reflected into the logic and, hence, we also have no reasoning principles in the logic which exploit the fair scheduling of the target" (§9).
- **It does not establish termination preservation for unfair infinite executions**: "we do not establish that our simulation relation is termination-preserving for the (unrealistic) case of unfair infinite executions, but we believe it is. (These two notions of correctness are incomparable.)" (§8)
- **It does not verify optimization *algorithms* or compiler passes**, only concrete transformations: "We have not verified optimization algorithms (which automatically apply program transformations based on a program analysis), as would be required in a compiler correctness proof" (§9).
- **It does not support whole-program optimizations** (e.g. removing global variables), because `⊑ctx` quantifies over all contexts (§9).
- **No weak memory**: only non-atomic and SC accesses; relaxed accesses are future work and would *invalidate* one of their verified reorderings (§8, §9).
- **No I/O** (§9).
- **No support for escaping cyclic structures** like doubly-linked lists (§9).
- Source/target memory mapping is a strict bijection — unlike CompCert memory injections it cannot map several source blocks into one target block (§8).

## Mechanized?

Yes, **in Coq**, on a variant of the Coq-based Iris framework called **Iris^light** — "Iris without the step-indexing": the BI logic and the persistence modality are kept, the later modality `⊲`, guarded recursion and impredicative invariants are dropped. "Technically, instead of defining a new logic, we found it easier to literally reuse the model of Iris itself, but fix the step-index to be 0" (§5.1). The Iris Proof Mode [Krebbers et al. 2017b, 2018] is inherited.

Scope of mechanization: "We also inherit the Iris Proof Mode, which lets us carry out interactive proofs in the Coq proof assistant for **all results presented in this paper (metatheory and examples)**. The Coq proofs are available in the supplementary material" (§1.1). The mechanization "is a shallow embedding into Coq's logic" so Coq's own types, recursive functions and induction principles are available inside Simuliris (§2.4). Artifact: Gäher et al. 2022, "Simuliris: Technical Documentation and Coq Development", https://doi.org/10.5281/zenodo.5667545.

Caveats the paper itself flags: the Fig. 12 `sim` is a *simplified* version ("glosses over two details", footnote 17); the fair-divergence proof details are omitted from the paper for space (footnote 19).

**Lean port: `NOT FOUND IN PDF`.** The string "Lean" does not appear anywhere in the paper.

## Quotable lines

- "under precondition 𝑃, the source expression 𝑒𝑠 simulates the target expression 𝑒𝑡 such that both terminate in values related by postcondition 𝛷, or both diverge" — §2, p. 28:6.
- "Our simulation relation enforces a one-to-one mapping between threads in the source and target programs: for each thread forked in the target, there must be a matching thread simulating it in the source." — §5.1 "Concurrency", p. 28:22.
- "we use a separating conjunction to concisely express that the simulation proofs of the forked-off threads, and of the original thread, are all based on disjoint resources." — §5.1 "Concurrency", p. 28:22.
- "we extend the operational semantics with a data-race detector that raises UB if two threads access the same location at the same time, where at least one access is a store and at least one access is non-atomic." — §3.1, p. 28:13.
- "Simuliris cannot be used to show, for example, that it is sound to replace a sequential program with a more efficient, concurrent implementation which uses spinlocks to synchronize." — §9, p. 28:29.
- "Simuliris only requires a single global invariant (namely, that escaped pointers point to related values in the source and target heaps). With all invariants being statically determined upfront, there is—for now—no need for step-indexing in Simuliris." — §8, p. 28:28.
- "The least fixed-point on the inside ensures that we can stutter the source, but we can only do so finitely often, which will be crucial for the adequacy proof of fair termination preservation." — §5.1, p. 28:21.

## Relevance to a parallel-equals-sequential equivalence theorem

- **This is the right judgment arity but the wrong relation and the wrong shape.** Simuliris is genuinely relational — `{P} e_t ⪯ e_s {Φ}` is about two programs, and `⊑ctx` is a statement about two whole programs' behaviour sets. But it is a **one-sided refinement** (`∀b_t ∃b_s`), not a set *equality*, and its model structurally forbids relating programs with different thread counts (`|T_t| = |T_s|` in Fig. 12). A `par p q` vs `p; q` theorem cannot be an instance of this simulation without changing that clause; §9's spinlock remark is the authors conceding exactly this class of transformation is out of scope.
- **The side condition is ownership/fractions, not Bernstein footprints.** Read/read sharing is expressed here as fractional points-to `ℓ ↦^q v` with the fractions summing to 1 across threads (`H_C`, §6), reached through `EXPLOIT-LOAD`. Nothing in the paper computes or compares read/write footprint *sets*; the separation is enforced by `∗` on resources, which is precisely the mechanism CLAUDE.md's fact 3 says is too strong for overlapping-read workloads unless fractions are threaded through.
- **Races are UB (`⊤`), and UB is *permissive*, not absorbing-and-excluding.** `b ⊑beh ⊤` means a racy source licenses *any* target behaviour — the opposite polarity from a `wrong` state that excludes racy programs from the theorem. A project whose races go to an absorbing `wrong` is making the race condition a *hypothesis discharged by the footprint analysis*; Simuliris makes it an *assumption exploited by the optimizer* (`safe(ρ_s, e_s, σ_s)` is a premise of `sim`, and `e_s ⇝ Q` mines consequences from it). The two uses of "races are UB" are not interchangeable.
- **The liveness machinery is avoidable for a terminating-programs-only setting.** The nested `νG.μL` fixed point, implicit stuttering, weak fairness and the "coinduction and three nested inductions" of Lemma 5.1 all exist to get *fair termination preservation* over possibly-diverging programs. An inductive program representation admitting only terminating programs removes that entire burden — but it also removes the part of Simuliris that was the paper's claimed novelty, so it is not a fair point of comparison on proof difficulty; the honest comparison is on the relation proved (refinement vs. outcome-set equality) and the side condition (fractional ownership vs. Bernstein footprints).
- **The non-step-indexed design is a transferable precedent.** Simuliris shows that a relational program logic over an Iris-style resource model does *not* need step-indexing when all invariants are fixed up front (§8). That is a direct argument for instantiating `Iris.BI` at a plain `State → Prop` rather than importing a step-indexed program logic.
