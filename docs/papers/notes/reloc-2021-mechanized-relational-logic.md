# ReLoC Reloaded: A Mechanized Relational Logic for Fine-Grained Concurrency and Logical Atomicity
Dan Frumin, Robbert Krebbers, Lars Birkedal · Logical Methods in Computer Science, Vol. 17 Issue 3 (pp. 9:1–9:59) 2021 (submitted Jun. 25 2020, published Jul. 21 2021; conference version: ReLoC, LICS'18 [FKB18]) · `reloc-2021-mechanized-relational-logic.pdf`

## One-line thesis
ReLoC makes the logical-refinement judgment `e ≾ e' : τ` a *first-class proposition of Iris separation logic*, so that refinements between fine-grained concurrent higher-order imperative programs can be proved with abstract type-directed structural rules and separation-logic symbolic-execution rules (and composed conditionally under invariants) instead of by unfolding into a step-indexed model.

## The setting

**Language** (Section 2, Figure 2): a typed version of **HeapLang**, Iris's default Coq language. Call-by-value λ-calculus with System-F-style types (`∀α.τ`, `∃α.τ`, `µα.τ`, `ref τ`), higher-order references, **fork-based unstructured concurrency**, and the atomic `CAS(e₁,e₂,e₃)`. From Section 2: "HeapLang is a call-by-value λ-calculus, with higher-order references, fork-based unstructured concurrency, and atomic operations for fine-grained concurrency, equipped with System-F-style types."

**Memory model / grain** (Section 2, "Operational semantics", Figure 3): three reduction relations — pure head reduction `→pure`, thread-local head reduction `→h`, and thread-pool reduction `→tp`. Sequentially consistent interleaving; no weak memory. The atomic grain is *per primitive head-step*: load, store, `CAS` each reduce in one step.

```text
Thread-pool reduction (~e, σ) →tp (~e', σ'):

        (e, σ) →h (e', σ')
  ───────────────────────────────          ──────────────────────────────────────────────────
  (e~1 K[e] e~2, σ) →tp (e~1 K[e'] e~2, σ')  (e~1 K[fork {e}] e~2, σ) →tp (e~1 K[()] e~2 e, σ)
```

"Thread-pool reduction →tp is defined on configurations ρ = (~e, σ) consisting of a state σ (a finite partial map from locations to values) and a thread-pool ~e (a list of expressions corresponding to the threads) by interleaving, i.e., by picking a thread and executing it, thread-locally, for one step." (Section 2)

**Terminating programs only?** No. The language has general recursion (`rec f x = e`) and iso-recursive types; the paper explicitly uses a diverging program (`diverge`, Section 6.4) in an equivalence. Contextual refinement is termination-sensitive only in the one-sided sense below.

**Judgment form** (Section 3.1): a **relational (binary) separation-logic judgment** — an Iris proposition `(∆ ⊨_E e₁ ≾ e₂ : τ)`, listed in the grammar of ReLoC propositions alongside `ℓ ↦ᵢ v`, `ℓ ↦ₛ v`, `⟦τ⟧_∆(v₁,v₂)`, Iris's `▷`, `□`, `|⇛`, and invariants `boxed P ^N`. It is *not* a Hoare triple and not a trace set; it is a simulation defined (Section 7.1) by an Iris weakest precondition on the left plus a **ghost thread pool** on the right.

**The target notion** (Section 2, "Contextual refinement", unnumbered display):

```text
Ξ | Γ ⊢ e₁ ≾ctx e₂ : τ  ≜  ∀τ' (C : (Ξ | Γ ⊢ τ) ⇒ (∅ | ∅ ⊢ τ')) v e~f σ.
                             (C[e₁], ∅) →*tp (v :: e~f, σ) ⟹
                             ∃v' e~f' σ'. (C[e₂], ∅) →*tp (v' :: e~f', σ').
```

"Contextual equivalence Ξ | Γ ⊢ e₁ ≃ctx e₂ : τ is defined as the symmetric closure of contextual refinement, i.e., (Ξ | Γ ⊢ e₁ ≾ctx e₂ : τ) ∧ (Ξ | Γ ⊢ e₂ ≾ctx e₁ : τ)." (Section 2)

Crucially: "Note that contextual refinement only takes termination into account, and does not require the resulting values v and v' to be equal. Demanding the equality on the resulting values would make contextual refinement too strong." (Section 2, p. 9:9)

## Main results, stated

### The judgment and its model

The refinement judgment is **defined** (Section 7.1, Figure 14) as:

```text
∆ ⊨_E e₁ ≾ e₂ : τ  ≜  ∀i, K. specCtx −∗ i ⤇ K[e₂] _E⟹*_⊤
                         wp e₁ { v₁. ∃v₂. i ⤇ K[v₂] ∗ ⟦τ⟧_∆(v₁, v₂) }
```

(`wp` = Iris weakest precondition; `i ⤇ e` = "the i-th *ghost* thread is executing e"; `specCtx` is the thread-pool invariant.) Intuition, Section 3.1: "The intuitive meaning of ∆ ⊨ e₁ ≾ e₂ : τ is that e₁ is safe, and all of its behaviors can be simulated by e₂. It is a simulation in the sense that any execution step of e₁ can be matched by a (possibly empty) sequence of execution steps of e₂." e₁ is **demonic** (the implementation), e₂ **angelic** (the specification).

### Theorem 3.1 (Soundness)
"If the refinement judgment ∅ ⊨ e₁ ≾ e₂ : τ is derivable in ReLoC, then ∅ | ∅ ⊢ e₁ ≾ctx e₂ : τ."

### Definition 4.3 (closing substitution)
"A mapping γ : Var → Val × Val is a closing substitution w.r.t. the typing environment Γ, notation ⟦Γ⟧*_∆(γ), if ∀(x, τ) ∈ Γ. ⟦τ⟧_∆(γ₁(x), γ₂(x))."

### Definition 4.4 (open refinement judgment)
```text
∆ | Γ ⊨ e₁ ≾ e₂ : τ  ≜  ∀γ. ⟦Γ⟧*_∆(γ) −∗ ∆ ⊨ γ₁(e₁) ≾ γ₂(e₂) : τ.
```

### Theorem 4.2 (Fundamental theorem for closed terms)
"If expression e is well typed, i.e., ⊢ e : τ, then e refines itself, i.e., the judgment e ≾ e : τ is derivable in ReLoC."

### Theorem 4.5 (Fundamental theorem for open terms)
"If Ξ | Γ ⊢ e : τ, then ∆ | Γ ⊨ e ≾ e : τ is derivable in ReLoC, for all ∆ which contain the variables from Ξ." Proof: "By induction on the typing derivation, using the versions of the type-directed structural rules for open terms."

### Theorem 4.6 (Soundness for open terms)
"Let Ξ be a type environment. Suppose that refinement judgment ∆ | Γ ⊨ e₁ ≾ e₂ : τ is derivable in ReLoC for all ∆ which contain the variables from Ξ. Then Ξ | Γ ⊢ e₁ ≾ctx e₂ : τ."

### Theorem 7.1 (Adequacy of ReLoC)
"If ⊢ ∆ ⊨ e₁ ≾ e₂ : τ is derivable in ReLoC, and (e₁, σ) →*tp (v₁ :: e~f1, σ₁'), then there exists v₂, e~f2, and σ₂' such that (e₂, σ) →*tp (v₂ :: e~f2, σ₂')."

### Lemma 7.2 (precongruence)
"Let C be a well-typed context C : (Ξ | Γ ⊢ τ) ⇒ (Ξ' | Γ' ⊢ τ'), then we have
(∀∆. ∆ | Γ ⊨ e₁ ≾ e₂ : τ) −∗ (∀∆'. ∆' | Γ' ⊨ C[e₁] ≾ C[e₂] : τ')
where ∆ and ∆' contain at least the type variables in Ξ and Ξ', respectively."

### Figure 6 — selected **primitive** rules of ReLoC (Section 4, p. 9:20), verbatim

```text
Value interpretation rules:

 VAL-VAR            VAL-UNIT          VAL-BOOL                VAL-INT
 ∆(α)(v₁,v₂)        v₁ = v₂ = ()      ∃b ∈ 𝔹. v₁ = v₂ = b     ∃n ∈ ℤ. v₁ = v₂ = n
 ───────────        ─────────────     ──────────────────      ─────────────────
 ⟦α⟧_∆(v₁,v₂)       ⟦unit⟧_∆(v₁,v₂)   ⟦bool⟧_∆(v₁,v₂)         ⟦int⟧_∆(v₁,v₂)

 VAL-PROD
 ∃v₁,v₂,w₁,w₂. v = (v₁,v₂) ∗ w = (w₁,w₂) ∗ ⟦τ⟧_∆(v₁,w₁) ∗ ⟦σ⟧_∆(v₂,w₂)
 ─────────────────────────────────────────────────────────────────────
                          ⟦τ × σ⟧_∆(v,w)

 VAL-ARR
 □(∀w₁ w₂. ⟦τ⟧_∆(w₁,w₂) −∗ ∆ ⊨ v₁ w₁ ≾ v₂ w₂ : σ)
 ────────────────────────────────────────────────
              ⟦τ → σ⟧_∆(v₁,v₂)

Monadic rules:

 REL-RETURN                 REL-BIND
 ⟦τ⟧_∆(v₁,v₂)                                      ∀v₁ v₂. ⟦τ⟧_∆(v₁,v₂) −∗
 ──────────────             ∆ ⊨ e₁ ≾ e₂ : τ           ∆ ⊨ K₁[v₁] ≾ K₂[v₂] : σ
 ∆ ⊨ v₁ ≾ v₂ : τ           ─────────────────────────────────────────────────
                                    ∆ ⊨ K₁[e₁] ≾ K₂[e₂] : σ

Type-directed structural rules:

 REL-FORK
   ∆ ⊨ e₁ ≾ e₂ : unit
 ──────────────────────────────
 ∆ ⊨ fork {e₁} ≾ fork {e₂} : unit

Symbolic execution rules:

 REL-LOAD-L
 ⊤⟹^E (∃v. ℓ ↦ᵢ v ∗ ▷ (ℓ ↦ᵢ v −∗ ∆ ⊨_E K[v] ≾ e₂ : τ))
 ──────────────────────────────────────────────────────
             ∆ ⊨ K[!ℓ] ≾ e₂ : τ

 REL-STORE-L
 ⊤⟹^E (ℓ ↦ᵢ − ∗ ▷ (ℓ ↦ᵢ v −∗ ∆ ⊨_E K[()] ≾ e₂ : τ))
 ──────────────────────────────────────────────────
            ∆ ⊨ K[ℓ ← v] ≾ e₂ : τ

 REL-CAS-L
 ⊤⟹^E ( ∃v'. ℓ ↦ᵢ v' ∗ ▷ (v' ≠ v₁ −∗ ▷(ℓ ↦ᵢ v' −∗ ∆ ⊨_E K[false] ≾ e₂ : τ)) ∧
                          ▷ (v' = v₁ −∗ ▷(ℓ ↦ᵢ v₂ −∗ ∆ ⊨_E K[true]  ≾ e₂ : τ)) )
 ───────────────────────────────────────────────────────────────────────────────
                     ∆ ⊨ K[CAS(ℓ, v₁, v₂)] ≾ e₂ : τ

Invariants rules (INV-ALLOC and INV-ACCESS are inherited from Iris):

 REL-UPD                     INV-ALLOC        INV-ACCESS
 ^E₁⟹^E₂ ∆ ⊨_E₂ e₁ ≾ e₂ : τ   ▷P              N ⊆ E     boxed P ^N
 ──────────────────────────   ──────────      ───────────────────────────────────────────
     ∆ ⊨_E₁ e₂ ≾ e₂ : τ        ⟹_E boxed P^N   ^E⟹^(E\N) ▷P ∗ (▷P _(E\N)⟹*_E True)
```

### Figure 4 — selected **derived** rules (Section 3, p. 9:12), verbatim

```text
Type-directed structural rules:

 REL-RETURN              REL-PAIR
 ⟦τ⟧_∆(v₁,v₂)            ∆ ⊨ e₁ ≾ e₂ : τ     ∆ ⊨ e₁' ≾ e₂' : σ
 ──────────────          ───────────────────────────────────────
 ∆ ⊨ v₁ ≾ v₂ : τ         ∆ ⊨ (e₁,e₁') ≾ (e₂,e₂') : τ × σ

 REL-PACK
 ∀v₁,v₂. persistent(R(v₁,v₂))      [α := R], ∆ ⊨ e₁ ≾ e₂ : τ
 ───────────────────────────────────────────────────────────
        ∆ ⊨ pack e₁ ≾ pack e₂ : ∃α.τ

 REL-REC
 □( ∀v₁,v₂. ⟦τ⟧_∆(v₁,v₂) −∗ (∆ ⊨ (rec f₁ x₁ = e₁) v₁ ≾ (rec f₂ x₂ = e₂) v₂ : σ) )
 ────────────────────────────────────────────────────────────────────────────────
        ∆ ⊨ (rec f₁ x₁ = e₁) ≾ (rec f₂ x₂ = e₂) : τ → σ

Symbolic execution rules:

 REL-PURE-L                                REL-PURE-R
 e₁ →pure e₁'   ▷(∆ ⊨ K[e₁'] ≾ e₂ : τ)     e₂ →pure e₂'   ∆ ⊨_E e₁ ≾ K[e₂'] : τ
 ─────────────────────────────────────     ───────────────────────────────────
      ∆ ⊨ K[e₁] ≾ e₂ : τ                        ∆ ⊨_E e₁ ≾ K[e₂] : τ

 REL-ALLOC-L'                               REL-ALLOC-R
 ∀ℓ. ℓ ↦ᵢ v −∗ ∆ ⊨ K[ℓ] ≾ e₂ : τ            ∀ℓ. ℓ ↦ₛ v −∗ ∆ ⊨_E e₁ ≾ K[ℓ] : τ
 ───────────────────────────────            ────────────────────────────────
   ∆ ⊨ K[ref(v)] ≾ e₂ : τ                     ∆ ⊨_E e₁ ≾ K[ref(v)] : τ

 REL-LOAD-L-INV
 boxed P ^N     (▷P ∗ closeInv_N(P)) −∗ ∃v. ℓ ↦ᵢ v ∗ ▷(ℓ ↦ᵢ v −∗ ∆ ⊨_(⊤\N) K[v] ≾ e₂ : τ)
 ─────────────────────────────────────────────────────────────────────────────────────────
                            ∆ ⊨ K[!ℓ] ≾ e₂ : τ

 REL-LOAD-R                                   REL-STORE-R
 ℓ ↦ₛ v    ℓ ↦ₛ v −∗ ∆ ⊨_E e₁ ≾ K[v] : τ      ℓ ↦ₛ −   ℓ ↦ₛ v −∗ ∆ ⊨_E e₁ ≾ K[()] : τ
 ────────────────────────────────────────     ───────────────────────────────────────
        ∆ ⊨_E e₁ ≾ K[!ℓ] : τ                        ∆ ⊨_E e₁ ≾ K[ℓ ← v] : τ

 REL-CAS-L-INV
             (▷P ∗ closeInv_N(P)) −∗
 boxed P^N    ∃v. ℓ ↦ᵢ v ∗ ▷ ( (v = v₁ ∗ ℓ ↦ᵢ v₂ −∗ ∆ ⊨_(⊤\N) K[true] ≾ e₂ : τ) ∧
                               (v ≠ v₁ ∗ ℓ ↦ᵢ v  −∗ ∆ ⊨_(⊤\N) K[false] ≾ e₂ : τ) )
 ─────────────────────────────────────────────────────────────────────────────────
                   ∆ ⊨ K[CAS(ℓ,v₁,v₂)] ≾ e₂ : τ

Invariants rules:

 REL-INV-ALLOC                              REL-INV-RESTORE
 ▷P     boxed P^N −∗ ∆ ⊨ e₁ ≾ e₂ : τ        closeInv_N(P)   ▷P   ∆ ⊨_E e₁ ≾ e₂ : τ
 ───────────────────────────────────        ──────────────────────────────────────
        ∆ ⊨ e₁ ≾ e₂ : τ                            ∆ ⊨_(E\N) e₁ ≾ e₂ : τ
```

### Ghost thread pool rules (Figure 15, Section 7.1), verbatim

```text
 STEP-PURE                              STEP-ALLOC
 specCtx   i ⤇ e   e →pure e'           specCtx    i ⤇ K[ref(v)]
 ───────────────────────────            ─────────────────────────────────
      ⟹_E i ⤇ e'                        ⟹_E ∃ℓ. i ⤇ K[ℓ] ∗ ℓ ↦ₛ v

 STEP-STORE                             STEP-FORK
 specCtx  i ⤇ K[ℓ ← w]   ℓ ↦ₛ v         specCtx    i ⤇ K[fork {e}]
 ───────────────────────────────        ─────────────────────────────────
  ⟹_E i ⤇ K[()] ∗ ℓ ↦ₛ w                ⟹_E ∃j. i ⤇ K[()] ∗ j ⤇ e
```

### Lifting rules (Section 7.4), verbatim

```text
 REL-WP-L                                REL-WP-ATOMIC-L
 wp_⊤ e₁ { v₁. K[v₁] ≾ e₂ : τ }          ⊤⟹^E wp_E e₁ { v₁. ⊨_E K[v₁] ≾ e₂ : τ }   atomic(e₁)
 ──────────────────────────────          ───────────────────────────────────────────────────
      K[e₁] ≾ e₂ : τ                                   K[e₁] ≾ e₂ : τ

 REL-STEP-R
 ∀j, K'. specCtx ∗ j ⤇ K'[K[e₂]] ⟹*_E ∃v₂. j ⤇ K'[K[v₂]] ∗ ⊨_E e₁ ≾ K[v₂] : τ
 ──────────────────────────────────────────────────────────────────────────────
                       ⊨_E e₁ ≾ K[e₂] : τ
```

### Lock specifications

Right-hand side (angelic) spec, Figure 5, Section 3.4 — verbatim:

```text
 NEWLOCK-R
 ∀lk. isLockₛ(lk, false) −∗ ∆ ⊨_E e₁ ≾ K[lk] : τ
 ───────────────────────────────────────────────
     ∆ ⊨_E e₁ ≾ K[newlock ()] : τ

 ACQUIRE-R
 isLockₛ(lk, false)    isLockₛ(lk, true) −∗ ∆ ⊨_E e₁ ≾ K[()] : τ
 ───────────────────────────────────────────────────────────────
             ∆ ⊨_E e₁ ≾ K[acquire lk] : τ

 RELEASE-R
 isLockₛ(lk, b)    isLockₛ(lk, false) −∗ ∆ ⊨_E e₁ ≾ K[()] : τ
 ────────────────────────────────────────────────────────────
             ∆ ⊨_E e₁ ≾ K[release lk] : τ
```

Left-hand side (demonic) spec, Figure 7, Section 5.1.2 — verbatim:

```text
 NEWLOCK-L                                            IS-LOCK-PERS
 R    ∀lk, γ. isLockᵢ(γ, lk, R) −∗ K[lk] ≾ e₂ : τ     isLockᵢ(γ, lk, R)
 ────────────────────────────────────────────────     ──────────────────────
          K[newlock ()] ≾ e₂ : τ                      □ isLockᵢ(γ, lk, R)

 ACQUIRE-L
 isLockᵢ(γ, lk, R)    (lockedᵢ(γ) −∗ R −∗ K[()] ≾ e₂ : τ)
 ────────────────────────────────────────────────────────
             K[acquire lk] ≾ e₂ : τ

 RELEASE-L
 isLockᵢ(γ, lk, R)    lockedᵢ(γ)    R    K[()] ≾ e₂ : τ
 ──────────────────────────────────────────────────────
             K[release lk] ≾ e₂ : τ
```

### Logically atomic relational specifications

General TaDA-style format (Section 5.3.3), verbatim:

```text
       R    ⊤⟹^E ∃x. P(x) ∗ ( P(x) _E⟹*_⊤ True  ∧
                              ∀v. Q(x,v) ∗ R −∗ ⊨_E K[v] ≾ e₂ : τ )
       ─────────────────────────────────────────────────────────────
                         K[e₁] ≾ e₂ : τ
```

Instance for the fine-grained counter, INC-I-L-TADA (Section 5.3.1):

```text
 ⊤⟹^E ∃n. c ↦ᵢ n ∗ ( c ↦ᵢ n _E⟹*_⊤ True  ∧
                      c ↦ᵢ (n+1) −∗ ⊨_E K[n] ≾ e : τ )
 ─────────────────────────────────────────────────────
                K[incᵢ c] ≾ e : τ
```

Note the **intuitionistic conjunction ∧ rather than ∗**: "we know that the computation can either succeed or be restarted—but not both. We have to accommodate for both situations, just not at the same time." (Section 5.3.1)

HOCAP-style non-linearizable spec CNT-WK-INCR-L (Section 5.4.4), verbatim:

```text
 CNT-WK-INCR-L
                            E ∩ N↑ = ∅        isCnt_γ(c, N)
 ∀n. cntAuth_γ(n) ⟹*_(⊤\N) cntAuth_γ(n) ∗ (∀m. cntAuth_γ(m) _(⊤\N)⟹*_(⊤\N\E)
                                               cntAuth_γ(n+1) ∗ ⊨_(⊤\E) K[()] ≾ e₂ : τ)
 ───────────────────────────────────────────────────────────────────────────────────────
                            K[wkincr c] ≾ e₂ : τ
```

### Prophecy variable rules (Figure 13, Section 6.2), verbatim

```text
 REL-NEWPROPH-L                                 REL-NEWPROPH-R
 ∀~v p. proph(p, ~v) −∗ ∆ ⊨ K[p] ≾ e₂ : τ       ∀p. (∆ ⊨_E e₁ ≾ K[p] : τ)
 ────────────────────────────────────────       ──────────────────────────────
      ∆ ⊨ K[newproph] ≾ e₂ : τ                  ∆ ⊨_E e₁ ≾ K[newproph] : τ

 REL-RESOLVEPROPH-L
 ⊤⟹^E ∃~v. proph(p, ~v) ∗ ∀w. ((~v = w :: ~w) ∗ proph(p, ~w) −∗ ∆ ⊨_E K[()] ≾ e₂ : τ)
 ────────────────────────────────────────────────────────────────────────────────────
                    ∆ ⊨ K[resolve p to w] ≾ e₂ : τ

 REL-RESOLVEPROPH-R
 ∆ ⊨_E e₁ ≾ K[()] : τ
 ───────────────────────────────────
 ∆ ⊨_E e₁ ≾ K[resolve p to w] : τ
```

### Case-study propositions (Section 5.5, ticket lock ≾ spin lock)
- **Proposition 5.1.** `[α := lockInt] ⊨ newlockTL ≾ newlock : unit → α.`
- **Lemma 5.2.** `ticket_γ(m) ⊢ [α := lockInt] ⊨ wait loop m l_o ≾ acquire lk : unit`, "provided we have `boxed lockInv_γ(γ_o, γ_n, lk) ^(N.inv)`."
- **Proposition 5.3.** `[α := lockInt] ⊨ acquireTL ≾ acquire : α → unit.`
- **Proposition 5.4.** `[α := lockInt] ⊨ releaseTL ≾ release : α → unit.`

### Equational laws proved (Section 6.4), verbatim

```text
 e₁ ≃ctx e₁ ⊕ e₁ : τ        e₁ ⊕ e₂ ≃ctx e₂ ⊕ e₁ : τ      e₁ ≃ctx e₁ ⊕ diverge : τ

 e₁ ⊕ (e₂ ⊕ e₃) ≃ctx (e₁ ⊕ e₂) ⊕ e₃ : τ     (e₁ ⊕ e₂); e₃ ≃ctx (e₁; e₃) ⊕ (e₂; e₃) : τ

 e₁; (e₂ ⊕ e₃) ≃ctx (e₁; e₂) ⊕ (e₁; e₃) : τ        (needs prophecy variables)
```

with the symbolic-execution rules for non-deterministic choice `⊕` (derived from `rand`):

```text
 REL-OR-L
 (∆ ⊨ K[e₁] ≾ t : τ) ∧ (∆ ⊨ K[e₂] ≾ t : τ)
 ──────────────────────────────────────────
       ∆ ⊨ K[e₁ ⊕ e₂] ≾ t : τ

 REL-OR-R-1                            REL-OR-R-2
 ∆ ⊨_E t ≾ K[e₁] : τ                   ∆ ⊨_E t ≾ K[e₂] : τ
 ───────────────────────────           ───────────────────────────
 ∆ ⊨_E t ≾ K[e₁ ⊕ e₂] : τ              ∆ ⊨_E t ≾ K[e₁ ⊕ e₂] : τ
```

## Proof technique

Soundness (Theorem 4.6) is proved from two lemmas (Section 7.5):

1. **Lemma 7.2 (precongruence)** — "proved by induction on C making using of ReLoC's type-directed structural rules (Section 4.4)". The induction is over the **shape of the typed program context C**.
2. **Theorem 7.1 (adequacy)** — proved by (i) allocating the thread-pool invariant `specCtx` and `0 ⤇ e₂`; (ii) unfolding the judgment to obtain `wp e₁ {v₁. ∃v₂. 0 ⤇ v₂ ∗ ⟦τ⟧_∆(v₁,v₂)}`; (iii) "by opening specCtx and using adequacy of Iris's weakest preconditions, we obtain (e₂, σ) →*tp (v₂ :: e~f2, σ₂')."

The thread-pool invariant is the key device:

```text
specCtx ≜ ∃~e₀, σ₀. boxed ( ∃~e, σ. spec_inv(~e, σ) ∗ (~e₀, σ₀) →*tp (~e, σ) ) ^(N_ReLoC)
```

"The invariant asserts that given an initial configuration (~e₀, σ₀) for the right-hand side (which we set to be (e₂, σ) when allocating the invariant), the configuration (~e, σ) can be reached via the reduction (~e₀, σ₀) →*tp (~e, σ)." (Section 7.5)

**What provides the induction / well-foundedness:** step-indexing, internalized as Iris's **later modality ▷**, not an explicit fuel counter. Section 1: "The technique of step-indexing [AAV02, Ahm04] has been used to stratify the definitions using recursion over a natural number, called the step-index, which corresponds to the number of computation steps performed by the program… Dreyer et al. thus proposed the 'logical approach' … to hide step-indices by abstracting and internalizing them in a modal logic using the later modality (▷)." Recursive loops are handled by **Löb induction** (Section 3.4.3; used in Lemma 5.2 and in the proof of INC-I-L-HOCAP). Recursive types use Iris's guarded fixed point `µΦ. …` requiring the recursive occurrence under `▷` (Section 7.2).

**Fundamental theorem** (Theorem 4.5) is by induction on the typing derivation.

**Derived-rule technique** (Section 4.3): all type-directed structural rules are derived from REL-RETURN and REL-BIND, "with the exception of rel-fork, which is the sole primitive type-directed structural rule." Example given as Lemma 4.1 (the π₁ rule), with a four-step proof using REL-BIND, VAL-PROD, REL-PURE-L/R, REL-RETURN.

## Side condition on parallel composition

**There is no Bernstein-style or disjointness-style side condition anywhere in the paper.** The language has no `par` primitive at all — concurrency is `fork {e}` (Figure 2), and the only structural rule for it is, verbatim (Figure 6, Section 4):

```text
 REL-FORK
   ∆ ⊨ e₁ ≾ e₂ : unit
 ──────────────────────────────
 ∆ ⊨ fork {e₁} ≾ fork {e₂} : unit
```

That is: the *entire* requirement for relating two forked threads is that their bodies are related at `unit`. There is no footprint, no separating conjunction between the two threads' resources, no read/write partition. Threads are allowed to share arbitrary mutable state.

Read/read sharing: **unrestricted**, and more — read/write and write/write sharing between threads are also permitted. What constrains concurrent access is not disjointness but **atomicity + invariants**: an invariant may be opened only across a single physically atomic left-hand step. Quoted (Section 3.4.2, "Accessing invariants"): "once a proposition P has been turned into an invariant, one is only allowed to access P during a single atomic execution step on the left-hand side. This restriction is crucial as the scheduling of threads on the left-hand side is demonic." Section 4.1 gives the concrete counterexample showing why multi-step access is unsound, using the context `let c = ref(0) in let f = [•] in fork {f c}; f c`.

Asymmetry: the right-hand (angelic) side may take **multiple** steps with an invariant open — "Scheduling on the right-hand side, however, is angelic… As a consequence, ReLoC allows us to execute multiple steps on the right-hand side while accessing an invariant." (Section 3.4.2)

Fractional permissions: **partially present but not a parallel-composition device.** The paper uses a fractional abstract predicate `cnt_γ(q, n)` in the HOCAP counter spec — "It is similar to the fractional heap points-to connective from separation logic—it associates a value (a natural number n) to the counter, and can be split and combined according to the fractional component q (cnt-agree', cnt-combine)" (Section 5.4.1) — and the Coq snippet in Section 8.2 shows `l ↦ₛ{q} v`. These are used for ghost-state bookkeeping in module specs, not as a side condition on forking.

Ownership transfer: yes, via invariants and the lock predicate `isLockᵢ(γ, lk, R)` — NEWLOCK-L consumes `R`, ACQUIRE-L hands `R` to the acquiring thread, RELEASE-L gives it back (Figure 7).

## Shared state / resources

Fully supported, by **Iris invariants + user-defined (higher-order) ghost state + prophecy variables**, with Iris's mask discipline for reentrancy.

- **Invariant allocation and access** (Figure 6): INV-ALLOC and INV-ACCESS as quoted above; REL-UPD lets an update modality around a judgment be eliminated. A strong variant for non-well-bracketed access is given in Section 5.4.3:

```text
 INV-ACCESS-STRONG
      N↑ ⊆ E
 boxed P ^N   _E⟹*_(E\N) ▷P ∗ (∀E'. ▷P _E'⟹*_(E'∪N) True)
```

- **Running example invariant** (Section 1 and 3.4.2): `I_cnt ≜ ∃n ∈ ℕ. cᵢ ↦ᵢ n ∗ cₛ ↦ₛ n ∗ isLockₛ(lk, false)`.
- **Two heaps.** "Since ReLoC is relational, these come in two forms: ℓ ↦ᵢ v and ℓ ↦ₛ v, which signify ownership of a location ℓ with value v on the implementation and specification side, respectively." (Section 3.1) The *specification* heap `↦ₛ` is itself ghost state, tied to the ghost thread pool by `specCtx`.
- **Reference type interpretation** is itself an invariant (Figure 14):
  `⟦ref τ⟧_∆(v₁,v₂) ≜ ∃ℓ₁,ℓ₂ ∈ Loc. v₁ = ℓ₁ ∗ v₂ = ℓ₂ ∗ boxed(∃w₁,w₂. ℓ₁ ↦ᵢ w₁ ∗ ℓ₂ ↦ₛ w₂ ∗ ⟦τ⟧_∆(w₁,w₂)) ^(ℓ₁,ℓ₂)`
- **Ghost theories** used in case studies: the ticket ghost theory (Figure 10: NEWISSUEDTICKETS, ISSUENEWTICKET, TICKET-NONDUP), and the counter ghost theory `cnt_γ(q,n)` / `cntAuth_γ(n)`.
- **Prophecy variables** (Section 6) for speculative/future-dependent reasoning; they appear as *instrumented instructions* `newproph` and `resolve p to v` in the source program, erased by a two-step argument (Section 6.2): prove `e₁ ≾ ê₁` and `ê₁ ≾ e₂`, then compose by transitivity of contextual refinement.

## What it does NOT claim

- **It does not prove any equality or equivalence between a parallel program and a sequential one.** The paper never relates `par p q` (or `fork e₁; e₂`) to `e₁; e₂`. There is no sequentialization theorem.
- **It does not prove outcome-set equality.** Contextual refinement, as defined in Section 2, is purely about *termination preservation under contexts*: `(C[e₁],∅) →*tp (v :: e~f, σ)` implies some `(C[e₂],∅) →*tp (v' :: e~f', σ')`. It explicitly does **not** require `v = v'` and says nothing about the final state σ. "Note that contextual refinement only takes termination into account, and does not require the resulting values v and v' to be equal." (Section 2, p. 9:9) The alternative formulation (Pitts' true-adequacy variant) fixes the observed value to `true` at type `bool`, but still says nothing about heaps.
- **The judgment is a one-directional simulation.** Equivalence is only obtained by proving *both* directions separately (as done for `bit_bool ≃ctx bit_nat`, Section 3.3, and for the coin module, Section 6.1).
- **It is not complete.** Section 10.2: "The rules of ReLoC are sound, but not complete. In particular, there are some examples that cannot be verified in ReLoC completely." Specifically, data structures with **external** linearization points (helping, work-stealing) require the "escape hatch" — unfolding the judgment and reasoning directly in the Iris model.
- **It does not relate a concurrent program to a sequential program.** The closest case studies compare a *fine-grained concurrent* implementation against a *coarse-grained concurrent* specification. The coarse-grained spec is still a concurrent program; it is just instrumented with a lock. From Section 1: "Due to the instrumentation of the coarse-grained version with locks, this refinement expresses that each operation of the fine-grained version takes place instantaneously." Examples: `counterᵢ ≾ctx counterₛ`, ticket lock ≾ spin lock (Section 5.5), Treiber stack, Michael-Scott queue, elimination-backoff stack (Section 10.1 / appendix).
- **The one bullet closest to par≡seq is stated but not developed in the paper.** Section 10.1 lists among the mechanized Coq case studies: "Algebraic laws for the parallel composition operation and its interaction with non-deterministic choice and sequential composition, inspired by the work on Concurrent Kleene Algebra [HMSW11]". **The statements of these laws are NOT GIVEN IN THE PDF** — no rule, equation or theorem for them appears anywhere in the body; only the Coq sources are cited. The only algebraic laws actually written out (Section 6.4) involve `⊕` and `;`, not `∥`.
- It does not address weak memory, data-race freedom as a property, or crash/termination-sensitive refinement (Section 10.3 lists the latter two as future work, citing [TJH17, CTKZ19]).
- It does not provide a decision procedure or automation beyond interactive tactics.

## Mechanized?

**Yes — Coq, on top of Iris**, as a shallow embedding, using the Iris Proof Mode (IPM) / MoSeL for interactive separation-logic tactics. The language HeapLang is a deep embedding.

Section 8.4 gives the breakdown verbatim: "The Coq mechanization contains around 10300 lines of code, of which approximately (1) 1315 lines for mechanization of the model of ReLoC (Section 7), including the adequacy theorem (Theorem 7.1), and the primitive and derived rules (Section 4); (2) 1200 lines for the tactics (Section 8.3); (3) 1450 lines for the mechanization of the type system (Section 2), and the soundness theorem for open term (Theorem 4.6); (4) 6050 lines for the examples and case studies (including the case studies we describe in the upcoming Sections 10.1 and 10.2); (5) and 140 lines for tests (mainly regression tests for the tactics)."

Everything in the paper is mechanized: "In addition to mechanizing all meta-theoretic results of ReLoC, like its soundness theorem, we have implemented new tactics that support mechanized interactive reasoning about program refinements in ReLoC in a practical and modular way." (Section 1). The mechanization is cited as [FKB21a].

Coq statements of soundness (Section 8.2):
```text
Lemma refines_sound Σ `{relocPreG Σ} e1 e2 τ :
  ...
Lemma refines_sound_open Σ `{relocPreG Σ} Γ e1 e2 τ :
  ...
Theorem bit_ctx_refinement : ∅ ⊨ bit_bool ≾ctx bit_nat : bitτ
Proof. auto using (refines_sound relocΣ), bit_refinement. Qed.
```
Trusted base: "the only parts of the trusted code base of our development are the notions that are involved in the definition of contextual refinement, i.e., the operational semantics and the typing of contexts." (Section 8.2)

Tactics named in Section 8.3: `rel_load_r`, `rel_pures_r`, `rel_values`, plus `refines_exists`, `refines_pair`, `refines_load_r`, and the IPM tactics `iIntros`, `iApply`.

**Lean port:** `NOT FOUND IN PDF` — the word "Lean" does not occur in the paper.

## Quotable lines

- "The intuitive meaning of ∆ ⊨ e₁ ≾ e₂ : τ is that e₁ is safe, and all of its behaviors can be simulated by e₂. It is a simulation in the sense that any execution step of e₁ can be matched by a (possibly empty) sequence of execution steps of e₂." — Section 3.1, p. 9:10

- "Note that contextual refinement only takes termination into account, and does not require the resulting values v and v' to be equal. Demanding the equality on the resulting values would make contextual refinement too strong." — Section 2, p. 9:9

- "we think of e₁ as being demonic and e₂ as being angelic. That is, the non-deterministic choices of e₁ (e.g., scheduling of forked-off threads) are selected by an external demon; whereas for the non-deterministic choices of e₂, an angle [sic] blesses the person proving the refinement with an ability to select a choice themselves." — Section 3.1, p. 9:10

- "once a proposition P has been turned into an invariant, one is only allowed to access P during a single atomic execution step on the left-hand side. This restriction is crucial as the scheduling of threads on the left-hand side is demonic." — Section 3.4.2, p. 9:16

- "In the context of concurrency, contextual refinement is often used to specify a fine-grained concurrent program module by stating that it contextually refines a coarse-grained version." — Section 1, p. 9:2

- "The rules of ReLoC are sound, but not complete. In particular, there are some examples that cannot be verified in ReLoC completely." — Section 10.2, p. 9:54

- "These rules are used to derive all type-directed structural rules of ReLoC, with the exception of rel-fork, which is the sole primitive type-directed structural rule." — Section 4.3, p. 9:23

## Relevance to a parallel-equals-sequential equivalence theorem

- ReLoC's judgment is genuinely relational and two-sided (`∆ ⊨ e₁ ≾ e₂ : τ`), so it is the right *shape* of judgment for a par≡seq statement; but its observable is only "the left terminating at a value implies the right can terminate at some value", with no constraint tying result values or final heaps together (Section 2). A project claiming "the parallel and the sequential program reach exactly the same set of (result, final-state) pairs" is asserting something ReLoC's `≾ctx` deliberately does not assert in either direction; even `≃ctx` (both directions) only equates observable termination under contexts.
- The composition side condition is completely different in kind. ReLoC's REL-FORK has **no** resource-disjointness premise; concurrent interference is controlled by requiring that an invariant be opened only across one physically atomic left-hand step (Section 3.4.2, 4.1). A Bernstein-independence-based theorem instead puts the burden entirely in a syntactic/semantic footprint condition and needs no invariants, no ghost state, no masks and no step-indexing.
- The infrastructure cost is the sharpest contrast: ReLoC needs Iris's step-indexing via `▷`, guarded fixed points, higher-order ghost state, invariant masks, a ghost thread pool (`i ⤇ e`, `↦ₛ`, `specCtx`), Löb induction, and for some examples prophecy variables (Section 6) — ~10 300 lines of Coq (Section 8.4). It also remains incomplete (Section 10.2).
- ReLoC's `fork` is unstructured (Figure 2/3), so the "sequential counterpart" of a program is not even expressible as a syntactic transformation in the language; the only sequentialization device in the paper is instrumenting the specification side with a **lock** (`counterₛ`, Figure 1), which keeps the spec concurrent. A structured N-ary `par` with a genuine `seqPair` counterpart is outside the paper's vocabulary, and the only mention of parallel-composition laws (Section 10.1) is an unstated Coq-only bullet.
