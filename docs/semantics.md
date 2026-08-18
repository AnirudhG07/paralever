# Semantics: step relation, races, and the shape of the theorem

Rationale for `Paralever/Core/{State,Semantics}.lean`.

## State is total

`State := Loc → Val`. No `Option`, so no failure threading through every lemma. Out-of-bounds is
not a semantic error; it becomes a well-formedness predicate on programs if we ever need it.

## Nondeterministic step, not a schedule datatype

```lean
step : ParM α → State → List (Conf α)
```

A computable list of successors. An explicit `Schedule` type was rejected: it would have to address
threads inside an arbitrarily nested `par` tree, and it fakes determinization of something that is
genuinely nondeterministic. Returning the successor list keeps the semantics honest *and*
computable, so `Plausible` can enumerate interleavings for property tests.

`Reaches` is the reflexive-transitive closure.

## Races step to an absorbing `wrong`

`Conf α` is `run (p : ParM α) (σ : State)` or `wrong`, with `wrong` terminal.

At a `par p q k` node we compute each branch's *immediate next actions* and abort if they conflict:

```lean
nextAccs : ParM α → List Label     -- head actions; recurses through nested par
racing   : List Label → List Label → Bool   -- same loc, at least one write
```

The freer representation is what makes this cheap: the head of the tree *is* the next action, so
`nextAccs` is four lines and needs no evaluation contexts. Nested races are caught when the
recursion reaches the inner `par` node.

Conflict = same location, at least one write. This is Bernstein's criterion at the level of a
single step, and it is why shared reads never abort.

**ref:** Vafeiadis, *CSL and Operational Semantics* (MFPS 2011) defines abort this way — the
`accesses`/`writes` of the next step of each thread. Reynolds, *Toward a Grainless Semantics*
(FSTTCS 2004) is why an absorbing `wrong` makes the choice of atomic grain irrelevant.

## The theorem splits in two

Because races are detected *semantically*, the metatheorem's hypothesis is semantic too:

```lean
-- Theory/Sequentialize.lean — the metatheorem
theorem par_eq_seq (hsafe : ¬ Reaches (.run (parPair p q) σ) .wrong) :
    Reaches (.run (parPair p q) σ) (.run (.pure r) σ')
  ↔ Reaches (.run (seqPair p q) σ) (.run (.pure r) σ')

-- Core/Access.lean, Logic/ — the discharge path
theorem indep_safe (h : Indep (accesses p σ) (accesses q σ)) :
    ¬ Reaches (.run (parPair p q) σ) .wrong
```

This mirrors the literature exactly: Brookes' soundness theorem is *provable ⇒ race-free*, and his
parallel decomposition lemma gives *race-free ⇒ sequentializable*. Bernstein/`Indep` is then one
sufficient condition for safety, not part of the metatheorem — so Tier-1 footprints, the Tier-2
ownership logic, and any later criterion all target the same `hsafe` obligation.

Since the sequential side is deterministic, **parallel determinism is a corollary**, not a separate
proof.

## The circularity to watch

`accesses p σ` is what `p` touches running *alone*. Inside `par p q`, `q`'s writes could change what
`p` reads, hence its control flow, hence its accesses — so the hypothesis appears to be defined in
terms of something the conclusion invalidates.

The resolution *is* the decomposition lemma: by induction on the interleaved run, under safety the
heap restricted to `p`'s footprint always agrees with what `p`'s solo run would see, so `p` behaves
identically. This is Brookes' `s₁ ∗ s₂` splitting (CONCUR'04 §5–7), and it is where the real work
of the project lives. Everything else in the core is bookkeeping.

## Anti-vacuity witness

`p = wr l 1`, `q = wr l 2`. Their next actions are `write l` and `write l` — conflicting — so
`parPair p q` steps to `wrong` and `hsafe` fails. Without the race check it would reach both
`l = 1` and `l = 2` while the sequential program reaches only `l = 2`, so the conclusion is false.
Either way the hypothesis is demonstrably load-bearing. Keep this as a test.
