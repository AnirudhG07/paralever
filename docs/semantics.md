# Semantics: step relation, races, and the shape of the theorem

Rationale for `Paralever/Core/{State,Semantics}.lean`.

## State is total

`State := Loc → Val`. No `Option`, so no failure threading through every lemma. Out-of-bounds is
not a semantic error; it becomes a well-formedness predicate on programs if we ever need it.

### What that means for pointers

There is no allocation and no `free`, and `Loc := Nat`, so **there are no dangling pointers** —
nothing to dangle. `ArrRef.loc a i = a.base + i` puts no bound on `i`, so `A.loc 1000` on a
ten-element `A` is an ordinary location with an ordinary value. "In bounds" is `ArrRef.InRange`, a
`Prop` used in proofs, never a check that runs. An index out of range is therefore an out-of-bounds
*intention*, not an out-of-bounds *access*: no undefined behaviour, no garbage, and the heap does
not change size, because it has none.

The consequence is worth stating plainly: `par_seq_eq` is **equivalence, not memory safety**. A
stray write is committed identically by the parallel and the sequential program, so the theorem goes
on holding over a program that is wrong. `Examples/Pointers.lean` `Stray` is exactly that case —
`wfB = true`, `ParSeqEq` by `decide`, and a `7` written to a cell the thread does not own.

What *is* caught is the stray pointer that collides with another thread, which is the only kind that
can break `par = seq`. Then it is an ordinary race: Bernstein fails on the literal address,
`raceSites` names it, and the search returns a schedule reaching `wrong`
(`Examples/Pointers.lean`: `Aliasing`, `Underflow`, `ReadWrite`). Two sharp edges that file pins
down:

* `Loc := Nat`, so `A.base - 1` truncates to `0` and a pointer "before" an array based at zero
  **is** its first element. The one case C would call undefined behaviour is here a silent alias,
  silent only until a second thread touches that element.
* Addresses in `Lang` are metalevel — `store : Loc → AExp` takes a Lean `Nat` for the address and an
  expression only for the value. There is no runtime pointer arithmetic, which is why `footprintOf`
  is exact and `wfB` is `decide`-able, and why a deliberately stray pointer cannot be hidden from
  the analysis: by the time there is a program, there are no addresses left to compute.

Data-dependent addressing (`A[B[i]]`) is what would change this, because the address becomes an
`AExp` and `footprintOf` stops being syntactic. Out of scope for now; the fallbacks are a bound
hypothesis or a `FootprintWithin` over-approximation (`Theory/Intervals.lean`).

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

`Examples/Racy.lean` refutes `ParSeqEq` outright, so the hypothesis is load-bearing against the
*conclusion* and not merely unprovable. Two cases:

`DetectedRace` — `p = wr l 1`, `q = wr l 2`. Their next actions are `write l` and `write l`, so
`parPair p q` steps to `wrong`, which is absorbing: the parallel program reaches no `.pure` leaf at
all, while the sequential one reaches its canonical outcome (`not_parSeqEq`).

`OrderDependent` — the sharper case, where both sides terminate normally and still disagree.
`observer = write own 7; read shared` against `mutator = write shared 99`. The first step is
race-free (`own ≠ shared`), so one schedule runs `mutator` to completion and `observer` then reads
`99`; the sequential order reads the original `1`. `par_reaches` exhibits the parallel outcome,
`seq_not_reaches` rules it out sequentially via `wellFormed_canonical`, and `par_reaches_wrong`
shows the *other* schedule aborts — the race is real, just not visible at the first step.
