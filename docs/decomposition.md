# The decomposition proof

Rationale for `Paralever/Theory/WellFormedCanonical.lean` (the theorem itself and its
dedicated supporting lemmas) and `Paralever/Theory/Decomposition.lean` (general `runSeq`/
`WellFormed`-through-`bind` facts reused elsewhere). `WellFormed` itself lives in
`Core/Access.lean`.

## Top-level `Indep` is not enough — `WellFormed` is recursive

Counterexample: `p := par (wr 5 1) (wr 5 2) pure`, `q := wr 100 0`. `p` races with *itself* on
location 5, but `accesses p σ = {writes:[5]}` and `accesses q σ = {writes:[100]}` are `Indep` —
disjoint at the outer level. Yet `par p q k` reaches `wrong`, because `step` recurses into `p`'s
own internal `par` node and finds the conflict there. `Indep (accesses p σ) (accesses q σ)` says
nothing about what is nested inside `p` or `q`.

So the real per-program obligation is recursive: independence checked at *every* `par` node,
against the state that node actually sees along the canonical run.

```lean
def WellFormed : ParM τ → State → Prop
  | .pure _,      _ => True
  | .read l k,    σ => WellFormed (k (σ l)) σ
  | .write l v k, σ => WellFormed (k ()) (σ.update l v)
  | .par p q k,   σ =>
      let (a, σ₁) := runSeq p σ
      let (b, σ₂) := runSeq q σ₁
      Indep (accesses p σ) (accesses q σ₁) ∧ WellFormed p σ ∧ WellFormed q σ₁ ∧
      WellFormed (k (a, b)) σ₂
```

Same recursion shape as `accesses`/`runSeq`, so no new induction principle is needed. This — not
the flat top-level `Indep` — is what `par_eq_seq` should assume, and what Tier-1's `decide`
obligation should actually check.

## Proof architecture — status

**All four pieces are fully proved** (checked via `#print axioms`: `propext`, `Classical.choice`,
`Quot.sound` — no `sorryAx`; `Classical.choice` is pre-existing, inherited transitively from
`grind`-based lemmas elsewhere in the codebase, not introduced by this proof). Zero `sorry` in the
project.

**1. `Reaches.terminal` / `Reaches.single_step`** (`Core/Semantics.lean`) — ✅ proved. Generic
facts about `Reaches` on configurations with zero or one successor. Needed because `read`/`write`
steps are deterministic (exactly one successor each); only `par` genuinely branches.

**2. Locality** (`Theory/WellFormedCanonical.lean`) — ✅ proved, in three layers:
- `runSeq_frame`: locations `p` doesn't write are untouched by its canonical run.
- `FDisjoint`/`.left`/`.right`: disjointness stated as *reads and writes separately*
  (`Disjoint F f.reads ∧ Disjoint F f.writes`) rather than one `Disjoint F (reads++writes)` list —
  the combined form doesn't project cleanly through `Footprint.union`'s nesting (reads-of-everything
  and writes-of-everything are interleaved separately, not grouped per branch), and every attempt
  to case-split it manually turned into fragile `Or`-shuffling. The conjunction form projects
  through `union` in one line each direction.
- `accesses_runSeq_locality`: if `σ`, `σ'` agree outside a footprint-disjoint set `F`, `p`'s
  canonical run agrees on `σ`, `σ'` in value, footprint, and everywhere outside `F`.
- `accesses_runSeq_isolated`: **the payoff.** Under `Indep`, `q`'s canonical run from the post-`p`
  state `σ₁` (the convention `accesses` uses, `docs/access.md`) provably agrees with its run from
  the *original* `σ` — `Indep`'s write-disjointness components are exactly the `FDisjoint`
  hypothesis at `F := p`'s writes, and `runSeq_frame` is exactly the agreement hypothesis needed.
  What `docs/access.md` called an asymmetry that "vanishes under `Indep`" is now a theorem, not a
  hand-wave.

**3. `wellFormed_canonical`** (the crux — ✅ fully proved) — under `WellFormed p σ`, the *only*
configuration `p` reaches via the real nondeterministic `step`/`Reaches` is the canonical
`runSeq p σ`:

```lean
theorem wellFormed_canonical (p : ParM τ) (σ : State) (h : WellFormed p σ) (r : τ) (σ' : State) :
    Reaches (.run p σ) (.run (.pure r) σ') ↔ (r, σ') = runSeq p σ
```

`pure`/`read`/`write` are immediate from (1) plus the definitions. `par` — the genuinely hard case,
Brookes' Parallel Decomposition Lemma mechanized for this operational semantics — is now also
proved, via the **operational** half described below: relating the real `step`/`Reaches`
interleaving to the canonical value, not `runSeq` to itself.
- **Join-point decomposition** — ✅ proved, `par_dichotomy`, but **no longer load-bearing**: after
  the N-ary migration the uniqueness direction routes through `runSeq_invariant_chain` instead, and
  no Lean declaration references `par_dichotomy` any more. It is kept as a statement of the
  trichotomy. Any interleaved run of `.par cs k` is, at every point, either still in `par` form,
  has passed through the join into `k`'s continuation, or has crashed — nothing else is possible.
  This pins down *that* a join happens
  and that nothing else can; it does **not** yet pin down *which* `(a, b, σ'')` the join lands on.
- **One-step non-racing from top-level `Indep`** — ✅ proved, `no_race_of_indep` (built on the
  purely structural `nextAccs_subset_accesses`: a program's *immediate* next label is always
  already inside its own `accesses`, no `Reaches` involved). This is what lets `reaches_par_left`/
  `reaches_par_right` (✅ proved) lift a *self-contained* run of one branch into the `.par` context
  while the other branch sits completely still — the schedule "run `p` to completion, then run
  `q`" is always legal once `p`, `q` are independent, `q` untouched.
- **The single-step canonical invariant** — ✅ proved, `step_combined`. This superseded an earlier
  line of attack (general containment of *every* reachable config against the *original* top-level
  footprint, at arbitrary depth) that ran into real difficulty: that version's "reached a join
  point" case needed `wellFormed_canonical`'s own uniqueness direction as an ingredient, making it
  a three-way mutual induction with no clean base case. The unlock came from a different question:
  *why does the theorem need `WellFormed` at all?* `step`'s racing check is re-evaluated fresh at
  every single step, not once at the top — so a real step that doesn't crash is automatically
  non-racing *at that instant*, for free, no matter how deep the program is nested. The part that
  actually needs independence is narrower: when the *right* branch of a `.par` moves before the
  left one, its real starting state is the raw joint state, not the canonical reference point
  `σ₁ := (runSeq p σ).2` the whole theorem is stated against, and only `Indep` guarantees replaying
  its step against `σ₁` gives the same result. `step_combined` proves exactly this — one step never
  changes `runSeq`'s value and never lets a location outside the original footprint leak in — by
  induction on the moving program, with no appeal to an arbitrary-depth containment argument: the
  hard "right branch moves first" case uses `step_locality` (an operational analogue of
  `accesses_runSeq_locality`) to replay that step against `σ₁`, then needs the *footprint* half of
  its own conclusion, applied one level down via the induction hypothesis, to pin the replayed
  state down exactly rather than just up to agreement outside some set — which is why the theorem
  is genuinely proved as one combined statement (`runSeq` invariance + footprint containment
  together), not two separate lemmas proved in sequence.
- **Preservation and chaining** — ✅ proved. Iterating `step_combined` along a *whole* `Reaches`
  chain — back to the start — needs `WellFormed`
  re-established at every intermediate step, to invoke `step_combined` again:
  - `step_subset_rw`: the finer, `.reads`/`.writes`-tracked-separately version of
    `step_combined`'s containment conjunct — needed because reconstructing `Indep`'s three
    separate Bernstein conditions after a step isn't possible from the combined, read-and-write-
    together `FDisjoint` version alone.
  - `WellFormed_preserved`: subject reduction — `WellFormed` survives one real step, whichever
    branch moved, at any nesting depth. Its compound-branch case doesn't re-derive containment
    from scratch; it uses the structurally-smaller induction hypothesis (itself
    `WellFormed_preserved`) for that branch's own `WellFormed`, and `step_subset_rw` only to check
    `Indep` monotonically shrinks.
  - `runSeq_invariant_chain` / `subset_chain`: `step_combined` / `step_subset_rw` iterated along a
    whole chain via `WellFormed_preserved`, giving the uniqueness direction (any real, non-crashing
    execution's value matches the canonical one) and the containment needed for `reaches_par_left`/
    `reaches_par_right`'s non-racing side condition on the existence direction — for a branch of
    *any* nesting depth, no separate general-containment development needed.
  - `no_race_contained`: `no_race_of_indep` generalized to take containment as explicit hypotheses,
    for use once labels are bounded by an *original* footprint several steps back rather than their
    own current one.

  Assembled in `wellFormed_canonical`'s `.par` case: the → direction is `runSeq_invariant_chain`
  applied to the given `Reaches`; the ← direction explicitly constructs the "run `p` fully, then
  run `q`, then step into `k`" witness schedule via `reaches_par_left`/`reaches_par_right`, with
  `subset_chain` + `no_race_contained` discharging the non-racing side conditions.

**4. `runSeq (parPair p q) σ = runSeq (seqPair p q) σ`** — ✅ proved (`runSeq_par_eq_seq`). A fact
purely about the *definitions*, no operational semantics involved. `runSeq` already treats
`.par p q k` by running `p` then `q` sequentially (that is how `accesses`'s reference execution
was built), and `runSeq` commutes with `bind` (`runSeq_bind`, ✅ proved), so unfolding
`seqPair p q = bind p (fun a => bind q ...)` gives the identical computation. No `Indep` needed.

## Assembly

```lean
theorem par_eq_seq (p : ParM α) (q : ParM β) (σ : State) (h : WellFormed (parPair p q) σ)
    (r : α × β) (σ' : State) :
    Reaches (.run (parPair p q) σ) (.run (.pure r) σ')
  ↔ Reaches (.run (seqPair p q) σ) (.run (.pure r) σ') := by
  rw [wellFormed_canonical _ _ h,
      wellFormed_canonical _ _ (wellFormed_of_seqPair h),   -- WellFormed transfers: no Indep needed,
      runSeq_par_eq_seq]                                    -- since seqPair has no top-level par node
```

`WellFormed (parPair p q) σ` unfolds to `Indep(...) ∧ WellFormed p σ ∧ WellFormed q σ₁ ∧ True`; the
`Indep` conjunct is exactly what is *not* needed to establish `WellFormed (seqPair p q) σ` (there is
no top-level `par` node to check there), so `wellFormed_of_seqPair` only needs the other two
conjuncts.

## N-ary generalization — ✅ done

`parAll_eq_seqAll` (`Theory/Sequentialize.lean`), exactly as predicted: built the same way as
`par_eq_seq` (`wellFormed_canonical` on each side + a definitional bridge), by induction on the
list. `runSeq_parAll_eq_seqAll` and `wellFormed_of_seqAll` are both fully proved, no `sorry`, and
now (with `wellFormed_canonical` complete) so is `parAll_par_seq_eq` itself.

`wellFormed_of_seqPair` also went from `sorry` to a real proof along the way, via a new general
lemma `WellFormed_bind` (well-formedness distributes through `bind`: the whole is well-formed iff
the first part is and the continuation is well-formed *at the canonical outcome*). This is the
kind of fact that made the N-ary case mechanical rather than a repeat of the `par` case's
difficulty.

**Current total: zero `sorry` in the codebase.** `wellFormed_canonical`, `par_seq_eq`, and
`parAll_par_seq_eq` are all fully proved — checked via `#print axioms` on each:
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`. `Classical.choice` is inherited
transitively through `grind`-annotated lemmas already in the codebase (e.g. `runSeq_frame`);
it is not something this proof itself needed to introduce.
