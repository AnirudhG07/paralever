# The decomposition proof

Rationale for `Paralever/Theory/Decomposition.lean` and the `WellFormed` predicate in
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

Four pieces. Three are fully proved (checked via `#print axioms`, no `sorryAx`); one remains.

**1. `Reaches.terminal` / `Reaches.single_step`** (`Core/Semantics.lean`) — ✅ proved. Generic
facts about `Reaches` on configurations with zero or one successor. Needed because `read`/`write`
steps are deterministic (exactly one successor each); only `par` genuinely branches.

**2. Locality** (`Theory/Decomposition.lean`) — ✅ proved, in three layers:
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

**3. `wellFormed_canonical`** (the crux, still open) — under `WellFormed p σ`, the *only*
configuration `p` reaches via the real nondeterministic `step`/`Reaches` is the canonical
`runSeq p σ`:

```lean
theorem wellFormed_canonical (p : ParM τ) (σ : State) (h : WellFormed p σ) (r : τ) (σ' : State) :
    Reaches (.run p σ) (.run (.pure r) σ') ↔ (r, σ') = runSeq p σ
```

`pure`/`read`/`write` are ✅ proved (immediate from (1) plus the definitions). `par` is `sorry`.
With locality (2) now available, what remains is specifically the **operational** half — relating
the real `step`/`Reaches` interleaving to the canonical value, not `runSeq` to itself:
- **Join-point decomposition**: any interleaved run of `.par p q k` factors into a prefix of `p`'s
  own reachable steps interleaved with a prefix of `q`'s, up to the point both finish. Forced by
  `step`'s own shape (a `.par p' q' k` config stays a `.par` node, progressing whichever side isn't
  done, until *both* are `.pure` — only then does it transition into `k`).
- **The diamond step**: two actions from different, independent branches commute
  (`State.update_comm`, already proved in `Core/Semantics.lean`) — this is what makes the
  interleaving order irrelevant once the join-point structure is established.

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
list. `runSeq_parAll_eq_seqAll` and `wellFormed_of_seqAll` are both fully proved, no `sorry`. The
metatheorem itself inherits the same and only open dependency as `par_eq_seq` — the `par` case of
`wellFormed_canonical` — nothing new.

`wellFormed_of_seqPair` also went from `sorry` to a real proof along the way, via a new general
lemma `WellFormed_bind` (well-formedness distributes through `bind`: the whole is well-formed iff
the first part is and the continuation is well-formed *at the canonical outcome*). This is the
kind of fact that made the N-ary case mechanical rather than a repeat of the `par` case's
difficulty.

**Current total: exactly one `sorry` in the codebase** — `wellFormed_canonical`'s `par` case,
tracked as a TODO there. Everything else in `Core/` and `Theory/` is sorry-free and axiom-checked
(`propext`/`Quot.sound` only, no `sorryAx`, no `Classical.choice`).
