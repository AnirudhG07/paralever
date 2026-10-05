# Cost: work, time, and why `max` is a theorem

Rationale for `Paralever/Lib/Cost.lean`. Code references this file as `docs/cost.md`.

## What was missing

`par_seq_eq` says the parallel program computes the same output as the sequential one. That is the
*extensional* half. It says nothing about why anyone would run the parallel version, because it says
nothing about time.

This file adds the *intensional* half: two more readings of the same `ParM` tree.

| reading | meaning |
|---|---|
| `work p σ` | how many memory operations execute in total |
| `time p σ` | how many **parallel rounds** the program needs |

## The earlier version was circular, and this one is not

An earlier `Cost.lean` *defined* `time` by a fold with `max` at the `par` node:

```lean
time (.par p q k) σ = max (time p σ) (time q σ₁) + time (k …) σ₂     -- stipulated
```

"Parallel is faster" was then true by unfolding a definition written to say so. The hypothesis
`Indep` appeared nowhere, which is the tell: a cost model that cannot tell a racy fork from a safe
one is not measuring anything about parallelism.

`time` is now **counted, not folded**. `pstep` is a parallel-round relation whose `par` case says
only *advance every ready branch*:

```lean
def pstep : ParM τ → State → Option (ParM τ × List (Loc × Val))
  | .pure _,      _ => none
  | .read l k,    σ => some (k (σ l), [])
  | .write l v k, _ => some (k (), [(l, v)])
  | .par p q k,   σ =>
      match pstep p σ, pstep q σ with
      | some (p', wp), some (q', wq) => some (.par p' q' k, wp ++ wq)   -- BOTH advance
      | some (p', wp), none          => some (.par p' q  k, wp)
      | none,          some (q', wq) => some (.par p  q' k, wq)
      | none,          none          => pstep (k ((runSeq p σ).1, (runSeq q σ).1)) σ
```

`time p σ := ptime (work p σ + 1) p σ`, where `ptime` counts rounds under a fuel bound. The words
`max` and `Indep` occur nowhere in either definition.

Two details in the `par` case are load-bearing, and both were bugs in earlier drafts:

- **The join charges no round.** Joining performs no memory operation. Charging for it inflates every
  parallel cost by the nesting depth.
- **The join fires when both branches are *finished*, not when they are syntactically `.pure`.** A
  nested `par` whose own work is exhausted is finished too. Testing for `.pure` skips the
  continuation entirely, so a program that performs a write reports zero rounds. The branch values
  are therefore read off `runSeq`, which is exact precisely because the branches are done.

## The theorems

```lean
theorem work_par_eq_seq    : work (parPair p q) σ = work (seqPair p q) σ
theorem ptime_parPair_eq_max (n) (hwf : WellFormed (parPair p q) σ) :
    ptime n (parPair p q) σ = max (ptime n p σ) (ptime n q σ)
theorem time_parPair_eq_max  (hwf) : time (parPair p q) σ = max (time p σ) (time q σ)
theorem time_seqPair_eq_add  (hwf) : time (seqPair p q) σ = time p σ + time q (runSeq p σ).2
theorem time_par_lt_seq (hwf) (hp : 0 < time p σ) (hq : 0 < time q σ) :
    time (parPair p q) σ < time (seqPair p q) σ
```

**Work is unchanged.** This is the claim most easily got wrong: a chunked sum performs `n` additions
whichever way it runs. Parallelism does not reduce the number of operations, and sometimes raises it
through combine overhead. Only the *time* drops. `docs/access.md` already warned against conflating
the two; these theorems make the distinction formal.

**`max` is earned by independence.** `time_parPair_eq_max` carries `WellFormed` as a hypothesis, and
the hypothesis is used at exactly one point (below). The sequential law carries no such hypothesis
for its shape — `bind` is sequential composition, so its rounds simply add.

**Time strictly drops exactly when both branches do something.** `0 < time p σ` and `0 < time q σ`
are necessary, not decoration: forking against a `pure` buys nothing.

Measured on `Examples/TwoProcesses.lean`, by `rfl`:

| | work | time |
|---|---|---|
| `procP` alone | 6 | 6 |
| `parPair procP procQ` | 12 | **6** |
| `seqPair procP procQ` | 12 | 12 |

Twelve operations either way; half the time in parallel.

## How `max` is derived

The proof is a fuel induction with four cases at a `par` node — both branches step, only `p`, only
`q`, neither. The arithmetic in each is trivial. All the content sits in one place:

> `p`'s remaining rounds must come out the same whether or not `q`'s writes *from this same round*
> have already landed.

That is `ptime_locality`, and it is false for interfering branches. So `max` is not an assumption
about parallel hardware; it is what round-counting *gives you* once the branches cannot see each
other. Branches that conflict share no round and get no `max` — see the `RacyCost` section of
`Cost.lean`, where `time (parPair racyP racyQ) σz = 3` while `max (time racyP σz) (time racyQ σz)
= 2`, because `racyQ` writes a cell `racyP` reads one round later.

### The bridge that makes it cheap

`ptime_locality` needs `WellFormed` and footprint containment re-established after *every* round, and
`Theory/WellFormedCanonical.lean` already proves exactly that for arbitrary `Reaches` derivations
(`runSeq_invariant_chain`, `subset_chain`). So rather than redo those inductions over `pstep`, one
lemma connects the two semantics:

```lean
theorem pstep_reaches (hwf : WellFormed p σ) (h : pstep p σ = some (p', ws)) :
    Reaches (Conf.run p σ) (Conf.run p' (applyAll σ ws))
```

**A parallel round is a sequence of ordinary steps**: `p`'s move, then `q`'s, then the joins, with
the round's batched writes landing in exactly the state that schedule produces. Its proof is where
`reaches_par_left`/`reaches_par_right` and the non-racing side conditions get used; everything a
round must preserve (`pstep_combined`) is then inherited rather than re-proved.

One extra ingredient is needed to make `time`'s fuel sufficient: `work_pstep_lt`, a round strictly
reduces the remaining work. Its `par` case has to cancel the continuation's work exactly, which it
does by applying `pstep_combined` to `parPair p q` — whose canonical run *is* the pair of branch
values together with the post-join state, so the join state is pinned rather than merely bounded.

## `TimeM`

`TimeM α := α × Cost` with a `Monad` instance whose `bind` **sums** both components.

That is correct rather than a simplification: `bind` *is* sequential composition, and
`time_bind_add` proves it adds. The `max` belongs to `par`, which is a constructor of `ParM` rather
than a bind, so the monad never has to know about it. The parallel structure lives in the program,
not in the monad.

`costOf p σ : Cost` is an interpreter — the fifth reading of a `ParM` term, alongside `run`,
`accesses`, `compile` and `render` (`docs/program-model.md`).

## What this does not claim

**`time` is a statement about the model, not the wall clock.** It counts rounds of dependent memory
operations on an idealised machine with unlimited cores, no scheduling overhead, no memory hierarchy,
and unit cost per operation. A proof that `time` drops is not a proof that the program runs faster on
real hardware.

Measured wall-clock belongs to `Compile/TaskFacts.lean`, which checks empirically — not by Lean's
proof — that spawned work genuinely overlaps. The two claims are complementary and should not be
stated as one.

**No asymptotics.** These are exact counts for a given program and state. Deriving `O(log n)` span
for a tree reduction would need the recursion analysed separately; calf/decalf is the framework that
does this properly.

**`ParM` is inductive, so every program terminates.** `work p σ` is therefore always a finite bound,
which is what lets `ptime`'s fuel be `work p σ + 1`. Nothing here extends to divergent programs.

## References

- Niu, Sterling, Grodin, Harper, *A Cost-Aware Logical Framework* (calf), POPL 2022; *decalf*
  (directed, effectful), OOPSLA 2024 — `papers.md` §8.1. Cost as an effect, with an internal **phase
  distinction**: input/output behaviour cannot depend on cost. That is precisely the split this file
  implements by hand — `par_seq_eq` for the extension, `work`/`time` for the intension — and their
  case studies derive bounds for sequential *and* parallel merge sort in one development. If cost
  reasoning here grows beyond exact counts, this is the design to adopt.
- Blelloch & Greiner, *A Provable Time and Space Efficient Implementation of NESL*, ICFP 1996;
  Blelloch, Gibbons, Matias, JACM 1999 — `papers.md` §8.2. The origin of work/span as the two
  measures, and of `max`-at-a-fork — stipulated there as the cost model, derived here from `pstep`.
- Brookes, *A Semantics for Concurrent Separation Logic*, CONCUR 2004 §5–7 — the decomposition
  lemma `pstep_reaches` leans on through `reaches_par_left`/`reaches_par_right`.
- Reynolds, *Toward a Grainless Semantics*, FSTTCS 2004 — why counting at a coarse grain is
  legitimate for race-free programs, and why racy ones are excluded rather than mismeasured.

Full list in [`../papers.md`](../papers.md).
