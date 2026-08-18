# Program model: why `ParM`

Rationale for `Paralever/Core/ParM.lean`. Code references this file as `docs/program-model.md`.

## `ParM` is a free monad

A program represented as **data** (a tree of effects), not as a function. `do`-notation builds the
tree; nothing runs. Meaning comes from separate interpreters over the same tree:

| interpreter | gives |
|---|---|
| `run : ParM α → State → Schedule → Option (α × State)` | semantics |
| `accesses : ParM α → State → Footprint` | dynamic footprints |
| `compile : ParM α → (Unit → α)` | real Lean + `Task` |
| `cost : ParM α → Nat × Nat` (later) | work / span |

One program, many meanings. This is why footprints can be dynamic without a separate static
analyser — `accesses` is just another fold over the tree.

## Why not the alternatives

Three requirements, each ruling out one option.

**1. Interleaving must be real, or the theorem is `rfl`.** Lean's `Task` is a one-field structure
with a real body (`Init/Core.lean:626,687`):

```lean
structure Task (α : Type u) : Type u where pure :: get : α
@[noinline, extern "lean_task_spawn"]
protected def Task.spawn (fn : Unit → α) (prio := .default) : Task α := ⟨fn ()⟩
```

So `(Task.spawn f).get = f ()` holds definitionally. Parallel and sequential are *the same term*;
there is no theorem and no meaningful independence hypothesis. Lean's effectful task API is worse:
`BaseIO.asTask`/`mapTask`/`bindTask`/`mapTasks`/`IO.wait` (`Init/System/IO.lean:245,258,272,300,567`)
are `opaque` + `@[extern]` with no equations, and `IO`/`ST` are no longer `EStateM`-based so
`Std.Do` has no `WP` instance for them. Proving there means *axiomatizing* the runtime.
→ rules out `Task` as the object of study. It remains the compilation target.

**2. Lean must supply binders, types, recursion, termination.** A deep embedding of syntax
(`Cmd`/`Expr`/`Store`) means hand-building scoping, an evaluator, and a procedure environment
before merge sort is expressible. → rules out deep syntax embedding.

**3. We must be able to induct.** The decomposition lemma (Brookes §5–7) is an induction. A bare
function type like `σ → Set (α × σ)` has no structure to induct on. → rules out shallow embedding.

The free monad is the unique point satisfying all three. `par` is *our* constructor, so we choose
its meaning.

## Why the freer (operational) form

`bind` is **not** a constructor; every effect node carries its own continuation. The naive
alternative `| bind : ParM α → (α → ParM β) → ParM β` makes `read l >>= f >>= g` and
`read l >>= (fun x => f x >>= g)` *different trees*, so associativity has to be fought everywhere
and the step relation needs evaluation contexts to locate the next redex.

In the freer form **the head of the tree is literally the next action**. Consequences:

- the step relation is a handful of cases with no congruence rules;
- `bind` is a defined grafting function whose monad laws are provable on the nose
  (`bind_pure_left` is `rfl`; the other two are one-line inductions).

Standard construction; same idea as interaction trees (Xia et al., POPL 2020) minus coinduction.

## Why there is no `parN` constructor

`parN : List (ParM α) → (List α → ParM β) → ParM β` is rejected by the kernel: `List (ParM α)` is
a *nested* inductive occurrence whose parameter `ParM α` mentions the locally bound `α`.

Workarounds we rejected: a mutual `ParM`/`ParMList` pair (mutual induction tax on every proof), or
fixing the branch result type to a global constant like `Val` (loses generality).

**Chosen:** derive N-ary parallelism from binary `par` (`parAll`). Better on three counts:

- fewer constructors → fewer cases in every induction;
- the N-ary sequentialization theorem becomes a *corollary* of the binary one by induction on the
  list, rather than a second proof;
- nothing is lost. The scheduler may interleave at any point, so a right-nested tree of binary
  `par`s is genuinely k-way parallel. The nesting fixes an *association*, not a *serialization*.

## `ParM` has no `iter` / unbounded-loop constructor

`ParM` values are finite trees built by Lean's own recursion, so representable programs are
exactly those **whose termination Lean can prove statically**. That excludes loops with no static
bound, e.g. `while A[i] > 0 do ...`, and non-terminating programs.

It does **not** exclude runtime-determined *splits*. Fork-join quicksort is definable,
structurally recursive on a fuel parameter, and the fuel is a genuine bound (sorting depth ≤
array length, known statically):

```lean
def qsort : Nat → Loc → Loc → ParM Unit
  | 0,        _,  _  => return ()
  | fuel + 1, lo, hi => do
      let p ← partitionAt lo hi                                 -- split from the heap
      let _ ← parPair (qsort fuel lo p) (qsort fuel (p+1) hi)    -- genuine fork-join
      return ()
```

An earlier draft added an `iter` constructor (`(β → ParM (β ⊕ α)) → β → (α → ParM γ) → ParM γ`,
the interaction-trees `iter` combinator without coinduction) specifically to reach unbounded
data-dependent loops. **It was removed**: none of the three flagship examples need it — reduce is
structural over `List`, merge sort is structural with a static split, quicksort and matmul/stencil
use fuel or a finite index range — and supporting it "properly" (no shortcuts) would mean
fuel-indexing `accesses`/`Footprint` through every M2/M3 lemma for a case nothing uses. It is a
self-contained constructor (one extra case per induction), so it can be reintroduced later,
in isolation, if a concrete example needs a genuinely unbounded loop.

Fork-join recursion always comes from Lean's own recursion, with fuel when the split is
data-dependent — never from a constructor of `ParM` itself. A general fixpoint constructor is in
any case impossible: `((β → ParM α) → β → ParM α) → ...` puts `ParM` left of an arrow, a negative
occurrence, which Lean rejects.

| shape | mechanism |
|---|---|
| structural recursion, static splits (mergesort) | plain Lean recursion |
| runtime split, statically bounded depth (quicksort) | fuel parameter |
| unbounded loop, no static bound; non-termination | out of scope — see above |

### Why not `partial def`

`partial def` does not assume termination — it removes the function from the logic. Lean compiles
it to an **opaque constant** (hence the `Inhabited` requirement): no equational lemmas, no
unfolding, no induction principle. You can state theorems about it and never prove them.

`partial_fixpoint` (`Init/Internal/Order/*`, present in 4.32.2) is the real alternative: least
fixpoints in a CCPO, with equations and a fixpoint induction principle. It requires the return
type to carry an order structure, which `ParM` does not naturally have. Revisit only if genuine
partiality becomes necessary.

This is the interaction-trees `iter` combinator without coinduction. (Lean 4 has no native
coinductive types, so full ITrees are not an option; `iter` recovers the expressiveness that
matters here.)

Consequence: `Reaches` may be infinite, so termination becomes a predicate rather than a
structural guarantee. The sequentialization theorem is about reachable outcomes, so it is
unaffected.

`nextAccs (.iter ..) = []` — unrolling is a *silent* step touching no memory, so a race involving
an `iter` branch is caught one step later, once the unroll exposes the real action. This is sound
and keeps `nextAccs` structurally recursive.

## Universes

`ParM : Type → Type 1`. The bump is forced: `par` quantifies over its branches' result types, so a
`ParM γ` node can contain `ParM α`, `ParM β` for `α`, `β` chosen at construction time. `Monad`
accepts `Type u → Type v` with `u ≠ v`, so `do`-notation is unaffected.

## References

- Brookes, *A Semantics for Concurrent Separation Logic*, CONCUR'04 §5–7 — the decomposition
  lemma the induction requirement comes from.
- Xia et al., *Interaction Trees*, POPL 2020 — the freer/operational representation.
- Reynolds, *Toward a Grainless Semantics for Shared-Variable Concurrency*, FSTTCS 2004 — races as
  absorbing `wrong`, which is why `run` returns `Option`.

Full list in [`../papers.md`](../papers.md).
