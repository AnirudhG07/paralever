# Paralever — plan

Working document. 
Reading list: [`papers.md`](./papers.md).

## Goal

Prove **once**:

> if parallel branches are pairwise **independent**, the parallel program and its sequential
> counterpart produce the same output — under *every* schedule.

Then verifying any parallel program = discharging an independence obligation. Never reasoning
about interleavings.

**Gap being filled.** This statement, mechanized generically and instantiated, exists in no proof
assistant. Brookes has the enabling lemma but never states the corollary; Vafeiadis has the
mechanization but not the corollary; DPJ has the corollary only on paper for a Java-like calculus;
PolCert has it only for affine loop nests; Blom et al. have exactly this architecture but no proof
assistant. Nothing in Lean 4.

**Deliverables:** a paper *and* a usable library.
**Flagship examples:** (1) chunked reduce, (2) parallel merge/quicksort, (3) loop parallelization
under Bernstein conditions (matmul, stencils).

---

## Program model: free monad over effects

**Decided.** Deep in *effects*, shallow in *everything else*.

```lean
inductive ParM : Type → Type 1 where
  | pure  {α : Type}     : α → ParM α
  | read  {α : Type}     : Loc → (Val → ParM α) → ParM α
  | write {α : Type}     : Loc → Val → (Unit → ParM α) → ParM α
  | par   {α β γ : Type} : ParM α → ParM β → (α × β → ParM γ) → ParM γ
```

**Implemented and typechecking** in `Paralever/Core/ParM.lean`, with `Monad` instance and both
non-trivial monad laws (`bind_pure_right`, `bind_assoc`) proved — no `sorry`.

Two decisions the code forced, both improvements:

- **Freer (operational) form: `bind` is *not* a constructor.** Every effect node carries its own
  continuation, so **the head of the tree is literally the next action**. The step relation needs
  no congruence rules and no evaluation contexts, and the monad laws hold on the nose. With `bind`
  as a constructor, `read l >>= f >>= g` and `read l >>= (fun x => f x >>= g)` are *different
  trees* and you fight associativity forever.
- **No `parN` constructor.** Lean rejects `parN : List (ParM α) → ...` — `List (ParM α)` is a
  nested inductive whose parameter mentions the locally bound `α`. Rather than work around it (a
  mutual `ParM`/`ParMList` pair, or fixing the branch type to `Val`), N-ary parallelism is
  **derived** from binary `par`. This is better: fewer constructors so fewer induction cases, and
  the N-ary theorem becomes a *corollary* of the binary one. Nothing is lost — the scheduler may
  interleave anywhere, so a right-nested tree of binary `par`s is genuinely k-way parallel. The
  nesting fixes an *association*, not a *serialization*.

- **No `iter` constructor.** An earlier draft added one for unbounded data-dependent loops
  (interaction-trees `iter` minus coinduction). **Dropped**: no flagship example needs it —
  quicksort's runtime split is reachable via a fuel parameter (structurally recursive on `fuel`,
  a genuine bound since sort depth ≤ array length), reduce/mergesort are structural, matmul/stencil
  use finite index ranges. Supporting `iter` "properly" would mean fuel-indexing
  `accesses`/`Footprint` through M2 and M3 for a case nothing uses. Self-contained (one
  constructor), so reintroducible in isolation if a real unbounded loop shows up. Consequence:
  every `ParM` value is now a finite tree and `accesses`/`runSeq` are plain total structural
  recursions — no partiality anywhere in `Core/`.

Three yes/no answers, since this was the confusing part:

- **Own syntax?** No. Programs are ordinary Lean `do`-blocks. Lean's `do`, `for`, `let mut`,
  pattern matching all work via the `Monad` instance.
- **Own language?** No. One inductive type. No parser, no elaborator, no VC generator.
- **Does Lean do the work?** Yes — binders, types, data structures, recursion, termination,
  `Array`/`List`. We supply exactly one thing Lean lacks: a `par` with real interleaving semantics.

### Why this and not the alternatives

| | Plain Lean + `Task` | **Free monad** | Deep embedding (`Cmd`/`Expr`) |
|---|---|---|---|
| Programs look like | Lean | Lean | unreadable AST literals |
| Recursion / scoping | free | free | hand-built (`ProcEnv`, substitution) |
| Interleaving real? | **no** — `Task.spawn f = ⟨f ()⟩` by `rfl` | **yes** — `par` is our constructor | yes |
| Mutable shared state | no | yes | yes |
| Examples 2 & 3 reachable | **no** | yes | yes |
| Induction for decomposition | n/a | yes (on `ParM`) | yes (on `Cmd`) |
| Static `by decide` footprints | n/a | no (dynamic) | yes |
| Time to the interesting proof | — | weeks | months |

The decisive facts:

1. **`Task` makes the theorem vacuous.** `Init/Core.lean:626,687` — `Task` is a one-field structure
   and `spawn` has a real body, so `(Task.spawn f).get = f ()` holds by `rfl`. Parallel and
   sequential are *the same term*; there is no theorem and no meaningful `Indep` hypothesis. (The
   algebraic content — `(chunks A k).map sum |>.sum = sum A` — is still real, but that is a
   homomorphism result, not a concurrency result.)
2. **Lean's effectful task API has no semantics at all.** `BaseIO.asTask`/`mapTask`/`bindTask`/
   `mapTasks`/`IO.wait` (`Init/System/IO.lean:245,258,272,300,567`) are `opaque` + `@[extern]` with
   no equations; `IO`/`ST` are no longer `EStateM`-based so `Std.Do` has no `WP` instance for them.
   Proving there means *axiomatizing* the runtime, not defining it.
3. **A purely shallow embedding loses induction.** An opaque `σ → Set (α × σ)` has no structure to
   induct on, and the decomposition lemma is an induction. The free monad keeps it.

`Task` stays in the project — as a **compilation target only**, never a place where anything is
proved. Fact (1) makes that direction sound and nearly free.

### Semantics

```lean
def run : ParM α → State → Schedule → Option (α × State)   -- none = race (wrong)
```

Schedule-parameterized; `none` is an absorbing `wrong` on races (Reynolds' grainless semantics —
this is what makes the atomic grain irrelevant and keeps the theorem honest by *excluding* racy
programs rather than silently assuming them away).

### The theorem

```lean
theorem par_eq_seq (p : ParM α) (q : ParM β) (σ : State)
    (h : Indep (accesses p σ) (accesses q σ)) :
    ∀ sched, run (ParM.par p q) σ sched
           = run (do let x ← p; let y ← q; return (x, y)) σ .sequential
```

"Under any schedule, parallel = sequential." Determinism and sequential-equivalence in one
statement. Then the N-ary `parN` version with pairwise `Indep`, then nesting.

**Anti-vacuity obligation — ✅ discharged** (`Examples/Races/Caught.lean`): two racy pairs with
`¬ ParSeqEq` proved in Lean, so `h` is load-bearing against the conclusion and not merely
unprovable. See `docs/semantics.md` § Anti-vacuity witness.

### Independence = Bernstein, not `∗` — ✅ implemented

```
Indep (r₁,w₁) (r₂,w₂)  :=  w₁∩w₂ = ∅  ∧  w₁∩r₂ = ∅  ∧  w₂∩r₁ = ∅
```

Shared **reads** allowed. Not optional: matmul's iterations write disjoint `C[i*n+j]` but read
overlapping rows of `A` and columns of `B`. Naive `∗`-disjointness rejects matmul; Bernstein
accepts it. Same for stencils and merge steps. Confirmed by `Test/AccessSanity.lean`: shared reads
→ independent; same-location writes → not.

`accesses`/`runSeq` (`Core/Access.lean`) compute this from a **canonical left-to-right reference
execution** — dynamic, not syntactic, so it sees through data-dependent addressing — total and
structural now that `iter` is gone. Full design and the `q`-branch asymmetry: `docs/access.md`.

**Cost note (corrected from discussion):** parallel programs do not have *fewer total operations*
than sequential — chunked sum still does `n` additions either way. **Work** (total ops) is
schedule-invariant; **span** (longest dependency chain) is what shrinks with more threads and is
what produces speedup. A flat access log gives footprint + work for free but not span — span needs
the `par`-branch structure preserved (`max` at a fork, not `Σ`). **Built** (`Lib/Cost.lean`,
`docs/cost.md`): `work` is a fold, but `time` is *not* — it counts rounds of a parallel-round
relation `pstep`, so `max` at a fork is the theorem `time_parPair_eq_max` rather than a stipulation,
and `time_par_lt_seq` is the speedup result. `max` is earned by `WellFormed`; `RacyCost` in that file
exhibits interfering branches where it genuinely fails. Region notation + `region_disjoint` (M4, below) is what keeps the per-example `Indep`
proofs short despite footprints being dynamic rather than syntactic.

---

## Notation layer (sugar, not a DSL)

All pure `syntax`/`macro_rules`/`notation` — expands to the same `ParM` terms you'd write by hand,
so it can never affect the semantics, the theorem, or any proof. Under ~100 lines total, addable
incrementally.

```lean
p ∥ q                    -- ParM.par        (`|||` is taken by HOr)
A[i]                     -- ParM.read
A[i] := v                -- ParM.write      (custom doElem, cf. Velvet's Syntax.lean)
parallel for x in xs do  -- ParM.parN
ro/wo/rw A[lo:hi]        -- footprint regions
region_disjoint          -- tactic: simp + omega on interval endpoints
```

The region notation is the one that's load-bearing rather than cosmetic: without it every
independence proof fights list manipulation instead of stating an interval fact.

```lean
def msort (A : Arr) (lo hi : Nat) : ParM Unit := do
  if hi - lo ≤ 1 then return ()
  let mid := (lo + hi) / 2
  msort A lo mid ∥ msort A mid hi
  merge A lo mid hi
```

---

## OpenMP-style pragmas — *checked*, not trusted

**The angle: real OpenMP pragmas are trusted and unchecked — that is why they are a bug factory.
Ours elaborate into `parN` plus a proof obligation the compiler will not take your word for.**
This is Blom et al.'s architecture (STTT'21) with the proof assistant they lacked, and it is
probably the most compelling demo in the paper.

```lean
def matmul (A B C : Arr) (n : Nat) : ParM Unit := do
  #parallel collapse 2
  for i in [0:n] do
    for j in [0:n] do
      let mut s : Int := 0
      for k in [0:n] do
        s := s + A[i*n + k] * B[k*n + j]
      C[i*n + j] := s
```

expands to `ParM.parN (List.ofFn fun (p : Fin (n*n)) => body (p/n) (p%n))` and emits

```lean
∀ p q : Fin (n*n), p ≠ q → Indep (fp (p/n) (p%n)) (fp (q/n) (q%n))
```

**This example cannot be proved without Bernstein** — iterations write disjoint `C[i*n+j]` but read
heavily overlapping rows of `A` and columns of `B`. That is the design decision justified in one
example.

And the one that must fail:

```lean
#parallel for i in [1:n] do
  A[i] := A[i-1] + 1        -- loop-carried dependence
```

Obligation is unprovable (take `j = i-1`: iteration `i` reads what iteration `j` writes). OpenMP
compiles this happily and gives a wrong answer at runtime. Keep as a regression test.

| OpenMP | Ours | Obligation |
|---|---|---|
| `parallel for` | `#parallel for` | pairwise `Indep` across iterations |
| `collapse(k)` | `#parallel collapse k` | same, over the flattened space |
| `reduction(+ : s)` | `#parallel reduction (+) s` | `Std.Associative` (+ `Commutative` iff schedule permutes) |
| `private(x)` | `#parallel private x` | none — thread-local by construction |
| `shared(A)` | default | the `Indep` goal |

---

## Dependencies

**Mathlib only.** Everything else is ideas, not imports.

**The BI question is closed, and the answer was no.** The plan called for instantiating a
bunched-implications interface at `ParaProp := State → Prop` to get `∗` and a proof mode for one
`instance`, with the step-indexing modality `▷ := id` as the risk to resolve first. A spike against
iris-lean resolved it: the instance costs nothing, because a fully proved non-step-indexed `BI` for
this shape of model already exists upstream — and that is beside the point, because the `∗` it
provides is *exclusive* separation, strictly narrower than `Indep`, which permits shared reads. The
dependency was removed once the spike had answered; `docs/theory.md` § 8 keeps the finding, and
`Logic/Rules.lean` frames with `∧` over `Core/Access.lean`'s footprints, which is what makes its
parallel rule general rather than narrowed. The fallback plan (hand-roll a minimal BI, ~2 weeks) is
not needed: no theorem here wants a BI. If read-sharing is ever wanted *inside* a separating
conjunction, the thing to build is a fractional-permission `∗` over `Core.State`, and nothing
supplies that off the shelf.

**An SMT solver is optional, external, and never linked.** `paralever vc` emits the independence
obligation as SMT-LIB and `--solve` discharges it with whatever solver is on the machine (z3, cvc5,
or `PARALEVER_SMT`); nothing in the tree depends on one and `lake build` is green without any. This
is the one place where an answer does not come from Lean's kernel, so it is labelled rather than
claimed: `unsat` is reported as *discharged by* the named solver, `sat` is recomputed in Lean before
it is believed, and `paralever prove` remains the only path that ends in a checked proof. The
architecture — generate the obligation, discharge it elsewhere — is what CSLib's Boole does at a
much larger scale (arXiv 2602.04846). Two things are not done: an invariant over several unknowns
must be written into the emitted file by hand (`--assume` states only `nonneg`), and a `sat` model is
not yet replayed as an interleaving, which needs a heap witness. See `docs/smt-vc.md`.

Do **not** depend on a HeapLang-style program logic — HeapLang's `par` is derived from *unstructured*
`fork`, it is nondeterministic in allocation and prophecies (so `⟦C⟧σ` isn't even a function), it has
no arrays, and `wp_par` is unary so it cannot express an equivalence. Read `HeapLang/Lib/{Par, Spawn,
Quicksort}` as *templates*, don't depend on them.

Toolchain: **v4.34.0**, with Mathlib pinned to the same tag. The package version tracks it:
`1.34.0`, declared in `lakefile.toml` and read from there by `Paralever/Version.lean`, whose
`#guard` fails the build if the two minors disagree.

**Open question:** drop Mathlib too? The plan leans on `List.prod_flatten` (Batteries,
`Associative`+`LawfulIdentity`, no commutativity needed), `splitLengths`/`flatten_splitLengths`, and
the fold-duality lemmas in `Mathlib/Data/List/Fold.lean`. Dropping Mathlib means proving those
ourselves — doable, but real work. `Core/` and `Theory/` already need none of it.

**Disk:** no longer tight — 625 GB free on `/` as of 2026-10-23, and dropping iris-lean returned
212 MB of fetched package. The original note said ~6 GB, which is stale.

---

## Layout

```
Paralever/
  Core/
    ParM.lean        -- ✅ ParM (no iter), Monad instance, monad laws, parAll/seqAll/parFor/seqFor
    Semantics.lean   -- ✅ State, Label, Conf (wrong), step, Reaches, Safe
    Access.lean      -- ✅ runSeq, accesses, Footprint, Bernstein Indep
  Theory/
    Decomposition.lean -- Brookes-style parallel decomposition
    Sequentialize.lean -- ★ par_eq_seq; N-ary; nested
    Determinism.lean   -- race-free ⇒ schedule-independent (confluence + Newman, cf. LVars)
  Logic/               -- Tier 2: DCSL-lite for data-dependent footprints (Vafeiadis' method)
  Notation/            -- ∥, A[i], regions, parallel-for
  Lib/Loop.lean        -- ✅ #parallel_for, the indexed read/write loop validator
  Compile/ToTask.lean  -- ParM → Task.spawn + Task.mapList; preservation
  Examples/{SumArray, Sort, MatMul, LoopPar}.lean
```

## Milestones

| # | Milestone |
|---|---|
| 0 | ✅ Toolchain 4.34.0. **BI spike** done and the dependency dropped — `∗` is narrower than `Indep` (`docs/theory.md` § 8) |
| 1 | ✅ `ParM` (no `iter` — dropped, see below) + `Semantics.lean` (`State`, `step`, `Reaches`, `Safe`, race ↦ `wrong`) |
| 2 | ✅ `Core/Access.lean` — `accesses`/`runSeq` (reference interpreter), `Footprint`, Bernstein `Indep` |
| 3 | **`par_eq_seq`** — binary, then N-ary, then nested. Plus the anti-vacuity counterexample |
| 4 | Notation layer (`∥`, `A[i]`, regions, `region_disjoint`) |
| 5 | Example 1: chunked reduce |
| 6 | `Lib/Loop.lean` — `#parallel_for`, `collapse`; Example 3a: matmul; the failing-prefix regression test |
| 7 | Tier-2 logic (BI instance + DCSL-lite); Example 2: parallel merge/quicksort |
| 8 | `Compile/ToTask` + preservation; upstream `Task.mapList_eq` and `mapAsyncChunked f xs = xs.map f` |
| 9 | `reduction`/`private` clauses; Example 3b: stencil; paper |

First PR: 1–2. Milestone 0's spike can run in parallel and gates only the Tier-2 work.

## Verification

- `lake build` green each milestone; CI runs the examples executable.
- **No-`sorry` gate** in CI over `Paralever/`.
- **Executable differential test**: compiled examples vs sequential on random inputs — catches
  semantics/compilation mismatch the proofs assume away, and confirms real speedup.
- **`Plausible` property tests**: `run (par p q) σ sched = run (seq p q) σ` for random *independent*
  `p`,`q`; and that it hits `wrong` for random racy ones. Main defence against a vacuous `Indep`.
- **Anti-vacuity theorem** (milestone 3) and the **failing-prefix pragma test** (milestone 6).

## Upstreamable side results

- `Task.mapList_eq : (Task.mapList f ts).get = f (ts.map Task.get)` — `Task.mapList`
  (`Init/Task.lean`) is the real fork-join combinator (there is no `Task.zip`), and neither core,
  Batteries, nor Mathlib has a single lemma about it.
- `List.mapAsyncChunked f xs = xs.map f` — `Mathlib/Data/List/Defs.lean:382`, zero lemmas attached.
- `(xs.toChunks n).flatten = xs` — stated only in a Batteries docstring, never proved.
