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

**Anti-vacuity obligation:** exhibit racy `p`, `q` where this *fails*, proved in Lean, so `h` is
demonstrably load-bearing.

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
the `par`-branch structure preserved (`max` at a fork, not `Σ`). Not built (not on the critical
path — `papers.md` §8), but `accesses`'s structure is chosen so this is an added fold later, not a
rewrite. Region notation + `region_disjoint` (M4, below) is what keeps the per-example `Indep`
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

**iris-lean only** (plus Mathlib — see open question). Everything else is ideas, not imports.

Import: `Iris/BI/*` + `Iris/ProofMode/*` (BI interface and ~35 proof-mode tactics — we instantiate
`Iris.BI` at our own `ParaProp := State → Prop` with `∗` as disjoint conjunction; one `instance`
buys the whole proof mode) and `Iris/Algebra/{Heap, GenMap, DFrac}`.

Do **not** import `Iris/ProgramLogic/*` or `Iris/HeapLang/*` — HeapLang's `par` is derived from
*unstructured* `fork`, HeapLang is nondeterministic in allocation and prophecies (so `⟦C⟧σ` isn't
even a function), it has no arrays (#526), `wp_par` is unary so it cannot express equivalence, and
that part of the tree churns weekly (#533, #548, #550, #567). Read `HeapLang/Lib/{Par, Spawn,
Quicksort}` as *templates*, don't depend on them.

**Risk, resolve first:** iris-lean's `BI` class carries a later modality `▷`; our model isn't
step-indexed so we set `▷ := id`. Standard ("BI without step-indexing"; cf. Simuliris'
non-step-indexed Iris), but unvalidated. **Fallback: hand-roll a minimal BI + Aesop rule set
(~2 weeks).**

Toolchain: 4.31.0 → **4.32.2** (both Mathlib and iris-lean have that tag; already staged in
`lean-toolchain` and `lakefile.toml`, `lake update` not yet run).

**Open question:** does "only iris-lean" mean dropping Mathlib too? The plan currently leans on
`List.prod_flatten` (Batteries, `Associative`+`LawfulIdentity`, no commutativity needed),
`splitLengths`/`flatten_splitLengths`, and the fold-duality lemmas in `Mathlib/Data/List/Fold.lean`.
Dropping Mathlib means proving those ourselves — doable, but real work.

**Disk:** only ~6 GB free on `/`. A Mathlib build (even via `lake exe cache get`) plus iris will be
tight. Free space before `lake update`.

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
  Pragma/              -- #parallel, collapse, reduction, private
  Compile/ToTask.lean  -- ParM → Task.spawn + Task.mapList; preservation
  Examples/{Reduce, Sort, MatMul, LoopPar}.lean
```

## Milestones

| # | Milestone |
|---|---|
| 0 | ✅ Toolchain 4.32.2 + iris. **BI spike** (`▷ := id`) still open — gates Tier-2 only, not the theorem |
| 1 | ✅ `ParM` (no `iter` — dropped, see below) + `Semantics.lean` (`State`, `step`, `Reaches`, `Safe`, race ↦ `wrong`) |
| 2 | ✅ `Core/Access.lean` — `accesses`/`runSeq` (reference interpreter), `Footprint`, Bernstein `Indep` |
| 3 | **`par_eq_seq`** — binary, then N-ary, then nested. Plus the anti-vacuity counterexample |
| 4 | Notation layer (`∥`, `A[i]`, regions, `region_disjoint`) |
| 5 | Example 1: chunked reduce |
| 6 | `Pragma/` — `#parallel for`, `collapse`; Example 3a: matmul; the failing-prefix regression test |
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
