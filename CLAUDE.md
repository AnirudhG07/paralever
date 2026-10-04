# Paralever

Verifying that **parallel programs produce the same output as their sequential counterparts**, in
Lean 4. Prove one metatheorem — independent branches ⇒ `par p q` ≡ `seqPair p q` under every
schedule — then every program reduces to discharging an independence obligation.

Deliverables: a paper *and* a usable library. Plan: [`PLAN.md`](./PLAN.md). Reading list:
[`papers.md`](./papers.md). Design rationale: [`docs/`](./docs/).

## The rule that matters most

**Every definition, hypothesis, and design choice must trace to a paper or to a recorded design
decision.** Nothing is invented on the spot. If you write a definition and cannot say which paper
it comes from or which `docs/` file justifies it, stop and resolve that first — write the doc, or
find the citation, before writing the code.

In practice: non-obvious declarations carry a one-line pointer, e.g.
`-- ref: docs/program-model.md` or `-- ref: Brookes CONCUR'04 §5`. Not every line; the ones a
reader would otherwise have to guess at.

## Code style

- **Code is code.** Theory, motivation, rejected alternatives, and comparisons go in `docs/`, not
  in source files. A module gets a short `/-! -/` header saying what it is and where the rationale
  lives.
- Comments are concise and only where needed. No essays, no restating what the code says.
- Prefer proving a lemma over leaving a `sorry`. A `sorry` that survives a session must be
  recorded in `PLAN.md` or a task.

## Commands

```bash
lean Paralever/Core/ParM.lean        # typecheck one file, fast, no deps needed
lake build                           # full build (Mathlib + iris — slow, needs disk)
lake exe cache get                   # fetch Mathlib oleans before a first full build
grep -rn "sorry" Paralever/          # the no-sorry gate
```

Toolchain `leanprover/lean4:v4.32.2`. Disk on `/` is tight (~5 GB) — check before a full build.

## Mathlib import policy

Never `import Mathlib`. Import the specific module a lemma lives in
(e.g. `import Mathlib.Data.List.Fold`), never an umbrella file — see `Paralever/Imports.lean` for
the convention and the modules already anticipated. `Core/` and `Theory/` should need no Mathlib
at all; keep it that way as long as possible so `lean <file>.lean` stays a fast standalone check.

## Dependencies

**iris-lean only**, plus Mathlib. Everything else is ideas, not imports (Velvet, Veil, Loom,
SyDPaCC, lean-smt are read for design, never required).

From iris-lean we take `Iris/BI/*`, `Iris/ProofMode/*`, and `Iris/Algebra/{Heap,GenMap,DFrac}` —
instantiating `Iris.BI` at our own `State → Prop` buys ~35 proof-mode tactics for one `instance`.

Do **not** import `Iris/ProgramLogic/*` or `Iris/HeapLang/*`. Reasons in `PLAN.md`: HeapLang's
`par` is derived from unstructured `fork`, HeapLang is nondeterministic in allocation/prophecies,
it has no arrays, `wp_par` is unary so cannot express equivalence, and that subtree churns weekly.
Read `HeapLang/Lib/{Par,Spawn,Quicksort}` as templates; never depend on them.

## Facts you must not forget

These are load-bearing; violating them silently produces vacuous theorems.

1. **Lean's `Task` cannot host the theorem.** `Task` is a one-field structure with a real body, so
   `(Task.spawn f).get = f ()` holds by `rfl` — parallel and sequential are the same term. `Task`
   is a *compilation target only*; nothing is ever proved about parallelism there.
2. **`par` is our constructor**, which is exactly why the theorem is non-vacuous. Its meaning is
   fixed by `run`, not by Lean.
3. **Independence is Bernstein, not `∗`**: `w₁∩w₂ = w₁∩r₂ = w₂∩r₁ = ∅`. Shared *reads* are
   allowed. Non-negotiable — matmul writes disjoint `C[i*n+j]` but reads overlapping rows/columns,
   so naive disjointness rejects it.
4. **`ParM` is inductive ⇒ only terminating programs exist.** `while true` is unrepresentable.
   Lean 4 has no native coinductive types, so this boundary is fixed, not a TODO.
5. **No `parN` constructor** — `List (ParM α)` is an illegal nested inductive. N-ary parallelism is
   derived from binary `par`, which makes the N-ary theorem a corollary.
6. **Races ↦ absorbing `wrong`** (`run` returns `Option`), per Reynolds' grainless semantics. This
   is what makes the atomic grain irrelevant and keeps racy programs *excluded* rather than
   silently assumed away.

## Anti-vacuity discipline

The main risk in this project is proving something true but empty. Two standing obligations:

- Exhibit racy `p`, `q` in Lean where `par_eq_seq`'s conclusion **fails**, so the hypothesis is
  demonstrably load-bearing.
- Keep the loop-carried-dependence pragma test (`A[i] := A[i-1] + 1`) as a case whose obligation is
  **unprovable**.

Property tests (`Plausible`) should check both directions: equality on random *independent*
programs, and `wrong` on random racy ones.

## Layout

```
Paralever/
  Core/      ParM.lean, Semantics (State, step, Reaches), Access (footprints, Indep)
  Theory/    Decomposition, WellFormedCanonical, Sequentialize (the theorem), Intervals
  Logic/     Tier-2 DCSL-lite (BIInstance, Rules — Hoare triples, frame, par composition)
  Lib/       Compose (bind lemmas), TypedRead, TouchesOnly, Notation, FootprintSimp,
             OpaqueOp (declared footprints for bodies we never read),
             Reduce (Σ-shaped loops with a pure accumulator)
  Pragma/    #parallel_for, #parallel[], ParMap, ArrRef, MapArray
  Compile/   TaskFacts
Examples/    SumArray, Sort, MatMul, MergeSort, DoubleInto, SharedReads, ParMapDemo,
             OpaqueAgents, *Task
Test/        Sanity, AccessSanity
docs/        design rationale (program-model.md, semantics.md, access.md, theory.md,
             opaque-ops.md, reductions.md, ...)
```
