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
lake build                           # full build (Mathlib — slow, needs disk)
lake exe cache get                   # fetch Mathlib oleans before a first full build
grep -rn "sorry" Paralever/          # the no-sorry gate
lake exe paralever --help            # the command line: check, run, autopar, prove, vc, convert
PARALEVER_SMT=path/to/z3 lake exe paralever vc F.prl --solve   # the obligation, via a solver
```

`paralever prove FILE -o OUT.lean` writes a Lean module that re-reads `FILE` while it elaborates
and states what holds of it — `par_seq_eq` when `wfB` accepts, the per-heap equivalence when only
the exact check does, and the two refusals when there is a race. See `docs/cli.md`.

`paralever vc FILE` emits the same independence obligation as SMT-LIB, for what `wfB` refuses
because its footprint is over-approximated. **An external solver's `unsat` is not a Lean proof**, so
it is reported as *discharged by* the named solver and never as proved; a `sat` is recomputed in
Lean before it is believed. No solver is a build dependency. See `docs/smt-vc.md`.

Toolchain `leanprover/lean4:v4.34.0` (see `lean-toolchain`); Mathlib pinned to `v4.34.0`.

Version **`1.34.0`** — our minor is Lean's minor. It is declared once, in `lakefile.toml`, and
`Paralever/Version.lean` reads it from there with `include_str`; never write a version literal
anywhere else. `#guard versionMinor == Lean.version.minor` fails the build if the two drift.

## Surface-syntax tokens are global

A `syntax "foo"` reserves `foo` as a token for the *whole project*, so no declaration anywhere can
then be named `foo`. This has bitten twice: `syntax "r "` broke `Test/NArySpike.lean`, and `mem l`
made `def mem` impossible — the obvious name for a `Layout`. Memory in `Lang/Core/Notation.lean` is now
`[l]`, which reserves nothing. Prefer tokens that already exist (`[`, `%`, `*`) over new keywords.

A *constructor* survives the reservation: `syntax "synchronize" : impStmt` makes `def synchronize`
impossible but leaves `ParProg.synchronize` and `.synchronize` usable, because an identifier carrying
a namespace is lexed as one token. So the keyword is spelled as the user expects and only the bare
name is spent — which is the trade to check before reserving a word.

`print` is the trade taken deliberately: `syntax "print " term : impStmt` reserves it, so the `.prl`
writer in `Lang/Compile/Print.lean` is **`toPrl`**, not `print`. A new keyword costs one bare name;
pick it knowing which one.

## Mathlib import policy

Never `import Mathlib`. Import the specific module a lemma lives in
(e.g. `import Mathlib.Data.List.Fold`), never an umbrella file — see `Paralever/Imports.lean` for
the convention and the modules already anticipated. `Core/` and `Theory/` should need no Mathlib
at all; keep it that way as long as possible so `lean <file>.lean` stays a fast standalone check.

## Dependencies

**Mathlib only.** `ProofWidgets` ships with Mathlib and is imported by `Search/ExplainHtml.lean`
alone — but building it runs `npm clean-install`, so that one module makes node/npm a build
requirement. `Search/Explain.lean` renders the same report with no dependency; see
`docs/race-search.md`. Everything else is ideas, not imports (Iris, Velvet, Veil, Loom, SyDPaCC,
lean-smt, CSLib are read for design, never required). An SMT solver is **optional and external**:
`paralever vc --solve` finds z3 or cvc5 at run time, nothing links against one, and `lake build` is
green on a machine with none.

**No separation-logic library, and that is a decision.** `Logic/Rules.lean` frames with plain `∧`
over `Core/Access.lean`'s own footprints, because a separating conjunction splits the heap into
disjoint domains and `Indep` does not — Bernstein permits two threads to *read* one cell, so `∗` is
strictly narrower than the relation the project is about. A BI instance therefore buys notation and
tactics for an assertion type no theorem here uses. The iris-lean dependency that proved this was
removed once it had; `docs/theory.md` § 8 keeps the finding.

Do **not** depend on a HeapLang-style program logic. HeapLang's `par` is derived from unstructured
`fork`, it is nondeterministic in allocation/prophecies, it has no arrays, and `wp_par` is unary so
cannot express an equivalence. Read `HeapLang/Lib/{Par,Spawn,Quicksort}` as templates; never depend
on them.

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
5. **`par` is N-ary and heterogeneous** — one constructor taking `Childs ParM αs`, a type-indexed
   spine, plus a `Results αs → ParM β` continuation. Binary `parPair` is the two-child case.
   `List (ParM α)` with a constructor-local `α` *is* rejected by the kernel ("nested inductive
   datatypes parameters cannot contain local variables"), which is why the children carry their own
   spine; the type index is what keeps the children's result types static. Consequence: Lean's
   `induction` tactic refuses `ParM`, so every proof uses `ParM.inductionOn` or
   `ParM.mutualInduction` (`Core/ParM.lean`), and the N-ary theorems are proved by induction on the
   children list — the `cons` case is the 2-to-N step.
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
Diag.lean    diagnostics: a code, a span, a reason, and the caret rendering. Its own library,
             below both front ends — see docs/diagnostics.md
Paralever/
  Version.lean  the one version, read out of `lakefile.toml` (`--version`, the Lean-minor guard)
  Core/      ParM.lean, Semantics (State, step, Reaches), Access (footprints, Indep)
  Theory/    Decomposition, WellFormedCanonical, Sequentialize (the theorem), Intervals
  Logic/     Tier-2 DCSL-lite (Rules — Hoare triples, frame, par composition, framed
             with `∧` over footprints rather than with `∗`)
  Lib/       Compose (bind lemmas), TypedRead (Storable α), TouchesOnly, Notation, FootprintSimp,
             ArrRef (array-shaped locations over bare `Loc`, `disjoint_of_range`),
             Loop (the indexed read/write loop validator, proved once, plus `#parallel_for`),
             Block (straight-line IR — footprints computed, not proved),
             OpaqueOp (declared footprints for bodies we never read),
             Reduce (Σ-shaped loops with a pure accumulator),
             Pure (pure↔ParM bridge + faithfulness theorem),
             Render (print a ParM tree — another interpreter, for debugging)
  Kernels/   named parallel shapes, each with its one-shot theorem: Assign (`parEach`,
             `broadcastPar`), Grid (`gridReducePar`), MapArray (`Out[i] := f(In[i])`),
             ParMap (pure chunks — no heap access to bound)
  AutoPar/   the sequential-to-parallel pass: Chain (regrouping lemmas), Plan (the schedule, order
             preserving by construction), Dag (dependence DAG + critical-path bound), Sound
             (rewrite_sound: seq = par, no hypothesis), Rewrite (units, the gate, surface round
             trip) — see docs/autopar-algorithm.md
  Tactic.lean  `paralever_race` (the search on the goal in hand, as the infoview widget) and
             `paralever_check` (the proof routes first, the counterexample second) — see
             docs/race-search.md § In tactic position
  Search/    RaceSearch (race-site scan, schedules, follow_sound, attribution, Prog grammar,
             findWrongGuided — phase 2 aimed by phase 1's conflict locations),
             Explain (the interleaving printed), ExplainHtml (the same as an infoview widget)
  Compile/   TaskFacts, Exec (execTask — runs a program on real threads)
Lang/         the paralever language and the `.prl` file in front of it — see docs/prl.md
  Core/      Prog (the `ParProg` AST, both interpreters, `wfB`, `par_seq_eq`; loadAt/storeAt —
             computed addresses; ifElse + whileAtMost — control flow; synchronize — a barrier
             the parallelizer may not cross; print — output, erased from both interpreters and a
             barrier too, with `dropPrints` and `execPar_dropPrints`, see docs/print.md;
             footprint over-approximated, see docs/block-ir.md),
             Layout (buffers, placement, lifetimes — `Arena.of`, `live_disjoint`),
             Heaps (the general-heap race search: which cells to probe, which values, and the
             two `HeapVerdict`s — see docs/general-heap.md),
             Agree (`AgreeOn` — two programs' outcomes compared on named cells, and
             `agreeOn_of_wfB`, which is `par_seq_eq` on each side plus one run of
             each; what `assert` means. `AgreeParSeq` — the same with the final
             register file, the pair `ParSeqEq` quantifies rather than its heap
             half; what `assertParSeq` means, and the registers compared are
             derived, not named — see docs/equivalence.md),
             Kernels, Cuda, Cost, Exec (real threads), Notation (`[l]` memory, `[A, e]` a
             computed cell, `%n` register, `if`, `while … in`, `synchronize`, `{…} :: "name"` —
             every ParProg constructor has a form, see docs/prl.md § The Lean form), Analysis (dependences, `atoms` — register-closed
             segments, `phases` — split at every barrier, `autoPar`), AutoParSound (the rewrite
             preserves the heap — see docs/autopar.md)
  Compile/   Ast + Parse (`.prl` text; a newline or `;` separates statements), Expand (`def`
             written out at every call site, hygienically — see docs/prl.md § Functions), Lower
             (names, placement, lifetimes, unrolling, `input` consumed → Layout × ParProg; an
             `assert` compiled twice, once per side — see docs/equivalence.md), Input (the
             stdin stream and `File.usesInput` — see docs/prl.md § Input), Print (`.prl` back out,
             the Lean block, ANSI colour)
  Smt/       the independence obligation for an external solver — Ast (SMT-LIB terms and the
             query), Vc (registers substituted away, the symbolic footprint, one query per fork),
             Solve (solver discovery, the answer, and `witness` — a `sat` recomputed in Lean),
             Report (what `vc` prints and the `.smt2` it writes). `unsat` is *discharged by* a
             solver, never proved — see docs/smt-vc.md
  Load.lean    `prl_file` — read and compile a file while Lean elaborates
  Verdict.lean the two-part verdict both reports print — `this heap` and `any heap`, so `check`
               and `vc` cannot disagree
  Report.lean  the `#eval` views: check, run, race, autoparallelize, and what `print` wrote
MLIR/        the other front end: Ast + Parse (MLIR generic form), Pretty (MLIR custom form —
             `affine.for %i = 0 to 8`, desugared to the generic `Op`; `parseAny` picks the reader,
             `parseFunctions` reads one function of twenty — see docs/mlir-pretty.md),
             Affine (map evaluation),
             Lower (Mlir.Op → Layout × ParProg, the verdict path, over Int),
             Eval (the same program over ℚ, the reference for differential execution),
             Load (`mlir_prog` — quote the lowered program at elaboration time, as `prl_file` does),
             Emit (generic form out: a buffer is a memref.global, a fork a group of async.execute
             ops closed by the await that names their tokens; `emitRoundTrips` compares memory,
             footprint, verdict and heap, not the tree — registers are not SSA values),
             Corpus (the seven labelled pilots in Examples/Mlir/*.mlir, as #guard gates, each
             race-free one carrying its `par_seq_eq` instance, plus the two custom-form pilots
             gated against their generic twins)
             — see docs/mlir.md
Examples/    every demonstrable thing in one tree, with the .prl and .mlir sources beside the
             Lean that reads them — see Examples/README.md. No module docstring headers here
             (deliberate: the README is the map).
  Tour.lean    the whole project on one program: write, check, prove, break, autoparallelize
  Programs/    the method on real algorithms — SharedReads, MapArray, SumArray, RowSums,
               CompareSwap, MergeSort, MatMul, SortBatches, OpaqueAgents, Pipeline
  Language/    the *.prl files, plus Files (ten read by `prl_file`, branch.prl among them
               — the `Inconclusive` witness), Writing, ControlFlow, Scatter, Stripe, NeuralNet,
               Functions (def), Equivalence (assert: equiv.prl and twofold.prl),
               Input (input.prl, which reads the shell, so Lean compiles it from text with the
               stream supplied)
  Mlir/        the seven *.mlir pilots, plus Files (one lowered end to end, and the corpus report)
  Scale/       matmul12.prl and the 14,451-line matmul12.mlir it emits — the command line's
               ceiling, measured; no Lean module reads it (see docs/mlir.md § Scale)
  AutoPar/     Pass — the parallelizing pass on chain.prl, every step evaluated
  Races/       Caught (the conclusion fails), Report (reading a counterexample), Pointers
  Threads/     RealThreads — a ParM tree on real Tasks
  BlogSnippets.lean  the code the blog post quotes, by ANCHOR region
Tool/        the `paralever` command line, as a lib (not `Cli`: Mathlib depends on a package of
             that name) — Run (the commands, the option grammar, reading either front end),
             Proof (the Lean module `prove` writes, and which of the three theorems it carries)
             — see docs/cli.md
Bench/       the evaluation harness as a lib plus the `paralever-bench` exe — Manifest (the corpus
             as data: 19 .prl + the 9 MLIR pilots, each with two labels and a justification),
             Verdict (the taxonomy and the matrices, called *by* MLIR/Corpus.lean), Run (one kernel
             → a Row, every number from code that already exists), Time (the only IO.monoMsNow in
             the repo), Scale (the rolled-against-unrolled cost curve: two texts per size, written
             and elaborated), Report — see docs/bench.md
Test/        Sanity, AccessSanity, RaceSearch, Lang, Tool, Tactic, Heaps (the general-heap
             search and the two-part verdict), Print (the surface, the erasure, and that the
             output walk leaves the heap the interpreter does), Smt (what the VC decides in
             Lean, what is left for a solver, and that the gap it closes is real — no guard runs a
             solver), Diag (the code registry and
             the rendered caret, with every code reached from a .prl file), LeanForm (three .prl
             files written by hand in Lean and gated against the compiled file), Stress (shapes
             generated as text, each gated against a closed form — see docs/scale.md)
docs/        design rationale (program-model.md, semantics.md, access.md, theory.md,
             general-heap.md, print.md,
             opaque-ops.md, reductions.md, pure-bridge.md, block-ir.md, strings.md, smt-vc.md,
             diagnostics.md, race-search.md, layout.md, autopar.md, equivalence.md,
             mlir.md, scale.md, website.md, ...)
index.html   the published site's cover; `web/` its pages, `slides/` the deck
web/         concept, language, autopar, races, mlir, cli, lean + css/site.css,
             js/site.js, snippets/ (the 22 verso-snippets files) and
             build-snippets.sh — hand-written static HTML, no generator; the
             theme is *linked* from anirudhg07.github.io, never copied. site.js
             renders the top bar (the main site's own, re-linked), the left
             sidebar and the footer: a new page is one HTML file plus one row in
             `PAGES`. **Every Lean block is a verso-snippets embed** of an
             `-- ANCHOR: site-…` region of a real module, never highlighted
             text. Every figure is HTML or inline SVG (`.dgm`), never monospace
             art. See docs/website.md
```
