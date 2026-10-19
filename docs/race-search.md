# Searching for the counterexample, and reading it

`wellFormedB p σ = false` says a program has a race. This is how the library turns that `false`
into an execution a reader can inspect: which `par` node failed, which interleaving realizes the
failure, and what the sequential counterpart would have produced instead.

Code: `Paralever/Search/RaceSearch.lean` (the search) and `Paralever/Search/Explain.lean` (the
report). Demo: `Examples/RaceReport.lean`.

Two entry points. `explainProg` takes a `Prog` — the first-order grammar the search generates and
shrinks over. `explainParM fuel p pseq σ ls` takes any `ParM` together with its sequential
counterpart and the locations to print, so a `ParProg` explains itself through `execPar`/`execSeq`:
that is the case a user hits, when `wfB` returns `false` and the question is why.

## Two phases

```text
        p, σ
          │
          ▼
  ┌───────────────────┐   raceSites        linear in the tree
  │ phase 1 · scan    │  ────────────►  [RaceSite]   (par nodes failing Bernstein)
  └───────────────────┘                     │
          │ empty?                          │ non-empty: which locations conflict
          │                                 ▼
          │                        ┌───────────────────┐  findWrongGuided
          ▼                        │ phase 2 · search  │ ────────────►  Schedule
   WellFormed holds                └───────────────────┘                   │
   (raceSites_nil_iff)             aimed at those locations                 ▼
   nothing to search for                                            follow_sound
                                                                           │
                                                                           ▼
                                                                    Reaches c wrong

Phase 1's output is not just a yes/no: it names the locations. Phase 2 uses them, which is the
difference between a linear walk and an exponential one (below).
```

The split is Sen's RaceFuzzer (PLDI'08): a cheap imprecise scan proposes candidate racing pairs,
then a search tries to realize one. Here the scan is *exactly* the obligation, which is the
difference that matters — see the next section.

## The algorithm

Three pieces: the step relation both phases are defined against, the scan, and the search.

### The step relation

Everything rests on `step` checking for a conflict *before* letting anyone move. Race detection is
therefore instantaneous, not retrospective — which is what keeps the search cheap on racy programs.

```text
conflict(a, b)   =  loc(a) == loc(b)  &&  (isWrite(a) || isWrite(b))   # no read/read clause

nextAccs(pure _)       = []                      # the actions a thread could do NEXT
nextAccs(read l _)     = [read l]
nextAccs(write l _ _)  = [write l]
nextAccs(par cs _)     = concat(nextAccs(c) for c in cs)   # recurses through nested forks

stepC(wrong)      = []                           # terminal and absorbing
stepC(run p σ)    = step(p, σ)

step(pure _,      σ) = []                                        # terminal
step(read l k,    σ) = [ run (k (σ l))  σ ]
step(write l v k, σ) = [ run (k ())     σ[l := v] ]
step(par cs k,    σ) =
    groups = [ nextAccs(c) for c in cs ]                         # one group per child
    if any two distinct groups contain a conflicting pair:
        return [ wrong ]                                         # detected, this instant
    if every c in cs is pure:
        return [ run (k results(cs)) σ ]                          # join
    return concat over j, child in enumerate(cs):                 # every ready child, in order
             [ run (par (cs with j := p') k) σ'  for (p', σ') in step(child, σ) ]
```

The list `step` returns *is* the nondeterminism: one entry per thread that could move. A `Schedule`
is a list of indices into it, and `follow` replays one:

```text
follow(c, [])     = c
follow(c, i :: s) = if i < len(stepC(c)) then follow(stepC(c)[i], s) else FAIL
```

### Phase 1 — the scan

Walk the tree against a heap. At each fork, measure each child's footprint along the canonical
(left-to-right) run and test Bernstein against everything after it; then recurse into the children
and past the join.

```text
bernstein(a, b) = disjoint(a.writes, b.writes)
               && disjoint(a.writes, b.reads)
               && disjoint(b.writes, a.reads)     # three clauses, not four

raceSites(p, σ):
    match p:
      pure _      -> []
      read l k    -> raceSites(k (σ l), σ)                 # follow the value the run produces
      write l v k -> raceSites(k (), σ[l := v])
      par cs k    ->
          sites = [] ;  σ' = σ
          for j, child in enumerate(cs):                   # each child vs. all the later ones
              f    = accesses(child, σ')
              rest = accesses(cs[j+1 ..], σ')               # the tail, as one footprint
              if not bernstein(f, rest):
                  sites += [ RaceSite(f, rest, witnesses(f, rest)) ]
              σ' = runSeq(child, σ').heap                   # next child starts where this ended
          (results, σ'') = runChilds(cs, σ)
          return sites
              ++ concat(raceSites(child, ·) for child in cs)     # forks nested inside a child
              ++ raceSites(k results, σ'')                       # and everything after the join
```

Each child against *the tail as a whole* rather than against each later child one at a time is what
makes this one `IndepAll` obligation instead of `n(n-1)/2` of them; `sitesOfChilds_nil_iff` is the
proof that the two agree.

### Phase 2 — the search

A bounded depth-first walk, with a one-step lookahead so a detected race is returned as soon as it
is reachable in one move.

```text
findWrong(fuel, c):
    if fuel == 0: return NONE                     # NOT "no race" — "not found this deep"
    succs = stepC(c)
    if some i has succs[i] == wrong:
        return [i]                                # one-step lookahead
    for i, c' in enumerate(succs):                # depth-first, left to right
        s = findWrong(fuel - 1, c')
        if s != NONE: return [i] ++ s
    return NONE
```

`fuel` is `Prog.stepBound`: one per memory action plus one per fork join, which is exactly a full
run's length. `size` alone is too small and misses a race behind a long prefix.

### Phase 2, aimed by phase 1

Left-to-right is the worst possible order. A race needs two threads poised at conflicting accesses
*at the same instant*, and the one move that destroys that position is letting a thread execute its
conflicting access and run on — which is exactly what `findWrong` does first. It drives child 0
through its access, finds nothing, and then backs up one step at a time until the two sides happen
to line up.

Phase 1 already says which locations conflict, so the fix is to try those moves *last*:

```text
targetsOf(sites) = dedup(concat(s.conflicts for s in sites))      # what phase 1 flagged

consumesTarget(p, σ, targets, i) =                  # does successor i give up the position?
    match attribution(p, σ, i).action:
      some a -> a.loc in targets
      none   -> false                               # a join consumes nothing

findWrongGuided(targets, fuel, c):
    if fuel == 0: return NONE
    succs = stepC(c)
    if some i has succs[i] == wrong: return [i]
    hold = [ i for i in indices(succs) if consumesTarget(..., i) ]
    for i in (indices(succs) \ hold) ++ hold:        # non-consuming moves first, order preserved
        s = findWrongGuided(targets, fuel - 1, succs[i])
        if s != NONE: return [i] ++ s
    return NONE

findWrongFrom(fuel, p, σ):                           # the entry point: phase 1, then phase 2
    sites = raceSites(p, σ)
    if sites == []: return NONE                      # raceSites_nil_iff — do not even look
    return findWrongGuided(targetsOf(sites), fuel, run p σ)
```

Each thread now advances freely until its next action is a flagged one and stops there; once two
threads are stopped, `step` reports the race itself and the one-step lookahead returns it. No
backtracking on any program we have measured.

This is a **reordering, not a restriction** — every successor is still visited, so nothing becomes
unfindable, and the result is still a `Schedule` that `follow` checks. `Test/RaceSearch.lean`
`#guard`s that the two searches agree on every tree of depth ≤ 2 and that every schedule the aimed
search returns really reaches `wrong`, with the same two checks repeated on random trees.

### Reading an index back

The search returns indices; `attribution` turns one into a thread by inverting the concatenation
`step` built it with.

```text
attribution(p, σ, i):
    match p:
      read l _    -> (path = [],  action = read l)
      write l _ _ -> (path = [],  action = write l)
      pure _      -> (path = [],  action = none)
      par cs k    ->
          if any two groups conflict:  return (path = [], abort = groups(cs))
          if every child is pure:      return (path = [], action = join)       # a join
          for j, child in enumerate(cs):
              w = len(step(child, σ))               # this child's slice of the successor list
              if i < w:
                  (sub, act) = attribution(child, σ, i)
                  return (path = [j] ++ sub, action = act)
              i -= w                                # not this child's; shift into the next slice
```

The `path` is why a nested race is reported at the fork that aborted: the recursion descends to the
node that actually produced the `wrong`, and `groups(cs)` there is literally the argument the
conflict check rejected.

## Phase 1 is complete for the obligation

`raceSites p σ` walks the tree and collects every `par` node whose children fail Bernstein, with
the locations witnessing each failure. It is not a heuristic:

```lean
theorem raceSites_nil_iff (p : ParM τ) (σ : State) :
    raceSites p σ = [] ↔ WellFormed p σ
```

So an empty result *is* the well-formedness proof, and a non-empty result is a real failure of the
hypothesis `par_seq_eq` needs — never a warning to triage. Two consequences the report relies on:

- `wellFormedB` is just `(raceSites p σ).isEmpty`, and it is linear in the program.
- On a clean program, phase 2 is guaranteed to return `none`, so `explainParM` **does not run it**.
  That matters: phase 2 on a clean program is the one exponential case (below).

## The search is untrusted; its answer is checked

`findWrong` is a bounded depth-first walk of `stepC`. It may return anything, or give up. What it
returns is a `Schedule = List Nat` — at each step, which successor to take — and

```lean
theorem follow_sound (s : Schedule) (c c' : Conf τ) : follow c s = some c' → Reaches c c'
```

turns any schedule that replays successfully into a `Reaches` proof. So a found counterexample is
*checked*, never believed, and the search's heuristics cannot make a false claim: at worst it fails
to find something.

## Reading a step back: thread attribution

A `Schedule` is a list of indices into `stepC`'s successor list. That is enough to replay, and not
enough to read. `Explain.attribution` recovers the rest by inverting the one concatenation that
produced the list.

`step` on `.par cs k` is

```text
  step (.par cs k) σ  =  (stepChilds cs σ).map (…)

  stepChilds (cons p ps) σ  =  (step p σ).map (…)  ++  (stepChilds ps σ).map (…)
                               └──── width w ────┘
```

so index `i` belongs to child `0` when `i < w`, and otherwise to `stepChilds ps σ` at index
`i - w`. `attributionChilds` subtracts widths left to right and prepends the child index it
stopped at; `attribution` recurses into that child, so the result is a *path* and nesting is
visible. A path is printed `T1.0`: child `1` of the root fork, child `0` of that.

Three cases produce no action:

| `step` case | `attribution` returns | printed |
|---|---|---|
| `racingAll` holds at this node | the node's path, and its children's ready actions | the race banner |
| `allPure cs` | the node's path, nothing else | `join` |
| child contributes a real action | path to the leaf, the `Label` | `write [5] ← 9` |

Because the abort case carries the *path*, a race nested three forks deep is reported at the fork
that aborted, not at the root. The ready-action groups it carries are literally the argument
`racingAll` rejected, so the banner names the conflicting children and the witnessing locations
without re-deriving anything.

Values are read off the heaps the real run produces: a read shows `σ l` in its pre-state, a write
shows `σ' l` in its post-state. `Label` deliberately drops values (races do not depend on them), so
there is nowhere else they could come from.

## What the report looks like

A counterexample is an execution, so the report is one: every action that ran, then the two that
could not, then what the sequential run leaves instead. `explainProg late σ0` on

```lean
def late : Prog :=
  .par (.seq (.wr 10 1) (.wr 9 1)) (.seq (.wr 20 1) (.wr 9 2))
```

prints

```text
step:thread  action          state
0:T0         write [10] ← 1  10↦1, 9↦0, 20↦0
1:T1         write [20] ← 1  10↦1, 9↦0, 20↦1
2:T1         write [9] ← 2   pending
2:T0         write [9] ← 1   pending
Parallel aborts at Step 2. Reason: T0, T1 write to: {9}.
Parallel: 9↦1
Sequential: 9↦2
```

Four things are doing work here.

**`step:thread` rather than a column per thread.** A column per thread costs ~19 characters, so six
threads need 115 — wider than a pane shows. An identifier costs nothing and says the same, and it
is how a parallel execution is normally written.

**Two threads share step 2.** That is not a formatting accident: `racingAll` rejects the pair for
being ready at the *same instant*, so the two actions genuinely belong to one step. Nothing else in
the trace has two rows at one number, which is what makes the clash visible at a glance.

**The clashing actions are shown, with their values.** `write [9] ← 2` against `write [9] ← 1` *is*
the contradiction; `Reason: T0, T1 write to: {9}` only summarises it. Getting the values back needed
`pendingOf`/`pendingChilds`, which mirror `nextAccs`/`nextAccsChilds` exactly but keep a write's
value — `Label` drops it on purpose, because a race does not depend on it
(`Core/Semantics.lean`). Those are the labels the check ranged over, not a re-derivation.

**The order is chosen because it disagrees, not because it is reversed.** The two actions are
simultaneous and unordered, so their *listing* order is a presentation choice — but child order is
what `seqPair` runs, so listing them that way reproduces the sequential outcome and makes the race
look harmless (`← 1` then `← 2` leaves `2`, exactly what `Sequential` shows). `divergingOrder` runs
each candidate ordering with `runPending` and picks the first whose **observable** differs from child
order, so the rows a reader follows really do land somewhere else. Nothing in the semantics picks an
order: the run aborts rather than choosing, which is the point of `wrong` being absorbing.

**`Parallel` against `Sequential`, over the conflicting cells only.** The rest of the heap is not in
question, and the aborted run has no final state to compare, so the two lines show what the clashing
actions leave under the displayed order and under child order. For the race above that is `9↦1`
against `9↦2`.

`pending` marks an action that never executed, so there is no state to show for it. The abort is the
line below, outside the rows.

`write to` is used only when no read is involved; a read against a write prints `access`, since
Bernstein has no `R∩R` clause and a read/write pair is still a race:

```text
2:T1         write [9] ← 2  pending
2:T0         read [9]       pending
Parallel aborts at Step 2. Reason: T0, T1 access: {9}.
Parallel: 9↦2, T0 reads 2
Sequential: 9↦2, T0 reads 0
```

This is why `runPending` reports read observations and not just the heap. A read-after-write race
leaves the **same heap** whichever order the two take — `9↦2` either way — and diverges only in what
`T0` observes. A heap comparison alone would call it harmless; the read observation is what makes it
a counterexample. `Search/ExplainHtml.lean`'s `raw` example is this case as a widget.

A race between grandchildren is attributed to them, not to the fork above:

```text
0:main       write [1] ← 1  1↦1, 2↦0, 3↦0, 7↦0, 4↦0
1:T0         write [2] ← 2  1↦1, 2↦2, 3↦0, 7↦0, 4↦0
2:T1.0       read [3] → 0   1↦1, 2↦2, 3↦0, 7↦0, 4↦0
3:T1.1       read [4] → 0   1↦1, 2↦2, 3↦0, 7↦0, 4↦0
4:T1.1       write [7] ← 2  pending
4:T1.0       write [7] ← 1  pending
Parallel aborts at Step 4. Reason: T1.0, T1.1 write to: {7}.
Sequential: 1↦1, 2↦2, 3↦0, 7↦2, 4↦0
```

The difference from the sequential run is not a heap diff, and cannot be: `wrong` is terminal and
absorbing (Reynolds FSTTCS'04), so the parallel program has *no* final heap while the sequential one
leaves `7↦2`. Racy programs are excluded, not given a behaviour.

A clean program has nothing to show:

```text
No counterexample: no par node fails Bernstein.
Sequential: 0↦0, 1↦1, 2↦2
```

### Long runs

A thousand-step trace is a thousand rows, and a counterexample's information is at its end. So
`stepItems` keeps the first `head` steps and the last `tail` (5 and 14 by default) and collapses the
middle into a count with the per-thread split:

```text
4:T0         write [1003] ← 1  …
⋮            104 steps elided (T0 ×56, T1 ×48)
109:T1       write [90047] ← 1  …
```

Location sets, the state column and the schedule all clip with `+N more` for the same reason.

## One model, two renderers

`reportOf` builds a `Report`. The model is *structured*, not pre-formatted — a step knows its
thread, its action and its cells, and a cell knows whether that step changed it:

```lean
structure Cell where
  loc     : String
  value   : String
  changed : Bool

structure Step where
  time   : Nat
  thread : String
  action : String
  state  : List Cell

inductive Item where
  | step   : Step → Item
  | elided : Nat → List (String × Nat) → Item
  | abort  : Nat → String → Item
  | line   : String → String → Item
  | note   : String → Item
```

That shape is what lets the two renderers differ in presentation without differing in content.
`Search/Explain.lean`'s `renderText` flattens it into padded columns — one row per step, `-` for an
idle thread, the cells joined with `, `. `Search/ExplainHtml.lean`'s `renderHtml` gives each step a
card: the time, a chip for the thread that moved, its action, and the heap below with the changed
cell picked out. The abort becomes a card with an error outline and an `ABORTS` badge.

```text
┌──────────────────────────────────────────────────────┐
│ STEP 0   THREAD (T0)   ACTION write [10] ← 1         │
├──────────────────────────────────────────────────────┤
│ STATE   ▌10 ↦ 1    9 ↦ 0    20 ↦ 0                   │   ▌ = changed this step
└──────────────────────────────────────────────────────┘
╔══════════════════════════════════════════════════════╗
║ STEP 2   THREAD (T0)   ACTION write [9] ← 1          ║   error accent
╠══════════════════════════════════════════════════════╣
║ ✗  never executed: ready at this step                ║
╚══════════════════════════════════════════════════════╝
╔══════════════════════════════════════════════════════╗
║ STEP 2   THREAD (T1)   ACTION write [9] ← 2          ║
╠══════════════════════════════════════════════════════╣
║ ✗  never executed: ready at this step                ║
╚══════════════════════════════════════════════════════╝
  Parallel aborts at Step 2. Reason: T0, T1 write to: {9}.
 PARALLEL    9 ↦ 1
 SEQUENTIAL  9 ↦ 2
```

Each field carries a small muted label, so there is no guessing which part is the step, which the
thread and which the heap. The two clashing actions are cards like any other, at the same step
number and with their values, carrying `pv-pending` for the error accent — the verdict is the line
below them, not a badge inside one.

Neither file builds any content of its own, which is the point: before this split the two produced
the same report in different words and drifted apart.

### Styling is inline, and that is forced

ProofWidgets renders a text node as `<>{text}</>` — a React *Fragment* — and passes an element's
children as an array (`widget/src/htmlDisplay.tsx`). A `<style>` element therefore receives an
element child where React needs a string, and the stylesheet is **silently dropped**: the report
renders as unstyled stacked text, which is exactly how it first looked. Veil's trace widget
(`verse-lab/veil`, `widget/src/traceDisplay.tsx`) can inject a `<style>` because it is hand-written
TSX; through the generic `Html` tree it cannot.

So each rule is a named `Json` object applied as a `style` attribute — `card`, `pill`, `sHead`,
`sBody`, `cellStyle`, `sAbort` in `ExplainHtml.lean`. Colours stay `--vscode-*` theme variables with
fallbacks (`--vscode-panel-border`, `--vscode-editorWidget-background`,
`--vscode-activityBarBadge-background`, `--vscode-editor-findMatchHighlightBackground`,
`--vscode-inputValidation-errorBorder`), so a report follows the editor's theme rather than imposing
one. `className` is set as well: it carries no weight, but it names the parts and is what the
`#guard_msgs` examples check.

```text
 (0:T0)  write [10] ← 1
         STATE  ▌10 ↦ 1   9 ↦ 0   20 ↦ 0        ▌ = changed this step
 (1:T1)  write [20] ← 1
         STATE   10 ↦ 1   9 ↦ 0  ▌20 ↦ 1
 (2:T1)  write [9] ← 2                          ┐ red border
         STATE   10 ↦ 1   9 ↦ 0   20 ↦ 1        ┘ nothing marked: it did not run
 (2:T0)  write [9] ← 1                          ┐ red border
         STATE   10 ↦ 1   9 ↦ 0   20 ↦ 1        ┘
 Parallel aborts at Step 2. Reason: T0, T1 write to: {9}.
 PARALLEL    9 ↦ 1
 SEQUENTIAL  9 ↦ 2
```

Every card has the same shape — pill, action, heap — because a pending step *is* an ordinary step
that happens not to have run. It carries the heap as it stands at that instant, with no cell marked,
since neither action took effect. The red border is the only difference, and the verdict is the line
below. The widget is shown by `#race p σ` (or `#html explainHtmlParM …`), and
*only* by those: a `#html` command saves a panel the infoview draws when the cursor is on it, and
produces no message. A file that only `#eval`s `htmlText` shows text and no widget, however correct
the tree is.

`htmlText`, `htmlTags` and `htmlClasses` walk a rendered tree, since `Html` has no `Repr`. The
`#guard_msgs` examples pin the content (identical to the text report's, cell for cell), the parts
that carry meaning (`pv-card pv-pending` on each clashing action, `pv-cell pv-changed` on exactly
the cell each step wrote), that no `<style>` element is emitted, and the item shape of the shared
report.

Building ProofWidgets runs `npm clean-install`, so that module makes node and npm a build
requirement; the bundled JS is then embedded in the olean by `include_str`. `Explain.lean` has no
such dependency.

## Scaling

Measured with `lake env lean`, `σ0 = fun _ => .int 0`, elapsed time around a forced computation.
Generators: `side base m` is `m` writes in sequence; `lateRace m` forks two sides that collide only
on their last write; `three m` forks three, where the middle one is innocent; `cleanPar m` forks two
that never collide.

**Aiming the search.** Same programs, blind `findWrong` against `findWrongFrom`:

| program | steps | blind | aimed |
|---|---|---|---|
| `lateRace 200` | 405 | 257 ms | 82 ms |
| `lateRace 500` | 1005 | 3.5 s | 494 ms |
| `three 8` | 31 | 2.7 s | **2 ms** |
| `three 20` | 67 | — | 5 ms |
| `three 60` | 187 | — | 34 ms |

`three` is the case that matters. Blind, an innocent third thread multiplies the backtracking and
the cost grows about 14× per two writes added to each side — 2.7 s at eight writes, hopeless at
twenty. Aimed, it is 34 ms at sixty, because there is no backtracking left to multiply: the innocent
thread's moves are never flagged, so it runs whenever it is reached, and the two guilty threads stop
at their conflicting writes.

What remains in `lateRace 500` is not search but program shape: `Prog.seq` lowers to left-nested
`bind`, so reaching the head of a 500-deep chain is `O(m)` per step and the whole walk is `O(m²)`.

**The scan.** Linear in the number of forks, quadratic in accesses:

| `m` | steps | phase 1 |
|---|---|---|
| 50 | 105 | 2 ms |
| 100 | 205 | 9 ms |
| 200 | 405 | 35 ms |
| 500 | 1005 | 216 ms |

The quadratic term is the footprint representation: `Footprint` holds `List Loc` and
`conflictsWith` uses `List.contains`, so a scan over `n` accesses does `O(n²)` membership tests.
Lists are deliberate — every use elsewhere is a `decide`-able membership or disjointness check
(`docs/access.md`) — so this is a cost of the representation, not a defect in the search.

**The clean case** is what neither phase 2 variant can answer by searching, since every path must
fail before `NONE` comes back:

| `m` | steps | phase 2 alone |
|---|---|---|
| 10 | 23 | 5.6 s |
| 11 | 25 | 21 s |
| 12 | 27 | > 60 s |

`C(2m, m)` interleavings. Guidance does not help here and cannot: there are no conflict locations to
aim at. It is also never paid — `findWrongFrom` returns `none` on an empty scan without searching,
which `raceSites_nil_iff` justifies rather than merely excuses. A clean program costs the scan and
the printing:

| `m` | steps | phase 1 | whole report |
|---|---|---|---|
| 50 | 103 | 3 ms | 7 ms |
| 200 | 403 | 36 ms | 87 ms |
| 500 | 1003 | 215 ms | 540 ms |
| 1000 | 2003 | 887 ms | 2.2 s |

## Limits

- **`Prog` has no conditionals**, so the two-differing-heaps report is unreachable from `Prog`:
  every racy `Prog` we have run has an aborting schedule. The reason is structural rather than
  accidental — the scheduler can advance each side independently to the instant before its
  conflicting action, at which point both actions are ready and `racingAll` fires — but this is an
  argument, not a theorem, and it is not proved anywhere in the library. `findDivergence` is kept
  because `explainParM` accepts hand-written `ParM` programs, where a continuation can branch on a
  value and the two sides' conflicting actions need not ever be ready together.
- **The report is per-heap.** `raceSites p σ` measures footprints along the canonical run from `σ`,
  so a report is a statement about that heap. `WellFormed` is likewise `State`-indexed; see
  `docs/access.md`.
- **`findWrong`'s `none` is not a proof.** Phase 1 is what proves race-freedom
  (`wellFormedB_iff`); phase 2 only ever provides evidence of failure.
