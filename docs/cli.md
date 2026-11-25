# The `paralever` command line

One file in, and one of four things out: a verdict, a run, a parallelization, or **a Lean file that
proves the program's parallel reading equals its sequential one**. The last is the point of the
tool. A checker that prints `race-free` is a linter, and you believe it or you do not; a tool that
writes a module Lean then checks is different in kind, because the claim leaves with its proof
attached. Name a file and no command and the tool answers the question a file arrives with — is
this program race-free, and if so what holds of it — which is `check` followed by the evidence
either way.

```bash
lake build paralever                      # ./.lake/build/bin/paralever
paralever         Examples/Language/sum.prl    # the verdict, and the evidence for it
paralever check   Examples/Language/sum.prl
paralever prove   Examples/Language/sum.prl -o Proofs/Sum.lean --typecheck
paralever to-mlir Examples/Language/sum.prl -o sum.mlir
paralever to-prl  Examples/Mlir/doall-no.mlir
```

Code: `Tool/Run.lean` (the commands), `Tool/Proof.lean` (the generated module). Gates:
`Test/Tool.lean`.

## Both front ends, one program

Every command takes a `.prl` file or a `.mlir` module in generic form, because both compile to the
same pair — a `Layout` saying where the buffers are, and an unrolled `ParProg`:

```text
      sum.prl ──► Lang.Compile ──┐                    ┌──► ⟨none⟩    the verdict, with evidence
                                ├──► Layout × ParProg ──┼──► check     the verdict
doall-no.mlir ──► MLIR.Lower ───┘                       ├──► run       the heap it leaves
                                                        ├──► autopar   the parallelized .prl
                                                        ├──► prove     a .lean file
                                                        └──► to-prl / to-mlir / to-lean
```

Which front end the file came through matters in exactly one place: the generated proof module has
to read the source again, so it names it with `prl_file` or with `mlir_prog`. Everything else is
written once.

## The commands

| command | what it prints | from |
|---|---|---|
| `init [DIR]` | a Lake project with paralever as its dependency, and a program in it | `Tool.Init.files` |
| `FILE` (no command) | `check`'s report, then what `print` wrote, then the interleaving if there is one | `Lang.checkReport`, `Lang.outReport` |
| `check FILE` | memory, reads, writes, thread count, rounds, verdict | `Lang.checkReport` |
| `run FILE [--buffer NAME]` | what `print` wrote, then the heap after a run, buffer by buffer, or one buffer of it | `Tool.runBody`, `Lang.runCell` |
| `run FILE --run-again N` | N runs under random schedules, grouped by the outcome each left | `Lang.interleaveReport` |
| `race FILE` | the interleaving that reaches `wrong`, step by step | `Lang.raceReport` |
| `autopar FILE` | the parallelized program as `.prl`, with the plan's numbers | `Lang.parReport` |
| `funcs FILE` | what an MLIR module holds, function by function, and whether the reader takes each | `Tool.funcsReport` |
| `prove FILE` | a Lean module stating what holds of the program | `Tool.proofFile` |
| `vc FILE` | the independence obligation as SMT-LIB, for a solver to discharge | `Smt.vcReport`, `Smt.smtFile` |
| `to-prl FILE` | the program as `.prl` | `Lang.print` |
| `to-mlir FILE` | the program as MLIR generic form | `MLIR.emitText` |
| `to-lean FILE` | a `Layout` and a `paralever { … }` block | `Lang.toLean` |
| `explain CODE` | what a diagnostic code means, and why the rule exists | `Diag.explain` |

`-o PATH` writes there instead of to standard output. `--real-threads` runs one `Task` per thread of
every fork rather than the canonical order — the heap is the same one, which is what `runTask_eq`
says for every program `wfB` accepts. `--run-again N` (`-ra N`) is the opposite knob: it runs the
program N times under *randomly chosen* schedules and groups the runs by outcome, so the schedule
dependence a program does or does not have becomes visible (`docs/interleave.md`). The two refuse to
combine, because a `Task`'s order is the runtime's to pick and not the tool's. `--autopar` makes `prove`, `to-mlir` and `to-lean` take the
parallelized program as their subject. `--color` paints `to-prl`'s output in the editor grammar's
token classes, and `--html` writes those same classes as `<span>` elements for a page or a deck to
style. Both are folds over one token scan in `Lang/Compile/Print.lean` (`prlTokens`), so the two
renderings can never disagree about where a token begins; `cssClass` there fixes the class names. `to-lean` writes a snippet rather than a module, so it carries no header: pasting it
needs `import Lang.Core.Notation`, `import Lang.Core.Layout` and `open Paralever Paralever.Lang`.
With those three lines every example's Lean form elaborates except a rolled nest, which has no
surface syntax yet and prints in the library's own vocabulary (`docs/loops.md`). The block is one
statement per line, two spaces per level, each line ending in the `;` the notation's
`sepBy1(impStmt, "; ")` requires — Lean's tokenizer does not see a line break, so without the
separator `%0 := 0` followed by `%1 := [0]` would read `0 % 1` as modulo. `docs/prl.md` § *The Lean
form* has the table. `--prove PATH` is for the no-command form: the verdict goes to standard output
and the Lean module that proves it goes to `PATH`, so one invocation gives both the answer and its
proof. With `--typecheck` as well, Lean's verdict on that module is the exit code. `--func NAME` names
the function to read in an MLIR module that holds several — a real test file holds twenty — and in
custom form it reads *that* function alone, so a reduction in the next one does not refuse the
file (`docs/mlir-pretty.md`). `--buffer NAME` is for `run`: it prints that buffer alone, or one cell of
it when the name carries a subscript, and `--full` prints every cell of every buffer instead of
the first 32 of each. `--quiet` (`-q`) and `--verbose` (`-v`) are the verbosity knob, described
below.

`--json` is for `check`: the same facts as one JSON object, built by `Tool.checkJson` from the
values `checkReport` already computes, so the two cannot disagree. It is refused on the other
commands rather than ignored.

### `--time`

`--time` adds a `time:` line to any command, and `race` prints one whether or not it was asked for.
The figure is **processor** time, not the wall clock: the two differ whenever the machine is busy,
and under `--real-threads` processor time exceeds wall time because it sums across threads.

Lean has no CPU clock. `IO.monoMsNow` and `IO.monoNanosNow` are monotonic clocks whose own
docstrings say they bear no relation to wall clock time, and the toolchain binds neither `clock`
nor `getrusage`. So `Tool.cpuMs` reads `/proc/self/stat`, whose fourteenth and fifteenth fields are
the process's user and system time in ticks, parsing after the *last* `)` because the second field
is the executable's name and may hold parentheses of its own. Where there is no `/proc` the wall
clock answers instead and the line says `(wall)`, which is the whole disclosure. A C stub around
`clock()` would be portable and would make this project's build need a C target for the first time,
which is not a trade worth making for a timing line.

`--version` prints the package, its version and the toolchain — `paralever 1.34.0
(leanprover/lean4:4.34.0)`. The version is declared once, in `lakefile.toml`, and
`Paralever/Version.lean` reads it from there with `include_str` rather than restating it. Its minor
number is Lean's own, which `#guard versionMinor == Lean.version.minor` enforces at build time: a
`1.34.x` release can only be built on a `v4.34.x` toolchain, and moving one forces the other.

### Exit codes

| code | means |
|---|---|
| 0 | the program is sound, or the command had nothing to decide |
| 1 | the program fails: a race, a claim that does not hold, a module Lean rejects |
| 2 | the invocation is wrong, or a file cannot be read |

`check` and the no-command form are therefore the gate a build wants:

```bash
for f in Examples/Language/*.prl; do paralever check "$f" || echo "$f is racy"; done
```

A mistyped flag or command is a 2 and names the spelling it expected, rather than printing the
whole usage block: `paralever chekc f.prl` answers `unknown command 'chekc'; did you mean 'check'?`,
and a flag this tool used to have is told what replaced it — `'--all-cells' is now '--full'`.

### init

`paralever init my-kernel` writes six files and nothing else:

```text
my-kernel/
  lakefile.toml      name, one lean_lib, one require — paralever from git
  lean-toolchain     a copy of this project's own, so the versions cannot disagree
  MyKernel.lean      prl_file "hello.prl", the verdict as #eval, and par_seq_eq
  hello.prl          two halves of one buffer, scaled by different factors at once
  README.md          the three commands
  .gitignore         /.lake
```

Then `lake exe cache get` and `lake build`. The module name is the directory's, camel-cased
(`my-kernel` ↦ `MyKernel`), and the toolchain is a byte-for-byte copy of this project's
`lean-toolchain`, read with `include_str` so the two cannot drift.

There is no build system of our own here and no generator to maintain: Lake resolves `paralever`,
`paralever` resolves Mathlib, and `lake build` is the whole check — the generated module ends in
`par_seq_eq`, so a program with a race fails the `by decide` above it and the build fails with it.
That is the point of the scaffold: the proof is not a separate step a user has to remember.

An existing file is never overwritten. Running `init` in a directory that already has a
`lakefile.toml` adds the program and the module, reports what it left alone, and exits 0; running it
where every file is already present writes nothing and exits 1. `init` is the one command that
reads no program, so it is answered before a file is demanded, as `explain` is.

The `require` names a branch rather than a tag, because there is no release yet: a pinned revision
that does not exist is worse than one that moves. Mathlib is not named at all — it arrives as
paralever's own dependency, and naming it twice is how a downstream project ends up with two
revisions of it.

### vc

`vc` emits the obligation `wfB` refuses. A computed address makes the syntactic footprint every cell
of its buffer (`docs/block-ir.md`), so `wfB` declines programs whose threads provably touch
different cells; `vc` states the same Bernstein condition over the *index expressions* instead and
lets an SMT solver decide it. Registers are substituted away first, so a computed index that folds
to a literal is decided in Lean and never reaches a solver:

```bash
paralever vc Examples/Language/stripe.prl            # the obligation, and what each unknown is
paralever vc Examples/Language/stripe.prl -o q.smt2  # the SMT-LIB file, to edit and to keep
paralever vc Examples/Language/stripe.prl --solve --assume nonneg
```

`--solve` uses the first solver it finds: whatever `PARALEVER_SMT` names, else `z3`, else `cvc5`.
`--solver NAME|PATH` names one outright and implies `--solve`, so `--solver cvc5` or `--solver
/opt/z3/bin/z3` both work and neither needs the solver on `PATH`. Either way, a solver that was
asked for and cannot be run is an error, never a fall-through to the next candidate. The name
decides the argument shape, which is why a path ending in `cvc5` gets cvc5's flags.

`--timeout MS` is milliseconds per query, 10000 by default and `0` for no limit. A query that runs
out answers `unknown`, which the report calls `inconclusive` and tells you to raise — so a hard
obligation is a knob to turn rather than a wrong answer. z3 gets `-t:MS` and cvc5 `--tlimit=MS`.

`--assume nonneg` asserts that every value read from the heap is at or above zero. It is needed more
often than it looks: `ArrRef.addr` clamps a negative index to its buffer's first cell (`i.toNat`),
so without the hypothesis *every* thread with a possibly-negative computed index aliases there, and
a solver will report that collision in preference to any other. The hypothesis weakens the claim, so
the report names it on its first line.

An `unsat` is reported as **discharged by the solver, not by Lean's kernel**, because that is what
it is; `paralever prove` remains the only path that ends in a checked proof. A `sat` is checked
here before it is believed: the model's values are substituted back into the symbolic addresses and
the collision is recomputed in Lean, so the two cells named in the report are named on our own
arithmetic. The exit code is 1 when any fork is left undischarged, 2 when no solver could be run.

Both reports lead with what the two existing checks already know — that the equivalence is proved at
the declared heap, and that `wfB` cannot prove it for every heap — so a solver's answer does not
have to be read to recover either half.

The gain is measurable on one file. `paralever Examples/Language/stripe.prl` reports the
equivalence at the declared heap, which is where the exact check speaks. `paralever vc stripe.prl
--solve --assume nonneg` answers *independent*, for every heap satisfying the hypothesis, because
`2k` is never `2m+1`. `Examples/Language/Stripe.lean` now proves that second statement in Lean
instead, so for this shape the solver is a cross-check rather than the route. See `docs/smt-vc.md`
for the encoding and the trust boundary.

`explain` reads no file: `paralever explain P108` prints the rule a code names and the reason it
exists, and exits 2 on a code that is not in the registry (`docs/diagnostics.md`). Every diagnostic
the `.prl` front end issues carries one of those codes, and a reader error carries the line and a
caret:

```text
error[P002]: 'buf' is a reserved word
 --> double.prl:2:5
  |
2 | reg buf
  |     ^^^
```

## Standard input

A `.prl` program whose text uses `input` draws its values from the pipe, and there is no option for
it — the shell is the interface, as in every other language:

```bash
echo "hello, world" | paralever run input.prl
paralever check double.prl < data
```

The values are consumed while the program compiles, so every command sees the same resolved
program: `check`, `run` and `race` all read the pipe once, and `to-prl` prints a `.prl` file with
the values written in. Standard input is read **only** for a program whose text asks for it, so no
invocation ever waits on a terminal that was not going to be piped.

`prove` is the exception and refuses such a program, because the module it writes re-reads the file
while Lean elaborates and Lean has no pipe to give it. It says so, and names the fix:

```bash
paralever to-prl prog.prl < data > resolved.prl    # then: paralever prove resolved.prl
```

Rationale, and the four places `input` may not appear: `docs/prl.md` § *Input*.

## A file on its own

`paralever FILE` with no command answers the question a file arrives with. It is `check`, plus what
the program's `print` statements wrote:

```console
$ paralever Examples/Language/stripe.prl
Examples/Language/stripe.prl
  memory:   A[8] @0, k[2] @8  (10 cells)
  reads:    {k[0], k[1]}
  writes:   {A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7]}
  threads:  2
  rounds:   2 parallel, 4 sequential
  verdict:  this heap   Proved: Yes — no two threads touch one cell here
            any heap    RACE found — with k[1] = -1: A[0] written by both threads

output:
k = [0, 1]
```

The report above the output is `Lang.checkReport`, the same function `check FILE` calls, so on a
program that prints nothing the two invocations agree line for line. The `output:` section is
`Lang.outReport`, which `run` calls too, so the two cannot drift on what a program said.

`run` executes and says nothing else. It consults neither `wfB` nor the race scan, so a racy program
runs like any other and prints whatever the schedule left, which may be a wrong answer; deciding that
is `check`'s job and exhibiting it is `race`'s. The bare form does **not** print the heap: it answers
the question a file arrives with — what holds, and what the program said — and the heap is `run`'s
answer, one command away. When there is a race the interleaving follows the output, because that is
the verdict's evidence rather than a second reading of the heap; a racy `run` marks its heading
`heap (one schedule)` for the same reason. Above the verdict a bare invocation also prints the
reader's approximations, when the front end made any — those bear on why the verdict is what it is,
so they travel with it rather than with the heap.

## Verbosity

`--verbose` (`-v`) is on by default. `--quiet` (`-q`) turns it off, and a quiet `run` — or a quiet
bare invocation — prints **only what the program's `print` statements wrote**, with no headings, no
heap and no verdict:

```console
$ paralever -q Examples/Language/stripe.prl
k = [0, 1]
```

A program with no `print` is then silent, not a blank line: `print` is the only thing a program says
on its own, and the rest of the report is the tool talking about it. The exit code is unchanged, so a
quiet invocation is still the gate — 1 for a race at the declared heap, 0 otherwise — which is the
shape a script wants. The two flags are read in order, so a wrapper may append `-v` to undo a `-q` it
inherited.

`--full` is the separate, older knob and keeps its own name: it lifts the per-buffer cell limit
in the heap view (§ *One buffer, and all of the cells*) and says nothing about verbosity.

## The verdict has two parts

The verdict is the last line of `check`'s report, which a bare invocation prints too. It answers two questions, because a
program with a computed address has two different answers: *this heap* is the one the file's `buf`
initializers describe, and *any heap* is the universally quantified statement. They are printed as one
line when they agree and as two when they differ.

| `wfB` | the `verdict` lines | exit |
|---|---|---|
| accepts | `every heap  Proved: Yes — wfB accepts: …` | 0 |
| refuses, a race at the declared heap | `every heap  RACE found — …` | 1 |
| refuses, declared heap clean, a race elsewhere | `this heap  Proved: Yes …` / `any heap  RACE found — with k[1] = -1: …` | 0 |
| refuses, and no race found | `this heap  Proved: Yes …` / `any heap  Inconclusive — …` | 0 |

`Proved: Yes` is a Lean proof either way: `wfB` accepting gives `par_seq_eq` for every heap, and an
empty `raceSites` gives it at the heap it was measured at (`raceSites_nil_iff`). A `RACE found` names
the cell and how it is contended, and, when the heap is not the declared one, the cells to change to
reach it. `Inconclusive` names both of its reasons — what `wfB` refused over and which constructor
widened the footprint, then how many heaps the search looked at and at which cells. The exit code is
1 only for a race at the declared heap: a counterexample at another heap refutes the quantified
statement but leaves the program as written correct.

Rationale, the probe set, and what a bounded search is allowed to claim: `docs/general-heap.md`.

### A claim, when the file states one

A file with an `assert` gets a second block under the verdict. The verdict lines are about the left
program alone, exactly as they are for a file with no claim; the `claim` lines are about the pair:

```text
  verdict:  every heap  Proved: Yes — wfB accepts: the threads' footprints are pairwise independent
  claim:    bubble == oddeven on A
            Agree: Yes — the same 8 cell(s), under every schedule of either side
```

| what holds | the second `claim` line | exit |
|---|---|---|
| the cells agree and both sides pass `wfB` | `Agree: Yes — the same n cell(s), under every schedule of either side` | 0 |
| the cells agree and a side needed the exact check | the same, `… of either side at this heap` | 0 |
| the cells agree and a side races | `Agree: Yes on the canonical run — but 'g' has a race, …` | 1 |
| the cells differ | `DISAGREE — A[1], A[2], … (7 of 8 cell(s) compared)` | 1 |

A claim that does not hold is a failure of the file and not a note on it, which is why the last two
rows exit 1 even though the program itself may be race-free. Every other command — `run`, `race`,
`autopar`, `vc`, `to-prl` — acts on the **left** program, which is the file read with the left call
written out where the `assert` stands. `prove` appends the matching section to
whichever of its three theorems the left program carried, so a claim file's module states both
`par_seq_eq` for the left side and `AgreeOn` for the pair. See `docs/equivalence.md`.

Nothing restates the verdict and nothing suggests a next command. What follows the run body is only
what neither already holds: the interleaving, when there is a race, and where a proof module went,
when `--prove` wrote one.

Under `vc` the same two lines head the report, so the two commands cannot disagree, and three further
things produce an `inconclusive` *per fork*: a widened footprint, a solver that did not finish, or a
solver that found an assignment colliding two cells — an assignment is not a run, so a `sat` is the
obligation failing rather than a race found. Only a real interleaving earns `RACE found`.

## What `run` prints

Most of what a `.prl` program says is the heap it leaves, so `run` prints the heap as the buffers
that were declared. A `print` statement writes a line above it, under its own heading, and a program
with no print has no such section at all (`docs/print.md`). A bare `paralever FILE` prints the
`output:` section alone, under `check`'s report, and leaves the heap here (§ *A file on its own*):

```console
$ paralever run Examples/Language/arena.prl
heap:
src [4] @0  [1, 2, 3, 4]
tmp [4] @4  [3, 5, 7, 9]   (freed)
out [4] @4  [3, 5, 7, 9]
```

Each row is one buffer: its name, its shape, the address of its first cell, and its values. A
`[2, 6]` buffer prints as two rows, and `n [1] @0  [3]` is a one-cell buffer holding the value `3`;
the address is where the buffer starts in the one flat heap `State = Loc → Val` gives. `tmp` and
`out` print the same numbers because `free` returns the cells and the next buffer is placed on
them (`docs/layout.md` § *Lifetimes*); the `(freed)` marker says which of the two is dead rather
than leaving the repetition to be guessed at.

### One buffer, and all of the cells

A buffer wider than the terminal is not a report. By default each one prints at most
`Lang.runCells` = 32 cells — rounded up to a whole row for a matrix — and then says how many it
left out, so the shape and the first values are still legible on a program whose heap is thousands
of cells:

```console
$ paralever run Examples/Scale/matmul12.prl
…
C [12, 12] @288  [6072, 6138, 6204, 6270, 6336, 6402, 6468, 6534, 6600, 6666, 6732, 6798]
                 [15576, 15786, 15996, 16206, 16416, 16626, 16836, 17046, 17256, 17466, 17676, 17886]
                 [25080, 25434, 25788, 26142, 26496, 26850, 27204, 27558, 27912, 28266, 28620, 28974]
                 … +9 more rows
```

Two options say otherwise. `--full` lifts the limit on every buffer. `--buffer` asks for one buffer by
name, printed in full and with nothing around it, and a subscript asks for the single cell:

```console
$ paralever run Examples/Language/matmul.prl --buffer C
C [2, 2] @8  [19, 22]
             [43, 50]

$ paralever run Examples/Language/matmul.prl --buffer 'C[1, 1]'
C[1, 1] @11  50
```

The address is printed with the value because the cell is one of `State = Loc → Val`'s, and `@11`
is where `Layout.at "C" [1, 1]` sends that subscript. A name no buffer has, or a subscript outside
the shape, is an error naming what the program does declare, and exits 2 rather than printing a
default. When the program has a race, `--buffer`'s caveat goes to standard error, so the one line on
standard output stays greppable.

### Many runs, randomly interleaved

`--run-again N` (`-ra N`) walks `step` choosing a successor at random, N times, and groups the runs
by what they left behind.

```console
$ paralever run Examples/Language/matmul.prl -ra 10
10 runs under random schedules, 1 distinct outcome — every schedule agreed.

outcome — 10 runs (seeds 0 1 2 3 4 5 6 7 … +2)
A [2, 2] @0  [1, 2]
             [3, 4]
B [2, 2] @4  [5, 6]
             [7, 8]
C [2, 2] @8  [19, 22]
             [43, 50]

$ paralever run Examples/Language/race.prl -ra 10
10 runs under random schedules, 3 distinct outcomes — the schedule decides what this program computes.

outcome 1 — 2 runs (seeds 0 7)
x [1] @0  [7]
log [2] @1  [1, 1]

outcome 2 — 6 runs (seeds 1 3 4 6 8 9): wrong — this schedule caught a race

outcome 3 — 2 runs (seeds 2 5)
x [1] @0  [9]
log [2] @1  [1, 1]
```

Outcomes are told apart on every cell of the arena and every register the file names, so `--buffer`
narrows what is printed and never what agreement is claimed on. The seeds are listed because the
generator is seeded rather than drawn from the operating system: re-running with a seed replays that
interleaving. This is evidence, not a decision — `check` decides and `prove` proves. See
`docs/interleave.md`.

A report is read, not elaborated, so none of it is commented out. `check`, `run`, `race` and the
no-command verdict print plain lines; the `--` prefix is kept for output that is *source* —
`autopar`, `to-prl`, `to-mlir` and `to-lean`, where the reader's approximations have to survive as
comments in a file that still compiles.

## What `prove` writes

Three cases, and no choice about which one applies. The program decides, by which check it passes:

| the program | the theorem | how |
|---|---|---|
| `wfB = true` | `ParSeqEq` at **every** heap and register file | `ParProg.par_seq_eq (by decide) ρ σ` |
| `wfB = false`, `wellFormedB` at the declared heap | `ParSeqEq` at **that** heap | `parSeqEq_of_runSeq_eq` from the exact check |
| both refuse | no theorem; both refusals, proved | `by decide` on each |

A file with an `assert` gets a fourth section **in addition** to whichever of those three it earned,
carrying `AgreeOn` for the pair of programs (§ *A claim, when the file states one*). The claim is
about the file's own two programs, so it does not follow `--autopar` into the pass's output.

The first case is the one the library is for. `wfB` decides Bernstein's condition at every `par`
node by reading the syntax, so it holds at every heap, and that is exactly `par_seq_eq`'s
hypothesis:

```lean
def src : Compiled := prl_file "Examples/Language/sum.prl"

example : ParProg.wfB src.prog = true := by decide

theorem sum_par_seq_eq (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar src.prog ρ) (ParProg.execSeq src.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ
```

The second case is a computed address. `dst[%i]` has a footprint of *all* of `dst`, because the
index is not known from the syntax, so two threads that write distinct cells still look like they
collide and `wfB` refuses. The per-heap check measures the accesses along the canonical run instead,
and accepts — which buys the equivalence at the heap the file declares, and nowhere else
(`docs/block-ir.md`):

```lean
theorem scatter_par_seq_eq :
    ParSeqEq (ParProg.execPar src.prog ρ0) (ParProg.execSeq src.prog ρ0) src.layout.state :=
  parSeqEq_of_runSeq_eq _ _ _
    ((wellFormedB_iff _ _).1 (by decide))
    ((wellFormedB_iff _ _).1 (by decide))
    (ParProg.execPar_runSeq_all.1 src.prog ρ0 src.layout.state)
```

The third case is a real race, and the generated file says so and proves both refusals. No theorem
of this shape exists for such a program: its parallel reading reaches `wrong`, which is no
terminating outcome, while its sequential reading terminates — `Examples/Races/Report.lean` carries
that refutation in full, and `paralever race FILE` prints the interleaving that does it.

With `--autopar` the module carries one more theorem, and it is the strongest of the three because
it has **no hypothesis at all**:

```lean
theorem chain_autopar_sound (ρ : Regs) (σ : State) :
    (runSeq (ParProg.execPar par ρ) σ).2 = (runSeq (ParProg.execSeq src.prog ρ) σ).2 :=
  AutoPar.rewrite_sound src.prog ρ σ
```

`rewrite` checks its own gate — independence and no register flow between threads — and returns the
program unchanged when the gate fails, so the equality holds for every input program
(`docs/autopar.md`).

Three details of the generated module. It reads the source through `prl_file` / `mlir_prog`, which
compile the file *while the module elaborates*, so `by decide` sees a program literal and never
runs the reader. The path it names is relative to the module's own directory when the two live in
one tree, and absolute otherwise. And `--typecheck` runs `lake env lean` on what was written, so the
tool can report Lean's verdict rather than its own:

```console
$ paralever prove Examples/Language/chain.prl --autopar -o /tmp/Chain.lean --typecheck
written to /tmp/Chain.lean
lake env lean /tmp/Chain.lean
/tmp/Chain.lean: Lean accepts it
```

`paralever_check` is the same ladder as a tactic, for a goal you are writing by hand rather than a
file you are checking: it tries the routes in the order above and, when none of them applies, fails
with the interleaving that disagrees. `docs/race-search.md` § *In tactic position*.

## The two conversions

`to-prl` on a `.mlir` file and `to-mlir` on a `.prl` file are the same program printed by the other
front end's printer, with the reader's approximations as comments at the top. A cycle changes one
thing: MLIR globals must carry an initial value, so a buffer the `.prl` file left implicit comes
back as `buf out[4] = 0, 0, 0, 0`.

What `to-mlir` cannot do is refuse quietly. Three programs have no generic form in the op set the
reader supports, and each gets a named error: a file with `if`/`while` (there is no conditional in
that op set), a computed subscript into a multi-dimensional buffer, and a layout where a `free`
returned space so two buffers share cells — two MLIR globals cannot alias. `docs/mlir.md`
§ *Generic form out* has the details, including what an `async.execute` group is and why a fork is
read as a group of operations rather than as one.

## Limits

- **`prove` writes; Lean checks.** Without `--typecheck` the tool does not run Lean, so a module it
  writes for a large program can still be slow to check: `decide` reduces the program against a
  heap, and the reader quotes the whole program into the elaborator first. The generated module
  raises `maxRecDepth` to 100000 and lifts the heartbeat limit, because both costs are the
  program's size and both terminate — a 14,451-line MLIR module takes Lean 34.65 s and would
  otherwise fail at the default budget before `decide` ran (`docs/scale.md`).
- **`prove` cannot carry input.** The generated module re-reads the source while Lean elaborates,
  so a program that reads standard input is refused with the `to-prl` route to take instead
  (§ *Standard input*). The same holds of `prl_file` in a hand-written Lean file.
- **`--typecheck` needs the repo.** It shells out to `lake env lean`, so it has to run from a directory
  where `lake` resolves this package.
- **One function per module.** An MLIR file with several `func.func`s and none called `main` is
  refused by the lowering rather than guessed at, because `func.call` is not supported.
- **No `--entry`.** The generated `func.func` is always called `main`, and the subject is always
  the whole program; a named region is reachable from Lean with `ParProg.findLabel`.
- **Registers come back renumbered.** Through MLIR, a `%r := e` with no memory in it is inlined
  into whatever reads it: SSA values are not assignable. The program's memory, footprint, verdict
  and heap are unchanged, which is what `MLIR.emitRoundTrips` gates.
