# The `paralever` command line

One file in, and one of four things out: a verdict, a run, a parallelization, or **a Lean file that
proves the program's parallel reading equals its sequential one**. The last is the point of the
tool. A checker that prints `race-free` is a linter, and you believe it or you do not; a tool that
writes a module Lean then checks is different in kind, because the claim leaves with its proof
attached.

```bash
lake build paralever                      # ./.lake/build/bin/paralever
paralever check   Examples/Language/sum.prl
paralever prove   Examples/Language/sum.prl -o Proofs/Sum.lean --check
paralever to-mlir Examples/Language/sum.prl -o sum.mlir
paralever to-prl  Examples/Mlir/doall-no.mlir
```

Code: `Tool/Run.lean` (the commands), `Tool/Proof.lean` (the generated module). Gates:
`Test/Tool.lean`.

## Both front ends, one program

Every command takes a `.prl` file or a `.mlir` module in generic form, because both compile to the
same pair — a `Layout` saying where the buffers are, and an unrolled `ParProg`:

```text
      sum.prl ──► Prl.Compile ──┐
                                ├──► Layout × ParProg ──┬──► check     the verdict
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
| `check FILE` | memory, reads, writes, thread count, rounds, verdict | `Prl.checkReport` |
| `run FILE [--threads]` | the heap after a run, buffer by buffer | `Prl.runReport` |
| `race FILE` | the interleaving that reaches `wrong`, step by step | `Prl.raceReport` |
| `autopar FILE` | the parallelized program as `.prl`, with the plan's numbers | `Prl.parReport` |
| `prove FILE` | a Lean module stating what holds of the program | `Tool.proofFile` |
| `to-prl FILE` | the program as `.prl` | `Prl.print` |
| `to-mlir FILE` | the program as MLIR generic form | `MLIR.emitText` |
| `to-lean FILE` | a `Layout` and a `paralever { … }` block | `Prl.toLean` |

`-o PATH` writes there instead of to standard output. `--threads` runs one `Task` per thread of
every fork rather than the canonical order — the heap is the same one, which is what `runTask_eq`
says for every program `wfB` accepts. `--autopar` makes `prove`, `to-mlir` and `to-lean` take the
parallelized program as their subject. `--colour` paints `to-prl`'s output in the editor grammar's
token classes.

`check` exits 1 when the program has a race, so a build can gate on it:

```bash
for f in Examples/Language/*.prl; do paralever check "$f" || echo "$f is racy"; done
```

## What `prove` writes

Three cases, and no choice about which one applies. The program decides, by which check it passes:

| the program | the theorem | how |
|---|---|---|
| `wfB = true` | `ParSeqEq` at **every** heap and register file | `ParProg.par_seq_eq (by decide) ρ σ` |
| `wfB = false`, `wellFormedB` at the declared heap | `ParSeqEq` at **that** heap | `parSeqEq_of_runSeq_eq` from the exact check |
| both refuse | no theorem; both refusals, proved | `by decide` on each |

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
one tree, and absolute otherwise. And `--check` runs `lake env lean` on what was written, so the
tool can report Lean's verdict rather than its own:

```console
$ paralever prove Examples/Language/chain.prl --autopar -o /tmp/Chain.lean --check
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

- **`prove` writes; Lean checks.** Without `--check` the tool does not run Lean, so a module it
  writes for a large program can still be slow to check or exceed `maxRecDepth` — `decide` reduces
  the program against a heap. The generated module sets the bound to 100000 and says why.
- **`--check` needs the repo.** It shells out to `lake env lean`, so it has to run from a directory
  where `lake` resolves this package.
- **One function per module.** An MLIR file with several `func.func`s and none called `main` is
  refused by the lowering rather than guessed at, because `func.call` is not supported.
- **No `--entry`.** The generated `func.func` is always called `main`, and the subject is always
  the whole program; a named region is reachable from Lean with `ParProg.findLabel`.
- **Registers come back renumbered.** Through MLIR, a `%r := e` with no memory in it is inlined
  into whatever reads it: SSA values are not assignable. The program's memory, footprint, verdict
  and heap are unchanged, which is what `MLIR.emitRoundTrips` gates.
