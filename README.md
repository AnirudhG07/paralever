# Paralever

> Paralever is BMW's rear drive architecture of most modern BMW shaft-driven motorcycles... But it runs sequentially...

As the modern day programming for AI workloads(or most fast processing workloads) involves using multithreads, multi-cores or running your parallel programs on GPU, TPU, other hardware accelerators, etc. there is a need to verify the correctness of your parallel programs i.e. they do not race and the output of parallel programs would be same as when it was run sequentially.

Paralever is a framework which allows you to represent parallel programs in a very intuitive way and lets you prove parallel-sequential equivalence or `par_seq_eq`/`ParSeqEq`.

**Website: <https://anirudhg07.github.io/paralever/>**

## What it can do

- Write parallel programs in a small imperative language with buffers, loops, conditionals,
  functions, barriers and N-ary forks.
- Produce a Lean 4 file proving that the parallel program and its sequential reading agree under
  every schedule.
- Show the counterexample when a program has a race: the interleaving that breaks it, step by step.
- Execute a program in the canonical order, on real threads, or under randomly chosen schedules.
- AutoParallelization pass for a program written sequentially, with a schedule that preserves the original order by
  construction.
- Read and write MLIR, in both generic and custom form.
- Hand the leftover independence obligation to an external SMT solver when the static footprint is
  too coarse to settle it.
- State with `assert` which cells two programs must leave equal, and decide that too.
- Report cost: round counts, scaling curves, and timings against real threads.

## Matrix Multiplication Example

The most classic example of parallel programs are matrix multiplication. Here is a 12×12 matrix multiply. Twelve threads, one per row of `C`.

```
const n = 12

buf A[12, 12] = arange
buf B[12, 12] = arange
buf C[12, 12]

parfor i in n {
  for j in n {
    %acc := 0
    for k in n {
      %x := A[i, k]
      %y := B[k, j]
      %acc := %acc + %x * %y
    }
    C[i, j] := %acc
  }
} :: "matmul 12x12"
```

The threads write disjoint cells of `C`. They also read all of `A` and all of `B`, so their reads
overlap everywhere. Anyone who has written this by hand knows it is correct, and knows that the
reason it is correct lives in their head rather than in the file. Change `C[i, j]` to `C[j, i]` and
it still is. Change it to `C[0, j]` and it is not, and nothing in the program will say so.

```console
$ paralever check Examples/Scale/matmul12.prl
Examples/Scale/matmul12.prl
  memory:   A[12, 12] @0, B[12, 12] @144, C[12, 12] @288  (432 cells)
  reads:    {A[0, 0], B[0, 0], A[0, 1], B[1, 0], A[0, 2], B[2, 0], A[0, 3], B[3, 0], A[0, 4], B[4, 0], … +278 more}
  writes:   {C[0, 0], C[0, 1], C[0, 2], C[0, 3], C[0, 4], C[0, 5], C[0, 6], C[0, 7], C[0, 8], C[0, 9], … +134 more}
  threads:  12
  rounds:   300 parallel, 3600 sequential
  verdict:  every heap  Proved: Yes — wfB accepts: the threads' footprints are pairwise independent
```

No run happened. `check` reads the program and decides.

## The theorem

> If the threads of every fork are **independent** which is our `WellFormedness` property, then the parallel program and its sequential
> reading reach exactly the same outcomes — the same result and the same final heap — under every
> schedule.

Independence is Bernstein's condition: no two threads write the same cell, and no thread writes a
cell that another one reads. Shared reads are allowed. That is the whole reason matmul passes:
`A` and `B` are read by all twelve threads and written by none. This is based on our regular needs of true parallel programs.

Separation logic's `∗` splits the heap into disjoint pieces, which would reject matmul. Bernstein
does not, and matmul is the program everybody actually wants to write.

For the matmul above, the theorem reads:

```lean
def src : Compiled := prl_file "Examples/Scale/matmul12.prl"

theorem matmul_par_seq_eq (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar src.prog ρ) (ParProg.execSeq src.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ
```

`σ` is the heap and `ρ` the registers, both universally quantified, and `ParSeqEq` says the two
readings reach the same outcomes. The whole program-specific part is the `by decide`: Bernstein's
condition, checked by the kernel on the twelve threads' footprints. You did not write that file.
`paralever prove` did.

## Installation

The toolchain version project is currently on is `leanprover/lean4:v4.36.0`.

```bash
git clone https://github.com/AnirudhG07/paralever
cd paralever
lake exe cache get
lake build paralever # the executable lands in ./.lake/build/bin/paralever
```

To start a project of your own:

```bash
paralever init my-project
```

That writes a Lake project, a `hello.prl` to edit and a README, with paralever as the only
dependency. To add it to a project you already have, put this in `lakefile.toml`:

```toml
[[require]]
name = "paralever"
git = "https://github.com/AnirudhG07/paralever"
rev = "main"
```

## The language and the program model

A `.prl` file has buffers, registers, `for`, `while`, `if`, `parallel { … } | { … }`, `parfor`,
functions, barriers and `print`. Addresses can be computed, so `A[i*n + j]` is a cell like any
other. Buffers get laid out, placed and freed for you.

Underneath, a program is a value of `ParM`, a monad with four constructors: a pure result, a read,
a write, and `par`, which forks a list of children and continues once it has all their results.

```lean
inductive ParM : Type → Type 1 where
  | pure  : α → ParM α
  | read  : Loc → (Val → ParM α) → ParM α
  | write : Loc → Val → (Unit → ParM α) → ParM α
  | par   : Childs ParM αs → (Results αs → ParM β) → ParM β
```

This monad is the backbone of our project and it lets us represent the program in a finite n-ary
tree. Both front ends compile to it, so a `.prl` file and an MLIR module share one notion of what
running a program means.

## Usage

| Command                           | What it does                                              |
| --------------------------------- | --------------------------------------------------------- |
| `paralever check f.prl`           | memory, footprints, thread count, verdict                 |
| `paralever prove f.prl -o P.lean` | a Lean file stating and proving what holds of the program |
| `paralever run f.prl`             | execute it and print the heap it leaves                   |
| `paralever run f.prl -ra 10`      | ten runs under random schedules, grouped by outcome       |
| `paralever race f.prl`            | the interleaving that breaks a racy program, step by step |
| `paralever autopar f.prl`         | the same program, parallelized by the dependence pass     |
| `paralever to-mlir f.prl`         | MLIR generic form out; `paralever f.mlir` reads it back   |
| `paralever vc f.prl --solve`      | the leftover independence obligation, handed to a solver  |
| `paralever init DIR`              | a Lake project with paralever as its dependency           |

`--real-threads` runs one real thread per fork. `--buffer C` narrows the heap to one buffer or one
cell. `--json` gives `check`'s verdict as data. `paralever --help` lists the rest, and
`paralever-bench` runs the example corpus and reports what each kernel costs and how it scales.

The verdict `check` prints comes in two parts: whether the program is sound on the heap in front of
it, and whether it is sound on every heap. The two cannot disagree, because the second implies the
first.

When a program is wrong, `race` finds the interleaving that proves it and replays it step by step.

```console
$ paralever race Examples/Language/race.prl
step:thread  action              state
0:T0         write [log[0]] ← 1  log[0]↦1, x[0]↦0, log[1]↦0
1:T1         write [log[1]] ← 1  log[0]↦1, x[0]↦0, log[1]↦1
2:T1         write [x[0]] ← 9    pending
2:T0         write [x[0]] ← 7    pending
Parallel aborts at Step 2. Reason: T0, T1 write to: {x[0]}.
Parallel: x[0]↦7
Sequential: x[0]↦9
```

`-ra N` is the same thing from the other side. It runs the program N times, choosing the next thread
at random each step, and groups the runs by the answer each one left. A program that passes `check`
gives one answer however the threads are interleaved; a racy one gives several.

```console
$ paralever run Examples/Scale/matmul12.prl -ra 10 -b C
10 runs under random schedules, 1 distinct outcome — every schedule agreed.

$ paralever run Examples/Language/race.prl -ra 10
10 runs under random schedules, 3 distinct outcomes — the schedule decides what this program computes.
```

`autopar` goes the other way again: it reads a program written in order, works out what depends on
what, and prints the parallel version. The schedule it produces preserves the original order by
construction, so the output needs no separate argument that it is correct.

```console
$ paralever autopar Examples/Language/chain.prl
buf a[5]

parallel {
  a[0] := 3
} | {
  a[1] := 4
}
parallel {
  %0 := a[0]
  a[2] := (%0 * %0)
} | {
  %1 := a[1]
  a[3] := (%1 * %1)
}
parallel {
  %2 := a[2]
  %3 := a[3]
  a[4] := (%2 + %3)
}

-- units 5, stages 3, depth 6 (sequential 9, lower bound 6)
-- committed true, optimal true
```

## Proving a program

`paralever prove f.prl -o Matmul.lean` writes a Lean file that re-reads `f.prl` while it elaborates
and states what holds of it. Which theorem it carries depends on what `check` found, and `prove` has
no choice about it. When the syntactic check accepts you get the every-heap statement shown above.
When only the exact check accepts you get the equivalence at the heap the file declares. When the
program really does race, the file proves that both checks refuse and states no equivalence.

Between those cases sits a program the checker cannot settle. A computed address such as `A[idx[i]]`
makes the footprint a bound on the cells touched rather than the set of them, so a program that is
in fact fine can be refused:

```console
$ paralever check Examples/Language/branch.prl
  verdict:  this heap   Proved: Yes — no two threads touch one cell here
            any heap    Inconclusive — wfB refuses over {A[0], A[1]}: a branch contributes both arms although only one runs
            no race found in 11 heap(s) probed over {c[0]}
```

Inconclusive is not a race. `paralever race` looked and found no interleaving that breaks it. What
is missing is an argument that the addresses stay apart for every heap, and that argument needs to
know something the syntax does not say. There are two ways to supply it.

The first is a solver. `paralever vc f.prl` writes the missing obligation as SMT-LIB, one query per
fork, and `--solve` hands it to z3 or cvc5. An `unsat` is reported as discharged by that solver and
never as proved, and no solver is a build dependency.

```console
$ paralever vc Examples/Language/scatter.prl
fork 0 — 3 threads
  9 pair(s) left to decide, over 3 unknown value(s), in QF_LIA
  u0  the value read from idx[0]
```

The second is to state the every-heap theorem yourself, in the file `prove` already wrote. The
program is compiled there and the per-heap theorem is proved, so what you add is the same statement
with `ρ` and `σ` quantified:

```lean
theorem branch_par_seq_eq_any (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar src.prog ρ) (ParProg.execSeq src.prog ρ) σ := by
  sorry   -- the addresses stay apart: your argument goes here
```

Mostly what you have to show is well-formedness for every set of parallel threads in the program.
This is also a reasonable thing to hand to an AI coding agent: the goal is written out, the program
is in scope, and whatever the agent produces is checked by Lean's kernel, so a wrong proof cannot
pass.

## Website and slides

The [website](https://anirudhg07.github.io/paralever/) exists. Check it out! haha.
The [slides](https://anirudhg07.github.io/paralever/slides/isp/)(coming soon) are the talk given for this project.

## Examples

Everything demonstrable lives in [`Examples/`](Examples/), with the `.prl` and `.mlir` sources next
to what reads them. [`Tour.lean`](Examples/Tour.lean) takes one program through the whole thing:
write it, check it, break it, parallelize it.

## Limitations

- We do not model locks, atomics(yet) and GTA-VI. I assume threads run completely independent tasks.
- Project still in progress so bugs can exist.

## Acknowledgements

This project is done as my Independent Semester Project (ISP) in Fall 2026 at the Indian Institute of Science, under
Prof. Siddhartha Gadgil. I have used Claude for help in my project coding part.
