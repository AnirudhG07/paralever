# `.prl` — the language as a file

A `.prl` file is a paralever program written as text instead of as Lean notation. Lean reads it:
`prl_file "sum.prl"` parses and compiles the file *while the Lean file elaborates*, and the
declaration it defines holds the resulting `ParProg` as a literal. There is no separate toolchain
and no second compiler — the file exists so a program can be taken out of Lean and brought back.

```text
                sum.prl
                   │   Lang.Compile.Parse      text → Lang.Compile.Ast.File
                   ▼
              Lang.Compile.Ast.File
                   │   Lang.Compile.Lower    names, constant folding, loop unrolling
                   ▼
            Layout × ParProg
                   │
        ┌──────────┼───────────┐
        ▼          ▼           ▼
   footprintOf    wfB    execPar / execTask
```

Everything below the third line is the existing library: a compiled `.prl` file is the same
`ParProg` a `paralever { … }` block elaborates to, so `footprintOf`, `wfB`, `par_seq_eq`,
`AutoPar.rewrite` and `runTask` apply to it unchanged, and nothing about them is `.prl`-specific.

## Why a file

Two reasons, both about programs being data.

A `ParProg` is first-order, so it can be printed; `Lang.print` prints it as `.prl` text and
`prl_file` reads that text back. A program can therefore leave the repository — into a bug report,
a paper appendix, another tool's output — and come back as the same program. `Lang.toLean` prints the
`paralever { … }` block instead, for pasting into a Lean source file.

A file is also the only surface a non-Lean producer can write. `MLIR/` lowers MLIR generic form to
`Layout × ParProg` directly; a producer that would rather emit text has `.prl` to emit.

## The grammar

```text
file    ::= stmt* | "paralever" "{" stmt* "}"
stmt    ::= "buf" name ( "[" exp ("," exp)* "]" )? ("at" exp)? ("=" init)?
          | "const" name "=" exp
          | "reg" name ("," name)* ("=" number)?    -- optional: pins an index
          | "free" name
          | "%" reg ":=" addr                       -- load
          | addr ":=" exp                           -- store
          | "%" reg ":=" exp                        -- register assignment
          | "parallel" thread ("|" thread)* label?
          | "parfor" name "in" exp thread label?
          | "for" name "in" exp thread
          | "if" exp thread ("else" thread)?
          | "while" exp "in" exp thread
init    ::= "zeros" | "ones" | "eye" | "arange" | "full" exp | ("[")? exp ("," exp)* ("]")?
thread  ::= "{" stmt* "}"
label   ::= "::" string
addr    ::= "[" exp "]" | name ( "[" exp ("," exp)* "]" )?
exp     ::= exp ("+"|"-"|"*"|"/"|"%") exp | "-"? number | name | "%" reg
          | "min" "(" exp "," exp ")" | "max" "(" exp "," exp ")" | "(" exp ")"
reg     ::= number | name
```

Comments run from `--` to the end of the line. The reserved words are in `Lang.keywords`.

Declarations are statements, because `free` is one: a buffer has a lifetime in the program text.
They are allowed only at the top level, where the whole program sees them — a `buf` or a `free`
inside one thread of a `parallel` would be visible to that thread alone.

Statements are separated by a line break, by `;`, or by both. The Lean notation cannot do this — its
statement list is `sepBy1(impStmt, "; ")`, a separator that whitespace does not substitute for, so
`paralever { … }` needs a `;` between every pair. A hand-written reader has no such constraint, and
in a file a line break is what a reader expects.

The optional `paralever { … }` wrapper means a program pasted out of a Lean file is already a valid
`.prl` file.

## Declaring memory

`State` is `Loc → Val` and total: every location exists and holds `.int 0` until written. A program
therefore cannot create or destroy a location — there is nothing to create. What a `.prl` file does
is *declare* ranges and end their lifetimes, which is what `Layout` plus a cursor is:

```prl
buf A[6] = 1, 2, 3, 4, 5, 6   -- the allocator places it
buf C[2, 3] = ones
buf S[4] at 100               -- placed by hand
const n = 2
free C                        -- C's lifetime ends here
```

A buffer with no `at` begins where the previous one ended, which is `alloc`'s placement, and then no
two *live* buffers can overlap for the reason `alloc_pairwise` gives. A buffer with an `at` was
placed by the author, so the compiler checks it against every live buffer and names both on failure.
`Layout.wfB` — names distinct, no buffer given more data than it has room for — is checked too.

`free A` ends `A`'s lifetime. Two things follow, and nothing else does:

* **The name is gone.** Any later mention of `A` is a compile error, which is the useful half: it is
  how a file states that nothing below this line may touch that memory.
* **The space comes back** when `A` is the most recent buffer placed, so `buf`/`free` is a stack and
  the next declaration is placed on `A`'s cells. Freeing out of order ends the name's scope and
  leaves the hole, because the cursor only moves back from the top.

Nothing is zeroed, and no location goes away: a buffer declared on a freed range begins holding
whatever the previous occupant left. This is an arena, not a heap — `Examples/Language/arena.prl` is the
worked case.

There is deliberately no **run-time** `alloc`/`free`, and adding one would cost the main theorem
twice over. `alloc` has to choose an address; two schedules choose differently, so the final heaps
differ and `par_seq_eq` — an equality of heaps — becomes false for reasons unrelated to races. This
is the objection `CLAUDE.md` records against HeapLang, which is nondeterministic in allocation. A
run-time `free` is worse: Bernstein's conditions are about reads and writes of locations, so two
threads freeing one block, or one freeing while another reads, is a race that
`w₁∩w₂ = w₁∩r₂ = w₂∩r₁ = ∅` cannot see. Independence would have to be re-derived. The `free` above
avoids both because it happens at compile time and leaves no trace in the program.

What "deleting" is usually a proxy for — did the program touch memory nobody declared — is
`Layout.strayLocs`, which lists footprint locations outside every buffer.

## Proving, with `buf` and `free`

Both are **erased**. Neither emits a `ParProg` node, so the compiled program of

```prl
buf A[2]
A[0] := 1
free A
```

is `[0] := 1` on the nose, and `Test/Lang.lean` pins that equality. Consequently no theorem about a
program can depend on either: `wfB`, `footprintOf`, `par_seq_eq`, `time_le` and `runTask_eq` are
statements about the `ParProg`, and they are proved exactly as they are for a program written in
Lean — `by decide` on `wfB`, then the theorem.

What a declaration does decide is *which addresses* the program names and what the initial heap is
(`Layout.state`). The theorems are parametric in the heap, so a different layout changes the numbers
in a `#guard`, never a proof obligation.

## Registers

A register needs no declaration. Every `%name` in the file is collected before anything is compiled
and given the lowest index no numbered register uses, in order of first appearance, so `%acc` is a
register wherever it occurs and `%0` is register `0` as always. `reg acc = 3` pins a name to an
index when that matters; `reg a, b` is accepted and does nothing a first use would not do.

Registers are thread-private — a `parallel` block hands each thread the pre-fork register file and
discards what the threads leave (`Lang/Core/Prog.lean`) — so two threads using `%acc` do not
interfere, and that is why independence is about memory alone.

## Addresses, values, and the two readings of `%`

An address is a compile-time number. `Lang.Compile.Lower` folds it: literals, `const`s, enclosing loop
variables, and `+ - * / %`. A buffer subscript `A[i, j]` becomes `Layout.at "A" [i, j]`, and the
subscript is range-checked then and there — `A[9]` on `buf A[6]` is a compile error, not a stray
write.

A value is an `AExp`: the same arithmetic, with `%r` for a register, and with `const`s folded to
literals. `AExp` has no modulo, so `%` in a value position is rejected rather than approximated.

`%` therefore reads two ways, decided by position: in operand position `%0` and `%acc` are
registers, and in operator position `n % 4` is modulo.

A subscript that mentions a register cannot be folded, and compiles to the data-dependent form —
`loadAt` / `storeAt` — which is confined to its array by construction (`ArrRef.addr_mem_cells`).
It must be the only subscript, and it indexes the buffer flat, wrapping on its size. A *bare*
address that mentions a register (`[%0] := 1`) is rejected: there is no array to confine it to, so
its footprint would be the whole heap. See `docs/block-ir.md`.

The price of a computed address is precision, not soundness: the footprint of `dst[%i] := 1` is
every cell of `dst`, so `Examples/Language/scatter.prl` is **rejected** by `wfB` although its three
threads write three distinct cells. The reports say so in those words, because `raceSites` — the
exact per-heap check — finds nothing.

## What a `.prl` file cannot say

A Lean `paralever { … }` block takes Lean `term`s for its addresses and values, so any Lean
expression of the right type works: `[n * 2 + 1]`, `%(f i)`, an address computed by a Lean function,
or a `ParProg` combinator spliced in. A `.prl` file has none of that, because the reader cannot call
the elaborator and `lake`'s copy of the file has to mean the same thing as the author's. The closed
expression language above, `const`, and `for`/`parfor` unrolling are what it has instead.

Labels (`:: "name"`) attach to `parallel` and `parfor`, matching the Lean notation. A `label` around
anything else, which the library allows, prints as a comment and does not read back.

## The round trip

`Lang.roundTrips src` is `true` when reading `print (compile (parse src))` gives the same program and
the same memory as reading `src`. It is the gate on the reader: a rule that reads a file in a way
nobody intended fails the build rather than a review. `Test/Lang.lean` runs it on every example,
alongside the verdict each example's header claims.

Printing resolves an address to a buffer name only when one *live* buffer owns it; a range that was
freed and claimed again has two owners and prints as a raw address, since which name was live there
is not recoverable from the program. A `free` that returned space prints where the space is claimed
again, and one that only ended a scope prints after the program, where it has the same effect.

The comparison is modulo the associativity of `;`, which `Lang.norm` normalizes. `seq` is associative
under `execPar` because `bind` is, and `whileAtMost` nests its unrolling the opposite way from the
chain the printer emits.

Printing picks buffer names over addresses (`A[1, 2]`, not `[7]`) via `Layout.nameOf`, and emits
`at` only where a base is not the allocator's — so a file written without `at` prints without one.

## Using one from Lean

```lean
import Lang.Load
open Paralever Paralever.Lang

def sum : Compiled := prl_file "../Examples/Language/sum.prl"

example : ParProg.wfB sum.prog = true := by decide

theorem sum_ok (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar sum.prog ρ) (ParProg.execSeq sum.prog ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ

#eval ParProg.evalTask sum.prog sum.layout.state [6, 7, 8]   -- [3, 7, 11]
```

`prl_file` quotes the compiled program into the term, so `decide` sees the program and never the
reader; `prl_prog` and `prl_layout` give the two halves alone. A file that does not compile is an
elaboration error at the `prl_file` term, carrying the `line:column` the reader reported.
`Lang.load` is the same compiler behind `IO`, for reading a path at run time.

`Lang/Report.lean` holds four views, for `#eval`:

| view | what it prints |
|---|---|
| `checkReport` | declared memory, footprint by name, thread count, rounds, verdict |
| `runReport` | the buffers after a run, sequential or on real threads |
| `raceReport` | the interleaving that realizes a race, replayed against `step` |
| `parReport` | `AutoPar.rewrite`'s output as `.prl`, with the plan's numbers |

`Lang.highlight` is the same text with ANSI colour, in token classes a scan of the text can
recognize: comment, keyword, register, number, string, `:=`.

The same four views are what the `paralever` executable prints, over `Lang.load` rather than
`prl_file`, so a file can be checked without writing a Lean file for it:
`paralever check sum.prl`. One command has no `#eval` counterpart — `paralever prove sum.prl -o
Sum.lean` writes the Lean module that states and proves what the verdict licenses, which is the
file above rather than a report about it. See `docs/cli.md`.

## The examples

`Examples/Language/` is gated by `Test/Lang.lean`, which compiles each file, prints it back, checks the
verdict it is labelled with, and — for each of the seven files `wfB` accepts — proves the instance
of `par_seq_eq` that the verdict licenses (`sum_ok`, `matmul_ok`, `stencil_ok`, `pipeline_ok`,
`control_ok`, `chain_ok`, `arena_ok`). The two it refuses have no such theorem: for `race.prl` the
conclusion is false, and `Examples/Races/Caught.lean` refutes that shape; for `scatter.prl` the conclusion
holds at heaps where the indices miss, which `Examples/Language/Scatter.lean` proves from the exact check.
Each file exists for a reason:

| file | what it is there for |
|---|---|
| `sum.prl` | `parfor` with a nested `for`; one thread per chunk, each writing its own cell |
| `matmul.prl` | disjoint writes over overlapping reads — the case `∗`-disjointness rejects |
| `stencil.prl` | neighbouring threads reading the same cell |
| `pipeline.prl` | a fork, then a join that reads what both threads wrote |
| `control.prl` | `while c in n`, bounded because `ParM` is inductive |
| `chain.prl` | written sequentially, for `AutoPar.rewrite` to regroup |
| `race.prl` | two threads, one cell: `wfB` false, and a counterexample |
| `scatter.prl` | a computed address, rejected by over-approximation rather than by a race |
| `arena.prl` | `free`, and the next buffer placed on the freed cells |
