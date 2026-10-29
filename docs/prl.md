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
          | "let" name "=" init                     -- the shape read off the initializer
          | "const" name "=" exp
          | "reg" name ("," name)* ("=" number)?    -- optional: pins an index
          | "slice" name "=" range                  -- a name for a sub-range; declares no memory
          | "copy" region "from" region             -- cell by cell, in index order
          | "free" name
          | "%" reg ":=" addr                       -- load
          | addr ":=" exp                           -- store
          | "%" reg ":=" exp                        -- register assignment
          | "parallel" thread ("|" thread)* label?
          | "parfor" name "in" exp thread label?
          | "for" name "in" exp thread
          | "if" exp thread ("else" (thread | ifstmt))?   -- `else if` needs no braces
          | "while" exp "in" exp thread
          | "print" parg ("," parg)*                -- output; erased from the program
          | "def" name "(" param ("," param)* ")" thread   -- a named statement list
          | name "(" arg ("," arg)* ")"             -- a call, written out where it stands
          | "assert" call "==" call ("on" name ("," name)*)?  -- the file's claim; top level only
          | "assertParSeq" call "==" call ("on" name ("," name)*)?  -- the same, registers too
init    ::= "zeros" | "ones" | "eye" | "arange" | "full" exp | ("str")? string
          | "input" | "input" "str"
          | ("[")? exp ("," exp)* ("]")?
thread  ::= "{" stmt* "}"
ifstmt  ::= "if" exp thread ("else" (thread | ifstmt))?
label   ::= "::" string
parg    ::= string | name ( "[" exp ("," exp)* "]" )? | exp
param   ::= name | "%" reg                          -- a name, or a register
arg     ::= "%" reg | exp                           -- a register, or a value
call    ::= name "(" arg ("," arg)* ")"
addr    ::= "[" exp "]" | name ( "[" exp ("," exp)* "]" )? | range "[" exp "]"
range   ::= name "[" exp ".." exp? "]"              -- half-open; `hi` omitted is the last cell
region  ::= name | range                            -- `A` alone is all of A
exp     ::= conj ("||" conj)*
conj    ::= cmp ("&&" cmp)*
cmp     ::= sum (("<"|">"|"<="|">="|"=="|"!=") sum)?        -- non-associative
sum     ::= term (("+"|"-") term)*
term    ::= atom (("*"|"/"|"%") atom)*
atom    ::= "-"? number | name | "%" reg | "!" atom | "(" exp ")" | "input" | "#" name
          | "min" "(" exp "," exp ")" | "max" "(" exp "," exp ")"
reg     ::= number | name
```

Comments run from `--` to the end of the line. The reserved words are in `Lang.keywords`.

`print` writes a line and changes nothing: both interpreters erase it, so every theorem about a
program is a theorem about the program with its prints removed. It is refused inside a `parallel`
thread, where threads have no order between them and the value printed would be whichever one ran
first. Its argument is a buffer, a cell, a `const`, a register or an expression — with a bare name
meaning the *whole* buffer, the one place in the language where a name without a subscript is not a
cell. See `docs/print.md`.

Declarations are statements, because `free` is one: a buffer has a lifetime in the program text.
They are allowed only at the top level, where the whole program sees them — a `buf` or a `free`
inside one thread of a `parallel` would be visible to that thread alone. `slice` is the exception
and is allowed anywhere, because it places no cells: see § *Slices*.

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

## Variables

A variable is a cell of memory, and `let` is how one is declared:

```prl
let a = 1              -- buf a            — a scalar: `a` alone is its address
let msg = "hello"      -- buf msg[5]       — one cell per UTF-8 byte
let xs = [3, 1, 4]     -- buf xs[3]        — one cell per value
let n = input          -- buf n            — one value read while the file compiles
```

`let` is `buf` with the shape read off the initializer, and nothing else: the reader desugars it
immediately, so there is no `let` in the AST, none in `Layout`, and `Lang.print` prints the `buf` a
`let` became. An initializer that fits any size and fixes none — `zeros`, `ones`, `eye`, `arange`,
`full e`, `input str` — is refused under `let` with code `P006`, because the size would then have to
come from somewhere the statement does not name; those are written with `buf`, which states a shape.
A single value gives the *scalar* shape `[]` rather than `[1]`, which is the point of the form: a
scalar's address is the bare name, so `%t := a` and `a := %t + 1` read and write it, while a
one-element buffer would have to be written `a[0]`.

There is no second kind of state for a variable to live in. `State` is the whole store, `Loc` is the
whole address space, and a variable is a cell of it — so the only thing that distinguishes `let a`
from `buf A[1024]` is how many cells it names. That is also why a variable, and not a register, is
what a `parallel` block can update and what the next statement then reads: a register is not
addressable (`docs/block-ir.md` § Why `AExp` has no memory operand), so it has no footprint, so it
is invisible to `Indep` and private to its thread. Two threads incrementing `let g = 0` is reported
as a race on `g`; the same program written with `%g` would be reported independent and would be
wrong. § *Registers* below is the other half of this.

## Slices

A slice is a name for a sub-range of a buffer's cells. `A[lo..hi]` is the cells `[lo, hi)` of `A`,
counted flat whatever `A`'s shape, and `slice h = A[lo..hi]` gives that range a name:

```prl
buf s[16] = arange
slice first = s[0..4]       -- cells 0..3 of s
slice rest  = s[4..]        -- `hi` omitted is s's last cell, so 12 cells
slice inner = rest[1..3]    -- a slice of a slice; the cells are still s's
%t := first[2]              -- the same cell as s[2]
#first                      -- 4, folded to a literal while the file compiles
```

Two properties make this worth having rather than a convenience.

**A slice is a view, and copies nothing.** It compiles to `ArrRef.slice`, which is
`⟨base + lo, hi - lo⟩` — a base and a length, no cells of its own. So `h[i]` *is* `A[lo + i]`, the
heap has one copy of the data, and a write through the slice is a write to the buffer. Nothing is
allocated, which is the only possibility anyway: `State` is total and nothing is ever created
(`docs/semantics.md`).

**A computed subscript is bounded by the slice, not by the buffer.** This is the reason the form
exists. A subscript mentioning a register is not known at compile time, so `footprintOf` bounds it
by every cell the access could reach — `⟨a.cells, []⟩` for a `loadAt` — and `ArrRef.addr` wraps the
index on the range's length, so that bound holds with no hypothesis (`ArrRef.addr_mem_cells`). When
the range is the whole buffer, the bound is the whole buffer. When it is a quarter of it, the bound
is that quarter. The two verdicts differ:

```prl
buf s[16] = arange
parfor t in 4 {
  slice mine = s[t*4 .. t*4+4]
  %p := t + 1
  %c := mine[%p]
  mine[%p] := %c + 100
} :: "quarters"
```
```text
verdict   independent — par = seq under every schedule (wfB = true)
```

The same program with `s[%p]` and the index arithmetic written out reports

```text
verdict   footprint over-approximated: wfB says no, the heap check says yes
```

— the program is in fact independent, and the proof does not go through, because each thread's
footprint is all sixteen cells and the four footprints then overlap. So a slice does not merely
shorten the program: it is what turns a per-thread computed index from an unprovable program into an
instance of `par_seq_eq`.

A slice is also the one declaration a thread may make. `P106` keeps `buf`, `const` and `free` at the
top level because a thread-local view of *memory* would be visible to one thread alone; for a slice
that is exactly the intent — a thread naming the range it owns — and since it places no cells and
ends no lifetime there is nothing for the allocator or for `Arena.live_disjoint` to check. A `for`
body may declare one too: the name is dropped at the end of each iteration, as the loop variable is.

What is refused, all under `P110`: a range running past its buffer, and an empty one. The second is
not pedantry. `ArrRef.addr` wraps on `max len 1`, so a zero-cell slice would address the cell at
`lo`, which is outside itself and may belong to another thread.

A view of a buffer leaves scope when the buffer does, so `free A` ends the scope of every slice of
`A`. The cells would still be addressable — `free` is erased and returns space to the allocator —
and a name that outlived its buffer would denote cells a later declaration may own.

### `#A`

`#A` is the number of cells `A` has, as a slice or as a buffer, folded to a literal while the file
compiles. It therefore costs nothing at run time and is legal in both roles an expression has, an
address and a value. It is a sigil rather than a word because `len`, `size` and `cells` are each
already a name in `Examples/` — `const len = 2` in `sum.prl`, `buf cells[…]` in three others — and a
reserved word would have broken them (`CLAUDE.md` § *Surface-syntax tokens are global*).

`#A` is the buffer's *extent*, not the length of what is stored in it. For a string the two differ:
`docs/strings.md` records that a buffer has no length field and that `0` is the terminator, so the
length of the text in `s` is a scan for `0` and not a projection.

## Copying

`copy d from s` writes `s`'s cells into `d`'s, one at a time, in index order. Either side may be a
range, and a bare name is the whole buffer:

```prl
let m = "hello"
buf d[8] = zeros
copy d from m                -- 5 cells
copy d[5..8] from m[0..3]    -- and again, into the tail
```

It is sugar, and it dies in the reader: `copy` becomes a `for` over a loop variable and a register
whose names begin with a digit, which `ident` and `regName` refuse, so a program can neither name
one nor collide with one. Nothing downstream sees a `copy`, and `Lang.print` prints the stores it
performed.

Two consequences follow from there being no allocation. A `copy` cannot grow a buffer: the
destination is declared with room, and the trip count is the *source*'s length, so a short
destination is reported as a subscript outside it rather than silently truncating. And the program
is O(cells) in size, because `for` is unrolled — `copy d from s` for a 1,024-cell buffer is 2,048
statements. That is the model's ceiling rather than this statement's, and `docs/scale.md` measures
it: every loop in the language is unrolled, because `ParProg` has no rolled loop constructor yet.

Direction is written rather than positional for one reason: `d[0..] := s[0..]` would read like an
assignment, and an assignment between two ranges looks like it might be O(1) — an aliasing
assignment, as in Rust — when it is O(n) and unrolled. `copy` says what happens.

## Functions

`def` names a statement list, and a call writes it out:

```prl
def square(A, i) {
  %t := A[i]
  A[i] := %t * %t
}

buf A[4] = 1, 2, 3, 4
parallel { square(A, 0) } | { square(A, 1) }
print A                      -- 1, 4, 3, 4
```

A call is *expanded*, not performed. `ParM` has no call constructor and the machine has no stack, so
a `def` is a named piece of program text rather than a procedure: `Lang/Compile/Expand.lean`
substitutes the arguments for the parameters, writes the body out where the call stood, and what
reaches `ParProg` is the program with every call written out. A `def` is therefore closer to a Lean
`macro` than to a C function, and the comparison is exact in both directions — it costs nothing at
run time, and it cannot recurse.

Three consequences, all of them intended:

* **Every theorem applies unchanged.** The expanded program is an ordinary `ParProg`, so
  `footprintOf`, `wfB`, `par_seq_eq`, `execTask` and the autoparallelizer neither know nor care that
  a `def` was involved — exactly as they do not know that a `for` loop was unrolled.
* **A `def` cannot call itself**, directly or through another `def`. Expansion would not terminate,
  and `ParM` is inductive, so a recursive program has no representation to expand *into* either. The
  cycle is reported as `P113` with the chain of calls that closes it.
* **`to-prl` prints the expanded program.** A `def` is erased by the time there is a `ParProg` to
  print, so the round trip in `Lang/Compile/Print.lean` compares programs and not texts, as it
  already does for `for`, `copy` and `slice`.

### Parameters

Two kinds, told apart by their spelling, the way the rest of the language tells a name from a
register:

| parameter | the call supplies | substituted into |
|---|---|---|
| `A` | a buffer name, a slice name, a `const`, a loop variable, or any compile-time expression | every `A`, `A[…]`, `#A` and `A[lo..hi]` in the body |
| `%acc` | a register | every `%acc` in the body |

```prl
def axpy(Y, X, a, n) {            -- n cells of Y += a * X
  for i in n {
    %x := X[i]
    %y := Y[i]
    Y[i] := %y + a * %x
  }
}

def accumulate(%s, A, n) {        -- a register parameter: the caller names the register
  for i in n { %v := A[i]; %s := %s + %v }
}
```

A name parameter is a *name*, so `axpy(C, A, 2, 4)` and `axpy(lo, hi, 2, 4)` both read, where `lo`
and `hi` are slices: a slice is a name for a range, and the body never learns which it was given. A
range has no spelling of its own as an argument — write `slice lo = C[0..4]` first, which a thread
may do for itself. An argument that is
not a name is a compile-time value, and `n` in the body is then the literal — which is what lets
`for i in n` unroll inside a function at all.

A register parameter is how a result leaves a call without going through memory. The argument is
written `%r`, and `%r` alone: an argument with an operator in it is a value, by the same rule that
makes `%p := n` a load and `%p := n + 1` an assignment.

### Hygiene

Every register in a `def` body that is not a parameter is *local*: it is renamed, per call site, to
a name the file does not use, so two calls never share one and a call never clobbers a register the
caller is still holding. `%t` in `square` above becomes `%t'1` in one expansion and `%t'2` in the
other. The suffix is `'` and a number, both of which `ident` already accepts, so the expanded
program is still a program a person could have written. A `slice` declared in a body is renamed the
same way and for the same reason.

A call *site* is a place in the program text, not a place in the run: a call inside `for i in 4` or
`parfor i in 4` is one site however many iterations or threads the loop unrolls to, so all four get
the same renamed registers. For `for` that is what the loop would do with its own registers anyway,
and for `parfor` it is not sharing at all — registers are thread-private (§ *Registers*), so each
thread is handed the pre-fork register file and what it leaves is discarded.

Hygiene is not only tidiness here. The parallelizing pass refuses to split a chain whose statements
share a register (`noRegFlow`, `docs/autopar.md`), so two calls that both wrote `%t` would be
sequential by construction — the hygienic rename is what lets `autopar` put two calls of one `def`
in the same fork.

### What a body may not contain

A `def` body holds statements, and the ones it may not hold are those whose meaning is positional in
the file as a whole: `buf`, `const`, `reg` and `free`, which place memory and end its lifetime, and
would do so once per call; and `input`, whose values are consumed in the order the file reads them
(§ *Input*). A nested `def` is refused for the same reason a declaration is — the file is where a
name becomes visible to the whole program. All five are `P106`. `slice`, `synchronize`, `print`,
`parallel`, `parfor`, `for`, `if` and `while` are all allowed, and a body may call another `def`.

A call is a statement and nothing else. There is no `%r := f(…)`: a `def` has no return value,
because a value coming out of a call would have to be a register or a cell, and both are already
sayable — pass `%r` in, or write to the buffer the caller named. For the same reason a call cannot
appear inside an expression, where a statement has no meaning.

### Why not a call in `ParProg`

A `call` constructor would need a semantics in both interpreters, a footprint, a `wfB` case and a
clause in every proof that matches on `ParProg` — and it would buy nothing a reader can see, because
a non-recursive call has exactly the meaning of its body. The cost is paid in program *size*, which
is the ceiling the whole language already lives under: `for` is unrolled, `copy` is a `for`, and
`docs/scale.md` measures where that ends. Rolled loops and a call node are the same future work and
would arrive together, if they arrive.

## Claims: `assert f(…) == g(…) on A`

`par_seq_eq` is about one program. A reader with a sequential sort and a parallel one is asking
something else — whether *these two programs* compute the same thing — and `assert` states that
question:

```prl
def bubble(A, m)  { … }                -- no parallel block at all
def oddeven(A, m) { … }                -- parfor + synchronize

buf A[8] = 5, 3, 8, 1, 7, 2, 6, 4
const n = 8

assert bubble(A, n) == oddeven(A, n) on A
```

The file is compiled **twice**: once with the left call's body written out where the `assert`
stands, once with the right's. Everything else — every declaration, every initializer, every
statement before and after — is shared, so the two programs start from one heap. `paralever check`
reports the claim beside the verdict, exits non-zero when it fails, and `paralever prove` writes
`ParProg.AgreeOn`, which says that every outcome either program reaches, under every schedule of
either, holds the same values at the named cells.

What makes this cheap is that the question factors. Each side's schedules agree with its own
sequential reading — that is `par_seq_eq`, twice — so what is left is whether two programs with no
fork in them compute the same thing, which is decided here by running both on the heap the file
declares. The rationale, the three things `AgreeOn` deliberately does not compare, and what it
would take to lift the last step to every heap are in `docs/equivalence.md`.

| rule | why |
|---|---|
| each side is a *call*, not a block | both sides get a name a report can print, and argument checking is the one already written for a call |
| at most one `assert` per file (`P114`) | a claim is two programs; a second would be a third and a fourth |
| top level only (`P106`) | each side is a whole program, not a statement reached at a point in a run |
| `on` names buffers; omitted, every live one | a parallel version commonly needs scratch its sequential counterpart does not, and the two will leave that scratch differing while agreeing on everything observable |
| `to-prl` prints the left program | the claim is erased by the time there is a `ParProg`, as a `def` is |

### `assertParSeq` — the register file too

`AgreeOn` compares the named cells of the final heap and nothing else, so a side can carry work that
lands only in a register and still agree everywhere the claim looks. `assertParSeq` is the same
surface form under a second keyword, and it compares the final register file as well:

```prl
assertParSeq counted(S, P, X, n) == miscounted(S, P, X, n) on S
```

```text
claim     counted == miscounted on S, and {%acc'3, %cnt'4, %p'5}
          DISAGREE — {%cnt'4} (1 of 3 register(s) compared; every compared cell agrees)
```

`paralever prove` writes `ParProg.AgreeParSeq` for such a file, which is `AgreeOn`'s conclusion
together with the final register file — the pair `ParSeqEq` quantifies, rather than its heap half.

The registers are not named in the file. They are derived as both sides' *written* registers, and a
`parallel` block writes none the parent can see, so what is compared is what either side leaves
outside a fork. A consequence worth knowing before reaching for the keyword: `assertParSeq` passes
only when both sides write the same registers outside their forks, which makes it the check for a
refactor and the wrong check for a sequential program against a parallel one. `docs/equivalence.md`
§ What `assertParSeq` adds has the reasoning and the two examples.

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

## Conditions

`if` and `while` take an expression and test it against zero, so a condition is an ordinary
expression rather than a second grammar. What the reader adds is the spelling:

```text
if (%i < n) { … } else { … }
while (%r != 0) in 16 { … }
if ((%i >= 4) && (%i != 6)) { … }
if (%k == 0) { … } else if (%k == 1) { … } else { … }
```

`else if` chains: the `else` arm is the one statement the next `if` reads, so the braces around it
are not written. It is sugar and nothing downstream sees it — `ParProg` has one `ifElse`, so the
chain is the nest, and `to-prl` prints the nest back.

Six comparisons (`<`, `>`, `<=`, `>=`, `==`, `!=`), two connectives (`&&`, `||`) and a prefix `!`,
desugared by the reader into the three primitives `AExp` actually has — `lt`, `eq` and `not`. The
derivations are in `docs/block-ir.md` § *Conditions*, together with the reason there are three and
not nine.

Five precedence levels, loosest first: `||`, then `&&`, then the comparisons, then `+`/`-`, then
`*`/`/`/`%`. A comparison **does not chain**: `a < b < c` is a parse error rather than
`(a < b) < c`, because the second reading is almost never what was written. Two-character operators
are matched before one-character ones, so `<=` never reads as `<` followed by a stray `=`.

Because the parser desugars, a condition is already a plain `AExp` by the time anything downstream
sees it — `footprintOf`, `wfB`, `autoPar` and `par_seq_eq` need no case for conditions, and a guard
reads no memory, so no footprint grows. What a condition does change is the *path*, and that is
`ifElse`'s footprint over-approximation, described in `docs/block-ir.md` § *Control flow*.

The round trip keeps the spelling. `a >= b` and `!(a < b)` are the same term, and `&&` is a `min` of
two normalized values, so a printer matching only constructors would hand back
`min(!(!(!((%0 < 4)))), …)`. Both printers instead recognize the derived shapes, and
`if ((%0 >= 4) && (%0 != 6))` comes back verbatim — which is what `Lang/Compile/Print.lean`'s
`roundTrips` gates.

## Input

A program reads from the shell the way every other language does — through the pipe, with no option
to pass:

```bash
paralever run double.prl < data
echo "3 1 4 1" | paralever run double.prl
```

There are three forms, and nothing else is needed:

```text
%n := input              -- one value into a register
buf A[4] = input          -- one value per cell, row-major
buf msg[16] = input str   -- a line, as its UTF-8 bytes (docs/strings.md)
```

A numeric value is a whitespace-separated word read as an integer, and `true` and `false` read as
`1` and `0` — which is what a condition tests. A `str` input takes the rest of the line, skipping
leading whitespace, so it can follow a numeric read on an earlier line.

### Read while the program compiles

The input is consumed at **lowering** time, not at run time. `%n := input` with `10` on the stream
compiles to `%0 := 10`; `buf A[4] = input` compiles to the declaration `buf A[4] = 3, 1, 4, 1`. The
program that results has no trace of where the values came from.

That is the whole design, and it buys three things:

- **No constructor is spent.** `ParProg` gains no statement and `ParM` gains no constructor, so
  `footprintOf`, `wfB`, `autoPar` and `par_seq_eq` are untouched. An input form is not a kind of
  access, because by the time there is a program there is no input left.
- **No hidden buffer.** A run-time read would have to put the value *somewhere*, and every location
  in this language is declared (§ *Declaring memory*). Resolving at compile time means the value
  lands in the cell the program already declared for it.
- **The resolved program is an ordinary file.** `paralever to-prl prog.prl < data` prints a `.prl`
  file with the values written in, which compiles, runs and proves like any other. So input and
  proof are not in tension: resolve first, prove second.

```text
   data ──┐
          ├──► parse ──► lower ──► Layout × ParProg ──► check / run / to-prl
   prog ──┘            (input consumed here)
```

Standard input is read only when the file's text contains an `input` form (`File.usesInput`), so a
program without one never waits on a pipe.

### Where `input` may not appear

Four refusals, all the same reason: the values a program reads, and the order it reads them in, must
be fixed by the program text.

| refused | why |
|---|---|
| inside a `parallel` thread | threads have no order between them, so neither would the reads |
| inside a `parfor` body | the same, one thread per index |
| inside an `if` or `else` branch | whether the branch runs is a run-time fact |
| inside a `while` body | how many times it runs is a run-time fact |

A `for` loop is **allowed**, and reads once per iteration — it is unrolled at compile time, so its
iterations have an order and a count that the text fixes:

```text
for i in 3 { %t := input; A[i] := %t }
```

The check is not a syntactic scan. Each nested body is compiled and the input cursor compared: if a
body consumed anything, that body is refused. So the rule is enforced by the one mechanism that
cannot drift from the consumption itself.

`input` is also refused *inside* an expression — `%r := input + 1` names no order between the read
and the arithmetic — and inside an address, where the message points at the register form. It is a
statement, and the statement is `%r := input`.

### What cannot read it

`prl_file "prog.prl"` and `paralever prove` both refuse a program that reads input, because both
re-read the file while **Lean** elaborates and Lean has no pipe to offer it. Both say so, and both
point at the same fix:

```bash
paralever to-prl prog.prl < data > resolved.prl    # then prove resolved.prl
```

`Lang.Compile.Lower`'s `compile` and `ofString` take the input text as an argument defaulting to
`""`, which is what lets a `#guard` supply a stream without one, and what makes a program that reads
input with nothing piped in fail with "input is exhausted" rather than hang.

There is no `output`. Printing is not a heap effect, `ParM` has no constructor for it, and what a
program computed is its heap — which `run` prints (§ *Using one from Lean*).

## What a `.prl` file cannot say

A Lean `paralever { … }` block takes Lean `term`s for its addresses and values, so any Lean
expression of the right type works: `[n * 2 + 1]`, `%(f i)`, an address computed by a Lean function,
or a `ParProg` combinator spliced in. A `.prl` file has none of that, because the reader cannot call
the elaborator and `lake`'s copy of the file has to mean the same thing as the author's. The closed
expression language above, `const`, and `for`/`parfor` unrolling are what it has instead.

Labels (`:: "name"`) attach to `parallel` and `parfor`. A `.prl` file cannot name anything else; the
Lean notation can, with `{ … } :: "name"` (below), so a label the library puts around a lone
statement survives printing to Lean but not printing to `.prl`.

## The Lean form

`Lang.toLean` prints a file as a `Layout` and a `paralever { … }` block. Every `ParProg`
constructor has a surface form, so the two surfaces say the same things:

| `.prl` | Lean | `ParProg` |
|---|---|---|
| `%0 := [4]` | `%0 := [4]` | `load` |
| `A[1, 2] := %0` | `[L.at "A" [1, 2]] := %0` | `store` |
| `%i := idx[t]`, `t` a register | `%i := [L.ref "idx", %t]` | `loadAt` |
| `dst[%i] := 1` | `[L.ref "dst", %i] := 1` | `storeAt` |
| `parallel {…} \| {…} :: "name"` | the same | `label (par …)` |
| `parfor i in n {…} :: "name"` | the same | `label (parFor …)` |
| — | `{ … } :: "name"` | `label` around anything |
| `buf A[6] = 1, 2, 3` | `buf "A" [6] (data [1, 2, 3])` | — (a `Layout`) |
| `buf S[4] at 100`, `free A` | an explicit `base`, or `Arena.of` | — |

Two of those rows are syntax rather than a translation, and neither reserves a token (`CLAUDE.md`
§ *Surface-syntax tokens are global*):

* `[A, e]` is the data-dependent access. `[l]` names a cell by its address; the comma form names it
  by range and index, which is the pair `loadAt` and `storeAt` take. Lean cannot spell it `A[e]` —
  that is `GetElem` — and a comma inside the brackets a cell address already uses needs no keyword.
* `{ … } :: "name"` names a region that is not a fork. `parallel` and `parfor` carry their own
  `::`; this is the general form, because `ParProg.label` takes any statement.

Initial contents print as `(data [...])` rather than as a bare list. `Init` is `List Nat → List Int`
and `Coe (List Int) Init` is declared, but a list literal in that position elaborates as `List Nat`,
so the coercion never fires and the printer names `data` itself.

The layout prints in one of two forms, decided rather than chosen. `Layout.of` places buffers
consecutively from 0, so it reproduces the addresses a program was compiled against only when the
file placed nothing with `at` and freed nothing. Otherwise the bases are printed — `arena.prl`'s
`out` and `tmp` share base 4, which no allocation can produce — because a layout that moved an
address would be a different program.

What stays file-only is the declaration syntax and the separator: `const`, `reg`, `buf`, `free`, and
a newline between statements. In Lean the memory is a `Layout` or an `Arena` term (`docs/layout.md`
§ *Lifetimes* has `buf`/`free` as library functions) and statements are separated by `;`.

`Test/LeanForm.lean` writes `sum.prl`, `scatter.prl` and `arena.prl` out by hand in Lean and gates
each against the compiled file: the same addresses, the same initial cells, the same program up to
`;`-associativity, and the same heap after a run. The three were chosen because they are the files
whose Lean form needed the forms above — a label, a computed access, and an arena.

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
verdict it is labelled with, and — for seven of the files `wfB` accepts — proves the instance
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
| `funcs.prl` | `def`: one row of a matrix-vector product, called from four threads over slices |
| `sortnet.prl` | one comparator called 28 times: eight phases of a sorting network, with barriers |
| `equiv.prl` | `assert`: a sequential sort against a parallel one, built from one comparator |
| `twofold.prl` | `assert`: two *different* parallel sums, agreeing on the one cell `on` names |
| `strength.prl` | `assertParSeq`: two programs agreeing in memory *and* in the register file |
| `tally.prl` | `assertParSeq`: a loop-peeling bug that leaves the heap identical and `%cnt` wrong |
