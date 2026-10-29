# `print` — output, and nothing else

A `.prl` program used to have no way to say anything: its output *was* the heap it left. `print` adds
one, under one constraint — it must not change what any theorem says.

## Erased, and a barrier

`ParProg.print` carries a list of `PrintItem` and both interpreters send it to `.pure ρ`:

```lean
@[simp] theorem execPar_print (is) (ρ) : execPar (.print is) ρ = .pure ρ := rfl
@[simp] theorem execSeq_print (is) (ρ) : execSeq (.print is) ρ = .pure ρ := rfl
@[simp] theorem footprintOf_print (is) : footprintOf (.print is) = Footprint.empty := rfl
```

That is the whole of "the proofs ignore those lines", and it is stated as an equation rather than left
as a convention. `ParProg.dropPrints` removes them, and `execPar_dropPrints` / `execSeq_dropPrints`
prove both interpreters agree with the original, so `parSeqEq_dropPrints_iff` makes `par_seq_eq` about
`s` and about `dropPrints s` the same theorem. That is what licenses `Examples/Language/Stripe.lean`
to gate a hand-written program against a file that ends in `print k`.

An erased statement is still a statement, and the one thing it does carry is a **barrier for the
parallelizer**. `Lang/Core/Analysis.lean`'s `canParSeg` refuses to group a `print` with anything, so a
print is always its own group and the statements around it keep their order relative to it. Without
that, a print's footprint is empty and nothing would stop `autoPar` from forking a statement past the
point where its value was observed.

A print is *not* a phase boundary. `joinPhases` emits `synchronize` between phases and could not put a
print back, so `isSynchronize` stays what it was and `isBarrier` is the predicate the grouping uses.

The proved rewrite route declines a print for the same reason it declines a `synchronize`:
`AutoPar.rewriteOk` requires `ParProg.barrierFree`, because `emit` wraps every stage in a `par` and a
barrier reaching the plan would end up inside a thread — which `Lower` then refuses on re-read
(`Diag.p106`), breaking the round trip. A program with a print therefore takes the greedy phase route,
whose `planPhase` emits a one-statement group as a bare statement and so leaves the print where it was.
-- ref: `docs/autopar.md` § The proved route declines

## Where a print may not go

Inside a `parallel` thread, refused with `P106`:

```console
error[P106]: 'print' cannot appear inside a 'parallel' thread
note: a print is erased from the program, so its value is read off the sequential run — and
      threads of one fork have no order between them
help: print after the block, where the heap it left is what the program means
```

A print is erased, so its value is read off the canonical sequential run. Threads of one fork have no
order between them, so a print inside one would name a value no schedule agrees on. Refusing it is
what keeps the output deterministic for a program the checker accepts — the same reason `input` is
refused there (`docs/prl.md` § *Input*).

A `for`, `if` or `while` body is a chain spliced into the one that encloses it, not a thread, so a
print is legal in all three and `for` is the useful case: one line per iteration.

## The surface form

```prl
print A              -- a whole buffer
print A[1, 2]        -- one cell
print n              -- a scalar buffer, or a const
print %p             -- a register
print 2 * %p + 1     -- any expression over registers
print "p =", %p, A[%p]   -- several items, one line
```

A bare name is the **whole buffer** — the one place in the language where a name without a subscript
is not a cell, because `print k` is how a reader asks to see `k`. A `const` under the same spelling is
its value, since `const` is folded away before the program exists.

A name and an expression are told apart the way `%r := …` tells a load from an assignment: a bare name
is the buffer only when the argument ends there, so `print n + 1` reads `n` as an address, cannot
continue, and is re-read as an expression. The operator decides.

A `slice` name is refused with `P111`. A slice declares no memory, so it is erased once the file
compiles and `to-prl` cannot write it back; a printed program that mentioned one would not read as
itself. Print the buffer, or the cell by its own name.

## Where the output comes from

No interpreter produces it — that is the point of the erasure — so `Lang/Report.lean`'s `outOf` walks
the program and collects the lines. The walk handles exactly three constructors: `print`, and the
`seq` and `ifElse` spines it has to descend to reach one. **Everything else it hands to
`runSeq ∘ execSeq`**, the interpreter the theorems are about, so the heap a print sees is the heap the
semantics gives rather than a second reading of the program.

That leaves one thing to check, and `Test/Print.lean` checks it: the heap `outOf` leaves equals the
heap `runTaskSeq` leaves, at every declared cell, for every program in the file. A drift between the
walk and the interpreter is a build failure.

A cell and a buffer print as `name = value`, so a line says what it is with no label:

```console
$ paralever run Examples/Language/branch.prl
output — what this program's print statements wrote, on the canonical run
A = [1, 2]

heap after the run — the cells the program left behind, which is most of what it says
...
```

One line per print, with a matrix as `[[0, 1, 2], [3, 4, 5]]` — unlike `run`'s view of the whole heap,
which gives a matrix a line per row, because a print sits in a sequence of prints a reader is
following.

## `print` is a reserved word, and `toPrl` is why

`syntax "print " term : impStmt` in `Lang/Core/Notation.lean` reserves `print` for the whole project,
so no declaration may be named it. `Lang/Compile/Print.lean`'s `.prl` writer was called `print`; it is
now `toPrl`. That is the trade `CLAUDE.md` § *Surface-syntax tokens are global* says to check before
reserving a word: the keyword is spelled the way a reader expects, and one bare name is spent.

The constructor survives the reservation, because an identifier carrying a namespace is lexed as one
token — `ParProg.print` and `.print` are both still usable.

## Not in scope

- Output from inside a `parallel` block. Refused, above.
- A format string. Items are concatenated with a space; a literal is how a line is labelled.
- MLIR. `print` has no spelling in the op set the reader supports, so `to-mlir` refuses a file with
  one rather than dropping it silently.
- Reading. `input` is the other direction and is consumed while the file compiles
  (`docs/prl.md` § *Input*).
