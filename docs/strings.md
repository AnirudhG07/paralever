# Strings — a buffer of bytes, not a value

Code: `Lang/Core/Layout.lean` (`str`, the `Coe String Init` instance), `Lang/Compile/Ast.lean`
(`BufInit.str`), `Lang/Compile/Parse.lean` (`strLit`, the `str` initializer).

## Two places a string could live

A string has to be somewhere, and the program model offers exactly two places.

**As a value.** Add `| str : String → Val` to `Core/ParM.lean`'s value universe. One cell holds the
whole string, `load`/`store` move it in one step, and Lean owns the storage — `String` is already a
Lean type with every operation on it already written.

**As a buffer.** A string is a region of cells, one byte per cell, and the language sees bytes. Lean
owns the storage only at *elaboration* time: `s.toUTF8` runs in the metalanguage and nothing but
integers reaches the heap.

The second is what is implemented, and the reason is not convenience.

## Why the buffer

The theorem this project proves is about *locations*. `Indep f g` is three intersections of location
lists (`docs/access.md`); `par_seq_eq`'s hypothesis is discharged by showing two threads touch
disjoint cells. A `Val.str` puts a string at **one** location, so:

- two threads working on different halves of a string conflict at that single cell, and the
  independence check refuses what is plainly independent;
- any operation on the string's *contents* happens inside a Lean function applied to a `Val`, which
  `footprintOf` cannot see into and `wfB` cannot reason about;
- `par_seq_eq` for a string-processing program would hold, and would say nothing about the string.

That last point is the vacuity failure `CLAUDE.md` warns against. The theorem would be true and
empty.

One byte per cell gives the opposite. `uppercase` over a 16-cell string is sixteen independent
single-cell updates, so

```text
   msg [16] @0   'h' 'e' 'l' 'l' 'o' …
                  ↑   ↑   ↑   ↑   ↑
                  t0  t1  t2  t3  t4      writes {0} {1} {2} {3} {4} — pairwise disjoint
```

and the obligation is `Layout.disjoint`-shaped: exactly the machinery `docs/layout.md` § *Two facts
a proof wants* already provides, with the same `by decide` ending. A `strlen`-shaped scan has
something to be parallel over; a split-and-merge has halves that are provably disjoint ranges via
`Theory/Intervals.lean`.

## What it costs

Three consequences, all of them visible in the surface language rather than hidden.

**Non-ASCII characters take several cells.** `str` is `s.toUTF8`, so `é` is two cells and an emoji
is four. The alternative — one Lean `Char` per cell as a codepoint — would make `[msg, i]` an index
into codepoints, which no byte-level operation can then compute with. UTF-8 is the encoding the heap
holds, and the language is honest that a cell is a byte.

**A string longer than its shape is refused, not truncated.** `buf msg[8] = str "hello, world"`
declares 8 cells and 13 bytes of contents, which `Layout.wfB` rejects:

```lean
L.bufs.all (fun p => p.init.length ≤ p.toBuf.size)
```

`rows` truncates (`docs/layout.md`), `str` does not, and the difference is deliberate: a padded row
of a matrix is a shape decision, while a silently cut string is a bug the layout check can catch for
free.

**There is no length field.** A buffer has a shape, and a string shorter than its shape leaves the
remaining cells at `0` — so `0` is the terminator, as in C, and `strlen` is a scan for it rather
than a projection. Nothing in the model could carry a length anyway: `State = Loc → Val` is total
and has no notion of an allocated extent (`docs/semantics.md`).

## The surface forms

```text
buf msg[16] = str "hello"      -- UTF-8 bytes, one per cell, rest 0
```

```lean
buf "msg" [16] (str "hello")   -- the Lean form
buf "msg" [16] "hello"         -- the same, through `Coe String Init`
```

The coercion exists so a declaration stays one line; `str` is spelled out in the `.prl` grammar
because a bare `"…"` there is already a region name (`{…} :: "name"`), and the parser must not have
to guess which it is reading.

The parser's own helper for a quoted string is `strLit`, not `str` — `Paralever.Lang.str` is this
initializer, and a second `str` in the same namespace shadows it. That is the ordinary name-collision
rule, not the global token reservation (`CLAUDE.md` § *Surface-syntax tokens are global*): `str` is
in the `.prl` keyword list, which costs nothing in Lean, because the `.prl` reader is a parser
written by hand rather than Lean `syntax`.

## Why character operations are sequential

A byte offset is a constant the compiler folds; a character offset is not. To address character *i*
of a UTF-8 buffer you have to know how many bytes characters `0 … i-1` occupied, which means reading
them, which makes the address depend on data. And a data-dependent subscript is bounded by every
cell it could reach (`docs/block-ir.md`), so the footprint of a per-character access is the whole
buffer. Measured on a five-byte string:

```prl
parfor i in 4 { %c := s[i]  ;  s[i] := %c - 32 }            -- i is unrolled to a constant
```
```text
reads     {s[0], s[1], s[2], s[3]}
writes    {s[0], s[1], s[2], s[3]}
verdict   independent — par = seq under every schedule (wfB = true)
```
```prl
parfor i in 4 { %p := 2 * 1 ;  %c := s[%p] ;  s[%p] := %c - 32 }   -- the index is in a register
```
```text
reads     {s[0], s[1], s[2], s[3], s[4]}
writes    {s[0], s[1], s[2], s[3], s[4]}
verdict   RACY — 3 conflicting fork(s): {s[2], …}
```

So `input.prl` — one thread per byte, sixteen singleton footprints, `wfB` accepting — works *because*
a cell is a byte. Character indexing would make every thread's footprint the whole string, reads
would overlap writes, and every per-character `parfor` in the language would be refused.

That places decoding, `strlen`, normalization and grapheme clustering with the sequential kernels:
each reads a prefix to find the next position, so each is a scan, and a scan has no parallel form
under the rule `docs/reductions.md` works from — a kernel is parallel when it factors as a map
composed with a reduce over an associative operator, which a prefix-dependent position does not.
They belong in `Lib/`-style kernels with their own one-shot theorems, as `docs/reductions.md`
describes, not as expression forms.

A slice recovers the parallelism wherever the *ranges* are known even though the indices are not
(`docs/prl.md` § Slices): four threads with a computed index into four disjoint quarters have four
disjoint footprints, and `wfB` accepts. What a slice cannot recover is a split on character
boundaries, because finding those boundaries is the scan.

## What is not here

**No string operations in the language.** There is no concatenation, no comparison, no formatting.
A program that processes a string reads and writes bytes with the ordinary `loadAt`/`storeAt`, which
is what makes its footprint computable. Operations belong in `Lib/`-style kernels with their own
one-shot theorems (`docs/reductions.md` is the pattern), not in `AExp`.

**No output.** Printing a string is not a heap effect and `ParM` has no constructor for it;
`Layout.render` shows a buffer's contents for debugging, from outside the program.

**`Val.str` is still the wrong fix.** `Core/ParM.lean`'s docstring records the standing rule:
`Storable α` (`Lib/TypedRead.lean`) encodes richer types into the three existing constructors, so
adding a `Val` constructor is never the answer. A string is a buffer, and a *character* is already
`Val.int`.
