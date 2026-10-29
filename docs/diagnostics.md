# Diagnostics — a code, a span, and a reason

Code: `Diag.lean`, its own library so both front ends can report through it and neither depends on
the other. Consumers: `Lang/Compile/Parse.lean`, `Lang/Load.lean`, `Tool/Run.lean`.

## What was wrong with the old messages

A `.prl` file with a syntax error produced this:

```text
double.prl:5:8: expected ':=' after a register (at: := input)
```

Three faults, and they are the three a production compiler does not have.

1. **No code.** Nothing to look up, nothing to grep for in a build log, nothing stable to cite in a
   bug report. The message text *is* the identifier, so rewording it breaks every reference to it.
2. **No source.** The reader knows the line and column and does not show the line, so the
   programmer has to go and count characters.
3. **No reason.** `expected ':=' after a register` says what the parser wanted. It does not say why
   a register assignment needs one, which is the thing a newcomer is missing.

## The shape taken instead

rustc's discipline, which is the most carefully designed of the ones surveyed, has three separable
parts, and all three are worth copying:

- **A unique code per error class**, `E0001`-style, each with a *long-form explanation* that
  explains the underlying rule rather than restating the message. `rustc --explain E0308` prints it.
- **The minimal span.** The caret points at the smallest range that is actually wrong, not at the
  enclosing statement.
- **A main message that stands alone.** The first line is a complete sentence; notes and helps are
  additions, never the place the real information hides.

So a diagnostic here is:

```text
error[P101]: 'B' is not declared
 --> double.prl:6:3
  |
6 |   B[i] := %t * 2
  |   ^
  |
  = note: a buffer must be declared before it is used, because `State` is total and declaring is
          the only way to obtain memory
  = help: add `buf B[4]` above, or subscript an existing buffer
```

and `paralever explain P101` prints the rule on its own.

## Codes classify kinds, not sites

The `.prl` front end has 46 places that can fail. It does **not** have 46 codes: a code names a
*kind* of mistake, so all twenty-one of the reader's `expected …` failures are one code whose
message says what was expected. The grouping is what makes a code worth looking up — a code that
occurs at exactly one source location explains nothing a message could not.

| code | kind |
|---|---|
| `P001` | unexpected token — the reader expected something else here |
| `P002` | a reserved word used as a name |
| `P003` | an unterminated string literal |
| `P004` | input left over after the program |
| `P005` | a load in expression position |
| `P006` | a `let` whose size cannot be read off its initializer |
| `P101` | an undeclared name |
| `P102` | a name declared twice |
| `P103` | two buffers placed on the same cells |
| `P104` | more initial values than the buffer has cells |
| `P105` | an address that is not known at compile time |
| `P106` | a statement out of place |
| `P107` | an operator used in the wrong role |
| `P108` | `input` where the order of reads is not fixed |
| `P109` | the input stream does not supply what the program asks for |
| `P110` | a slice that is not inside its buffer |
| `P111` | a `print` argument with no spelling of its own |

`P` is the `.prl` front end; `M` is MLIR and `T` the command line, and those are not yet converted.
The registry is one list, so a code cannot be issued without an explanation existing for it, and
`Test/Diag.lean` gates that every code in the table is reachable and distinct.

## Positions stay lazy

`Diag`'s `Pos` is a line and a column, and nothing computes one until a diagnostic is rendered.
This is not a style preference. `Lang/Compile/Parse.lean`'s `PErr` carries a bare offset precisely
because `attempt` throws most failures away, and the MLIR reader — which backtracks far more — went
from 20.54 s to 0.40 s on a 14,451-line file when its messages stopped being built eagerly
(`docs/scale.md` § *Where the time went*). A diagnostics layer that resolved a position at every
failure would hand that cost straight back.

So the division is: readers carry offsets, `Diag.Source` converts an offset to a `Pos` exactly once,
on the failure that escaped.

## What is not here yet

- **Spans on lowering diagnostics.** The surface AST (`Lang/Compile/Ast.lean`) carries no
  positions, so a `P1xx` diagnostic names the rule and the file and has nothing to point a caret at.
  The reader's `P0xx` codes do have spans, because the reader knows the offset it failed at. Giving
  `Stmt` a span is the fix and is the same change MLIR's `Op` needs.
- **Multi-error recovery.** The first failure still aborts. Collecting diagnostics needs a
  resynchronization point in each reader (the statement separator, for `.prl`), and the `Except`
  plumbing has to become a writer. Recorded as the next step rather than half-done.
- **MLIR spans.** `MLIR/Ast.lean`'s `Op` carries no position, so an MLIR diagnostic can name the
  module and not the op. Adding the field breaks one positional construction site
  (`MLIR/Emit.lean`), and MLIR's own `loc(…)` is the thing to read back into it.
- **Signals.** A `paralever` interrupted during a race search exits through Lean's default handler,
  so the exit code is not `130` and a half-written `-o` file is not cleaned up. The conventions are
  settled (`128 + signum`; SIGTERM is shutdown, SIGINT is the developer's stop; on a second signal
  of the same kind, exit immediately rather than trying again), and `Tool/Run.lean` is where they
  belong.

## References

- rustc's error-code index and `--explain`: a stable code per error class, each with a long-form
  explanation of the rule, and diagnostics whose first line stands alone.
- clang's caret diagnostics, which are where the `-->`/`^^^` rendering comes from.
- MLIR's `Location` attribute (`loc(…)` on every op), which is how the MLIR front end will get
  spans without inventing a side table.
