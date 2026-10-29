/-! # `Diag` — diagnostics with a code, a span and a reason

Its own library, below both front ends: `Lang` and `MLIR` report through it and neither depends on
the other. Nothing here is imported from Mathlib or from `Paralever`, so a reader can be checked on
its own.

Rationale, the code table, and what is not here yet: `docs/diagnostics.md`. -/

namespace Paralever.Diag

/-! ## Positions

A `Pos` is a line and a column, both 1-based, because that is what an editor shows. Nothing
computes one until a diagnostic is rendered — a reader carries a bare offset, and `Source.posAt`
converts it once, on the failure that escaped.
-- ref: `docs/diagnostics.md` § Positions stay lazy -/

structure Pos where
  line : Nat
  col  : Nat
  deriving Repr, DecidableEq, Inhabited

instance : ToString Pos := ⟨fun p => s!"{p.line}:{p.col}"⟩

/-- A range of source, as offsets. `start == stop` is a point, which renders as one caret. -/
structure Span where
  start : Nat
  stop  : Nat
  deriving Repr, DecidableEq, Inhabited

/-- A span covering one character. -/
def Span.at (off : Nat) : Span := ⟨off, off⟩

/-- A span of `n` characters from `off`. -/
def Span.of (off n : Nat) : Span := ⟨off, off + n⟩

/-! ## Codes

A code names a *kind* of mistake, not a source location: the `.prl` reader's twenty-one
`expected …` failures are one code whose message says what was expected. A code that occurs in one
place explains nothing a message could not. -/

/-- A diagnostic code: the identifier, the rule it names, and why the rule exists. `why` is the
long-form explanation `explain` prints, and is about the rule rather than the occurrence. -/
structure Code where
  id    : String
  title : String
  why   : String
  deriving Repr, DecidableEq, Inhabited

inductive Severity where
  | error | warning | note
  deriving Repr, DecidableEq, Inhabited

def Severity.label : Severity → String
  | .error   => "error"
  | .warning => "warning"
  | .note    => "note"

/-- One diagnostic. `msg` is a complete sentence and stands alone; `notes` and `hints` add to it and
are never where the real information is. -/
structure Diagnostic where
  severity : Severity := .error
  code     : Option Code := none
  msg      : String
  span     : Option Span := none
  notes    : List String := []
  hints    : List String := []
  deriving Repr, Inhabited

/-! ## The source a diagnostic is rendered against -/

/-- A file's name and its lines, split once. -/
structure Source where
  name  : String
  lines : Array String
  deriving Repr, Inhabited

def Source.of (name text : String) : Source := ⟨name, (text.splitOn "\n").toArray⟩

/-- The line and column an offset falls on. One pass over the lines, which is why it is called once
rather than at every failure. -/
private def posIn : List String → Nat → Nat → Pos
  | [],      ln, rem => ⟨ln, rem + 1⟩
  | l :: ls, ln, rem =>
      if rem ≤ l.length then ⟨ln, rem + 1⟩
      else posIn ls (ln + 1) (rem - l.length - 1)

def Source.posAt (s : Source) (off : Nat) : Pos := posIn s.lines.toList 1 off

/-- The text of a 1-based line, or `""` past the end. -/
def Source.lineAt (s : Source) (n : Nat) : String := s.lines[n - 1]?.getD ""

/-- One step of `wrap`: `cur` is the line being filled, `acc` the lines already closed. -/
private def wrapGo (w : Nat) : List String → String → List String → List String
  | [],      cur, acc => acc ++ [cur]
  | x :: xs, cur, acc =>
      if cur.isEmpty then wrapGo w xs x acc
      else if cur.length + 1 + x.length ≤ w then wrapGo w xs (cur ++ " " ++ x) acc
      else wrapGo w xs x (acc ++ [cur])

/-- A paragraph broken at `w` columns on spaces, for the long-form explanations. -/
def wrap (w : Nat) (text : String) : String :=
  "\n".intercalate (wrapGo w ((text.splitOn " ").filter (· != "")) "" [])

/-! ## Rendering

clang's caret form, with rustc's gutter: the message, the location, the offending line, and a caret
under the span. -/

private def pad (w : Nat) (s : String) : String :=
  String.ofList (List.replicate (w - s.length) ' ') ++ s

private def indent (w : Nat) : String := String.ofList (List.replicate w ' ')

/-- The caret line: the span's columns marked under the source line. A tab in the source is copied
into the caret line so the marks stay under the characters they point at. -/
private def caretLine (src : String) (from_ to_ : Nat) : String :=
  let cs := src.toList
  let stop := max to_ (from_ + 1)
  String.ofList ((List.range (stop - 1)).map fun i =>
    if i + 1 < from_ then (if cs[i]?.getD ' ' == '\t' then '\t' else ' ') else '^')

/-- A diagnostic, as the command line prints it. No trailing newline: the caller's `println` adds
one. A diagnostic with no span still names the file, which is all a lowering error has
(`docs/diagnostics.md` § What is not here yet). -/
def render (s : Source) (d : Diagnostic) : String :=
  let head :=
    d.severity.label ++ (match d.code with | some c => s!"[{c.id}]" | none => "") ++ ": " ++ d.msg
  let body : List String :=
    match d.span with
    | none    => [" --> " ++ s.name]
    | some sp =>
        let p := s.posAt sp.start
        let q := s.posAt sp.stop
        let ln := toString p.line
        let w  := ln.length
        let text := s.lineAt p.line
        -- a span running past the line's end is clipped to it, so the caret never overhangs
        let stopCol := if q.line == p.line then max q.col p.col else text.length + 1
        [ indent w ++ "--> " ++ s.name ++ ":" ++ toString p
        , indent w ++ " |"
        , ln ++ " | " ++ text
        , indent w ++ " | " ++ caretLine text p.col stopCol ]
  let gutter := match d.span with
    | none    => ""
    | some sp => indent (toString (s.posAt sp.start).line).length
  "\n".intercalate ([head] ++ body
    ++ d.notes.map (fun n => gutter ++ " = note: " ++ n)
    ++ d.hints.map (fun h => gutter ++ " = help: " ++ h))

/-! ## The registry

One list, so a code cannot be issued without an explanation existing for it. `P` is the `.prl` front
end; `M` (MLIR) and `T` (the command line) are not converted yet. -/

/-- A code, named once so a reader cites `Diag.p101` rather than the string `"P101"`. -/
private def code (id title why : String) : Code := ⟨id, title, why⟩

def p001 : Code := code "P001" "unexpected token"
  "The reader reached a character it cannot continue from. The message names what it expected \
instead. A `.prl` file has a closed grammar — no user-defined syntax and no elaborator — so what \
is legal at a point is decided entirely by the position in the grammar (docs/prl.md § The grammar)."

def p002 : Code := code "P002" "a reserved word used as a name"
  "Every word in `Lang.keywords` is reserved, so a buffer, a register or a `const` cannot be \
named one. Unlike the Lean notation, the reader has no namespace to hide behind: a bare word \
is either a keyword or a name, and the choice is made lexically."

def p003 : Code := code "P003" "an unterminated string literal"
  "A quoted string closes on the same line it opens: it is a region's name or the contents of a \
`str` initializer, and neither spans lines. There are no escape sequences, so a `\"` always ends \
the literal."

def p004 : Code := code "P004" "input left over after the program"
  "The reader consumed a complete program and then found more text. Usually a stray closing \
brace, or a statement the grammar does not have and which therefore ended the program early."

def p005 : Code := code "P005" "a load in expression position"
  "`A[i]` reads memory, and an expression in this language has no memory operand — every heap \
value comes through an explicit load first. That is what keeps a footprint syntactic and keeps \
registers out of it (docs/block-ir.md § Why AExp has no memory operand). Load into a register, \
then use the register."

def p006 : Code := code "P006" "a `let` whose size cannot be read off its initializer"
  "`let a = …` exists so that a one-cell variable needs no shape, so the initializer has to say \
how many cells there are: a string takes one per UTF-8 byte, a list one per value, and a single \
value is a scalar. `zeros`, `ones`, `eye`, `arange`, `full` and `input str` each fit any size and \
fix none, so they are written with `buf`, which states the shape (docs/prl.md § Variables)."

def p110 : Code := code "P110" "a slice that is not inside its buffer"
  "`A[lo..hi]` names the cells `[lo, hi)` of `A`, counted flat whatever `A`'s shape, so the range \
has to satisfy `lo < hi ≤ len A`. A slice is a *view* and copies nothing: its cells are `A`'s, which \
is what makes two disjoint slices of one buffer independent. An empty range is refused rather than \
allowed, because a computed subscript wraps on the range's length (`ArrRef.addr`), so a zero-cell \
slice would address a cell outside itself (docs/prl.md § Slices)."

def p111 : Code := code "P111" "a `print` argument with no spelling of its own"
  "`print` takes a buffer, a cell of one, a `const` or a register expression. A `slice` name is \
none of those: a slice declares no memory, so it is erased once the file compiles and `to-prl` \
cannot write it back — a printed program that mentioned one would not read as itself. Print the \
buffer the slice is a view of, or the cell by its own name (docs/print.md § The surface form)."

def p101 : Code := code "P101" "an undeclared name"
  "A buffer, `const` or loop variable must be declared before it is used. `State` is total, so \
no location is ever created — declaring is how a program names memory it is allowed to touch \
(docs/prl.md § Declaring memory). A name that was `free`d is also undeclared from that point on."

def p102 : Code := code "P102" "a name declared twice"
  "Two buffers cannot share a name, because a name is how an address is written and how a \
diagnostic reports one. To reuse a buffer's cells, `free` the first and declare the second: the \
allocator then places it on the same cells and `Arena.live_disjoint` still holds of what is live \
(docs/layout.md § Lifetimes)."

def p103 : Code := code "P103" "two buffers placed on the same cells"
  "A base given by hand with `at` put this buffer on top of one that is still live. The \
allocator never does this; only an explicit base can. Overlapping live buffers would make two \
names denote one cell, so an independence proof about one would say nothing about the other."

def p104 : Code := code "P104" "more initial values than the buffer has cells"
  "The shape says how many cells there are and the initializer gave more. Values are not \
truncated here, deliberately: `rows` pads to a shape because a short row is a shape decision, \
while extra contents are a mistake the declaration check can catch for free (docs/strings.md)."

def p105 : Code := code "P105" "an address that is not known at compile time"
  "A bare `[e]` address is folded to a number while the file compiles, so it cannot mention a \
register. Write the access as a subscript, `A[%i]`, which compiles to the data-dependent form: \
the index wraps on the buffer's length, so the access is confined to `A` by construction and the \
footprint is `A`'s cells rather than the whole heap (docs/prl.md § Addresses)."

def p106 : Code := code "P106" "a statement out of place"
  "Declarations and `free` belong at the top level, where the whole program sees them — one \
inside a `parallel` thread would be visible to that thread alone, and one inside a `def` body \
would place its memory once per call. `slice` is the exception: it declares no memory and ends no \
lifetime, so a name for a range the thread already reaches is exactly what it should be, and it is \
allowed anywhere. `synchronize` is the mirror image of a declaration: it separates phases of a \
sequential chain, and threads of one fork have no barrier between them. A `def` is itself a \
top-level form, and `input` cannot appear in a body, because a call site does not fix the order \
values are read in (docs/prl.md § Functions)."

def p107 : Code := code "P107" "an operator used in the wrong role"
  "An expression has two roles in this language — an address, folded at compile time, and a \
value, which becomes an `AExp` — and not every operator exists in both. `%` is compile-time \
modulo and has no `AExp` counterpart, because `footprintOf` must stay decidable (docs/block-ir.md)."

def p108 : Code := code "P108" "`input` where the order of reads is not fixed"
  "The values a program reads, and the order it reads them in, must be fixed by the program \
text, because they are consumed while the file compiles. A `parallel` thread and a `parfor` \
index have no order between them; an `if` branch and a `while` body may run any number of \
times. A `for` loop is allowed: it is unrolled, so its count is in the text (docs/prl.md § Input)."

def p109 : Code := code "P109" "the input stream does not supply what the program asks for"
  "Either the stream ran out, or a word is not a value. A numeric input is a \
whitespace-separated integer, with `true` and `false` read as `1` and `0`; `input str` takes a \
line. Nothing is piped in when standard input is empty, which is why a program that reads \
input and gets none fails here rather than waiting (docs/prl.md § Input)."

def p112 : Code := code "P112" "a call that does not match its `def`"
  "The number of arguments, or the kind of one. A parameter is a name or a register, told apart by \
its spelling: `A` is substituted wherever the body writes a name, `%acc` wherever it writes that \
register, and the two are not interchangeable — a register's value is a value, while `%r` alone is \
the register itself. The same code reports a name parameter that was given a value and then used to \
name cells, which is the one mismatch that cannot be seen until the arguments are known \
(docs/prl.md § Functions)."

def p113 : Code := code "P113" "a `def` that calls itself"
  "Directly, or through a chain of calls, which the message spells out. A call is written out where \
it stands, so a recursive one has no end; and `ParM` is inductive, so a recursive program has no \
representation to expand into either — `while true` is unrepresentable for the same reason. \
Bounded repetition is `while c in n`, whose count is in the program text (docs/prl.md § Functions)."

def p114 : Code := code "P114" "more than one `assert`"
  "A claim compiles the file twice over — once with each side's body written out where the \
`assert` stands — so a file holds two programs and a second claim would ask for a third and a \
fourth. Split the file, or write one `def` that calls the others and compare that \
(docs/equivalence.md)."

/-- Every code, in order. A code not in this list has no explanation and must not be issued. -/
def codes : List Code :=
  [p001, p002, p003, p004, p005, p006,
   p101, p102, p103, p104, p105, p106, p107, p108, p109, p110, p111, p112, p113, p114]

/-- The code with this identifier, for `paralever explain`. Case-insensitive, so `p108` works. -/
def find? (id : String) : Option Code :=
  codes.find? (fun c => c.id.toLower == id.toLower)

/-- What `paralever explain CODE` prints: the rule, then why it exists. -/
def explain (id : String) : String :=
  match find? id with
  | some c => s!"{c.id}: {c.title}\n\n{wrap 78 c.why}\n"
  | none   =>
      s!"no such code: '{id}'\n\nthe codes are: " ++ ", ".intercalate (codes.map Code.id) ++ "\n"

end Paralever.Diag
