import Lang.Core.Layout

/-! # The syntax of a `.prl` file

The statement forms `paralever { … }` has, plus declarations, which in Lean are ordinary `Buf` and
`Reg` definitions. Names survive here and are resolved in `Lang/Compile/Lower.lean`.

Grammar and rationale: `docs/prl.md`. -/

namespace Paralever.Lang

/-- An expression. One type for both roles: an *address*, folded to a `Loc` at compile time, and a
*value*, which becomes an `AExp`. Position decides which, and `Lang/Compile/Lower.lean` rejects the
combinations that do not exist. -/
inductive Exp where
  | num  : Int → Exp
  /-- A `const` or an enclosing loop variable. Folded to a literal. -/
  | name : String → Exp
  /-- `%0` or `%acc`. Makes the expression run-time. -/
  | reg  : String → Exp
  | add  : Exp → Exp → Exp
  | sub  : Exp → Exp → Exp
  | mul  : Exp → Exp → Exp
  | div  : Exp → Exp → Exp
  /-- `%` as an infix operator — compile-time only. -/
  | mod  : Exp → Exp → Exp
  | min  : Exp → Exp → Exp
  | max  : Exp → Exp → Exp
  /-- `a < b`, `a == b`, `!a`. The other six comparisons and the two boolean operators are
  desugared by the reader into these, exactly as `AExp` derives them. -- ref: `docs/prl.md` § Conditions -/
  | lt   : Exp → Exp → Exp
  | eq   : Exp → Exp → Exp
  | not  : Exp → Exp
  /-- `#A` — the number of cells in a buffer or a slice. Folded to a literal, so it is legal in
  both roles and costs nothing at run time. -- ref: `docs/prl.md` § Slices -/
  | len  : String → Exp
  /-- `input` — one value from standard input, consumed while the file compiles. Legal only as the
  whole right-hand side of `%r := input`; anywhere else inside an expression it is refused, because
  the order values are consumed in has to be the order they are written in.
  -- ref: `docs/prl.md` § Input -/
  | input : Exp
  deriving Repr, Inhabited

/-- An address: `[e]` is a bare location, `A[i, j]` a cell of a declared buffer, and `A[lo..hi][i]`
a cell of a sub-range of one. -/
inductive Addr where
  | raw  : Exp → Addr
  | cell : String → List Exp → Addr
  /-- `A[lo..hi][i]` — index `i` of the cells `[lo, hi)` of `A`, counted flat whatever `A`'s shape.
  `hi` is exclusive, and `none` is `A`'s last cell. A slice is indexed once, because it is flat.
  -- ref: `docs/prl.md` § Slices -/
  | part : String → Exp → Option Exp → Exp → Addr
  deriving Repr, Inhabited

/-- How a buffer starts out, matching `Layout`'s initializers one for one. -/
inductive BufInit where
  | zeros | ones | eye | arange
  | full : Exp → BufInit
  /-- `= 1, 2, 3` — contents row-major, short lists padded with `0`. -/
  | data : List Exp → BufInit
  /-- `= str "hello"` — the string's UTF-8 bytes, one per cell. -- ref: `docs/strings.md` -/
  | str  : String → BufInit
  /-- `= input` — one value per cell, row-major, from standard input.
  -- ref: `docs/prl.md` § Input -/
  | input : BufInit
  /-- `= input str` — a line of standard input, as its UTF-8 bytes. -/
  | inputStr : BufInit
  deriving Repr, Inhabited

/-- What a Lean file states with `buf`, `abbrev n : Nat` and `abbrev acc : Reg`. -/
inductive Decl where
  /-- `buf A[2, 3] = ones`, or `buf S[4] at 100` with the base by hand. `[]` is a scalar.
  Declaring is the only way to obtain memory: `State` is total, so a location is never created.
  -- ref: `docs/prl.md` § Declaring memory -/
  | buf   : String → List Exp → BufInit → Option Exp → Decl
  | const : String → Exp → Decl
  /-- `reg acc` takes the next free index; `reg acc = 3` names one. -/
  | reg   : String → Option Nat → Decl
  /-- `slice h = A[lo..hi]` — a name for a sub-range. Erased: it declares no memory and ends no
  lifetime, so `h[i]` is `A[lo..hi][i]` and nothing reaches the program.
  -- ref: `docs/prl.md` § Slices -/
  | slice : String → String → Exp → Option Exp → Decl
  deriving Repr, Inhabited

/-- One thing a `print` names: a quoted literal, a buffer or a cell of one, or an expression.
`print k` and `print 2 * %p` are told apart the way `%r := …` tells a load from an assignment — an
operand belongs to an expression. -- ref: `docs/print.md` § The surface form -/
inductive PrintArg where
  | text : String → PrintArg
  | addr : Addr → PrintArg
  | exp  : Exp → PrintArg
  deriving Repr, Inhabited

/-- A `def`'s parameter. The two kinds are told apart by spelling, as the rest of the language
tells a name from a register: `A` is substituted wherever the body writes a name, `%acc` wherever
it writes that register. -- ref: `docs/prl.md` § Functions -/
inductive Param where
  | name : String → Param
  | reg  : String → Param
  deriving Repr, Inhabited

/-- What a call supplies for one parameter. `%r` alone is the register; `%r + 1` is a value, by the
rule that an operand belongs to an expression. -/
inductive Arg where
  | exp : Exp → Arg
  | reg : String → Arg
  deriving Repr, Inhabited

/-- One side of an `assert`: the call whose body stands in its place. A side is a call and not a
block so that both sides have a name a report can print, and so that argument checking is the one
already written for a call. -- ref: `docs/equivalence.md` § Why the surface form is two calls -/
structure Side where
  callee : String
  args   : List Arg
  deriving Repr, Inhabited

/-- **How strong a claim an `assert` states.** `assert` compares the named cells of the final heap;
`assertParSeq` compares the final register file as well, which is the pair `ParSeqEq` quantifies.
-- ref: `docs/equivalence.md` § What `assertParSeq` adds -/
inductive Strength where
  /-- `assert` — the named cells of the final heap. -/
  | heap
  /-- `assertParSeq` — those cells and both sides' written registers. -/
  | parSeq
  deriving Repr, Inhabited, DecidableEq, BEq

/-- A statement; the forms are `paralever { … }`'s, plus the two that move memory in and out of
scope. A declaration is positional because `free` is: a buffer has a lifetime in the program text. -/
inductive Stmt where
  /-- `%r := [l]` or `%r := A[i]` — a load. -/
  | load   : String → Addr → Stmt
  /-- `[l] := e` or `A[i] := e` — a store. -/
  | store  : Addr → Exp → Stmt
  /-- `%r := e` — register assignment, touches no memory. -/
  | set    : String → Exp → Stmt
  /-- `parallel {…} | {…}`, optionally `:: "name"`. -/
  | par    : List (List Stmt) → Option String → Stmt
  /-- `for i in n {…}` — unrolled at compile time. -/
  | forIn  : String → Exp → List Stmt → Stmt
  /-- `parfor i in n {…}` — one thread per index. -/
  | parfor : String → Exp → List Stmt → Option String → Stmt
  /-- `if c {…} else {…}`; the `else` branch is empty when omitted. -/
  | ifElse : Exp → List Stmt → List Stmt → Stmt
  /-- `while c in n {…}` — at most `n` iterations, the guard tested before each. -/
  | whileIn : Exp → Exp → List Stmt → Stmt
  /-- `buf`, `const`, `reg`. A list because `reg a, b` declares two. -/
  | decl    : List Decl → Stmt
  /-- `free A` — the end of a buffer's lifetime. Erased: it compiles to nothing, and its whole
  effect is on what the compiler will accept afterwards. -/
  | free    : String → Stmt
  /-- `synchronize` — the end of a phase. Nothing before it and after it is grouped into one fork. -/
  | synchronize   : Stmt
  /-- `def f(A, %acc) {…}` — a named statement list. Erased: `Lang/Compile/Expand.lean` writes the
  body out at every call site, so no `ParProg` node corresponds to it.
  -- ref: `docs/prl.md` § Functions -/
  | defn    : String → List Param → List Stmt → Stmt
  /-- `f(A, %acc)` — a call, replaced by the body it names. -/
  | call    : String → List Arg → Stmt
  /-- `assert f(A) == g(A) on A, B` — the file's claim that its two sides agree on those buffers,
  compared over every live buffer when the list is empty; `assertParSeq` for the same claim with
  the register file included. Erased twice over: `Lang/Compile/Lower.lean` compiles the file once
  with each side's call in this statement's place, and neither program contains a node for the
  claim itself. -- ref: `docs/equivalence.md` -/
  | assert  : Strength → Side → Side → List String → Stmt
  /-- `print k`, `print "x =", %p` — output. Erased from the program, so it is legal only outside a
  `parallel` block, where what it observes does not depend on a schedule.
  -- ref: `docs/print.md` -/
  | print   : List PrintArg → Stmt
  deriving Repr, Inhabited

/-- A whole file. -/
structure File where
  body : List Stmt
  deriving Repr, Inhabited

end Paralever.Lang
