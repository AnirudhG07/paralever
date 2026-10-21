import Prl.Lang.Layout

/-! # The syntax of a `.prl` file

The statement forms `paralever { … }` has, plus declarations, which in Lean are ordinary `Buf` and
`Reg` definitions. Names survive here and are resolved in `Prl/Compile/Lower.lean`.

Grammar and rationale: `docs/prl.md`. -/

namespace Paralever.Prl

/-- An expression. One type for both roles: an *address*, folded to a `Loc` at compile time, and a
*value*, which becomes an `AExp`. Position decides which, and `Prl/Compile/Lower.lean` rejects the
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
  deriving Repr, Inhabited

/-- An address: `[e]` is a bare location, `A[i, j]` a cell of a declared buffer. -/
inductive Addr where
  | raw  : Exp → Addr
  | cell : String → List Exp → Addr
  deriving Repr, Inhabited

/-- How a buffer starts out, matching `Layout`'s initializers one for one. -/
inductive BufInit where
  | zeros | ones | eye | arange
  | full : Exp → BufInit
  /-- `= 1, 2, 3` — contents row-major, short lists padded with `0`. -/
  | data : List Exp → BufInit
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
  deriving Repr, Inhabited

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
  deriving Repr, Inhabited

/-- A whole file. -/
structure File where
  body : List Stmt
  deriving Repr, Inhabited

end Paralever.Prl
