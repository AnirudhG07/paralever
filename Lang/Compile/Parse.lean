import Lang.Compile.Ast

/-! # A reader for `.prl` files

Recursive descent, and untrusted like `MLIR/Parse.lean`'s reader: what is believed is `wfB` on the
`ParProg` it produces, and the gate that a file was read as written is the round trip in
`Lang/Compile/Print.lean`. A newline ends a statement, so `ws` crosses one only inside brackets (`depth > 0`)
and `wsl` crosses one deliberately, before `|`, `::` or `else`.

Grammar: `docs/prl.md`. -/

namespace Paralever.Lang

/-- Every reserved word. `Test/Lang.lean` gates the editor grammar against this list. -/
def keywords : List String :=
  [ "paralever", "parallel", "parfor", "for", "while", "if", "else", "in", "at", "free", "synchronize",
    "buf", "const", "reg", "min", "max", "zeros", "ones", "eye", "arange", "full" ]

/-- Input, a cursor, and the bracket depth: `depth > 0` means a line break is whitespace. -/
structure PState where
  cs    : Array Char
  i     : Nat
  depth : Nat := 0
  deriving Inhabited

/-- A reader: consumes input, or fails with a message naming the line and column. -/
abbrev P (α : Type) := StateT PState (Except String) α

namespace P

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdentCont  (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

/-- The 1-based line and column of an offset. -/
def lineCol (cs : Array Char) (i : Nat) : Nat × Nat :=
  let before := cs.toList.take i
  (1 + (before.filter (· == '\n')).length,
   1 + (before.reverse.takeWhile (· != '\n')).length)

/-- Fail, quoting the line, the column, and the rest of that line. -/
def err (msg : String) : P α := do
  let st ← get
  let (ln, col) := lineCol st.cs st.i
  let near := String.ofList (((st.cs.toList.drop st.i).take 32).takeWhile (· != '\n'))
  StateT.lift (Except.error s!"{ln}:{col}: {msg} (at: {near})")

/-- Run `p`, and on failure consume nothing. -/
def attempt (p : P α) : P (Option α) := fun st =>
  match p st with
  | .ok (a, st') => .ok (some a, st')
  | .error _     => .ok (none, st)

def atEnd : P Bool := do let st ← get; pure (st.cs.size ≤ st.i)

def peek : P (Option Char) := do
  let st ← get
  pure (if st.i < st.cs.size then some st.cs[st.i]! else none)

def peekAt (k : Nat) : P (Option Char) := do
  let st ← get
  pure (if st.i + k < st.cs.size then some st.cs[st.i + k]! else none)

def bump : P Unit := modify fun st => { st with i := st.i + 1 }

def lookingAt (s : String) : P Bool := do
  let st ← get
  pure (s.toList.zipIdx.all fun (c, k) => st.i + k < st.cs.size && st.cs[st.i + k]! == c)

/-- Spaces, tabs and `--` comments. A line break only when inside brackets. -/
partial def ws : P Unit := do
  match ← peek with
  | none => pure ()
  | some c =>
      if c == ' ' || c == '\t' then do bump; ws
      else if c == '\n' || c == '\r' then do
        if (← get).depth > 0 then do bump; ws else pure ()
      else if c == '-' && (← peekAt 1) == some '-' then do skipLine; ws
      else pure ()
where
  /-- To the end of the line, leaving the newline itself: at depth `0` it is a separator. -/
  skipLine : P Unit := do
    match ← peek with
    | some d => if d == '\n' then pure () else do bump; skipLine
    | none   => pure ()

/-- Whitespace including line breaks, whatever the depth. -/
partial def wsl : P Unit := do
  match ← peek with
  | none => pure ()
  | some c =>
      if c == ' ' || c == '\t' || c == '\n' || c == '\r' then do bump; wsl
      else if c == '-' && (← peekAt 1) == some '-' then do skipLine; wsl
      else pure ()
where
  skipLine : P Unit := do
    match ← peek with
    | some d => if d == '\n' then pure () else do bump; skipLine
    | none   => pure ()

/-- Consume exactly this character. -/
def ch (c : Char) : P Unit := do
  ws
  if (← peek) == some c then bump else err s!"expected '{c}'"

/-- Consume this character if it is there. -/
def tryCh (c : Char) : P Bool := do
  ws
  if (← peek) == some c then do bump; pure true else pure false

/-- Consume this symbol if it is there, looking past line breaks. -/
def trySymNl (s : String) : P Bool := do
  let st ← get
  wsl
  if ← lookingAt s then do
    modify (fun st' => { st' with i := st'.i + s.length }); pure true
  else do set st; pure false

/-- Consume this keyword if it is there, respecting word boundaries. -/
def tryKw (s : String) : P Bool := do
  ws
  if ← lookingAt s then do
    let st ← get
    let after := st.i + s.length
    if after < st.cs.size && isIdentCont st.cs[after]! then pure false
    else do set { st with i := after }; pure true
  else pure false

/-- Consume this keyword, looking past line breaks. -/
def tryKwNl (s : String) : P Bool := do
  let st ← get
  wsl
  if ← tryKw s then pure true else do set st; pure false

/-- Consume this keyword, or fail. -/
def kw (s : String) : P Unit := do
  if ← tryKw s then pure () else err s!"expected '{s}'"

/-- Just past the identifier starting at `j`. -/
partial def identEnd (cs : Array Char) (j : Nat) : Nat :=
  if j < cs.size && isIdentCont cs[j]! then identEnd cs (j + 1) else j

/-- Just past the digits starting at `j`. -/
partial def digitEnd (cs : Array Char) (j : Nat) : Nat :=
  if j < cs.size && cs[j]!.isDigit then digitEnd cs (j + 1) else j

/-- The characters of `cs` in `[a, b)`. -/
def slice (cs : Array Char) (a b : Nat) : String :=
  String.ofList ((cs.toList.drop a).take (b - a))

/-- An identifier that is not a reserved word. -/
def ident : P String := do
  ws
  match ← peek with
  | some c =>
      if isIdentStart c then do
        let st ← get
        let j := identEnd st.cs st.i
        let s := slice st.cs st.i j
        if keywords.contains s then err s!"'{s}' is a reserved word"
        else do set { st with i := j }; pure s
      else err "expected a name"
  | none => err "expected a name"

/-- A run of digits. -/
def num : P Nat := do
  ws
  let st ← get
  let j := digitEnd st.cs st.i
  if j == st.i then err "expected a number"
  else do
    set { st with i := j }
    pure (slice st.cs st.i j).toNat!

/-- The rest of a string literal, after the opening quote. -/
partial def strRest (acc : List Char) : P String := do
  match ← peek with
  | none      => err "unterminated string"
  | some '"'  => do bump; pure (String.ofList acc.reverse)
  | some '\n' => err "unterminated string"
  | some c    => do bump; strRest (c :: acc)

/-- A `"…"` string, for a region name. No escapes: a label is a name. -/
def str : P String := do
  ws
  if (← peek) != some '"' then err "expected a quoted name"
  else do
    bump
    strRest []

/-- Run `p` between brackets, where line breaks are insignificant. -/
def inside (open' close : Char) (p : P α) : P α := do
  ch open'
  modify fun st => { st with depth := st.depth + 1 }
  let a ← p
  wsl
  if (← peek) == some close then bump else err s!"expected '{close}'"
  modify fun st => { st with depth := st.depth - 1 }
  pure a

/-- `p`, comma-separated. `ws` is depth-aware, so items may span lines inside brackets and may not
outside them — an unbracketed `buf A[2] = 1, 2` ends where its line ends. -/
partial def commaList (p : P α) : P (List α) := do
  let a ← p
  ws
  if ← tryCh ',' then pure (a :: (← commaList p)) else pure [a]

end P

open P

/-! ## Expressions

`+ -` loosest, then `* / %`, then an atom. `%` is a register in operand position and modulo in
operator position, which is what lets `%0` and `n % 4` share the character. -/

mutual

/-- `%0`, `%acc`, a number, a name, `min(a, b)`, `(e)`, or a negation. -/
partial def atom : P Exp := do
  ws
  match ← peek with
  | none => err "expected an expression"
  | some c =>
      if c == '%' then do
        bump
        match ← peek with
        | some d => if d.isDigit then pure (.reg (toString (← num))) else pure (.reg (← ident))
        | none   => err "expected a register after '%'"
      else if c == '(' then inside '(' ')' exp
      else if c == '-' then do
        -- a minus on a literal belongs to the literal, or the printer's output would not read back
        bump
        match ← peek with
        | some d => if d.isDigit then pure (.num (-(Int.ofNat (← num)))) else pure (.sub (.num 0) (← atom))
        | none   => err "expected an expression after '-'"
      else if c.isDigit then pure (.num (Int.ofNat (← num)))
      else if ← tryKw "min" then do
        let (a, b) ← inside '(' ')' (do let a ← exp; ch ','; pure (a, ← exp))
        pure (.min a b)
      else if ← tryKw "max" then do
        let (a, b) ← inside '(' ')' (do let a ← exp; ch ','; pure (a, ← exp))
        pure (.max a b)
      else if isIdentStart c then pure (.name (← ident))
      else err "expected an expression"

/-- `*`, `/`, `%`. -/
partial def term : P Exp := do
  let a ← atom
  termRest a

partial def termRest (a : Exp) : P Exp := do
  ws
  if ← tryCh '*' then termRest (.mul a (← atom))
  else if ← tryCh '/' then termRest (.div a (← atom))
  else if ← tryCh '%' then termRest (.mod a (← atom))
  else pure a

/-- `+`, `-`. -/
partial def exp : P Exp := do
  let a ← term
  expRest a

partial def expRest (a : Exp) : P Exp := do
  ws
  if ← tryCh '+' then expRest (.add a (← term))
  else if ← tryCh '-' then expRest (.sub a (← term))
  else pure a

end

/-- `[e]` or `A[i, j]`. -/
def addr : P Addr := do
  ws
  if (← peek) == some '[' then
    pure (.raw (← inside '[' ']' exp))
  else do
    let nm ← ident
    ws
    if (← peek) == some '[' then
      pure (.cell nm (← inside '[' ']' (commaList exp)))
    else pure (.cell nm [])

/-! ## Declarations -/

/-- `zeros`, `ones`, `eye`, `arange`, `full e`, or a list of values, optionally bracketed. -/
def bufInit : P BufInit := do
  if ← tryKw "zeros" then pure .zeros
  else if ← tryKw "ones" then pure .ones
  else if ← tryKw "eye" then pure .eye
  else if ← tryKw "arange" then pure .arange
  else if ← tryKw "full" then pure (.full (← exp))
  else do
    ws
    if (← peek) == some '[' then pure (.data (← inside '[' ']' (commaList exp)))
    else pure (.data (← commaList exp))

/-- Whether a declaration keyword begins here. -/
def atDecl : P Bool := do
  let st ← get
  ws
  let r ← (do
    if ← lookingAt "buf" then pure true
    else if ← lookingAt "const" then pure true
    else if ← lookingAt "reg" then pure true
    else pure false)
  set st
  pure r

/-- `buf A[2, 3] = ones`, `buf S[4] at 100`, `const n = 4`, `reg acc`. -/
def decl : P (List Decl) := do
  if ← tryKw "buf" then do
    let nm ← ident
    ws
    let shape ← if (← peek) == some '[' then inside '[' ']' (commaList exp) else pure []
    ws
    let base ← if ← tryKw "at" then pure (some (← exp)) else pure none
    ws
    let init ← if ← tryCh '=' then bufInit else pure .zeros
    pure [.buf nm shape init base]
  else if ← tryKw "const" then do
    let nm ← ident
    ch '='
    pure [.const nm (← exp)]
  else if ← tryKw "reg" then do
    let ns ← commaList ident
    ws
    if ← tryCh '=' then
      match ns with
      | [n] => pure [.reg n (some (← num))]
      | _   => err "'reg a, b = 3' names one register at a time"
    else pure (ns.map (fun n => .reg n none))
  else err "expected a declaration"

/-! ## Statements -/

/-- `%0` or `%acc`, after the `%`. -/
def regName : P String := do
  match ← peek with
  | some d => if d.isDigit then pure (toString (← num)) else ident
  | none   => err "expected a register name"

mutual

/-- One statement. -/
partial def stmt : P Stmt := do
  ws
  if ← tryKw "synchronize" then pure .synchronize
  else if ← tryKw "free" then pure (.free (← ident))
  else if ← atDecl then pure (.decl (← decl))
  else if ← tryKw "parallel" then do
    let ts ← threads
    let nm ← label
    pure (.par ts nm)
  else if ← tryKw "parfor" then do
    let i ← ident
    kw "in"
    let n ← exp
    let b ← thread
    let nm ← label
    pure (.parfor i n b nm)
  else if ← tryKw "for" then do
    let i ← ident
    kw "in"
    let n ← exp
    pure (.forIn i n (← thread))
  else if ← tryKw "while" then do
    let c ← exp
    kw "in"
    let n ← exp
    pure (.whileIn c n (← thread))
  else if ← tryKw "if" then do
    let c ← exp
    let t ← thread
    if ← tryKwNl "else" then pure (.ifElse c t (← thread)) else pure (.ifElse c t [])
  else if (← peek) == some '%' then do
    bump
    let r ← regName
    ws
    if ← lookingAt ":=" then do
      modify fun st => { st with i := st.i + 2 }
      match ← attempt addr with
      | some a => do noArith; pure (.load r a)
      | none   => pure (.set r (← exp))
    else err "expected ':=' after a register"
  else do
    let a ← addr
    ws
    if ← lookingAt ":=" then do
      modify fun st => { st with i := st.i + 2 }
      pure (.store a (← exp))
    else err "expected ':=' after an address"

/-- A load is not an operand: every heap value comes through its own load. -- ref: docs/block-ir.md -/
partial def noArith : P Unit := do
  ws
  match ← peek with
  | some c =>
      if c == '+' || c == '*' || c == '/' then
        err "a load cannot be part of an expression — load into a register first"
      else pure ()
  | none => pure ()

/-- `{ … }`, one group of statements. -/
partial def thread : P (List Stmt) := do
  wsl
  if (← peek) != some '{' then err "expected '{'"
  else do
    bump
    let ss ← stmtsAcc []
    wsl
    if (← peek) == some '}' then bump else err "expected '}'"
    pure ss

/-- `{…} | {…} | …`. -/
partial def threads : P (List (List Stmt)) := do
  let t ← thread
  if ← trySymNl "|" then pure (t :: (← threads)) else pure [t]

/-- An optional `:: "name"`. -/
partial def label : P (Option String) := do
  if ← trySymNl "::" then pure (some (← str)) else pure none

/-- Statements until `}` or the end of input, separated by `;`, by line breaks, or by both. -/
partial def stmtsAcc (acc : List Stmt) : P (List Stmt) := do
  seps
  if (← atEnd) || (← peek) == some '}' then pure acc.reverse
  else do
    let s ← stmt
    ws
    match ← peek with
    | none => pure (s :: acc).reverse
    | some c =>
        if c == ';' || c == '\n' || c == '\r' || c == '}' then stmtsAcc (s :: acc)
        else err "expected ';', a line break or '}' after a statement"
where
  /-- Any run of separators and blank lines. -/
  seps : P Unit := do
    wsl
    if (← tryCh ';') then seps else pure ()

end

/-! ## The file

One statement list, optionally wrapped in `paralever { … }` so that a program pasted out of a Lean
file is a `.prl` file unchanged. -/

/-- Read a whole file. -/
def file : P File := do
  wsl
  let body ← if ← tryKw "paralever" then thread else stmtsAcc []
  wsl
  if ← atEnd then pure ⟨body⟩ else err "unexpected input after the program"

/-- **Read `.prl` text.** -/
def parse (src : String) : Except String File :=
  match file ⟨src.toList.toArray, 0, 0⟩ with
  | .ok (f, _)   => .ok f
  | .error e     => .error e

end Paralever.Lang
