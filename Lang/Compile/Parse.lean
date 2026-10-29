import Lang.Compile.Ast
import Diag

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
    "print", "def", "assert", "assertParSeq", "on",
    "buf", "let", "const", "reg", "slice", "copy", "from", "min", "max", "zeros", "ones", "eye",
    "arange", "full", "str", "input" ]

/-- Input, a cursor, and the bracket depth: `depth > 0` means a line break is whitespace. -/
structure PState where
  cs    : Array Char
  i     : Nat
  depth : Nat := 0
  deriving Inhabited

/-- A failure: where it happened, and what was wrong. The position is *not* rendered here, because
`attempt` throws most failures away and quoting the source costs a pass over the file; the MLIR
reader, which backtracks far more, went from 20.54 s to 0.40 s on a 14,451-line file for this one
reason. -- ref: docs/scale.md § Where the time went -/
structure PErr where
  pos : Nat
  msg : String
  /-- How many characters the caret covers. One unless the reader knows the token's length. -/
  len : Nat := 1
  /-- Which rule was broken. Most failures are one token the grammar does not allow here.
  -- ref: `docs/diagnostics.md` § Codes classify kinds, not sites -/
  code : Diag.Code := Diag.p001
  /-- The route out, when there is one the message should not have to carry. -/
  hints : List String := []

/-- A reader: consumes input, or fails at an offset. -/
abbrev P (α : Type) := StateT PState (Except PErr) α

namespace P

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdentCont  (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

/-- The 1-based line and column of an offset. -/
def lineCol (cs : Array Char) (i : Nat) : Nat × Nat :=
  let before := cs.toList.take i
  (1 + (before.filter (· == '\n')).length,
   1 + (before.reverse.takeWhile (· != '\n')).length)

/-- Fail at the cursor. -/
def err (msg : String) : P α := do
  let st ← get
  StateT.lift (Except.error { pos := st.i, msg := msg })

/-- Fail at the cursor under a named rule, with the caret covering `len` characters. -/
def errAs (code : Diag.Code) (msg : String) (len : Nat := 1) (hints : List String := []) :
    P α := do
  let st ← get
  StateT.lift
    (Except.error { pos := st.i, msg := msg, len := len, code := code, hints := hints })

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

/-- Whether the statement ends at the cursor: a separator, a closing brace, or the end of input.
At depth `0` a line break is a separator, which is what `ws` already decides. -/
def atStmtEnd : P Bool := do
  ws
  match ← peek with
  | none   => pure true
  | some c => pure (c == ';' || c == '\n' || c == '\r' || c == '}')

/-- The end of one `print` argument: a comma, or the end of the statement. -/
def atArgEnd : P Bool := do
  ws
  match ← peek with
  | none   => pure true
  | some c => pure (c == ',' || c == ';' || c == '\n' || c == '\r' || c == '}')

/-- Consume this symbol if it is there, looking past line breaks. -/
def trySymNl (s : String) : P Bool := do
  let st ← get
  wsl
  if ← lookingAt s then do
    modify (fun st' => { st' with i := st'.i + s.length }); pure true
  else do set st; pure false

/-- Consume this symbol if it is there, without crossing a line break: an expression continues
onto the next line only inside brackets, which is what `ws` already decides. -/
def trySym (s : String) : P Bool := do
  ws
  if ← lookingAt s then do
    modify (fun st => { st with i := st.i + s.length }); pure true
  else pure false

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

/-- The characters of `cs` in `[a, b)`. `Array.extract` rather than `cs.toList.drop a`, which
converts the whole array: every identifier and every number cost a pass over the file, which made
reading a 10,000-statement file quadratic (21.19 s, against 0.08 s now).
-- ref: docs/scale.md § Where the time went -/
def slice (cs : Array Char) (a b : Nat) : String :=
  String.ofList (cs.extract a b).toList

/-- An identifier that is not a reserved word. -/
def ident : P String := do
  ws
  match ← peek with
  | some c =>
      if isIdentStart c then do
        let st ← get
        let j := identEnd st.cs st.i
        let s := slice st.cs st.i j
        if keywords.contains s then
          errAs Diag.p002 s!"'{s}' is a reserved word" s.length
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
  | none      => errAs Diag.p003 "unterminated string"
  | some '"'  => do bump; pure (String.ofList acc.reverse)
  | some '\n' => errAs Diag.p003 "unterminated string"
  | some c    => do bump; strRest (c :: acc)

/-- A `"…"` string: a region's name, or a `str` initializer's contents. No escapes. Not named `str`,
which is `Layout`'s string initializer and would shadow it here. -/
def strLit : P String := do
  ws
  if (← peek) != some '"' then err "expected a quoted string"
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

`||` loosest, then `&&`, then one comparison, then `+ -`, then `* / %`, then an atom. `%` is a
register in operand position and modulo in operator position, which is what lets `%0` and `n % 4`
share the character.

A comparison does not chain: `a < b < c` is refused rather than read as `(a < b) < c`, because the
second reading is almost never what was meant. The six comparisons and the two boolean operators
are desugared here into `lt`, `eq` and `not` — the same three `AExp` keeps — so nothing downstream
grows a case. -- ref: `docs/prl.md` § Conditions -/

/-- `e ≠ 0` as a `0`/`1` value, which is what `&&` and `||` take the `min`/`max` of. A comparison
and a negation already answer in `0`/`1`, so normalizing them is the identity — without that test
`a && b` would print back as a triple negation. -/
private def nz : Exp → Exp
  | .lt a b => .lt a b
  | .eq a b => .eq a b
  | .not a  => .not a
  | e       => .not (.not e)

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
      else if c == '!' then do
        bump
        pure (.not (← atom))
      -- `#A` is A's cell count. A sigil rather than a word, because `len`, `size` and `cells` are
      -- each already a name in `Examples/` — CLAUDE.md § *Surface-syntax tokens are global*
      else if c == '#' then do
        bump
        pure (.len (← ident))
      else if c.isDigit then pure (.num (Int.ofNat (← num)))
      else if ← tryKw "min" then do
        let (a, b) ← inside '(' ')' (do let a ← exp; ch ','; pure (a, ← exp))
        pure (.min a b)
      else if ← tryKw "max" then do
        let (a, b) ← inside '(' ')' (do let a ← exp; ch ','; pure (a, ← exp))
        pure (.max a b)
      else if ← tryKw "input" then pure .input
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
partial def sum : P Exp := do
  let a ← term
  sumRest a

partial def sumRest (a : Exp) : P Exp := do
  ws
  if ← tryCh '+' then sumRest (.add a (← term))
  else if ← tryCh '-' then sumRest (.sub a (← term))
  else pure a

/-- One comparison, or none. Two-character operators are tried first, so `<=` is never read as
`<` followed by a stray `=`. -/
partial def cmp : P Exp := do
  let a ← sum
  ws
  if ← trySym "<=" then do pure (.not (.lt (← sum) a))
  else if ← trySym ">=" then do pure (.not (.lt a (← sum)))
  else if ← trySym "==" then do pure (.eq a (← sum))
  else if ← trySym "!=" then do pure (.not (.eq a (← sum)))
  else if ← trySym "<" then do pure (.lt a (← sum))
  else if ← trySym ">" then do pure (.lt (← sum) a)
  else pure a

/-- `&&`, as the smaller of two values normalized to `0`/`1` — the derivation `AExp.and` uses. -/
partial def conj : P Exp := do
  let a ← cmp
  conjRest a

partial def conjRest (a : Exp) : P Exp := do
  ws
  if ← trySym "&&" then do conjRest (.min (nz a) (nz (← cmp))) else pure a

/-- `||`, the loosest level, as the larger of the two. -/
partial def exp : P Exp := do
  let a ← conj
  expRest a

partial def expRest (a : Exp) : P Exp := do
  ws
  if ← trySym "||" then do expRest (.max (nz a) (nz (← conj))) else pure a

end

/-- What a `[…]` after a name holds: a subscript list, or a range `lo..hi` whose `hi` may be left
off to mean the buffer's end. -- ref: `docs/prl.md` § Slices -/
inductive Brack where
  | subs  : List Exp → Brack
  | range : Exp → Option Exp → Brack

/-- The contents of one `[…]`. `..` decides which form it is, and a number stops at the `.`, so
`0..4` needs no lookahead. -/
def brack : P Brack := do
  let a ← exp
  ws
  if ← trySym ".." then do
    ws
    if (← peek) == some ']' then pure (.range a none) else pure (.range a (some (← exp)))
  else if ← tryCh ',' then pure (.subs (a :: (← commaList exp)))
  else pure (.subs [a])

/-- `[e]`, `A[i, j]`, or `A[lo..hi][i]`. -/
def addr : P Addr := do
  ws
  if (← peek) == some '[' then
    pure (.raw (← inside '[' ']' exp))
  else do
    let nm ← ident
    ws
    if (← peek) == some '[' then
      match ← inside '[' ']' brack with
      | .subs es     => pure (.cell nm es)
      | .range lo hi => do
          ws
          if (← peek) == some '[' then pure (.part nm lo hi (← inside '[' ']' exp))
          else
            errAs Diag.p001 "a slice is a range of cells, so it is indexed before it is an address"
              1 [s!"write '{nm}[lo..hi][i]', or name it with 'slice h = {nm}[lo..hi]'"]
    else pure (.cell nm [])

/-- A whole buffer or a slice of one — `copy`'s operand. `A` alone is all of `A`. -/
def region : P (String × Exp × Option Exp) := do
  let nm ← ident
  ws
  if (← peek) == some '[' then
    match ← inside '[' ']' brack with
    | .range lo hi => pure (nm, lo, hi)
    | .subs _      =>
        errAs Diag.p001 "'copy' moves a range of cells, not one cell" 1
          [s!"a range is written '{nm}[lo..hi]', and '{nm}' alone is all of {nm}"]
  else pure (nm, .num 0, none)

/-! ## Declarations -/

/-- `zeros`, `ones`, `eye`, `arange`, `full e`, `str "…"`, `input`, `input str`, or a list of
values, optionally bracketed. -/
def bufInit : P BufInit := do
  if ← tryKw "zeros" then pure .zeros
  else if ← tryKw "ones" then pure .ones
  else if ← tryKw "eye" then pure .eye
  else if ← tryKw "arange" then pure .arange
  else if ← tryKw "full" then pure (.full (← exp))
  else if ← tryKw "str" then pure (.str (← strLit))
  else if ← tryKw "input" then
    if ← tryKw "str" then pure .inputStr else pure .input
  else do
    ws
    if (← peek) == some '"' then pure (.str (← strLit))
    else if (← peek) == some '[' then pure (.data (← inside '[' ']' (commaList exp)))
    else pure (.data (← commaList exp))

/-- Whether a declaration keyword begins here. -/
def atDecl : P Bool := do
  let st ← get
  ws
  let r ← (do
    if ← lookingAt "buf" then pure true
    else if ← lookingAt "let" then pure true
    else if ← lookingAt "const" then pure true
    else if ← lookingAt "reg" then pure true
    else if ← lookingAt "slice" then pure true
    else pure false)
  set st
  pure r

/-- The shape a `let` reads off its initializer: a string takes one cell per UTF-8 byte, a list one
per value, and a single value is a scalar, so the name alone is its address.
-- ref: `docs/prl.md` § Variables -/
def letShape : BufInit → Option (List Exp)
  | .str s   => some [.num (Int.ofNat s.toUTF8.size)]
  | .data es => some (if es.length == 1 then [] else [.num (Int.ofNat es.length)])
  | .input   => some []
  | _        => none

/-- `buf A[2, 3] = ones`, `buf S[4] at 100`, `let a = 1`, `const n = 4`, `reg acc`,
`slice h = A[lo..hi]`. -/
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
  else if ← tryKw "let" then do
    let nm ← ident
    ch '='
    ws
    let st ← get
    let init ← bufInit
    match letShape init with
    | some shape => pure [.buf nm shape init none]
    | none => do
        let st' ← get
        set st
        errAs Diag.p006
          "a 'let' takes its size from its initializer, and this one has no size" (st'.i - st.i)
          ["an initializer that fits any size is written with 'buf', which states the shape"]
  else if ← tryKw "slice" then do
    let nm ← ident
    ch '='
    ws
    let parent ← ident
    ws
    if (← peek) != some '[' then
      errAs Diag.p001 "expected the range a slice names" 1
        [s!"write 'slice {nm} = {parent}[lo..hi]'"]
    else match ← inside '[' ']' brack with
      | .range lo hi => pure [.slice nm parent lo hi]
      | .subs _      =>
          errAs Diag.p001 "a slice names a range of cells, not one cell" 1
            [s!"write 'slice {nm} = {parent}[lo..hi]'"]
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

/-- The loop variable and the register `copy` desugars to. Both begin with a digit, which `ident`
and `regName` refuse, so a program can neither name one nor collide with one. `assignRegs` scans the
tree after reading, so `cpReg` is given an index like any other name. -/
def cpIdx : String := "0i"
def cpReg : String := "0t"

/-- `copy d from s` — one cell at a time, in index order, through `cpReg`. Sugar: it becomes a
`for`, so nothing downstream sees a `copy`. The trip count is the *source*'s length, so a short
destination is reported as a subscript outside it rather than silently truncating.
-- ref: `docs/prl.md` § Copying -/
def copyStmt : P Stmt := do
  let (d, dlo, dhi) ← region
  ws
  if ← tryKw "from" then pure () else
    errAs Diag.p001 "expected 'from' after what a 'copy' writes to" 1
      ["'copy' names the destination first, as an assignment does: 'copy d from s'"]
  let (s, slo, shi) ← region
  let n := match shi with | some h => Exp.sub h slo | none => Exp.sub (.len s) slo
  pure (.forIn cpIdx n
    [ .load cpReg (.part s slo shi (.name cpIdx))
    , .store (.part d dlo dhi (.name cpIdx)) (.reg cpReg) ])

/-- `%0` or `%acc`, after the `%`. -/
def regName : P String := do
  match ← peek with
  | some d => if d.isDigit then pure (toString (← num)) else ident
  | none   => err "expected a register name"

/-- A `def`'s parameter: a name, or `%r`. -- ref: `docs/prl.md` § Functions -/
def param : P Param := do
  ws
  if (← peek) == some '%' then do bump; pure (Param.reg (← regName))
  else pure (Param.name (← ident))

mutual

/-- One statement. -/
partial def stmt : P Stmt := do
  ws
  if ← tryKw "synchronize" then pure .synchronize
  else if ← tryKw "print" then pure (.print (← printArgs))
  else if ← tryKw "free" then pure (.free (← ident))
  else if ← tryKw "assertParSeq" then assertStmt .parSeq
  else if ← tryKw "assert" then assertStmt .heap
  else if ← tryKw "copy" then copyStmt
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
  else if ← tryKw "def" then do
      let f ← ident
      let ps ← inside '(' ')' (commaList param)
      pure (.defn f ps (← thread))
  else if ← tryKw "if" then ifRest
  else if (← peek) == some '%' then do
    bump
    let r ← regName
    ws
    if ← lookingAt ":=" then do
      modify fun st => { st with i := st.i + 2 }
      let st ← get
      match ← attempt addr with
      -- a bare name is a load only when the statement ends there. `%r := n + 1` reads `n` as an
      -- address and then cannot continue, and the reader cannot tell a scalar buffer from a `const`
      -- by its spelling, so the operator decides: an operand belongs to an expression.
      | some (.cell nm []) =>
          if ← atStmtEnd then pure (.load r (.cell nm []))
          else do set st; pure (.set r (← exp))
      | some a => do noArith; pure (.load r a)
      | none   => pure (.set r (← exp))
    else err "expected ':=' after a register"
  else do
    -- a call is a name followed by `(`, which no address can be: `A(` is not a subscript
    let st ← get
    match ← attempt callStmt with
    | some c => pure c
    | none   => do
        set st
        let a ← addr
        ws
        if ← lookingAt ":=" then do
          modify fun st => { st with i := st.i + 2 }
          pure (.store a (← exp))
        else err "expected ':=' after an address"

/-- `assert f(A) == g(A) on A, B` — the two sides and the buffers they are compared on. The
`on` list is optional and empty means every live buffer. The strength is the keyword that was
read: `assertParSeq` compares the register file too. -- ref: `docs/equivalence.md` -/
partial def assertStmt (st : Strength) : P Stmt := do
  let l ← callSide
  ws
  if !(← trySym "==") then err "expected '==' between the two sides of an 'assert'"
  else do
    let r ← callSide
    let ns ← if ← tryKw "on" then commaList ident else pure []
    pure (.assert st l r ns)

/-- `f(a, b)` — a call. Fails unless the name is followed by `(`, so the caller can fall back to
reading an address. -- ref: `docs/prl.md` § Functions -/
partial def callStmt : P Stmt := do
  let s ← callSide
  pure (.call s.callee s.args)

/-- `f(a, b)` as the two pieces an `assert` side holds. -/
partial def callSide : P Side := do
  let f ← ident
  ws
  if (← peek) != some '(' then err "expected '(' after a name"
  else pure ⟨f, ← inside '(' ')' (commaList arg)⟩

/-- One argument: `%r` alone is the register, and anything else is a value. -/
partial def arg : P Arg := do
  ws
  if (← peek) == some '%' then do
    let st ← get
    bump
    let r ← regName
    ws
    match ← peek with
    | some c => if c == ',' || c == ')' then pure (.reg r) else do set st; pure (.exp (← exp))
    | none   => pure (.reg r)
  else pure (.exp (← exp))

/-- An `if`, with the keyword already consumed. `else if` chains: the `else` arm is the single
statement the next `if` reads, so a chain needs no nested braces. -- ref: `docs/prl.md` § Conditions -/
partial def ifRest : P Stmt := do
  let c ← exp
  let t ← thread
  if ← tryKwNl "else" then
    if ← tryKwNl "if" then pure (.ifElse c t [← ifRest])
    else pure (.ifElse c t (← thread))
  else pure (.ifElse c t [])

/-- `print`'s arguments: a comma-separated list, at least one. -/
partial def printArgs : P (List PrintArg) := do
  let a ← printArg
  if ← trySym "," then pure (a :: (← printArgs)) else pure [a]

/-- One argument. A bare name is the buffer only when the argument ends there, by the same rule
`%r := …` uses: `print n + 1` reads `n` as an address and then cannot continue, so the operator
decides that it was an expression. -- ref: `docs/print.md` § The surface form -/
partial def printArg : P PrintArg := do
  ws
  if (← peek) == some '"' then pure (.text (← strLit))
  else if (← peek) == some '%' then pure (.exp (← exp))
  else do
    let st ← get
    match ← attempt addr with
    | some a => if ← atArgEnd then pure (.addr a) else do set st; pure (.exp (← exp))
    | none   => do set st; pure (.exp (← exp))

/-- A load is not an operand: every heap value comes through its own load. -- ref: docs/block-ir.md -/
partial def noArith : P Unit := do
  ws
  match ← peek with
  | some c =>
      if c == '+' || c == '*' || c == '/' then
        errAs Diag.p005 "a load cannot be part of an expression — load into a register first"
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
  if ← trySymNl "::" then pure (some (← strLit)) else pure none

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
  if ← atEnd then pure ⟨body⟩ else errAs Diag.p004 "unexpected input after the program"

/-- The failure as a diagnostic. Offsets only: the line and column are resolved against the source
once, when it is rendered. -- ref: `docs/diagnostics.md` § Positions stay lazy -/
def PErr.toDiag (e : PErr) : Diag.Diagnostic :=
  { code := some e.code, msg := e.msg, span := some (Diag.Span.of e.pos e.len)
  , hints := e.hints }

/-- **Read `.prl` text.** -/
def parse (src : String) : Except Diag.Diagnostic File :=
  match file ⟨src.toList.toArray, 0, 0⟩ with
  | .ok (f, _) => .ok f
  | .error e   => .error e.toDiag

end Paralever.Lang
