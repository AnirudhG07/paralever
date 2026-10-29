import Lang.Compile.Ast
import Diag

/-! # `input` — values from the shell, read while the program compiles

The stream the program's `input` forms draw from, and the test for whether a file has any. The
consumption itself is in `Lang/Compile/Lower.lean`, because it happens at lowering time: an `input`
becomes a literal before any program exists, so no `ParProg` constructor and no `ParM` constructor
is spent on it.

Rationale, and why not a run-time read: `docs/prl.md` § Input. -/

namespace Paralever.Lang

/-- What is left to read. Characters rather than words, because a `str` input takes a whole line and
a numeric one takes a word. -/
abbrev Input := List Char

/-- Everything here breaks one rule: the stream does not supply what the program asks for. -/
private def exhausted (what : String) : Diag.Diagnostic :=
  { code := some Diag.p109
  , msg := s!"input is exhausted: the program asks for {what} and none is left" }

private def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r' || c == '\n'

/-- The next whitespace-separated word. -/
def Input.word (s : Input) : Except Diag.Diagnostic (String × Input) :=
  let s := s.dropWhile isSpace
  if s.isEmpty then .error (exhausted "a value")
  else .ok (String.ofList (s.takeWhile (fun c => !isSpace c)), s.dropWhile (fun c => !isSpace c))

/-- The rest of the line. Leading whitespace is skipped first, newlines included, so a `str` input
after a numeric one reads the next non-empty line rather than the empty tail of the current one.
An empty line is therefore not readable as the empty string. -/
def Input.line (s : Input) : Except Diag.Diagnostic (String × Input) :=
  let s := s.dropWhile isSpace
  if s.isEmpty then .error (exhausted "a line")
  else .ok (String.ofList (s.takeWhile (fun c => c != '\n')),
            (s.dropWhile (fun c => c != '\n')).drop 1)

/-- A word as a number. `true` and `false` read as `1` and `0`, which is what a condition tests. -/
def intOfWord (w : String) : Except Diag.Diagnostic Int :=
  if w == "true" then .ok 1
  else if w == "false" then .ok 0
  else match w.toInt? with
    | some n => .ok n
    | none   => .error
        { code := some Diag.p109, msg := s!"'{w}' is not a number"
        , hints := ["an input value is an integer, or 'true' or 'false'"] }

/-! ## Whether a file reads input

The command line reads standard input only for a program that asks for it, and `prl_file` and
`prove` refuse such a program outright, so the test has to be answerable before compiling. -/

def Exp.usesInput : Exp → Bool
  | .input          => true
  | .num _ | .name _ | .reg _ | .len _ => false
  | .not a          => a.usesInput
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b
  | .min a b | .max a b | .lt a b | .eq a b => a.usesInput || b.usesInput

def Addr.usesInput : Addr → Bool
  | .raw e     => e.usesInput
  | .cell _ es => es.any Exp.usesInput
  | .part _ lo hi i => lo.usesInput || hi.any Exp.usesInput || i.usesInput

def BufInit.usesInput : BufInit → Bool
  | .input | .inputStr => true
  | .full e            => e.usesInput
  | .data es           => es.any Exp.usesInput
  | .zeros | .ones | .eye | .arange | .str _ => false

def Decl.usesInput : Decl → Bool
  | .buf _ shape init at? => shape.any Exp.usesInput || init.usesInput || at?.any Exp.usesInput
  | .const _ e            => e.usesInput
  | .reg _ _              => false
  | .slice _ _ lo hi      => lo.usesInput || hi.any Exp.usesInput

mutual

def Stmt.usesInput : Stmt → Bool
  | .load _ a        => a.usesInput
  | .store a e       => a.usesInput || e.usesInput
  | .set _ e         => e.usesInput
  | .par ts _        => threadsUseInput ts
  | .forIn _ n b     => n.usesInput || stmtsUseInput b
  | .parfor _ n b _  => n.usesInput || stmtsUseInput b
  | .ifElse c t e    => c.usesInput || stmtsUseInput t || stmtsUseInput e
  | .whileIn c n b   => c.usesInput || n.usesInput || stmtsUseInput b
  | .decl ds         => ds.any Decl.usesInput
  | .free _          => false
  | .synchronize     => false
  -- a `def` body is read before it is written out, so a file that defines a function reading input
  -- asks for input whether or not the function is ever called
  | .defn _ _ b      => stmtsUseInput b
  | .call _ as       => as.any fun | .exp e => e.usesInput | .reg _ => false
  | .assert _ l r _  => (l.args ++ r.args).any fun | .exp e => e.usesInput | .reg _ => false
  | .print as        => as.any fun
      | .exp e  => e.usesInput
      | .text _ => false
      | .addr _ => false

def stmtsUseInput : List Stmt → Bool
  | []      => false
  | s :: ss => s.usesInput || stmtsUseInput ss

def threadsUseInput : List (List Stmt) → Bool
  | []      => false
  | t :: ts => stmtsUseInput t || threadsUseInput ts

end

/-- Whether the file has any `input` form, so the caller knows to read standard input. -/
def File.usesInput (f : File) : Bool := stmtsUseInput f.body

end Paralever.Lang
