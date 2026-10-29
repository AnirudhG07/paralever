import Lang.Compile.Lower
import Lean

/-! # `prl_file` — reading a `.prl` file from a Lean file

The file is read, compiled and **quoted** while the Lean file elaborates, so what the declaration
holds is a `Compiled` literal: `by decide` on `wfB` sees the program, never the reader. A file that
does not compile is an elaboration error at the `prl_file` term, carrying the `line:column` the
reader reported. -/

namespace Paralever.Lang
open Lean Elab Term

deriving instance ToExpr for Paralever.AExp
deriving instance ToExpr for Paralever.ArrRef
deriving instance ToExpr for Paralever.Lang.PrintItem
deriving instance ToExpr for Paralever.Nest.AffAccess
deriving instance ToExpr for Paralever.Lang.NestStmt
deriving instance ToExpr for Paralever.Lang.LoopNest
deriving instance ToExpr for Paralever.Lang.ParProg
deriving instance ToExpr for Paralever.Buf
deriving instance ToExpr for Paralever.Placed
deriving instance ToExpr for Paralever.Layout
deriving instance ToExpr for Strength
deriving instance ToExpr for Claim
deriving instance ToExpr for Compiled

/-- The contents of the file named by a string literal, through `include_str` so that the path is
resolved against the Lean file's own directory. -/
private def readLit (s : TSyntax `str) : TermElabM String := do
  let e ← instantiateMVars (← elabTerm (← `(include_str $s)) (some (mkConst ``String)))
  match e.consumeMData with
  | .lit (.strVal src) => pure src
  | _ => throwErrorAt s "cannot read {s.getString}"

/-- Why a reader with no pipe refuses a program that reads input, and what to do instead. The
input is consumed while the program compiles, so a resolved program is an ordinary `.prl` file with
the values written in — which is what `to-prl` prints. -- ref: `docs/prl.md` § Input -/
def inputRefusal (reader : String) : String :=
  "this program reads 'input', which " ++ reader ++ " cannot supply. Resolve the input first: \
'paralever to-prl FILE < data > resolved.prl' prints the same program with the values it read \
written in"

private def compileLit (s : TSyntax `str) : TermElabM Compiled := do
  let src ← readLit s
  -- rendered against the file, so the message carries the code, the line and the caret
  let S := Diag.Source.of s.getString src
  match parse src with
  | .error d => throwErrorAt s "{Diag.render S d}"
  | .ok f =>
      if f.usesInput then
        throwErrorAt s "{Diag.render S { code := some Diag.p108
                                       , msg := inputRefusal "a Lean file" }}"
      else match compile f with
        | .ok c    => pure c
        | .error d => throwErrorAt s "{Diag.render S d}"

/-- `prl_file "sum.prl"` — the file as a `Compiled`. -/
syntax "prl_file " str : term
/-- `prl_prog "sum.prl"` — the file's program alone. -/
syntax "prl_prog " str : term
/-- `prl_layout "sum.prl"` — the file's memory alone. -/
syntax "prl_layout " str : term

elab_rules : term
  | `(prl_file $s:str)   => do pure (toExpr (← compileLit s))
  | `(prl_prog $s:str)   => do pure (toExpr (← compileLit s).prog)
  | `(prl_layout $s:str) => do pure (toExpr (← compileLit s).layout)

/-- Read a file at run time — the `prl` executable's path into the same compiler. Standard input
is read only for a program whose text asks for it, so a pipe is never required. -/
def load (path : System.FilePath) : IO Compiled := do
  let src ← IO.FS.readFile path
  let S := Diag.Source.of path.toString src
  match parse src with
  | .error d => throw (IO.userError (Diag.render S d))
  | .ok f => do
      let stdin ← if f.usesInput then (← IO.getStdin).readToEnd else pure ""
      match compile f stdin with
      | .ok c    => pure c
      | .error d => throw (IO.userError (Diag.render S d))

end Paralever.Lang
