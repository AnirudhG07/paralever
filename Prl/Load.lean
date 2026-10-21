import Prl.Compile.Lower
import Lean

/-! # `prl_file` — reading a `.prl` file from a Lean file

The file is read, compiled and **quoted** while the Lean file elaborates, so what the declaration
holds is a `Compiled` literal: `by decide` on `wfB` sees the program, never the reader. A file that
does not compile is an elaboration error at the `prl_file` term, carrying the `line:column` the
reader reported. -/

namespace Paralever.Prl
open Lean Elab Term

deriving instance ToExpr for Paralever.AExp
deriving instance ToExpr for Paralever.ArrRef
deriving instance ToExpr for Paralever.Prl.ParProg
deriving instance ToExpr for Paralever.Buf
deriving instance ToExpr for Paralever.Placed
deriving instance ToExpr for Paralever.Layout
deriving instance ToExpr for Compiled

/-- The contents of the file named by a string literal, through `include_str` so that the path is
resolved against the Lean file's own directory. -/
private def readLit (s : TSyntax `str) : TermElabM String := do
  let e ← instantiateMVars (← elabTerm (← `(include_str $s)) (some (mkConst ``String)))
  match e.consumeMData with
  | .lit (.strVal src) => pure src
  | _ => throwErrorAt s "cannot read {s.getString}"

private def compileLit (s : TSyntax `str) : TermElabM Compiled := do
  match ofString (← readLit s) with
  | .ok c    => pure c
  | .error e => throwErrorAt s "{s.getString}:{e}"

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

/-- Read a file at run time — the `prl` executable's path into the same compiler. -/
def load (path : System.FilePath) : IO Compiled := do
  match ofString (← IO.FS.readFile path) with
  | .ok c    => pure c
  | .error e => throw (IO.userError s!"{path}:{e}")

end Paralever.Prl
