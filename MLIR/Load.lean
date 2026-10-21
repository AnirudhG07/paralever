import MLIR.Lower
import Lang.Load
import Lean

/-! # `mlir_prog` — lowering a `.mlir` file while the Lean file elaborates

The same door `prl_file` is (`Lang/Load.lean`): the file is parsed, lowered and **quoted** at
elaboration time, so the declaration holds a `ParProg` literal and `by decide` on `wfB` sees the
program rather than the reader. Without it a corpus pilot can only carry a `#guard` on its verdict,
because `decide` would have to run the parser in the kernel. -- ref: `docs/mlir.md` -/

namespace Paralever.MLIR
open Lean Elab Term

/-- The file's contents, through `include_str`, so the path is read against the Lean file that
names it. -/
private def readLit (s : TSyntax `str) : TermElabM String := do
  let e ← instantiateMVars (← elabTerm (← `(include_str $s)) (some (mkConst ``String)))
  match e.consumeMData with
  | .lit (.strVal src) => pure src
  | _ => throwErrorAt s "cannot read {s.getString}"

private def lowerLit (s : TSyntax `str) : TermElabM Lowered := do
  match parse (← readLit s) with
  | .error e  => throwErrorAt s "{s.getString}: {e}"
  | .ok ops   =>
      match lower ops with
      | .error e => throwErrorAt s "{s.getString}: {e}"
      | .ok r    => pure r

/-- `mlir_prog "../Examples/Mlir/doall-no.mlir"` — the lowered program. -/
syntax "mlir_prog " str : term
/-- `mlir_layout "../Examples/Mlir/doall-no.mlir"` — its memory. -/
syntax "mlir_layout " str : term

elab_rules : term
  | `(mlir_prog $s:str)   => do pure (toExpr (← lowerLit s).prog)
  | `(mlir_layout $s:str) => do pure (toExpr (← lowerLit s).layout)

end Paralever.MLIR
