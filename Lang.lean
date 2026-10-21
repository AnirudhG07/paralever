import Lang.Core.Prog
import Lang.Core.Layout
import Lang.Core.Kernels
import Lang.Core.Cuda
import Lang.Core.Cost
import Lang.Core.Exec
import Lang.Core.Analysis
import Lang.Core.AutoParSound
import Lang.Core.Notation
import Lang.Core.Imp
import Lang.Compile.Ast
import Lang.Compile.Parse
import Lang.Compile.Lower
import Lang.Compile.Print
import Lang.Load
import Lang.Report

/-! # The paralever language, and the `.prl` file in front of it

| where | contents |
|---|---|
| `Core/` | the `ParProg` language: syntax, both interpreters, computed footprints, kernels, cost, real threads, dependence analysis |
| `Compile/` | the `.prl` front end: `Ast`, `Parse`, `Lower` (names, placement, unrolling), `Print` |
| `Load.lean` | `prl_file` — read and compile a file while Lean elaborates |
| `Report.lean` | the `#eval` views: check, run, race, autoparallelize |

The `.prl` files themselves live in `Examples/Language/`, gated by `Test/Lang.lean` and demonstrated
by `Examples/Language/Files.lean`.

Rationale: `docs/prl.md`. The language's own design is `docs/block-ir.md` and `docs/layout.md`. -/
