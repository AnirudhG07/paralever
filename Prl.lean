import Prl.Lang.Core
import Prl.Lang.Layout
import Prl.Lang.Kernels
import Prl.Lang.Cuda
import Prl.Lang.Cost
import Prl.Lang.Exec
import Prl.Lang.Analysis
import Prl.Lang.AutoParSound
import Prl.Lang.Notation
import Prl.Lang.Imp
import Prl.Compile.Ast
import Prl.Compile.Parse
import Prl.Compile.Lower
import Prl.Compile.Print
import Prl.Load
import Prl.Report

/-! # Prl — the language, and the `.prl` file in front of it

| where | contents |
|---|---|
| `Lang/` | the `ParProg` language: syntax, both interpreters, computed footprints, kernels, cost, real threads, dependence analysis |
| `Compile/` | the `.prl` front end: `Ast`, `Parse`, `Lower` (names, placement, unrolling), `Print` |
| `Load.lean` | `prl_file` — read and compile a file while Lean elaborates |
| `Report.lean` | the `#eval` views: check, run, race, autoparallelize |

The `.prl` files themselves live in `Examples/Language/`, gated by `Test/Prl.lean` and demonstrated
by `Examples/Language/Files.lean`.

Rationale: `docs/prl.md`. The language's own design is `docs/block-ir.md` and `docs/layout.md`. -/
