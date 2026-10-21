import Tool.Proof
import Tool.Run

/-! # `Tool` — the `paralever` command line

| where | contents |
|---|---|
| `Tool/Proof.lean` | the Lean module `paralever prove` writes, and which of the three theorems it carries |
| `Tool/Run.lean` | the commands, the option grammar, and reading either front end |

`Main.lean` is the executable's root and does nothing but call `Paralever.Tool.main`.
Rationale and the worked examples: `docs/cli.md`. -/
