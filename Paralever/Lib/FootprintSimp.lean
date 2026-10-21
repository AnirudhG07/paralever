import Paralever.Lib.Compose
import Paralever.Lib.TypedRead
import Paralever.Lib.TouchesOnly
import Paralever.Kernels.MapArray

/-! # Footprint automation — all footprint lemmas are `@[simp, grind .]`

Every footprint lemma in Lib/ and Kernels/ is tagged `@[simp, grind .]`, so:
- `grind` discharges most footprint goals automatically
- `simp` works for simpler goals
- For manual proof, the key lemmas are in `Lib/Compose`, `Lib/TypedRead`, `Lib/ArrRef`,
  and `Kernels/MapArray`.

This file is a convenience import — `import Paralever.Lib.FootprintSimp` brings in all footprint
infrastructure at once. -/
