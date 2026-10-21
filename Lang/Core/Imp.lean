import Lang.Core.Prog
import Lang.Core.Layout
import Lang.Core.Kernels
import Lang.Core.Cuda
import Lang.Core.Cost
import Lang.Core.Exec
import Lang.Core.Analysis
import Lang.Core.Notation

/-! # The surface language, assembled

One import for the whole of `Lang/`. The pieces, in dependency order:

| file | contents |
|---|---|
| `Core` | `ParProg`, the lowering into `ParM`, `footprintOf`, `wfB`, and `par_seq_eq` |
| `Layout` | `Buf`/`alloc` — declare buffers by shape, the allocator assigns addresses |
| `Kernels` | `mapK`, `broadcastK`, `reduceK`, `gridK` and their obligations |
| `Cuda` | `launch`, `launchGrid`, `Tid`, `globalTid` |
| `Cost` | `time_le` — the parallel reading is never slower |
| `Exec` | `runTask` / `runTaskSeq`, running on real threads |
| `Analysis` | `dependences`, `autoPar` — finding the parallelism |
| `Notation` | printing, and the `paralever { … }` surface syntax (needs `Kernels`: `parfor` expands to `parFor`) |
-/
