import Paralever.Lib.Block
import Paralever.Lib.Render
import Paralever.Pragma.ArrRef

/-! # Example: two independent processes, written as IR blocks

The same two processes as before, but written as `Block`s — lists of `load`/`store` instructions —
instead of hand-nested `ParM.bind` chains. Nothing about the programs changed; what changed is that

* the binds are **generated** by `exec`, not written here, and
* the footprint is **computed** by `footprintOf`, so every proof below is `rfl` or `decide`.

Compare the previous version of this file in git history: `procP_within` was a twelve-line chain of
`footprintWithin_bind` applications. It is now gone entirely — `exec_accesses` replaced it, once,
for all blocks.

`procP` works over `a` at `[0,4)` and `b` at `[4,8)`; `procQ` over `c` at `[8,12)` and `d` at
`[12,16)`. Each reads back a cell it just wrote, so neither is a reorderable element-wise map; they
are independent only because their regions never meet. -/

namespace Paralever.Examples.TwoProcesses
open Paralever

/-! ### Layout -/

def a : ArrRef := Array[0, 4]      -- procP's first array
def b : ArrRef := Array[4, 4]      -- procP's second
def c : ArrRef := Array[8, 4]      -- procQ's first
def d : ArrRef := Array[12, 4]     -- procQ's second

/-! ### The two processes, as straight-line IR

`R n` is register `n`; arithmetic is ordinary `+`/`-`/`*` on `AExp`. Registers are not memory, so
none of them appears in a footprint. -/

/-- `b[0] := a[0]+a[1]` ; `a[2] := 2·b[0]` ; `b[3] := a[0]-a[1]` -/
def procP : Block :=
  [ .load  0 (a.loc 0),                    -- r0 := a[0]
    .load  1 (a.loc 1),                    -- r1 := a[1]
    .store   (b.loc 0) (R 0 + R 1),        -- b[0] := r0 + r1
    .load  2 (b.loc 0),                    -- r2 := b[0]   ← reads back what it wrote
    .store   (a.loc 2) (2 * R 2),          -- a[2] := 2 * r2
    .store   (b.loc 3) (R 0 - R 1) ]       -- b[3] := r0 - r1

/-- `d[2] := c[1]+5` ; `c[3] := d[2]-c[0]` ; `d[0] := c[3]` -/
def procQ : Block :=
  [ .load  0 (c.loc 1),                    -- r0 := c[1]
    .store   (d.loc 2) (R 0 + 5),          -- d[2] := r0 + 5
    .load  1 (d.loc 2),                    -- r1 := d[2]   ← reads back what it wrote
    .load  2 (c.loc 0),                    -- r2 := c[0]
    .store   (c.loc 3) (R 1 - R 2),        -- c[3] := r1 - r2
    .store   (d.loc 0) (R 1 - R 2) ]       -- d[0] := r1 - r2

/-! ### Footprints — now `rfl`, read straight off the instruction lists

No state is mentioned, because `footprintOf` never looks at one. -/

example : footprintOf procP = ⟨[0, 1, 4], [4, 2, 7]⟩ := rfl
example : footprintOf procQ = ⟨[9, 14, 8], [14, 11, 12]⟩ := rfl

/-- The Bernstein check is a decision procedure on the two lists. -/
example : indepB (footprintOf procP) (footprintOf procQ) = true := rfl

/-! ### The payoff — one `decide`, for every initial state and every register file

`exec_accesses` (proved once in `Lib/Block.lean`) is what connects the syntactic footprint to the
`accesses` the metatheorem is stated against. Nothing problem-specific is proved here at all. -/

theorem procs_par_seq_eq (ρ₁ ρ₂ : Regs) (σ : State) :
    ParM.parPair (exec procP ρ₁) (exec procQ ρ₂)
      ∥≡ ParM.seqPair (exec procP ρ₁) (exec procQ ρ₂) from σ :=
  block_par_seq_eq_of_indepB procP procQ ρ₁ ρ₂ σ (by decide)

/-! ### Anti-vacuity: overlap the regions and the check fails

`procQ'` writes `b[3]` — one of `procP`'s cells — so the `decide` above would not succeed for it,
and the footprints genuinely conflict. -/

def procQ' : Block := [ .load 0 (c.loc 1), .store (b.loc 3) (R 0) ]

example : indepB (footprintOf procP) (footprintOf procQ') = false := rfl

/-! ### The trees

`exec` generated the binds; `render` walks the resulting `ParM` term. -/

def σ0 : State
  | 0  => .int 10 | 1  => .int 3  | 2  => .int 0 | 3  => .int 0      -- a
  | 4  => .int 0  | 5  => .int 0  | 6  => .int 0 | 7  => .int 0      -- b
  | 8  => .int 7  | 9  => .int 2  | 10 => .int 0 | 11 => .int 0      -- c
  | _  => .int 0                                                      -- d

def ρ0 : Regs := fun _ => 0

/--
info: read  [0] → Paralever.Val.int 10
read  [1] → Paralever.Val.int 3
write [4] ← Paralever.Val.int 13
read  [4] → Paralever.Val.int 13
write [2] ← Paralever.Val.int 26
write [7] ← Paralever.Val.int 7
pure
-/
#guard_msgs in #eval IO.println (renderStr (exec procP ρ0) σ0)

/--
info: par ⟨
  left ∥
    read  [0] → Paralever.Val.int 10
    read  [1] → Paralever.Val.int 3
    write [4] ← Paralever.Val.int 13
    read  [4] → Paralever.Val.int 13
    write [2] ← Paralever.Val.int 26
    write [7] ← Paralever.Val.int 7
    pure
  right ∥
    read  [9] → Paralever.Val.int 2
    write [14] ← Paralever.Val.int 7
    read  [14] → Paralever.Val.int 7
    read  [8] → Paralever.Val.int 7
    write [11] ← Paralever.Val.int 0
    write [12] ← Paralever.Val.int 0
    pure
⟩
pure
-/
#guard_msgs in #eval IO.println (renderStr (ParM.parPair (exec procP ρ0) (exec procQ ρ0)) σ0)

end Paralever.Examples.TwoProcesses
