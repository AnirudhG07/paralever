import Paralever.Lib.Block
import Paralever.Lib.Cost
import Paralever.Lib.Render
import Paralever.Pragma.ArrRef

/-! # Two independent processes, written as IR blocks

`procP` works over `a = [0,4)` and `b = [4,8)`; `procQ` over `c = [8,12)` and `d = [12,16)`. Each
reads back a cell it just wrote, so neither is a reorderable element-wise map; they are independent
only because their regions never meet.

The six steps: **pure**, **seq**, **par**, then `pure = seq`, `seq = par`, `time par < time seq`.
Rationale: `docs/block-ir.md`, `docs/cost.md`. -/

namespace Paralever.Examples.TwoProcesses
open Paralever

/-! ### Layout and the two blocks

`R n` is register `n`; arithmetic is ordinary `+`/`-`/`*` on `AExp`. Registers are not memory, so
none of them appears in a footprint. -/

def a : ArrRef := Array[0, 4]       -- procP's first array
def b : ArrRef := Array[4, 8]       -- procP's second
def c : ArrRef := Array[8, 12]      -- procQ's first
def d : ArrRef := Array[12, 16]     -- procQ's second

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

/-- A concrete heap and register file, for the numeric checks and the tree dumps below. -/
def σ0 : State
  | 0  => .int 10 | 1  => .int 3  | 2  => .int 0 | 3  => .int 0      -- a
  | 4  => .int 0  | 5  => .int 0  | 6  => .int 0 | 7  => .int 0      -- b
  | 8  => .int 7  | 9  => .int 2  | 10 => .int 0 | 11 => .int 0      -- c
  | _  => .int 0                                                      -- d

def ρ0 : Regs := fun _ => 0

/-! ### pure

A `Block` is data, so its pure counterpart is an ordinary interpreter: no monad, no footprints,
registers and heap threaded by hand. -/

/-- `procP` then `procQ`, purely. -/
def procsPure (ρ₁ ρ₂ : Regs) (σ : State) : State :=
  (execPure procQ ρ₂ (execPure procP ρ₁ σ).2).2

/-! ### seq -/

def procsSeq (ρ₁ ρ₂ : Regs) : ParM (Unit × Unit) :=
  ParM.seqPair (exec procP ρ₁) (exec procQ ρ₂)

/-! ### par -/

def procsPar (ρ₁ ρ₂ : Regs) : ParM (Unit × Unit) :=
  ParM.parPair (exec procP ρ₁) (exec procQ ρ₂)

/-! ### pure = seq -/

theorem pure_eq_seq (ρ₁ ρ₂ : Regs) (σ : State) :
    (runSeq (procsSeq ρ₁ ρ₂) σ).2 = procsPure ρ₁ ρ₂ σ := by
  simp only [procsSeq, procsPure, ParM.seqPair, runSeq_bind, runSeq]
  rw [exec_eq_execPure procP ρ₁ σ, exec_eq_execPure procQ ρ₂]

/-- At `σ0`: `b[0] = 10 + 3`, `a[2] = 2 · 13`, `b[3] = 10 - 3`. -/
example : (procsPure ρ0 ρ0 σ0 (b.loc 0), procsPure ρ0 ρ0 σ0 (a.loc 2),
           procsPure ρ0 ρ0 σ0 (b.loc 3)) = (.int 13, .int 26, .int 7) := rfl

/-! ### seq = par

The footprints are read off the instruction lists — `footprintOf` never looks at a state — and
`exec_accesses` connects them to the `accesses` the metatheorem is stated against. So the whole
obligation is one `decide`. -/

example : footprintOf procP = ⟨[0, 1, 4], [4, 2, 7]⟩ := rfl
example : footprintOf procQ = ⟨[9, 14, 8], [14, 11, 12]⟩ := rfl
example : indepB (footprintOf procP) (footprintOf procQ) = true := rfl

theorem seq_eq_par (ρ₁ ρ₂ : Regs) (σ : State) : procsPar ρ₁ ρ₂ ∥≡ procsSeq ρ₁ ρ₂ from σ :=
  block_par_seq_eq_of_indepB procP procQ ρ₁ ρ₂ σ (by decide)

/-! ### time par < time seq -/

private theorem wf (ρ₁ ρ₂ : Regs) (σ : State) : WellFormed (procsPar ρ₁ ρ₂) σ :=
  block_wellformed_parPair procP procQ ρ₁ ρ₂ σ ((indepB_iff _ _).mp (by decide))

/-- `max` is derived from the parallel-round semantics, not written into it (`docs/cost.md`). -/
theorem time_eq_max (ρ₁ ρ₂ : Regs) (σ : State) :
    time (procsPar ρ₁ ρ₂) σ = max (time (exec procP ρ₁) σ) (time (exec procQ ρ₂) σ) :=
  time_parPair_eq_max _ _ σ (wf ρ₁ ρ₂ σ)

theorem time_lt (ρ₁ ρ₂ : Regs) (σ : State) :
    time (procsPar ρ₁ ρ₂) σ < time (procsSeq ρ₁ ρ₂) σ :=
  time_par_lt_seq _ _ σ (wf ρ₁ ρ₂ σ) (exec_time_pos _ _ ρ₁ σ) (exec_time_pos _ _ ρ₂ σ)

/-- Same operation count either way, with no hypothesis at all — only the rounds shrink. -/
theorem work_eq (ρ₁ ρ₂ : Regs) (σ : State) :
    work (procsPar ρ₁ ρ₂) σ = work (procsSeq ρ₁ ρ₂) σ := work_par_eq_seq _ _ σ

/-- Measured at `σ0`: twelve operations either way, six rounds in parallel against twelve in
sequence. -/
example : (work (procsPar ρ0 ρ0) σ0, time (procsPar ρ0 ρ0) σ0) = (12, 6) := rfl
example : (work (procsSeq ρ0 ρ0) σ0, time (procsSeq ρ0 ρ0) σ0) = (12, 12) := rfl

/-! ### Anti-vacuity

`procQ'` writes `b[3]`, one of `procP`'s cells, so the `decide` above would not succeed for it. -/

def procQ' : Block := [ .load 0 (c.loc 1), .store (b.loc 3) (R 0) ]

example : indepB (footprintOf procP) (footprintOf procQ') = false := rfl

/-! ### The rendered trees

`exec` generated the binds; `render` walks the resulting `ParM` term. -/

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

/-- info: par ⟨
  [0] ∥
    read  [0] → Paralever.Val.int 10
    read  [1] → Paralever.Val.int 3
    write [4] ← Paralever.Val.int 13
    read  [4] → Paralever.Val.int 13
    write [2] ← Paralever.Val.int 26
    write [7] ← Paralever.Val.int 7
    pure
  [1] ∥
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
#guard_msgs in #eval IO.println (renderStr (procsPar ρ0 ρ0) σ0)

end Paralever.Examples.TwoProcesses
