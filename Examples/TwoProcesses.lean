import Paralever.Lib.Render
import Paralever.Lib.TypedRead
import Paralever.Lib.Notation
import Paralever.Pragma.ArrRef

/-! # Example: two genuinely independent processes, tree printed, equivalence proved

Two processes with messy, interleaved read/write patterns over their own pairs of arrays:

* `procP` works over `a` at `[0,4)` and `b` at `[4,8)`
* `procQ` works over `c` at `[8,12)` and `d` at `[12,16)`

Each reads several cells, writes several cells, and *reads back cells it has written* — so neither is
a tidy map or reduction. They are independent only because their regions never meet, which is exactly
the hypothesis `par_seq_eq_of_disjoint_arrefs` wants.

Use `#eval` on the `renderStr` lines at the bottom to see the actual trees. -/

namespace Paralever.Examples.TwoProcesses
open Paralever

/-! ### Layout

`procP`'s whole world is `[0,8)`; `procQ`'s is `[8,16)`. Naming them as single `ArrRef`s is what
makes the disjointness check one `omega` call. -/

def a : ArrRef := Array[0, 4]      -- procP's first array
def b : ArrRef := Array[4, 4]      -- procP's second
def c : ArrRef := Array[8, 4]      -- procQ's first
def d : ArrRef := Array[12, 4]     -- procQ's second

/-- Everything `procP` may touch. -/
def regionP : ArrRef := Array[0, 8]
/-- Everything `procQ` may touch. -/
def regionQ : ArrRef := Array[8, 8]

/-! ### The two processes

Written with `readInt` (`Lib/TypedRead.lean`) so the proofs never case-split on `Val`. Note both
processes read back a cell they just wrote — `procP` reads `b[0]` after writing it — so each is
genuinely sequential internally, not a reorderable element-wise map. -/

/-- `b[0] := a[0]+a[1]` ; `a[2] := 2·b[0]` ; `b[3] := a[0]-a[1]` -/
def procP : ParM Unit :=
  ParM.bind (readInt (a.loc 0)) (fun a0 =>
  ParM.bind (readInt (a.loc 1)) (fun a1 =>
  ParM.bind (ParM.wr (b.loc 0) (.int (a0 + a1))) (fun _ =>
  ParM.bind (readInt (b.loc 0)) (fun b0 =>                   -- reads back what it wrote
  ParM.bind (ParM.wr (a.loc 2) (.int (2 * b0))) (fun _ =>
            ParM.wr (b.loc 3) (.int (a0 - a1)))))))

/-- `d[2] := c[1]+5` ; `c[3] := d[2]-c[0]` ; `d[0] := c[3]` -/
def procQ : ParM Unit :=
  ParM.bind (readInt (c.loc 1)) (fun c1 =>
  ParM.bind (ParM.wr (d.loc 2) (.int (c1 + 5))) (fun _ =>
  ParM.bind (readInt (d.loc 2)) (fun d2 =>                   -- reads back what it wrote
  ParM.bind (readInt (c.loc 0)) (fun c0 =>
  ParM.bind (ParM.wr (c.loc 3) (.int (d2 - c0))) (fun _ =>
            ParM.wr (d.loc 0) (.int (d2 - c0)))))))

/-! ### A concrete state to walk them against -/

def σ0 : State
  | 0  => .int 10 | 1  => .int 3  | 2  => .int 0 | 3  => .int 0      -- a
  | 4  => .int 0  | 5  => .int 0  | 6  => .int 0 | 7  => .int 0      -- b
  | 8  => .int 7  | 9  => .int 2  | 10 => .int 0 | 11 => .int 0      -- c
  | _  => .int 0                                                      -- d

/-! ### Footprints — computed, by `rfl`

`procP` reads `{0,1,4}` and writes `{4,2,7}`; note `4` appears in both (it is written then read).
All inside `[0,8)`. Likewise `procQ` stays inside `[8,16)`. -/

example : accesses procP σ0 = ⟨[0, 1, 4], [4, 2, 7]⟩ := rfl
example : accesses procQ σ0 = ⟨[9, 14, 8], [14, 11, 12]⟩ := rfl

/-- The Bernstein check passes — decided by computation on the concrete footprints. -/
example : indepB (accesses procP σ0) (accesses procQ (runSeq procP σ0).2) = true := rfl

/-! ### Footprint confinement, for *every* state

The concrete `rfl`s above are a sanity check; the theorem below is what the proof actually needs,
and it holds for all `σ` because `readInt`'s footprint is state-independent. -/

/-- Membership in `procP`'s region, from a plain numeric bound. -/
private theorem memP {l : Loc} (h : l < 8) : regionP.InRange l := by
  show 0 ≤ l ∧ l < 0 + 8
  grind

/-- Membership in `procQ`'s region. -/
private theorem memQ {l : Loc} (h1 : 8 ≤ l) (h2 : l < 16) : regionQ.InRange l := by
  show 8 ≤ l ∧ l < 8 + 8
  grind

/-- A write node's footprint is confined as soon as its one location is. -/
private theorem wrWithin {l : Loc} {P : Loc → Prop} (hl : P l) (v : Val) (σ : State) :
    FootprintWithin (accesses (ParM.wr l v) σ) P :=
  ⟨Within.empty _, Within.singleton hl⟩

theorem procP_within (σ : State) : FootprintWithin (accesses procP σ) regionP.InRange := by
  unfold procP
  refine footprintWithin_bind _ _ _ _ (readInt_footprintWithin _ _ _ _ (memP (by decide))) ?_
  rw [readInt_runSeq]
  refine footprintWithin_bind _ _ _ _ (readInt_footprintWithin _ _ _ _ (memP (by decide))) ?_
  rw [readInt_runSeq]
  refine footprintWithin_bind _ _ _ _ (wrWithin (memP (by decide)) _ _) ?_
  refine footprintWithin_bind _ _ _ _ (readInt_footprintWithin _ _ _ _ (memP (by decide))) ?_
  rw [readInt_runSeq]
  refine footprintWithin_bind _ _ _ _ (wrWithin (memP (by decide)) _ _) ?_
  exact wrWithin (memP (by decide)) _ _

theorem procQ_within (σ : State) : FootprintWithin (accesses procQ σ) regionQ.InRange := by
  unfold procQ
  refine footprintWithin_bind _ _ _ _
    (readInt_footprintWithin _ _ _ _ (memQ (by decide) (by decide))) ?_
  rw [readInt_runSeq]
  refine footprintWithin_bind _ _ _ _ (wrWithin (memQ (by decide) (by decide)) _ _) ?_
  refine footprintWithin_bind _ _ _ _
    (readInt_footprintWithin _ _ _ _ (memQ (by decide) (by decide))) ?_
  rw [readInt_runSeq]
  refine footprintWithin_bind _ _ _ _
    (readInt_footprintWithin _ _ _ _ (memQ (by decide) (by decide))) ?_
  rw [readInt_runSeq]
  refine footprintWithin_bind _ _ _ _ (wrWithin (memQ (by decide) (by decide)) _ _) ?_
  exact wrWithin (memQ (by decide) (by decide)) _ _

/-! ### WellFormed — trivial, there is no nested `par` -/

theorem procP_wellformed (σ : State) : WellFormed procP σ := by
  unfold procP; grind [readInt, WellFormed, ParM.bind, ParM.wr]

theorem procQ_wellformed (σ : State) : WellFormed procQ σ := by
  unfold procQ; grind [readInt, WellFormed, ParM.bind, ParM.wr]

/-! ### The payoff -/

/-- **`procP ∥ procQ` ≡ `procP ; procQ`, for every initial state.** The only genuinely
problem-specific input is `by omega`: region `[0,8)` ends where region `[8,16)` begins. -/
theorem procs_par_seq_eq (σ : State) :
    ParM.parPair procP procQ ∥≡ ParM.seqPair procP procQ from σ :=
  par_seq_eq_of_disjoint_arrefs regionP regionQ procP procQ σ
    (procP_wellformed σ) (procQ_wellformed _)
    (procP_within σ) (procQ_within _)
    (Or.inl (by decide))

/-! ### The trees

`#eval` these to see what the terms actually look like. -/

/--
info: read  [0] → Paralever.Val.int 10
read  [1] → Paralever.Val.int 3
write [4] ← Paralever.Val.int 13
read  [4] → Paralever.Val.int 13
write [2] ← Paralever.Val.int 26
write [7] ← Paralever.Val.int 7
pure
-/
#guard_msgs in #eval IO.println (renderStr procP σ0)

/-- info: reads [0, 1, 4]   writes [4, 2, 7] -/
#guard_msgs in #eval IO.println (footprintStr procP σ0)

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
#guard_msgs in #eval IO.println (renderStr (ParM.parPair procP procQ) σ0)

end Paralever.Examples.TwoProcesses
