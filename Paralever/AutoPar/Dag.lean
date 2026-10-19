import Paralever.Lang.Analysis

/-! # The dependence DAG, and the bound it gives

The DAG is built by one scoreboard pass, not by a pairwise scan: Bernstein's three clauses are the
three kinds of edge (RAW, WAW, WAR), and each is read off `lastWriter` / `readersSince`. Its
critical path is a **lower bound** on the depth of any schedule, so it is what says whether a plan
is optimal. -- ref: docs/autopar-algorithm.md § The bound -/

namespace Paralever.AutoPar
open Paralever Paralever.Lang Paralever.Lang.ParProg

/-! ## A syntactic cost

`Lib/Cost.lean`'s `time` needs a heap and is quadratic in `work` to evaluate. The scheduler needs
only an ordering, so it counts memory operations off the syntax, with `foldr max` at a fork exactly
as `time` has it. -/

mutual

/-- Memory operations along the longest path of a statement. -/
def depth : ParProg → Nat
  | .load _ _      => 1
  | .store _ _     => 1
  | .set _ _       => 0
  | .seq a b       => depth a + depth b
  | .par ss        => depthAll ss
  | .label _ s     => depth s
  | .loadAt _ _ _  => 1
  | .storeAt _ _ _ => 1
  | .ifElse _ t e  => max (depth t) (depth e)

/-- The longest of the threads' depths — `time`'s `foldr max` at a fork. -/
def depthAll : List ParProg → Nat
  | []      => 0
  | s :: ss => max (depth s) (depthAll ss)

end

/-! ## The scoreboard -/

/-- The last unit to write each cell, and the units that have read it since. -/
structure Board where
  lastW : List (Loc × Nat)
  rdrs  : List (Loc × List Nat)

/-- The writer of `l`, if any. -/
def Board.writer (b : Board) (l : Loc) : Option Nat :=
  (b.lastW.find? (fun e => e.1 == l)).map (·.2)

/-- The units that have read `l` since it was last written. -/
def Board.readers (b : Board) (l : Loc) : List Nat :=
  (b.rdrs.find? (fun e => e.1 == l)).elim [] (·.2)

/-- Record `i` as `l`'s writer, and clear `l`'s readers: they are now ordered before `i`. -/
def Board.wrote (b : Board) (l : Loc) (i : Nat) : Board :=
  ⟨(l, i) :: b.lastW.filter (fun e => e.1 != l), b.rdrs.filter (fun e => e.1 != l)⟩

/-- Record `i` as a reader of `l`. -/
def Board.read (b : Board) (l : Loc) (i : Nat) : Board :=
  ⟨b.lastW, (l, i :: b.readers l) :: b.rdrs.filter (fun e => e.1 != l)⟩

/-- The units unit `i` must follow, given the board before it ran. All three Bernstein clauses:
`W∩R` is RAW, `W∩W` is WAW, `R∩W` is WAR. -/
def predsOf (b : Board) (f : Footprint) : List Nat :=
  let raw := f.reads.filterMap b.writer
  let waw := f.writes.filterMap b.writer
  let war := f.writes.flatMap b.readers
  (raw ++ waw ++ war).eraseDups

/-- The board after unit `i` with footprint `f` has run. Readers are collected *after* the writes
clear them, so a unit that both reads and writes a cell is left as its reader. -/
def Board.after (b : Board) (f : Footprint) (i : Nat) : Board :=
  f.reads.foldl (fun b' l => b'.read l i) (f.writes.foldl (fun b' l => b'.wrote l i) b)

/-- The predecessor lists of a unit chain, in order. One pass. -/
def preds (us : List ParProg) : List (List Nat) :=
  let rec go (b : Board) (i : Nat) : List ParProg → List (List Nat)
    | []      => []
    | u :: us =>
        let f := ParProg.footprintOf u
        predsOf b f :: go (b.after f i) (i + 1) us
  go ⟨[], []⟩ 0 us

/-! ## The bound -/

/-- Earliest start of each unit: every predecessor must have finished. Predecessors always have
smaller indices, so one left fold suffices. -/
def asap (us : List ParProg) : List Nat :=
  let ps := preds us
  let cs := us.map depth
  (List.range us.length).foldl (fun acc i =>
    acc ++ [((ps.getD i []).map (fun j => acc.getD j 0 + cs.getD j 0)).foldl max 0]) []

/-- **The critical path** — no schedule of these units, fork–join or otherwise, has smaller depth. -/
def critical (us : List ParProg) : Nat :=
  let a := asap us
  let cs := us.map depth
  ((List.range us.length).map (fun i => a.getD i 0 + cs.getD i 0)).foldl max 0

end Paralever.AutoPar
