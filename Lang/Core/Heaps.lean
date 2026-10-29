import Lang.Core.Layout
import Lang.Core.Prog
import Paralever.Search.Explain

/-! # The general-heap search — a race at a heap the file does not declare

`wfB` answers for every heap and `raceSites` answers for one. Between them sits the question a
reader actually asks of a program with a computed address: *is there any heap at which these threads
collide?* This file searches for one, by probing the cells whose loaded values become indices.

The search is bounded, so finding nothing is `unknown` and never `proved` — the complete answer for
every heap is `wfB`, and this is what runs when `wfB` has refused. Finding something is decisive:
`raceSites` is exact at the heap it is given (`raceSites_nil_iff`), so a hit refutes
`∀ σ, ParSeqEq …` outright. -- ref: `docs/general-heap.md` -/

namespace Paralever.Lang
open Paralever

/-- A heap named by how it differs from the one the file declares, so a counterexample prints as the
few cells a reader has to change rather than as a function. -/
structure Heap where
  edits : List (Loc × Int)
  deriving Repr, BEq, Inhabited

namespace Heap

/-- The heap the file's `buf` initializers describe. -/
def declared : Heap := ⟨[]⟩

def apply (h : Heap) (σ : State) : State :=
  h.edits.foldl (fun τ (l, n) => τ.update l (.int n)) σ

end Heap

namespace ParProg

/-! ## What to probe

Only a value that *becomes* an index can move an access, and in this language a value enters a
register through `load`. A `loadAt`'s own cell is computed, so probing it would mean guessing a
second index; those cells are left out rather than approximated. -/

mutual

/-- The cells a `load` names, in program order. -/
def loadCells : ParProg → List Loc
  | .load _ l      => [l]
  | .store _ _     => []
  | .set _ _       => []
  | .seq a b       => loadCells a ++ loadCells b
  | .par ss        => loadCellsAll ss
  | .label _ s     => loadCells s
  | .loadAt _ _ _  => []
  | .storeAt _ _ _ => []
  | .ifElse _ t e  => loadCells t ++ loadCells e
  | .synchronize   => []
  | .print _       => []
  -- a nest's reads are at affine subscripts of a point, so probing one would mean guessing the
  -- point; left out rather than approximated, exactly as a `loadAt`'s own cell is
  | .loop _        => []

def loadCellsAll : List ParProg → List Loc
  | []      => []
  | s :: ss => loadCells s ++ loadCellsAll ss

end

/-- The cells to probe, without repeats. -/
def probeCells (s : ParProg) : List Loc := nubLocs (loadCells s)

end ParProg

/-! ## Why `wfB` refused

`wfB` compares footprints read off the syntax, and a computed address contributes every cell of its
buffer. When it refuses, the pair of threads it refused over is the reason the general verdict is not
`proved`, and naming those cells is what turns "inconclusive" into a statement a reader can act on.
-/

mutual

/-- The first `parallel` block whose *syntactic* footprints overlap, with the cells that witness it.
Pairwise, exactly as `indepAllB` is: each thread against every later one. -/
def refusedAt : ParProg → Option RaceSite
  | .seq a b      => (refusedAt a).or (refusedAt b)
  | .par ss       => (synSites ss).head?.or (refusedAtAll ss)
  | .label _ s    => refusedAt s
  | .ifElse _ t e => (refusedAt t).or (refusedAt e)
  | _             => none

def refusedAtAll : List ParProg → Option RaceSite
  | []      => none
  | s :: ss => (refusedAt s).or (refusedAtAll ss)

/-- Every pair of threads of one block that fails Bernstein on the syntax. -/
def synSites : List ParProg → List RaceSite
  | []      => []
  | s :: ss =>
      ss.flatMap (fun t => siteOf (ParProg.footprintOf s) (ParProg.footprintOf t))
        ++ synSites ss

end

mutual

/-- Whether the program has a computed address. -/
def hasComputed : ParProg → Bool
  | .loadAt _ _ _  => true
  | .storeAt _ _ _ => true
  | .seq a b       => hasComputed a || hasComputed b
  | .par ss        => hasComputedAll ss
  | .label _ s     => hasComputed s
  | .ifElse _ t e  => hasComputed t || hasComputed e
  | _              => false

def hasComputedAll : List ParProg → Bool
  | []      => false
  | s :: ss => hasComputed s || hasComputedAll ss

/-- Whether the program has a run-time branch. -/
def hasBranch : ParProg → Bool
  | .ifElse _ _ _ => true
  | .seq a b      => hasBranch a || hasBranch b
  | .par ss       => hasBranchAll ss
  | .label _ s    => hasBranch s
  | _             => false

def hasBranchAll : List ParProg → Bool
  | []      => false
  | s :: ss => hasBranch s || hasBranchAll ss

end

/-- Why `footprintOf` is a bound and not the footprint. These are the only two constructors that
widen it, and `footprintExact` is their conjunction read as one `Bool` — this says *which*, because
that is what a reader needs to know to narrow it. -- ref: `docs/block-ir.md` -/
def ParProg.widenedBy (s : ParProg) : List String :=
  (if hasComputed s then
     ["a computed address contributes every cell of its buffer"] else [])
    ++ (if hasBranch s then
          ["a branch contributes both arms although only one runs"] else [])

/-- The index values worth trying. `ArrRef.addr a i = a.base + i.toNat % max a.len 1` aliases two
ways, and these are the witnesses to both: the `Int.toNat` clamp sends every negative index to cell
`0`, and the `% max len 1` wrap sends `n` back to `0` and `n + 1` to `1`. Values `0` and `1` are in
range for every non-empty buffer, so a collision between an in-range and a wrapped index is reached
too. -/
def probeValues (L : Layout) : List Int :=
  let ns := L.bufs.flatMap fun p =>
    let n : Int := p.toBuf.size
    [n - 1, n, n + 1]
  ((-1 : Int) :: 0 :: 1 :: ns).foldl
    (fun acc v => if acc.contains v then acc else acc ++ [v]) []

/-- Unordered pairs of distinct elements. -/
private def pairsOf {α : Type} : List α → List (α × α)
  | []      => []
  | x :: xs => xs.map (fun y => (x, y)) ++ pairsOf xs

/-- The heaps to try, nearest the declared one first: the declared heap, then one cell changed, then
every cell changed to one value, then two cells changed. The uniform pass is what catches a stride
whose threads alias only when *both* indices clamp — `A[2*%p]` against `A[2*%q+1]` needs `%p` and
`%q` negative together, which no single-cell change reaches. -/
def probeHeaps (budget : Nat) (cells : List Loc) (vals : List Int) : List Heap :=
  let one := cells.flatMap fun l => vals.map fun v => Heap.mk [(l, v)]
  let uni := vals.map fun v => Heap.mk (cells.map fun l => (l, v))
  let two := (pairsOf cells).flatMap fun (l, m) =>
    vals.flatMap fun v => vals.map fun w => Heap.mk [(l, v), (m, w)]
  (Heap.declared :: (one ++ uni ++ two)).take budget

/-- How many heaps a search looks at before giving up. The count a report prints is the number
actually tried, which is smaller whenever the shape generates fewer. -/
def probeBudget : Nat := 512

/-- What is known about a program at a class of heaps. `unknown` carries the size of the search that
came back empty, because "we looked at 89 heaps" is the reason the verdict is not `proved`. -/
inductive HeapVerdict where
  /-- `par = seq` under every schedule, at every heap in the class. -/
  | proved   : HeapVerdict
  /-- This heap has two threads touching one cell. -/
  | race     : Heap → RaceSite → HeapVerdict
  /-- Nothing found, in a search of this many heaps. -/
  | unknown  : Nat → HeapVerdict
  deriving Repr, Inhabited

/-- **At the heap the file declares.** Exact, by `raceSites_nil_iff`: `proved` is a Lean proof of
`ParSeqEq` at this heap and `race` is a schedule that reaches `wrong`. Never `unknown`. -/
def ParProg.verdictHere (L : Layout) (s : ParProg) : HeapVerdict :=
  match raceSites (ParProg.execPar s (fun _ => 0)) L.state with
  | []     => .proved
  | st :: _ => .race Heap.declared st

/-- **At every heap.** `wfB` decides it outright; otherwise the bounded search looks for a
counterexample, and `unknown` is the honest answer when it finds none. -/
def ParProg.verdictAnywhere (L : Layout) (s : ParProg) (budget : Nat := probeBudget) :
    HeapVerdict :=
  if ParProg.wfB s then .proved
  else
    let hs := probeHeaps budget (ParProg.probeCells s) (probeValues L)
    let hit := hs.findSome? fun h =>
      match raceSites (ParProg.execPar s (fun _ => 0)) (h.apply L.state) with
      | []      => none
      | st :: _ => some (h, st)
    match hit with
    | some (h, st) => .race h st
    | none         => .unknown hs.length

end Paralever.Lang
