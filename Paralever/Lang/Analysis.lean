import Paralever.Lang.Core

/-! # Finding the parallelism

A `ParProg` carries its own footprint, so "may these two statements run together?" is a `Bool`.
The analysis is **untrusted** — it proposes — and `wfB` is the proved check that accepts or rejects
the proposal, the architecture of `Search/RaceSearch.lean`.

There are two routes to a forked program, and this file is the first. `autoPar` below proposes one
and `wfB` is `decide`d on the result, per program. `Paralever/AutoPar/` is the second: it builds on
this file's `flatten`, `atoms`, `canParSeg` and `regFootprint`, and its rewrite is *proved* to
preserve the heap for every program — at the cost of refusing more. `docs/autopar.md § The two
routes` has the comparison, and `Test/AutoPar.lean` pins it. -/

namespace Paralever.Lang
open Paralever

namespace ParProg

/-! ## Detecting parallelism

A `ParProg` carries its own footprint, so "may these two statements run together?" is a `Bool`:
flatten a `;`-chain, compute each statement's footprint, test Bernstein on every pair.

`Search/RaceSearch.lean`'s architecture — the analysis is **untrusted** and `wfB` is the proved
check — which is why `autoPar` is allowed to be greedy and approximate. -/

/-- The statements of a `;`-chain, in order. A `parallel` block is one statement; this does not
descend into it. -/
def flatten : ParProg → List ParProg
  | .seq a b => flatten a ++ flatten b
  | s        => [s]

/-- The region with this name, if the program has one. Extraction, so a named region can be stated
about on its own. -/
def findLabel (nm : String) : ParProg → Option ParProg
  | .label nm' s => if nm' = nm then some s else findLabel nm s
  | .seq a b     => (findLabel nm a).orElse (fun _ => findLabel nm b)
  | _            => none

/-- The registers an expression reads. -/
def regsOf : AExp → List Reg
  | .lit _   => []
  | .reg r   => [r]
  | .add a b => regsOf a ++ regsOf b
  | .sub a b => regsOf a ++ regsOf b
  | .mul a b => regsOf a ++ regsOf b
  | .min a b => regsOf a ++ regsOf b
  | .max a b => regsOf a ++ regsOf b
  | .div a b => regsOf a ++ regsOf b

mutual

/-- A statement's register footprint, the exact analogue of `footprintOf` for the register file.

A `parallel` block writes no register the parent can see — threads get a copy and it is discarded
(§Lowering) — but it does *read* the parent's registers at the fork, so its reads are its threads'.
That asymmetry is the whole reason a fork isolates register effects. -/
def regFootprint : ParProg → Footprint
  | .load r _  => ⟨[], [r]⟩
  | .store _ e => ⟨regsOf e, []⟩
  | .set r e   => ⟨regsOf e, [r]⟩
  | .seq a b   => Footprint.union (regFootprint a) (regFootprint b)
  | .par ss    => ⟨(regFootprintsOf ss).reads, []⟩
  | .label _ s => regFootprint s
  | .loadAt r _ e  => ⟨regsOf e, [r]⟩
  | .storeAt _ e v => ⟨regsOf e ++ regsOf v, []⟩
  | .ifElse c t e  =>
      Footprint.union ⟨regsOf c, []⟩ (Footprint.union (regFootprint t) (regFootprint e))

/-- The threads' register footprints, combined. -/
def regFootprintsOf : List ParProg → Footprint
  | []      => .empty
  | s :: ss => Footprint.union (regFootprint s) (regFootprintsOf ss)

end

/-- **May these two run concurrently?** Bernstein on memory *and* on registers.

The register clause is not decoration. `t0 := M[1]` and `M[4] := t0 + 1` touch disjoint memory, so
memory-Bernstein alone would group them — but the second reads a register the first writes, and in a
fork it would never see it, because threads get a private copy. Requiring independence on both
footprints is what makes a proposal from `autoPar` an actual rewrite rather than a suggestion. -/
def canPar (a b : ParProg) : Bool :=
  indepB (footprintOf a) (footprintOf b) && indepB (regFootprint a) (regFootprint b)

/-- Every ordered pair of statements in a chain that may **not** run together, with the index of
each. This is the dependence report: it says where the sequential order is forced. -/
def dependences (p : ParProg) : List (Nat × Nat) :=
  let ss := (flatten p).zipIdx
  ss.flatMap fun a => ss.filterMap fun b =>
    if a.2 < b.2 && !canPar a.1 b.1 then some (a.2, b.2) else none

/-! ### Register liveness across a fork

A `par` node resets the register file to its pre-fork contents (`execPar`, `Lang/Core.lean`), so a
register written on one side of a fork boundary and read on the other reads a stale value. That is
not a race — both readings agree — so `wfB` cannot see it, and a scheduler that ignores it silently
changes the program's answer. The boundary must therefore be placed where no register is live
across it. -/

/-- The registers a statement is **certain** to write. Not `regFootprint`'s write set, which is a
*may*-write: a conditional's is the union of its branches, and only one branch runs. Liveness must
kill on must-writes or it under-approximates what is live, which is unsound — and the conditional is
exactly where the two differ. A `par` node kills nothing: the parent's file is restored at the
join. -/
def regKills : ParProg → List Reg
  | .load r _      => [r]
  | .store _ _     => []
  | .set r _       => [r]
  | .seq a b       => regKills a ++ regKills b
  | .par _         => []
  | .label _ s     => regKills s
  | .loadAt r _ _  => [r]
  | .storeAt _ _ _ => []
  | .ifElse _ t e  => (regKills t).filter (fun r => (regKills e).contains r)

/-- Registers live at the entry of a chain: read before being certainly overwritten. Backward
liveness — without the kill a reused register like `%0` would appear live across the whole program
and no boundary would ever be legal. -/
def liveIn : List ParProg → List Reg
  | []      => []
  | s :: ss =>
      (regFootprint s).reads ++ (liveIn ss).filter (fun r => !(regKills s).contains r)

/-- Whether a fork boundary may be placed after `pre`: no register `pre` writes is still live.
Every stage sees the *same* pre-fork file, so the condition is about the whole prefix, not the
adjacent statement. -/
def cutOK (pre post : List ParProg) : Bool :=
  disjointB (regFootprintsOf pre).writes (liveIn post)

/-- Split a chain at every legal cut, finest first. Each segment is register-closed, so making it a
thread loses nothing; the segments, not the statements, are what a scheduler may move. -/
def atomsGo : List ParProg → List ParProg → List ParProg → List (List ParProg)
  | _,   acc, []      => if acc.isEmpty then [] else [acc.reverse]
  | pre, acc, s :: ss =>
      let pre' := pre ++ [s]
      let acc' := s :: acc
      if cutOK pre' ss then acc'.reverse :: atomsGo pre' [] ss
      else atomsGo pre' acc' ss

/-- The chain's register-closed segments, in order. -/
def atoms (ss : List ParProg) : List (List ParProg) := atomsGo [] [] ss

/-- **May these two segments be siblings in a fork?** Bernstein on memory, and nothing about
registers.

The register clause of `canPar` is deliberately absent. Threads get a *private* copy of the
register file, so two siblings may clobber the same register freely — and they routinely do, since
a reused `%0` is the normal way to write a loop body. What registers constrain is not which
statements may be siblings but *where a fork boundary may be placed*, and that is `cutOK`: a
property of the boundary, not of a pair. `atoms` has already enforced it by the time this is
asked. -/
def canParSeg (a b : ParProg) : Bool := indepB (footprintOf a) (footprintOf b)

/-- The longest prefix of `ss` that is pairwise independent — the next group a greedy scheduler
would fork. -/
def groupPrefix : List ParProg → List ParProg → List ParProg
  | acc, []      => acc.reverse
  | acc, s :: ss =>
      if acc.all (fun a => canParSeg a s) then groupPrefix (s :: acc) ss else acc.reverse

/-- Greedily partition a chain into maximal pairwise-independent runs. Approximate on purpose: a
better grouping may exist, and `wfB` checks whichever one is produced. -/
def groups : Nat → List ParProg → List (List ParProg)
  | 0,        _  => []
  | _,        [] => []
  | fuel + 1, ss =>
      let g := groupPrefix [] ss
      let k := g.length
      if k = 0 then [ss] else g :: groups fuel (ss.drop k)

/-- **The proposal.** Rewrite a `;`-chain as a sequence of `parallel` blocks, one per independent
run. A singleton run stays a plain statement rather than a one-thread fork.

The unit scheduled is the register-closed segment (`atoms`), not the statement: a load and the store
that consumes its register are one segment and are never split across a fork. -/
def autoPar (p : ParProg) : ParProg :=
  let ats := (atoms (flatten p)).map block
  block ((groups (ats.length + 1) ats).map fun g => match g with
    | [s] => s
    | g   => .par g)

/-! ### What the proposal is, and is not

`canPar` requires independence on the *register* footprint too, which stops the one rewrite that
would otherwise be wrong: registers are thread-private, so a statement forked away from the one that
set its register would read a stale copy.

Two non-claims. The grouping is **greedy** — `groups` takes the longest independent prefix rather
than searching — and `wfB (autoPar p) = true` is about the *proposal*, per program; that `autoPar`
always preserves `p`'s outcomes would need Bernstein at the statement level, not proved here.
`AutoPar.rewrite_sound` is that missing statement, for a different scheduler.

What this route still has over the proved one: `atoms` kills a register by **liveness**, so a chain
reusing `%0` forks here, where `AutoPar.rewriteOk`'s `noRegFlow` — a condition on raw read sets —
declines it. -- ref: docs/autopar.md § The two routes -/
end ParProg

end Paralever.Lang
