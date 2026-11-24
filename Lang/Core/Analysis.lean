import Lang.Core.Prog

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
  | .lt a b  => regsOf a ++ regsOf b
  | .eq a b  => regsOf a ++ regsOf b
  | .not a   => regsOf a

/-- The registers a nest body reads. Its induction registers are written inside the thread and a
fork's register writes are discarded at the join, so only the reads are visible to the parent.
-- ref: `docs/loops.md` -/
def regsOfNest : List NestStmt → List Reg
  | []            => []
  | .rd _ _ :: ss => regsOfNest ss
  | .wr _ e :: ss => regsOf e ++ regsOfNest ss
  | .st _ e :: ss => regsOf e ++ regsOfNest ss

/-- The registers a `print` reads. A literal and a whole-buffer item read none; an expression and a
computed subscript read theirs. -- ref: `docs/print.md` -/
def regsOfItems : List PrintItem → List Reg
  | []      => []
  | i :: is =>
      (match i with
       | .text _   => []
       | .exp e    => regsOf e
       | .buf ..   => []
       | .cell ..  => []
       | .at _ _ e => regsOf e) ++ regsOfItems is

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
  | .synchronize     => .empty
  | .print items     => ⟨regsOfItems items, []⟩
  -- a nest forks, so its register writes are discarded too
  | .loop n          => ⟨regsOfNest n.body, []⟩

/-- The threads' register footprints, combined. -/
def regFootprintsOf : List ParProg → Footprint
  | []      => .empty
  | s :: ss => Footprint.union (regFootprint s) (regFootprintsOf ss)

end

/-- Whether a statement is a `synchronize`. Its footprints are empty, so Bernstein alone would
happily group it with anything — this is the case `canPar` and `canParSeg` answer before they look
at a footprint. -/
def isSynchronize : ParProg → Bool
  | .synchronize => true
  | _      => false

/-- Whether a statement may not be grouped with its neighbours: a `synchronize`, or a `print`. A
print is erased from the program and its value read off the sequential run, so a scheduler that
moved a statement across one would change what it prints. Distinct from `isSynchronize`, which
`phases` splits on: `joinPhases` puts a `synchronize` back between phases and could not put a print
back. -- ref: `docs/print.md` § A print is a barrier for the parallelizer -/
def isBarrier : ParProg → Bool
  | .synchronize => true
  | .print _     => true
  | _            => false

/-- **May these two run concurrently?** Bernstein on memory *and* on registers, and never across a
synchronize.

The register clause is not decoration. `t0 := M[1]` and `M[4] := t0 + 1` touch disjoint memory, so
memory-Bernstein alone would group them — but the second reads a register the first writes, and in a
fork it would never see it, because threads get a private copy. Requiring independence on both
footprints is what makes a proposal from `autoPar` an actual rewrite rather than a suggestion. -/
def canPar (a b : ParProg) : Bool :=
  !a.isSynchronize && !b.isSynchronize &&
    indepB (footprintOf a) (footprintOf b) && indepB (regFootprint a) (regFootprint b)

/-- Every ordered pair of statements in a chain that may **not** run together, with the index of
each. This is the dependence report: it says where the sequential order is forced. -/
def dependences (p : ParProg) : List (Nat × Nat) :=
  let ss := (flatten p).zipIdx
  ss.flatMap fun a => ss.filterMap fun b =>
    if a.2 < b.2 && !canPar a.1 b.1 then some (a.2, b.2) else none

/-! ### Register liveness across a fork

A `par` node resets the register file to its pre-fork contents (`execPar`, `Lang/Core/Prog.lean`), so a
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
  | .synchronize         => []
  | .print _             => []
  | .loop _              => []

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
def canParSeg (a b : ParProg) : Bool :=
  !a.isBarrier && !b.isBarrier && indepB (footprintOf a) (footprintOf b)

/-! ### The same cuts, in one pass

`atomsGo` asks `cutOK (pre ++ [s]) ss` at every statement, and `cutOK` walks the whole prefix for
`regFootprintsOf` and the whole suffix for `liveIn`. One pass over `n` statements is therefore `n²`
list traversals, which on a phase of a few thousand statements is where the planner's time goes.

The quantities both depend on are prefix-to-suffix monotone: the prefix's register writes only
grow, and the suffix's live-in set is one backward pass. `atomsFast` carries the first and
precomputes the second, cutting in exactly the same places. `AutoPar.rewrite` keeps `atoms`, which
`AutoPar/Chain.lean` proves `flatten`s back to the chain; this is the greedy route's copy, and
`Test/Lang.lean` gates the two against each other on every example. -/

/-- `liveIn` of every suffix, longest first: the head is `liveIn ss` and the tail is the same for
`ss.tail`. One backward pass. -/
def liveSuffixes : List ParProg → List (List Reg)
  | []      => [[]]
  | s :: ss =>
      let rest := liveSuffixes ss
      ((regFootprint s).reads ++ (rest.headD []).filter (fun r => !(regKills s).contains r)) :: rest

/-- `atomsGo` with the prefix's register writes carried and the suffixes' live-in sets handed in.
`w` is `(regFootprintsOf pre).writes` up to repeats, and `lives` is `liveSuffixes` of what remains,
so `lives.tail.headD []` is the `liveIn post` that `cutOK` asks for. -/
def atomsFastGo : List Reg → List ParProg → List ParProg → List (List Reg) → List (List ParProg)
  | _, acc, [],      _     => if acc.isEmpty then [] else [acc.reverse]
  | w, acc, s :: ss, lives =>
      let w' := (regFootprint s).writes.foldl (fun a r => if a.contains r then a else r :: a) w
      let tl := lives.tail
      if disjointB w' (tl.headD []) then (s :: acc).reverse :: atomsFastGo w' [] ss tl
      else atomsFastGo w' (s :: acc) ss tl

/-- `atoms`, in one pass. Same cuts, same segments. -/
def atomsFast (ss : List ParProg) : List (List ParProg) :=
  atomsFastGo [] [] ss (liveSuffixes ss)

/-! ### The same test, linear

`groupPrefix` asks `canParSeg a s` for every `a` already in the group, so one group of `k` segments
costs `k²` independence tests, and each test is `disjointB`, which is quadratic in the footprints.
On a program whose segments touch many cells — a matrix multiply's inner product reads `2d` of them
— that product is what the planner spends its time on (`docs/autopar.md` § Regions).

Sorting each footprint once and merging turns the inner test linear. The planner's *answer* is
unchanged: these functions decide the same relation on the same inputs, and `wfB` re-checks
whatever grouping comes out either way. -/

/-- A sorted list with its repeats removed. -/
def dedupSorted : List Loc → List Loc
  | []           => []
  | [l]          => [l]
  | l :: l' :: ls => if l == l' then dedupSorted (l' :: ls) else l :: dedupSorted (l' :: ls)

/-- `disjointSorted` with its fuel exposed. A merge shrinks a different argument in each branch, so
without the fuel Lean compiles this by well-founded recursion and marks it `@[irreducible]` — and
then nothing built over the planner reduces, so every `decide` on `autoPar`'s output fails.
-- ref: `docs/autopar.md` § Regions -/
def disjointSortedGo : Nat → List Loc → List Loc → Bool
  | 0,     _,       _       => false
  | _ + 1, [],      _       => true
  | _ + 1, _,       []      => true
  | n + 1, a :: as, b :: bs =>
      if a == b then false
      else if a < b then disjointSortedGo n as (b :: bs)
      else disjointSortedGo n (a :: as) bs

/-- Two sorted lists with no element in common. One merge, where `disjointB` is one product. Each
step drops one cell, so `as.length + bs.length + 1` steps are always enough and the `false` the
fuel runs out on is unreachable — it is the refusing answer either way. -/
def disjointSorted (as bs : List Loc) : Bool :=
  disjointSortedGo (as.length + bs.length + 1) as bs

/-- `Access.indepB` over sorted footprints: Bernstein, with shared reads still allowed. -/
def indepSorted (f₁ f₂ : Footprint) : Bool :=
  disjointSorted f₁.writes f₂.writes
    && disjointSorted f₁.writes f₂.reads
    && disjointSorted f₂.writes f₁.reads

/-- Two sorted lists merged. The `Nat` is fuel, so the recursion is structural on it.

`List.mergeSort` is well-founded and `@[irreducible]`, so a term built over it does not reduce and
every `decide` downstream of `autoPar` fails. -- ref: `docs/autopar.md` § Regions -/
def mergeLocs : Nat → List Loc → List Loc → List Loc
  | 0,     as,      bs      => as ++ bs
  | _ + 1, [],      bs      => bs
  | _ + 1, as,      []      => as
  | n + 1, a :: as, b :: bs =>
      if a ≤ b then a :: mergeLocs n as (b :: bs) else b :: mergeLocs n (a :: as) bs

/-- One bottom-up pass: adjacent runs merged pairwise, halving their number. -/
def mergePass : List (List Loc) → List (List Loc)
  | a :: b :: rs => mergeLocs (a.length + b.length) a b :: mergePass rs
  | rs           => rs

/-- Runs merged down to one. Fuel: a pass halves the count, so a list's length is more than enough
passes. -/
def mergeRuns : Nat → List (List Loc) → List Loc
  | _,     []  => []
  | _,     [r] => r
  | 0,     rs  => rs.flatten
  | n + 1, rs  => mergeRuns n (mergePass rs)

/-- A sorted list of the same cells. Bottom-up merge sort, so the cost is the one the linear
independence test was bought with. -/
def sortLocs (ls : List Loc) : List Loc := mergeRuns ls.length (ls.map ([·]))

/-- A statement's footprint, sorted and deduplicated, ready to be tested many times. -/
def sortedFootprint (p : ParProg) : Footprint :=
  let f := footprintOf p
  ⟨dedupSorted (sortLocs f.reads), dedupSorted (sortLocs f.writes)⟩

-- the two hand-rolled functions against the library ones they stand in for
#guard ((List.range 40).all fun k =>
  let xs := (List.range k).map (fun i => (i * 37 + 11) % 23)
  sortLocs xs == xs.mergeSort (· ≤ ·))
#guard ((List.range 14).all fun i => (List.range 14).all fun j =>
  let as := sortLocs ((List.range i).map (fun k => (k * 7 + i) % 13))
  let bs := sortLocs ((List.range j).map (fun k => (k * 5 + j) % 13))
  disjointSorted as bs == disjointB as bs)

/-- `canParSeg` on segments whose footprints have already been taken. -/
def canParSegFp (a b : ParProg × Footprint) : Bool :=
  !a.1.isBarrier && !b.1.isBarrier && indepSorted a.2 b.2

/-- `groupPrefix` over segments carrying their footprints. -/
def groupPrefixFp : List (ParProg × Footprint) → List (ParProg × Footprint) →
    List (ParProg × Footprint)
  | acc, []      => acc.reverse
  | acc, s :: ss =>
      if acc.all (fun a => canParSegFp a s) then groupPrefixFp (s :: acc) ss else acc.reverse

/-- `groups` over segments carrying their footprints. -/
def groupsFp : Nat → List (ParProg × Footprint) → List (List (ParProg × Footprint))
  | 0,        _  => []
  | _,        [] => []
  | fuel + 1, ss =>
      let g := groupPrefixFp [] ss
      let k := g.length
      if k = 0 then [ss] else g :: groupsFp fuel (ss.drop k)

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

/-! ### Phases

A `synchronize` ends a phase. The parallelizer plans each phase on its own and joins them back with
the barriers still in place, so they survive the rewrite and say in the output what they said in the
input. -- ref: `docs/autopar.md` § Synchronization -/

/-- The statements before the first `synchronize`, and the phases after it. -/
def phasesGo : List ParProg → List ParProg × List (List ParProg)
  | []      => ([], [])
  | s :: ss =>
      if s.isSynchronize then ([], (phasesGo ss).1 :: (phasesGo ss).2)
      else (s :: (phasesGo ss).1, (phasesGo ss).2)

/-- The chain's phases, in order, split at every `synchronize`. Always at least one, so a chain with
no barrier in it is one phase and the analysis below is unchanged for it. -/
def phases (us : List ParProg) : List (List ParProg) := (phasesGo us).1 :: (phasesGo us).2

/-- The phases back into one chain, `synchronize` between them. -/
def joinPhases : List (List ParProg) → List ParProg
  | []        => []
  | [ph]      => ph
  | ph :: phs => ph ++ .synchronize :: joinPhases phs

/-- **Splitting into phases loses nothing.** So the barriers in an autoparallelized program are
exactly the ones that were written, and `planPhase` may be applied phase by phase. -/
theorem joinPhases_phases (us : List ParProg) : joinPhases (phases us) = us := by
  induction us with
  | nil => rfl
  | cons s ss ih =>
      simp only [phases] at ih ⊢
      cases hg : phasesGo ss with
      | mk ph phs =>
      simp only [hg] at ih
      by_cases h : s.isSynchronize = true
      · have hs : s = .synchronize := by cases s <;> simp_all [isSynchronize]
        subst hs
        simp only [phasesGo, isSynchronize, hg, ite_true]
        simp only [joinPhases, List.nil_append]
        rw [ih]
      · simp only [Bool.not_eq_true] at h
        simp only [phasesGo, h, Bool.false_eq_true, ite_false, hg]
        cases phs with
        | nil => simp only [joinPhases] at ih ⊢; rw [ih]
        | cons q qs =>
            simp only [joinPhases] at ih ⊢
            rw [List.cons_append, ih]

mutual

/-- Whether the statement contains no `synchronize` at all. -/
def synchronizeFree : ParProg → Bool
  | .synchronize        => false
  | .seq a b      => synchronizeFree a && synchronizeFree b
  | .par ss       => synchronizeFreeAll ss
  | .label _ s    => synchronizeFree s
  | .ifElse _ t e => synchronizeFree t && synchronizeFree e
  | _             => true

def synchronizeFreeAll : List ParProg → Bool
  | []      => true
  | s :: ss => synchronizeFree s && synchronizeFreeAll ss

end

mutual

/-- Whether the statement contains no barrier at all — no `synchronize` and no `print`. The gate on
the *proved* rewrite route: `emit` wraps every stage in a `par`, so either would end up inside a
thread, where neither has a meaning. -- ref: `docs/print.md`, `docs/autopar.md` § Synchronization -/
def barrierFree : ParProg → Bool
  | .synchronize  => false
  | .print _      => false
  | .seq a b      => barrierFree a && barrierFree b
  | .par ss       => barrierFreeAll ss
  | .label _ s    => barrierFree s
  | .ifElse _ t e => barrierFree t && barrierFree e
  | _             => true

def barrierFreeAll : List ParProg → Bool
  | []      => true
  | s :: ss => barrierFree s && barrierFreeAll ss

end

/-- Whether no barrier — no `synchronize`, no `print` — sits inside a `parallel` thread. A
`synchronize` there is refused by `Lang.Compile.Lower` (`P106`): between phases it constrains the
schedule, but between siblings `ParM` has no synchronisation node to give it a meaning. A `print`
there is *written* freely, so what this gates is the parallelizer rather than the reader — moving a
print into a thread changes which heap it sees, so the rewrite would preserve the program's heap and
still change what it says. -- ref: `docs/print.md` § In a thread -/
def noBarrierInThread : ParProg → Bool
  | .par ss        => barrierFreeAll ss
  | .seq a b       => noBarrierInThread a && noBarrierInThread b
  | .label _ s     => noBarrierInThread s
  | .ifElse _ t e  => noBarrierInThread t && noBarrierInThread e
  | _              => true

/-- Split `xs` into at most `width` contiguous chunks of near-equal length. Contiguous, so each
chunk is the statements it holds in their original order and `block` of it is the same program.
At or below the budget every chunk is a singleton, which is the unbounded plan unchanged. -/
def chunkInto {α : Type} (width : Nat) (xs : List α) : List (List α) :=
  let w := max 1 width
  let n := xs.length
  if n ≤ w then xs.map ([·])
  else
    let per := (n + w - 1) / w
    (List.range w).filterMap fun i =>
      let c := (xs.drop (i * per)).take per
      if c.isEmpty then none else some c

/-- The thread budget `autoPar` plans to when the caller does not say. A **default**, not a limit:
`autoParWith` takes any width, and the command line's `--width` passes one through.

Unbounded was the wrong default, and the measurement says so: on a sequential `n × n` matmul the
unbounded plan proposes one thread per output cell — 400 threads at `n = 20` — and that shape runs
*slower* than a handful of fat ones, because each thread pays spawn and join costs for a few
instructions of work. The join is the sharper of the two: `Compile/ExecArr`'s is
O(threads × cells), so a thread per cell makes it quadratic in the heap.

Eight is a placeholder for a machine-aware number, not a tuned one. -- ref: `docs/autopar.md` -/
def defaultWidth : Nat := 8

/-! ### What a group is worth

A fork costs something whether or not the work inside it is worth forking, so a planner that forks
every independent group loses on a program made of many small phases. Measured on
`Bench/Chaos.lean`'s thousand-line program: its sorting networks contribute most of the forks and
almost none of the work, and at `n = 10` the plan forks 2,256 times for 59,472 instructions — 26
instructions a fork.

`weight` is what a group is costed by, and `grain` is the least it must carry before it is forked.
The gate lives in the untrusted analysis, so like the thread budget it cannot make an accepted
program wrong: `wfB` re-checks whatever comes out. -/

mutual

/-- Memory operations and register assignments in a statement. Static, so a branch counts its larger
arm and a rolled nest its whole iteration space — a bound rather than a count, which is the safe
direction here: over-counting can only propose a fork that was not worth it, never refuse one that
was. -/
def weight : ParProg → Nat
  | .load _ _      => 1
  | .store _ _     => 1
  | .set _ _       => 1
  | .loadAt _ _ _  => 1
  | .storeAt _ _ _ => 1
  | .seq a b       => weight a + weight b
  | .par cs        => weightAll cs
  | .label _ b     => weight b
  | .ifElse _ t e  => 1 + max (weight t) (weight e)
  | .loop nst      => (nst.sizes.foldl (· * ·) 1) * nst.body.length
  | _              => 0

def weightAll : List ParProg → Nat
  | []      => 0
  | s :: ss => weight s + weightAll ss

end

/-- The grain `autoPar` plans to when the caller does not say. **Zero — no gate**, which is the
behaviour this pass has always had, so that nothing already measured or published moves. What the
right number is, is a measurement and not a guess; `Bench/Chaos.lean` sweeps it. -/
def defaultGrain : Nat := 0

/-- **The proposal, for one phase.** The groups a greedy scheduler would fork, each group striped
into at most `width` threads: a singleton run stays a plain statement rather than a one-thread fork,
and so does a group carrying less than `grain` work.

The unit scheduled is the register-closed segment (`atoms`), not the statement: a load and the store
that consumes its register are one segment and are never split across a fork. -/
def planPhaseAt (width grain : Nat) (ss : List ParProg) : List ParProg :=
  let ats := ((atomsFast ss).map block).map fun a => (a, sortedFootprint a)
  (groupsFp (ats.length + 1) ats).map fun g => match g.map Prod.fst with
    | [s] => s
    | g   => if weightAll g < grain then block g else .par ((chunkInto width g).map block)

/-- `planPhaseAt` with no grain gate. -/
def planPhase (width : Nat) (ss : List ParProg) : List ParProg := planPhaseAt width defaultGrain ss

/-- **The proposal, at a stated thread budget and grain.** Each phase planned on its own, the
barriers kept. -/
def autoParTuned (width grain : Nat) (p : ParProg) : ParProg :=
  block (joinPhases ((phases (flatten p)).map (planPhaseAt width grain)))

/-- **The proposal, at a stated thread budget.** Each phase planned on its own, the barriers kept. -/
def autoParWith (width : Nat) (p : ParProg) : ParProg := autoParTuned width defaultGrain p

/-- **Plan inside the named regions only**, leaving everything outside one exactly as written.

A long program is mostly not worth parallelizing: its branches, its serial folds and its bookkeeping
carry no threads, and a planner that looks at them anyway pays for every group it forks and for the
search that found it. A region says where to look. It is a `label`, which both interpreters ignore,
so marking one changes no meaning and cannot change an answer — it changes only which part of the
program the *analysis* reads.

What the gate still is: `wfB` on the result. A region is a hint about where threads might be, never
a promise that they are there, and a region whose statements are not independent is refused exactly
as the same statements would be outside one. -- ref: `docs/autopar.md` § Regions -/
def autoParIn (width grain : Nat) (keep : String → Bool) : ParProg → ParProg
  | .label nm s =>
      .label nm (if keep nm then autoParTuned width grain s else autoParIn width grain keep s)
  | .seq a b    => .seq (autoParIn width grain keep a) (autoParIn width grain keep b)
  | p           => p

/-- `autoParIn` at the default budget, over every region the program names. -/
def autoParRegions (p : ParProg) : ParProg := autoParIn defaultWidth defaultGrain (fun _ => true) p

/-- The names of the regions a program marks, outermost first. -/
def regionNames : ParProg → List String
  | .label nm s => nm :: regionNames s
  | .seq a b    => regionNames a ++ regionNames b
  | _           => []

/-- **The proposal.** `autoParWith` at `defaultWidth`.

Untrusted either way: `wfB` re-checks whatever comes out, and `par_block_heap` is a lemma about any
`.par g` against `block g`, not about the grouping chosen here. So the budget is a tuning knob and
cannot make an accepted program wrong. -/
def autoPar (p : ParProg) : ParProg := autoParWith defaultWidth p

/-! ### The analysis, evaluated

`flatten` cuts a `;`-chain into statements, `atoms` regroups those into register-closed segments,
`dependences` says which pairs may not be siblings, and `autoPar` is the proposal. Written in raw
constructors because `paralever { … }` is defined downstream of this file. -/

section Demo

/-- `[l] := n` -/
private def wr (l : Loc) (n : Int) : ParProg := .store l (.lit n)
/-- `%r := [l]` -/
private def rd (r : Reg) (l : Loc) : ParProg := .load r l
/-- `[l] := %r * %r` -/
private def sq (l : Loc) (r : Reg) : ParProg := .store l (.mul (.reg r) (.reg r))

/-- `[0] := 3; [1] := 4; %0 := [0]; [2] := %0*%0; %1 := [1]; [3] := %1*%1` -/
private def chain : ParProg := block [wr 0 3, wr 1 4, rd 0 0, sq 2 0, rd 1 1, sq 3 1]

-- six statements on the page …
#guard (flatten chain).length == 6
-- … but four scheduling units: a load and the store consuming its register are never split
#guard (atoms (flatten chain)).map (fun seg => seg.length) == [1, 1, 2, 2]

-- the four ordered pairs that may not be siblings. `(0,2)` and `(1,4)` are memory: a cell written
-- then read. `(2,3)` and `(4,5)` are *registers*: statement 3 reads the register statement 2
-- wrote, and in a fork it would get a private copy and read a stale value — which is why `canPar`
-- tests Bernstein on the register footprint too
#guard dependences chain == [(0, 2), (1, 4), (2, 3), (4, 5)]

-- the proposal passes the proved check, which is the whole architecture: analysis proposes, `wfB`
-- accepts or rejects
#guard ParProg.wfB (autoPar chain)

/-- `%0 := [0]; [1] := %0+1; %1 := [1]; [2] := %1+1` — a loop-carried dependence. -/
private def carried : ParProg :=
  block [rd 0 0, .store 1 (.add (.reg 0) (.lit 1)), rd 1 1, .store 2 (.add (.reg 1) (.lit 1))]

-- every statement depends on the one before it, so there is no proposal to make
#guard (atoms (flatten carried)).map (fun seg => seg.length) == [2, 2]
#guard dependences carried == [(0, 1), (1, 2), (2, 3)]

end Demo

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
