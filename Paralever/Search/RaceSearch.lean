import Paralever.Theory.Sequentialize

/-! # Searching for the counterexample

`WellFormed` says a program has no races. When it *fails*, this module finds the execution that
proves it: a schedule reaching `Conf.wrong`, or two schedules reaching different outcomes.

Two phases, after Sen's RaceFuzzer (PLDI'08). Phase 1 is a cheap imprecise scan proposing candidate
racing pairs — here that scan is exactly Bernstein, so `raceSites` is complete for the obligation
(`raceSites_nil_iff`). Phase 2 searches schedules to realize one of them.

The search itself is untrusted: `findWrong` may return anything or give up. What it returns is a
`Schedule`, and `follow_sound` turns any schedule into a `Reaches` proof — so a found counterexample
is checked, never believed. Rationale: `docs/semantics.md`. -/

namespace Paralever

/-! ### Schedules

A schedule says which successor to take at each step. `step` returns a list, so an index into that
list names a branch; a `Schedule` is a path through the nondeterminism. -/

/-- A path through `step`'s nondeterminism: at each step, which successor to take. -/
abbrev Schedule := List Nat

/-- Follow a schedule, or fail if an index runs off the end of the successor list. -/
def follow {τ : Type} : Conf τ → Schedule → Option (Conf τ)
  | c, []      => some c
  | c, i :: s  => match (stepC c)[i]? with
                  | some c' => follow c' s
                  | none    => none

/-- **A followed schedule is a run.** This is what makes the search trustworthy: whatever produced
the schedule, following it successfully yields a `Reaches` proof. -/
theorem follow_sound {τ : Type} :
    ∀ (s : Schedule) (c c' : Conf τ), follow c s = some c' → Reaches c c'
  | [],     c, c', h => by simp only [follow, Option.some.injEq] at h; exact h ▸ Reaches.refl
  | i :: s, c, c', h => by
      simp only [follow] at h
      match hg : (stepC c)[i]? with
      | none    => rw [hg] at h; simp at h
      | some c'' =>
          rw [hg] at h
          exact (Reaches.single (List.mem_of_getElem? hg)).trans (follow_sound s c'' c' h)

/-! ### Reading a step back

`step` on `.par cs k` concatenates the children's successors in order, so an index into that list
determines which child moved. `attribution` inverts the concatenation. -/

/-- The heap of a configuration; `none` at `wrong`, which has none. -/
def Conf.heap? {τ : Type} : Conf τ → Option State
  | .run _ σ => some σ
  | .wrong   => none

/-! `Label` records a location and read/write and deliberately drops the value, because a race does
not depend on it (`Core/Semantics.lean`). A *report* does want it: `write [9]` leaves the reader
guessing where `write [9] ← 2` does not. These two mirror `nextAccs`/`nextAccsChilds` exactly — same
recursion, same grouping — and keep the value a write would have stored. -/

mutual

/-- The actions `p`'s live threads are each about to perform, with a write's value. -/
def pendingOf {α : Type} : ParM α → List (Label × Option Val)
  | .pure _      => []
  | .read l _    => [(.read l, none)]
  | .write l v _ => [(.write l, some v)]
  | .par cs _    => (pendingChilds cs).flatten

/-- One list per child, so the report can range over the pairs the check rejected. -/
def pendingChilds {αs : List Type} : Childs ParM αs → List (List (Label × Option Val))
  | .nil       => []
  | .cons p ps => pendingOf p :: pendingChilds ps

end

/-- What one successor index resolves to: the thread that moved, the memory action it performs,
and — when the step is a race detection rather than a move — the pending actions of every child of
the forking node, which is exactly what `racingAll` rejected. -/
structure Attrib where
  path   : List Nat
  action : Option Label
  abort  : Option (List (List (Label × Option Val)))

mutual

/-- Which thread the `i`-th successor of `step p σ` belongs to, as a path of child indices, together
with what that step does. A step with no action and no abort is a `par` join. The forking node may
be nested, so `path` points at the fork that aborted, not only at the root. -/
def attribution {α : Type} : ParM α → State → Nat → Attrib
  | .pure _,      _, _ => ⟨[], none, none⟩
  | .read l _,    _, _ => ⟨[], some (.read l), none⟩
  | .write l _ _, _, _ => ⟨[], some (.write l), none⟩
  | .par cs _,    σ, i =>
      if racingAll (nextAccsChilds cs) then ⟨[], none, some (pendingChilds cs)⟩
      else match allPure cs with
        | some _ => ⟨[], none, none⟩
        | none   => attributionChilds cs σ i 0

/-- Walk the children in the order `stepChilds` lays them out, subtracting each child's width. -/
def attributionChilds {αs : List Type} :
    Childs ParM αs → State → Nat → Nat → Attrib
  | .nil,       _, _, _ => ⟨[], none, none⟩
  | .cons p ps, σ, i, j =>
      let w := (step p σ).length
      if i < w then
        let r := attribution p σ i
        ⟨j :: r.path, r.action, r.abort⟩
      else attributionChilds ps σ (i - w) (j + 1)

end

/-! ### Phase 1 — where the races could be

A walk of the tree collecting every `par` node whose Bernstein check fails, with the locations that
witness the failure. Cheap, and complete for the obligation: the list is empty exactly when the
program is well-formed. -/

/-- The locations witnessing a Bernstein violation between two footprints. -/
def Footprint.conflictsWith (a b : Footprint) : List Loc :=
  a.writes.filter (fun l => b.writes.contains l || b.reads.contains l) ++
    b.writes.filter (fun l => a.reads.contains l)

/-- One `par` node whose branches are not independent. -/
structure RaceSite where
  left      : Footprint
  right     : Footprint
  conflicts : List Loc
  deriving Repr

/-- The site at one `par` node: empty when its branches are independent. -/
def siteOf (a b : Footprint) : List RaceSite :=
  match indepB a b with
  | true  => []
  | false => [⟨a, b, a.conflictsWith b⟩]

@[simp] theorem siteOf_nil_iff (a b : Footprint) : siteOf a b = [] ↔ Indep a b := by
  rw [← indepB_iff]
  unfold siteOf
  cases h : indepB a b <;> simp

mutual

/-- Every `par` node in the tree whose children fail Bernstein, measured along the canonical run. -/
def raceSites {τ : Type} : ParM τ → State → List RaceSite
  | .pure _,      _ => []
  | .read l k,    σ => raceSites (k (σ l)) σ
  | .write l v k, σ => raceSites (k ()) (σ.update l v)
  | .par cs k,    σ =>
      let r := runChilds cs σ
      sitesOfChilds cs σ ++ raceSitesChilds cs σ ++ raceSites (k r.1) r.2

/-- The sites at one fork: every ordered pair of children that fails Bernstein. -/
def sitesOfChilds {αs : List Type} : Childs ParM αs → State → List RaceSite
  | .nil,       _ => []
  | .cons p ps, σ =>
      siteOf (accesses p σ) (accessesChilds ps (runSeq p σ).2) ++
        sitesOfChilds ps (runSeq p σ).2

/-- Sites nested inside the children themselves. -/
def raceSitesChilds {αs : List Type} : Childs ParM αs → State → List RaceSite
  | .nil,       _ => []
  | .cons p ps, σ => raceSites p σ ++ raceSitesChilds ps (runSeq p σ).2

end

theorem sitesOfChilds_nil_iff {αs : List Type} (cs : Childs ParM αs) :
    ∀ σ, sitesOfChilds cs σ = [] ↔ IndepAll (childFootprints cs σ) := by
  induction cs with
  | nil => intro σ; simp [sitesOfChilds, IndepAll]
  | cons p ps ih =>
      intro σ
      simp only [sitesOfChilds, childFootprints, IndepAll, List.append_eq_nil_iff,
        siteOf_nil_iff, ih (runSeq p σ).2]
      constructor
      · intro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        intro g hg
        obtain ⟨hgr, hgw⟩ := childFootprint_subset ps (runSeq p σ).2 g hg
        exact Indep.mono_right h1 hgr hgw
      · intro ⟨h1, h2⟩
        exact ⟨indep_accessesChilds ps (accesses p σ) (runSeq p σ).2 h1, h2⟩

theorem raceSitesChilds_nil_iff_all :
    (∀ {τ : Type} (p : ParM τ), ∀ σ, raceSites p σ = [] ↔ WellFormed p σ) ∧
    (∀ {αs : List Type} (cs : Childs ParM αs), ∀ σ,
        raceSitesChilds cs σ = [] ↔ WellFormedChilds cs σ) := by
  refine ParM.mutualInduction ?_ ?_ ?_ ?_ ?_ ?_
  · intro α a σ; simp [raceSites, WellFormed]
  · intro α l k ih σ; exact ih (σ l) σ
  · intro α l v k ih σ; exact ih () (σ.update l v)
  · intro β αs cs k ih2 ihk σ
    have e : raceSites (.par cs k) σ =
        sitesOfChilds cs σ ++ raceSitesChilds cs σ ++
        raceSites (k (runChilds cs σ).1) (runChilds cs σ).2 := rfl
    have f : WellFormed (.par cs k) σ ↔
        (IndepAll (childFootprints cs σ) ∧ WellFormedChilds cs σ ∧
          WellFormed (k (runChilds cs σ).1) (runChilds cs σ).2) := Iff.rfl
    rw [e, f]
    simp only [List.append_eq_nil_iff, sitesOfChilds_nil_iff, ih2, ihk, and_assoc]
  · intro σ; simp [raceSitesChilds, WellFormedChilds]
  · -- **the 2-to-N step**: no nested site in the head and none in the tail
    intro α αs p ps ihp ihps σ
    simp only [raceSitesChilds, WellFormedChilds, List.append_eq_nil_iff, ihp,
      ihps (runSeq p σ).2]

/-- **The scan is complete for the obligation.** No sites means well-formed, and a well-formed
program has no sites — so a non-empty result is a real failure to explain, not a heuristic
warning. -/
theorem raceSites_nil_iff {τ : Type} (p : ParM τ) (σ : State) :
    raceSites p σ = [] ↔ WellFormed p σ :=
  raceSitesChilds_nil_iff_all.1 p σ

/-- `WellFormed` as a `Bool`, for a concrete heap: the scan found nothing. -/
def wellFormedB {τ : Type} (p : ParM τ) (σ : State) : Bool := (raceSites p σ).isEmpty

theorem wellFormedB_iff {τ : Type} (p : ParM τ) (σ : State) :
    wellFormedB p σ = true ↔ WellFormed p σ := by
  rw [wellFormedB, List.isEmpty_iff, raceSites_nil_iff]

/-! ### Phase 2 — realizing one of them

A bounded depth-first search for a schedule that reaches `wrong`. Untrusted; its result is a
`Schedule`, checked by `follow`. -/

/-- Whether this configuration is the aborted one. -/
def Conf.isWrong {τ : Type} : Conf τ → Bool
  | .wrong => true
  | _      => false

/-- Search for a schedule reaching `wrong`, to depth `fuel`. `none` means "not found within `fuel`",
never "there is no race". -/
def findWrong {τ : Type} : Nat → Conf τ → Option Schedule
  | 0,        _ => none
  | fuel + 1, c =>
      match (stepC c).findIdx? Conf.isWrong with
      | some i => some [i]
      | none   => (stepC c).zipIdx.findSome? fun (c', i) =>
                    (findWrong fuel c').map (fun s => i :: s)

/-! ### Phase 2, aimed by phase 1

A step touching a location phase 1 flagged is tried *last*, so each thread runs up to its
conflicting access and stops there. A reordering, not a restriction: nothing becomes unfindable, and
the result is still a `Schedule` checked by `follow`. -- ref: docs/race-search.md § Phase 2 -/

/-- The locations phase 1 flagged, without repeats. -/
def targetsOf (sites : List RaceSite) : List Loc :=
  (sites.flatMap RaceSite.conflicts).foldl
    (fun acc l => if acc.contains l then acc else acc ++ [l]) []

/-- Whether successor `i` moves a thread *past* a flagged location. Such a step gives up the
position the race needs, so it is tried after every alternative. -/
def consumesTarget {α : Type} (p : ParM α) (σ : State) (targets : List Loc) (i : Nat) : Bool :=
  match (attribution p σ i).action with
  | some a => targets.contains a.loc
  | none   => false

/-- `findWrong`, visiting the same successors in an order aimed by phase 1's conflict locations.
On the programs where `findWrong` backtracks once per step, this reaches the abort on its first
descent. -/
def findWrongGuided {τ : Type} (targets : List Loc) : Nat → Conf τ → Option Schedule
  | 0,        _ => none
  | fuel + 1, c =>
      match (stepC c).findIdx? Conf.isWrong with
      | some i => some [i]
      | none   =>
          let idx := (stepC c).zipIdx
          let hold : Conf τ × Nat → Bool := match c with
            | .run p σ => fun x => consumesTarget p σ targets x.2
            | .wrong   => fun _ => false
          (idx.filter (fun x => !hold x) ++ idx.filter hold).findSome? fun (c', i) =>
            (findWrongGuided targets fuel c').map (fun s => i :: s)

/-- Phase 1 then phase 2, aimed: the scan's conflict locations steer the schedule search. -/
def findWrongFrom {τ : Type} (fuel : Nat) (p : ParM τ) (σ : State) : Option Schedule :=
  let sites := raceSites p σ
  if sites.isEmpty then none    -- `raceSites_nil_iff`: no schedule can abort, so do not look
  else findWrongGuided (targetsOf sites) fuel (.run p σ)

/-- Search for two schedules whose terminal heaps differ at some location in `probes` — the stronger
counterexample, where both schedules terminate normally and disagree. -/
def findDivergence {τ : Type} (fuel : Nat) (p : ParM τ) (σ : State) (probes : List Loc) :
    Option (Schedule × Schedule × Loc) :=
  let outs := terminals fuel (.run p σ) []
  outs.findSome? fun (s₁, σ₁) =>
    outs.findSome? fun (s₂, σ₂) =>
      (probes.find? fun l => σ₁ l != σ₂ l).map fun l => (s₁, s₂, l)
where
  /-- Every terminal heap reachable within `fuel`, paired with the schedule reaching it. -/
  terminals : Nat → Conf τ → Schedule → List (Schedule × State)
    | 0,        _,          _   => []
    | _,        .wrong,     _   => []
    | fuel + 1, .run pr σ', acc =>
        match stepC (.run pr σ') with
        | [] => [(acc.reverse, σ')]
        | cs => (cs.zipIdx.map fun (c', i) => terminals fuel c' (i :: acc)).flatten

/-! ### A finite grammar to search over

`ParM` carries continuations as functions, so it can be neither generated nor shrunk. `Prog` is a
first-order tree of reads, writes, `seq` and `par` that elaborates into `ParM`; generators and
shrinkers live on `Prog` (`Test/RaceSearch.lean`) and the search runs on its image. -/

/-- A first-order program tree: the input language for the search. -/
inductive Prog where
  | rd  : Loc → Prog
  | wr  : Loc → Int → Prog
  | seq : Prog → Prog → Prog
  | par : Prog → Prog → Prog
  deriving Repr, DecidableEq, Inhabited

namespace Prog

def toParM : Prog → ParM Unit
  | .rd l    => .read l (fun _ => .pure ())
  | .wr l v  => .write l (.int v) (fun _ => .pure ())
  | .seq a b => ParM.bind a.toParM (fun _ => b.toParM)
  | .par a b => ParM.bind (ParM.parPair a.toParM b.toParM) (fun _ => .pure ())

/-- Number of memory actions. -/
def size : Prog → Nat
  | .rd _            => 1
  | .wr _ _          => 1
  | .seq a b         => a.size + b.size
  | .par a b         => a.size + b.size

/-- Steps a full run takes: one per action, plus one per `par` join. `seq` adds none — `bind` is a
graft, not an action. This is the exact fuel a schedule search needs; `size` alone is too small, and
a race late in a long program is then missed. -/
def stepBound : Prog → Nat
  | .rd _            => 1
  | .wr _ _          => 1
  | .seq a b         => a.stepBound + b.stepBound
  | .par a b         => a.stepBound + b.stepBound + 1

/-- Every location the program mentions, for probing terminal heaps. -/
def locs : Prog → List Loc
  | .rd l            => [l]
  | .wr l _          => [l]
  | .seq a b         => a.locs ++ b.locs
  | .par a b         => a.locs ++ b.locs

/-- The sequential counterpart: every `par` replaced by `seqPair`. -/
def toSeq : Prog → ParM Unit
  | .rd l    => .read l (fun _ => .pure ())
  | .wr l v  => .write l (.int v) (fun _ => .pure ())
  | .seq a b => ParM.bind a.toSeq (fun _ => b.toSeq)
  | .par a b => ParM.bind (ParM.seqPair a.toSeq b.toSeq) (fun _ => .pure ())

end Prog

/-- **Phase 1 then phase 2.** The failing `par` nodes, and a schedule realizing one of them. A
`some` schedule is checkable by `follow`; `none` means the bounded search gave up. -/
def diagnose (p : Prog) (σ : State) : List RaceSite × Option Schedule :=
  (raceSites p.toParM σ, findWrongFrom p.stepBound p.toParM σ)

end Paralever
