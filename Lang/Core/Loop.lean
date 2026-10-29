import Paralever.Theory.Nest
import Paralever.Lib.Loop
import Paralever.Lib.Block
import Paralever.Lib.TypedRead

/-! # `LoopNest` — a rolled affine nest, as data

A `for`-nest the program carries **rolled**: the trip counts stay numbers, so the term is the same
size at `N = 4` and at `N = 1000`, and the independence check is over the subscript maps rather than
over the iteration space. Unrolling a nest of depth `d` costs `O(N^d)` syntax and tops out at about
a hundred threads (`Examples/Programs/MatMul.lean`); this costs `O(k²)` in the number of accesses.

Two restrictions make it honest.

* The body is a **straight-line list of affine statements**, not a `ParProg`. So `reads` and
  `writes` are *computed* from it, never declared — `Lib/OpaqueOp.lean`'s discipline, where a
  footprint is a theorem rather than an annotation. A declared access list nothing ties to the body
  would make `wfB`'s nest case vacuous.
* `LoopNest` therefore contains no `ParProg`, so `ParProg.loop` is a leaf constructor and needs no
  mutual inductive and no new recursion scheme.

The forked depth `parDepth` is what makes gemm expressible: a nest forks its `d` outermost levels
and runs the rest inside each thread, so a write need only be injective in the forked coordinates.

Rationale: `docs/loops.md`. -/

namespace Paralever.Lang
open Paralever Paralever.Box Paralever.Nest

/-! ## Syntax -/

/-- One statement of a nest body. Three forms, and deliberately no control flow: the accesses are
read off the list, so there is no branch for them to hide behind. -- ref: `docs/loops.md` -/
inductive NestStmt where
  /-- `%r := A[aff(p)]` — a read at an affine subscript of the loop point. -/
  | rd : Reg → AffAccess → NestStmt
  /-- `A[aff(p)] := e` — a write at an affine subscript. -/
  | wr : AffAccess → AExp → NestStmt
  /-- `%r := e` — pure arithmetic, touching no memory. -/
  | st : Reg → AExp → NestStmt
  deriving Repr, DecidableEq, Inhabited

/-- A perfect affine nest. `sizes` is the trip count per level, outermost first, so the iteration
space is `∏ sizes` points and the thread count is `∏ (sizes.take parDepth)`.

`lo` and `step` carry the *values* the induction registers take — level `k`'s register holds
`lo[k] + step[k] * c` at coordinate `c`. The subscripts are over the coordinate, not the value, so
nothing in the certificate depends on either: a normalized nest has `lo = 0` and `step = 1`, and a
non-normalized one checks identically. -- ref: MLIR's affine normalization; `docs/loops.md` -/
structure LoopNest where
  /-- One induction register per level, outermost first. -/
  ivs      : List Reg
  /-- Trip count per level. -/
  sizes    : List Nat
  /-- First value per level — `0` when normalized. -/
  lo       : List Int
  /-- Stride per level — `1` when normalized. -/
  step     : List Int
  /-- How many leading levels are forked. -/
  parDepth : Nat
  /-- The straight-line body, run once per point. -/
  body     : List NestStmt
  deriving Repr, DecidableEq, Inhabited

/-! ## The accesses, computed from the body -/

/-- The read subscripts of a body. -/
def readsOf : List NestStmt → List AffAccess
  | []            => []
  | .rd _ a :: ss => a :: readsOf ss
  | _ :: ss       => readsOf ss

/-- The write subscripts of a body. -/
def writesOf : List NestStmt → List AffAccess
  | []            => []
  | .wr a _ :: ss => a :: writesOf ss
  | _ :: ss       => writesOf ss

/-- Memory operations in a nest body. -/
def nestOps : List NestStmt → Nat
  | []            => 0
  | .rd _ _ :: ss => 1 + nestOps ss
  | .wr _ _ :: ss => 1 + nestOps ss
  | .st _ _ :: ss => nestOps ss

namespace LoopNest

/-- What the nest reads, read off its body. -/
def reads (n : LoopNest) : List AffAccess := readsOf n.body
/-- What the nest writes, read off its body. -/
def writes (n : LoopNest) : List AffAccess := writesOf n.body

/-- The forked levels' trip counts — the `parDepth` outermost. -/
def outerSizes (n : LoopNest) : List Nat := n.sizes.take n.parDepth
/-- The sequential levels' trip counts — what one thread iterates over. -/
def innerSizes (n : LoopNest) : List Nat := n.sizes.drop n.parDepth

/-- The forked coordinates, one per thread. -/
def outerBox (n : LoopNest) : List (List Nat) := boxNat n.outerSizes
/-- The coordinates one thread runs through, in order. -/
def innerBox (n : LoopNest) : List (List Nat) := boxNat n.innerSizes

/-- How many threads the nest forks. -/
def threadCount (n : LoopNest) : Nat := prodN n.outerSizes

/-- Memory operations in the body, once per point. A pure `st` costs none. -/
def bodyOps (n : LoopNest) : Nat := nestOps n.body

/-- Memory operations one thread performs: the body once per sequential point. -/
def threadOps (n : LoopNest) : Nat := prodN n.innerSizes * n.bodyOps

/-- A forked point followed by a sequential point is a point of the whole box. -/
theorem inBox_whole (n : LoopNest) {u p : List Nat} (hu : u ∈ n.outerBox) (hp : p ∈ n.innerBox) :
    InBox n.sizes (u ++ p) := by
  have h := inBox_append n.outerSizes n.innerSizes u p
    (inBox_of_mem_boxNat hu) (inBox_of_mem_boxNat hp)
  rwa [outerSizes, innerSizes, List.take_append_drop] at h

end LoopNest

/-! ## Semantics

The body is lowered into `ParM` directly, never through `ParProg`: a nest's body is not a statement
of the outer language, so `execPar` recurses into nothing and stays structural. -/

/-- The induction register's value at coordinate `c`. -/
def ivVal (lo step : Int) (c : Nat) : Int := lo + step * (c : Int)

/-- Set each induction register to its value at the point `q`. Levels past the shortest list are
dropped, so a malformed nest sets fewer registers rather than failing. -/
def setIvs : List Reg → List Int → List Int → List Nat → Regs → Regs
  | r :: rs, l :: ls, s :: ss, c :: cs, ρ => setIvs rs ls ss cs (ρ.set r (ivVal l s c))
  | _,       _,       _,       _,       ρ => ρ

/-- One statement at one point. -/
def NestStmt.exec : NestStmt → List Nat → Regs → ParM Regs
  | .rd r a, q, ρ => ParM.bind (readAs (a.addr q) (0 : Int)) (fun v => .pure (ρ.set r v))
  | .wr a e, q, ρ => ParM.bind (writeAs (a.addr q) (e.eval ρ)) (fun _ => .pure ρ)
  | .st r e, _, ρ => .pure (ρ.set r (e.eval ρ))

/-- The body at one point, in order. -/
def runStmts : List NestStmt → List Nat → Regs → ParM Regs
  | [],      _, ρ => .pure ρ
  | s :: ss, q, ρ => ParM.bind (s.exec q ρ) (fun ρ' => runStmts ss q ρ')

namespace LoopNest

/-- The body at one point, with the induction registers set. -/
def atPoint (n : LoopNest) (q : List Nat) (ρ : Regs) : ParM Regs :=
  runStmts n.body q (setIvs n.ivs n.lo n.step q ρ)

/-- One thread's sequential sweep over the given inner points. -/
def inner (n : LoopNest) (u : List Nat) : List (List Nat) → Regs → ParM Regs
  | [],      ρ => .pure ρ
  | p :: ps, ρ => ParM.bind (n.atPoint (u ++ p) ρ) (fun ρ' => n.inner u ps ρ')

/-- The thread forked at the coordinates `u`: every point of the inner box, in order. -/
def thread (n : LoopNest) (ρ : Regs) (u : List Nat) : ParM Regs := n.inner u n.innerBox ρ

/-- One child per forked coordinate. -/
def threads (n : LoopNest) (ρ : Regs) : List (ParM Regs) := n.outerBox.map (n.thread ρ)

end LoopNest

/-! ### What one statement does

The canonical run of each form, so a proof about a nest body never unfolds `readAs`/`writeAs`
again. -/

@[simp] theorem runSeq_exec_rd (r : Reg) (a : AffAccess) (q : List Nat) (ρ : Regs) (σ : State) :
    runSeq ((NestStmt.rd r a).exec q ρ) σ
      = (ρ.set r ((Storable.decode (σ (a.addr q))).getD (0 : Int)), σ) := by
  show runSeq (ParM.bind (readAs (a.addr q) (0 : Int)) _) σ = _
  rw [runSeq_bind, readAs_runSeq]; rfl

@[simp] theorem runSeq_exec_wr (a : AffAccess) (e : AExp) (q : List Nat) (ρ : Regs) (σ : State) :
    runSeq ((NestStmt.wr a e).exec q ρ) σ
      = (ρ, σ.update (a.addr q) (Storable.encode (e.eval ρ))) := by
  show runSeq (ParM.bind (writeAs (a.addr q) _) _) σ = _
  rw [runSeq_bind, writeAs_runSeq]; rfl

@[simp] theorem runSeq_exec_st (r : Reg) (e : AExp) (q : List Nat) (ρ : Regs) (σ : State) :
    runSeq ((NestStmt.st r e).exec q ρ) σ = (ρ.set r (e.eval ρ), σ) := rfl

/-- One thread peeled off a sequenced list, on the heap. `ParM.seqAll`'s own cons lemma is stated
for `ParProg` threads (`Paralever/AutoPar/Sound.lean`); a nest's children are bare `ParM`s. -/
theorem runSeq_seqAll_cons' (m : ParM Regs) (ms : List (ParM Regs)) (σ : State) :
    (runSeq (ParM.seqAll (m :: ms)) σ).2 = (runSeq (ParM.seqAll ms) (runSeq m σ).2).2 := by
  show (runSeq (ParM.bind (ParM.seqPair _ _) _) σ).2 = _
  simp only [ParM.seqPair, runSeq_bind, runSeq]

/-! ## The footprint, over-approximated by the buffers

`Footprint` is concrete cell lists, so a rolled nest cannot have an exact one without enumerating
the iteration space — the cost the roll exists to avoid. The bound is each access's `span`: the
cells from its base through the furthest the box can reach. Unconditional, and no more approximate
than a computed subscript's whole-array bound already is. -- ref: `docs/loops.md` -/

/-- The cells one statement can touch, over the whole box. -/
def NestStmt.spanOf (sizes : List Nat) : NestStmt → Footprint
  | .rd _ a => ⟨a.span sizes, []⟩
  | .wr a _ => ⟨[], a.span sizes⟩
  | .st _ _ => .empty

/-- The cells a body can touch, over the whole box. -/
def stmtsSpan (sizes : List Nat) : List NestStmt → Footprint
  | []      => .empty
  | s :: ss => Footprint.union (s.spanOf sizes) (stmtsSpan sizes ss)

/-- The nest's footprint bound. -/
def LoopNest.footprint (n : LoopNest) : Footprint := stmtsSpan n.sizes n.body

/-! ### The bound holds

`Footprint.Sub` into a fixed bound, which is what `execPar_accesses_sub` needs of the nest case. -/

private theorem empty_sub (f : Footprint) : Footprint.empty.Sub f :=
  ⟨fun _ m => (List.not_mem_nil m).elim, fun _ m => (List.not_mem_nil m).elim⟩

private theorem union_self_sub (f : Footprint) : (Footprint.union f f).Sub f :=
  ⟨fun _ m => (List.mem_append.mp m).elim id id,
   fun _ m => (List.mem_append.mp m).elim id id⟩

private theorem accesses_exec_sub (sizes : List Nat) (s : NestStmt) {q : List Nat}
    (hq : InBox sizes q) (ρ : Regs) (σ : State) :
    (accesses (s.exec q ρ) σ).Sub (s.spanOf sizes) := by
  cases s with
  | rd r a =>
      have e1 : accesses (NestStmt.exec (.rd r a) q ρ) σ = ⟨[a.addr q], []⟩ := by
        show accesses (ParM.bind (readAs (a.addr q) (0 : Int)) _) σ = _
        rw [accesses_bind, readAs_accesses, readAs_runSeq]
        simp [accesses, Footprint.union, Footprint.empty]
      rw [e1]
      refine ⟨fun l m => ?_, fun l m => (List.not_mem_nil m).elim⟩
      rw [List.mem_singleton] at m
      exact m ▸ addr_mem_span hq
  | wr a e =>
      have e1 : accesses (NestStmt.exec (.wr a e) q ρ) σ = ⟨[], [a.addr q]⟩ := by
        show accesses (ParM.bind (writeAs (a.addr q) _) _) σ = _
        rw [accesses_bind, writeAs_accesses, writeAs_runSeq]
        simp [accesses, Footprint.union, Footprint.empty]
      rw [e1]
      refine ⟨fun l m => (List.not_mem_nil m).elim, fun l m => ?_⟩
      rw [List.mem_singleton] at m
      exact m ▸ addr_mem_span hq
  | st r e => exact Footprint.Sub.rfl' _

private theorem accesses_runStmts_sub (sizes : List Nat) {q : List Nat} (hq : InBox sizes q) :
    ∀ (body : List NestStmt) (ρ : Regs) (σ : State),
      (accesses (runStmts body q ρ) σ).Sub (stmtsSpan sizes body) := by
  intro body
  induction body with
  | nil => intro ρ σ; exact Footprint.Sub.rfl' _
  | cons s ss ih =>
      intro ρ σ
      show (accesses (ParM.bind (s.exec q ρ) _) σ).Sub _
      rw [accesses_bind]
      exact Footprint.Sub.union (accesses_exec_sub sizes s hq ρ σ) (ih _ _)

private theorem accesses_inner_sub (n : LoopNest) (u : List Nat) :
    ∀ (ps : List (List Nat)), (∀ p ∈ ps, InBox n.sizes (u ++ p)) →
      ∀ (ρ : Regs) (σ : State), (accesses (n.inner u ps ρ) σ).Sub n.footprint := by
  intro ps
  induction ps with
  | nil => intro _ ρ σ; exact empty_sub _
  | cons p ps ih =>
      intro h ρ σ
      show (accesses (ParM.bind (n.atPoint (u ++ p) ρ) _) σ).Sub _
      rw [accesses_bind]
      refine Footprint.Sub.trans
        (Footprint.Sub.union ?_ (ih (fun q hq => h q (List.mem_cons_of_mem p hq)) _ _))
        (union_self_sub _)
      exact accesses_runStmts_sub n.sizes (h p List.mem_cons_self) n.body _ _

private theorem accesses_parAll_sub {F : Footprint} :
    ∀ (ms : List (ParM Regs)), (∀ m ∈ ms, ∀ σ, (accesses m σ).Sub F) →
      ∀ σ, (accesses (ParM.parAll ms) σ).Sub F := by
  intro ms
  induction ms with
  | nil => intro _ σ; exact empty_sub _
  | cons m ms ih =>
      intro h σ
      rw [accesses_parAll_cons]
      exact Footprint.Sub.trans
        (Footprint.Sub.union (h m List.mem_cons_self σ)
          (ih (fun m' hm' => h m' (List.mem_cons_of_mem m hm')) _))
        (union_self_sub _)

/-- **The nest's accesses are bounded by its syntax**, at every register file and heap — the fact
`footprintOf (.loop n)` rests on. -/
theorem LoopNest.accesses_threads_sub (n : LoopNest) (ρ : Regs) (σ : State) :
    (accesses (ParM.parAll (n.threads ρ)) σ).Sub n.footprint := by
  refine accesses_parAll_sub (n.threads ρ) ?_ σ
  intro m hm σ'
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hm
  exact accesses_inner_sub n u n.innerBox (fun p hp => n.inBox_whole hu hp) _ _


/-! ## The nest is well-formed when its certificate holds

`parAll_wellformed_of_indexed_rw` (`Paralever/Lib/Loop.lean`) is the metatheorem: give it the index
list, the per-index read and write regions, and one disjointness fact per distinct pair, and it
returns `WellFormed` for the whole fork at any size. Here the index type is `List Nat` — the forked
coordinates — and the two disjointness facts are `nestIndepB_ww` and `nestIndepB_wr`. -/

@[simp] theorem readsOf_rd (r : Reg) (a : AffAccess) (ss : List NestStmt) :
    readsOf (.rd r a :: ss) = a :: readsOf ss := rfl
@[simp] theorem readsOf_wr (a : AffAccess) (e : AExp) (ss : List NestStmt) :
    readsOf (.wr a e :: ss) = readsOf ss := rfl
@[simp] theorem readsOf_st (r : Reg) (e : AExp) (ss : List NestStmt) :
    readsOf (.st r e :: ss) = readsOf ss := rfl
@[simp] theorem writesOf_rd (r : Reg) (a : AffAccess) (ss : List NestStmt) :
    writesOf (.rd r a :: ss) = writesOf ss := rfl
@[simp] theorem writesOf_wr (a : AffAccess) (e : AExp) (ss : List NestStmt) :
    writesOf (.wr a e :: ss) = a :: writesOf ss := rfl
@[simp] theorem writesOf_st (r : Reg) (e : AExp) (ss : List NestStmt) :
    writesOf (.st r e :: ss) = writesOf ss := rfl

private theorem readsOf_sub_cons (s : NestStmt) (ss : List NestStmt) :
    readsOf ss ⊆ readsOf (s :: ss) := by
  cases s with
  | rd r a => exact List.subset_cons_self _ _
  | wr a e => exact fun _ h => h
  | st r e => exact fun _ h => h

private theorem writesOf_sub_cons (s : NestStmt) (ss : List NestStmt) :
    writesOf ss ⊆ writesOf (s :: ss) := by
  cases s with
  | rd r a => exact fun _ h => h
  | wr a e => exact List.subset_cons_self _ _
  | st r e => exact fun _ h => h

/-! ### Each thread is well-formed

A nest body contains no fork, so `WellFormed` is about nothing — but it is still an induction over
the body and the point list, because `WellFormed` of a `bind` is `WellFormed` of both halves. -/

private theorem wellFormed_exec (s : NestStmt) (q : List Nat) (ρ : Regs) (σ : State) :
    WellFormed (s.exec q ρ) σ := by cases s <;> trivial

private theorem wellFormed_runStmts : ∀ (body : List NestStmt) (q : List Nat) (ρ : Regs)
    (σ : State), WellFormed (runStmts body q ρ) σ := by
  intro body
  induction body with
  | nil => intro q ρ σ; trivial
  | cons s ss ih =>
      intro q ρ σ
      show WellFormed (ParM.bind (s.exec q ρ) _) σ
      rw [WellFormed_bind]
      exact ⟨wellFormed_exec s q ρ σ, ih _ _ _⟩

theorem LoopNest.wellFormed_inner (n : LoopNest) (u : List Nat) :
    ∀ (ps : List (List Nat)) (ρ : Regs) (σ : State), WellFormed (n.inner u ps ρ) σ := by
  intro ps
  induction ps with
  | nil => intro ρ σ; trivial
  | cons p ps ih =>
      intro ρ σ
      show WellFormed (ParM.bind (n.atPoint (u ++ p) ρ) _) σ
      rw [WellFormed_bind]
      exact ⟨wellFormed_runStmts n.body _ _ _, ih _ _⟩

/-! ### Where a thread's reads and writes land -/

namespace LoopNest

/-- Where the thread forked at `u` reads: a read subscript of the body, at some point of the inner
box under `u`. -/
def readsAt (n : LoopNest) (u : List Nat) (l : Loc) : Prop :=
  ∃ a ∈ n.reads, ∃ p ∈ n.innerBox, l = a.addr (u ++ p)

/-- Where the thread forked at `u` writes. -/
def writesAt (n : LoopNest) (u : List Nat) (l : Loc) : Prop :=
  ∃ a ∈ n.writes, ∃ p ∈ n.innerBox, l = a.addr (u ++ p)

end LoopNest

private theorem rw_runStmts (q : List Nat) :
    ∀ (body : List NestStmt) (ρ : Regs) (σ : State),
      ReadsWithin (accesses (runStmts body q ρ) σ) (fun l => ∃ a ∈ readsOf body, l = a.addr q) ∧
      WritesWithin (accesses (runStmts body q ρ) σ)
        (fun l => ∃ a ∈ writesOf body, l = a.addr q) := by
  intro body
  induction body with
  | nil =>
      intro ρ σ
      exact ⟨ReadsWithin.empty _, WritesWithin.empty _⟩
  | cons s ss ih =>
      intro ρ σ
      show ReadsWithin (accesses (ParM.bind (s.exec q ρ) _) σ) _
         ∧ WritesWithin (accesses (ParM.bind (s.exec q ρ) _) σ) _
      rw [accesses_bind]
      have hmR : ∀ l, (∃ a ∈ readsOf ss, l = a.addr q) → ∃ a ∈ readsOf (s :: ss), l = a.addr q :=
        fun l ⟨a, ha, hl⟩ => ⟨a, readsOf_sub_cons s ss ha, hl⟩
      have hmW : ∀ l, (∃ a ∈ writesOf ss, l = a.addr q) → ∃ a ∈ writesOf (s :: ss), l = a.addr q :=
        fun l ⟨a, ha, hl⟩ => ⟨a, writesOf_sub_cons s ss ha, hl⟩
      obtain ⟨ihR, ihW⟩ := ih (runSeq (s.exec q ρ) σ).1 (runSeq (s.exec q ρ) σ).2
      refine ⟨ReadsWithin.union ?_ (ReadsWithin.mono hmR ihR),
              WritesWithin.union ?_ (WritesWithin.mono hmW ihW)⟩
      · cases s with
        | rd r a =>
            have e1 : accesses (NestStmt.exec (.rd r a) q ρ) σ = ⟨[a.addr q], []⟩ := by
              show accesses (ParM.bind (readAs (a.addr q) (0 : Int)) _) σ = _
              rw [accesses_bind, readAs_accesses, readAs_runSeq]
              simp [accesses, Footprint.union, Footprint.empty]
            rw [e1]
            exact ReadsWithin.read _ _ ⟨a, by simp, rfl⟩
        | wr a e =>
            have e1 : accesses (NestStmt.exec (.wr a e) q ρ) σ = ⟨[], [a.addr q]⟩ := by
              show accesses (ParM.bind (writeAs (a.addr q) _) _) σ = _
              rw [accesses_bind, writeAs_accesses, writeAs_runSeq]
              simp [accesses, Footprint.union, Footprint.empty]
            rw [e1]
            exact ReadsWithin.write _ _
        | st r e => exact ReadsWithin.empty _
      · cases s with
        | rd r a =>
            have e1 : accesses (NestStmt.exec (.rd r a) q ρ) σ = ⟨[a.addr q], []⟩ := by
              show accesses (ParM.bind (readAs (a.addr q) (0 : Int)) _) σ = _
              rw [accesses_bind, readAs_accesses, readAs_runSeq]
              simp [accesses, Footprint.union, Footprint.empty]
            rw [e1]
            exact WritesWithin.read _ _
        | wr a e =>
            have e1 : accesses (NestStmt.exec (.wr a e) q ρ) σ = ⟨[], [a.addr q]⟩ := by
              show accesses (ParM.bind (writeAs (a.addr q) _) _) σ = _
              rw [accesses_bind, writeAs_accesses, writeAs_runSeq]
              simp [accesses, Footprint.union, Footprint.empty]
            rw [e1]
            exact WritesWithin.write _ _ ⟨a, by simp, rfl⟩
        | st r e => exact WritesWithin.empty _

theorem LoopNest.rw_inner (n : LoopNest) (u : List Nat) :
    ∀ (ps : List (List Nat)), (∀ p ∈ ps, p ∈ n.innerBox) → ∀ (ρ : Regs) (σ : State),
      ReadsWithin (accesses (n.inner u ps ρ) σ) (n.readsAt u) ∧
      WritesWithin (accesses (n.inner u ps ρ) σ) (n.writesAt u) := by
  intro ps
  induction ps with
  | nil => intro _ ρ σ; exact ⟨ReadsWithin.empty _, WritesWithin.empty _⟩
  | cons p ps ih =>
      intro h ρ σ
      show ReadsWithin (accesses (ParM.bind (n.atPoint (u ++ p) ρ) _) σ) _
         ∧ WritesWithin (accesses (ParM.bind (n.atPoint (u ++ p) ρ) _) σ) _
      rw [accesses_bind]
      obtain ⟨hR, hW⟩ := rw_runStmts (u ++ p) n.body (setIvs n.ivs n.lo n.step (u ++ p) ρ) σ
      obtain ⟨ihR, ihW⟩ := ih (fun p' hp' => h p' (List.mem_cons_of_mem p hp')) _ _
      refine ⟨ReadsWithin.union (ReadsWithin.mono ?_ hR) ihR,
              WritesWithin.union (WritesWithin.mono ?_ hW) ihW⟩
      · exact fun l ⟨a, ha, hl⟩ => ⟨a, ha, p, h p List.mem_cons_self, hl⟩
      · exact fun l ⟨a, ha, hl⟩ => ⟨a, ha, p, h p List.mem_cons_self, hl⟩

/-- **The certificate discharges the obligation, at any size.** `nestIndepB` is `O(k²)` in the
number of accesses and never looks at a point of the box; this is what it buys. -/
theorem LoopNest.wellFormed_threads {n : LoopNest}
    (h : nestIndepB n.sizes n.parDepth n.reads n.writes = true) (ρ : Regs) (σ : State) :
    WellFormed (ParM.parAll (n.threads ρ)) σ := by
  have hww : ∀ u v, u ∈ n.outerBox → v ∈ n.outerBox → u ≠ v → ∀ l,
      n.writesAt u l → n.writesAt v l → False := by
    intro u v hu hv hne l hul hvl
    obtain ⟨a, ha, p, _, hla⟩ := hul
    obtain ⟨b, hb, q, _, hlb⟩ := hvl
    exact nestIndepB_ww h a ha b hb u v p q
      (inBox_of_mem_boxNat hu) (inBox_of_mem_boxNat hv) hne
      (n.inBox_whole hu ‹p ∈ n.innerBox›) (n.inBox_whole hv ‹q ∈ n.innerBox›)
      (hla.symm.trans hlb)
  have hwr : ∀ u v, u ∈ n.outerBox → v ∈ n.outerBox → u ≠ v → ∀ l,
      n.writesAt u l → n.readsAt v l → False := by
    intro u v hu hv hne l hul hvl
    obtain ⟨a, ha, p, _, hla⟩ := hul
    obtain ⟨b, hb, q, _, hlb⟩ := hvl
    exact nestIndepB_wr h a ha b hb u v p q
      (inBox_of_mem_boxNat hu) (inBox_of_mem_boxNat hv) hne
      (n.inBox_whole hu ‹p ∈ n.innerBox›) (n.inBox_whole hv ‹q ∈ n.innerBox›)
      (hla.symm.trans hlb)
  show WellFormed (ParM.parAll (n.outerBox.map (n.thread ρ))) σ
  exact (Paralever.Loop.parAll_wellformed_of_indexed_rw n.outerBox (n.thread ρ)
    n.readsAt n.writesAt (boxNat_nodup _)
    (fun u _ σ' => n.wellFormed_inner u n.innerBox ρ σ')
    (fun u _ σ' => (n.rw_inner u n.innerBox (fun _ hp => hp) ρ σ').1)
    (fun u _ σ' => (n.rw_inner u n.innerBox (fun _ hp => hp) ρ σ').2)
    hww hwr σ).1

/-- The sequential reading of a nest is well-formed too, and for a smaller reason: `seqAll` of
fork-free children contains no fork. -/
theorem LoopNest.wellFormed_seqAll (n : LoopNest) (ρ : Regs) (σ : State) :
    WellFormed (ParM.seqAll (n.threads ρ)) σ := by
  have key : ∀ (ms : List (ParM Regs)), (∀ m ∈ ms, ∀ σ', WellFormed m σ') →
      ∀ σ', WellFormed (ParM.seqAll ms) σ' := by
    intro ms
    induction ms with
    | nil => intro _ σ'; trivial
    | cons m ms ih =>
        intro hm σ'
        show WellFormed (ParM.bind (ParM.seqPair m (ParM.seqAll ms)) _) σ'
        have h1 := hm m List.mem_cons_self
        have h2 := ih (fun m' hm' => hm m' (List.mem_cons_of_mem m hm'))
        grind [ParM.seqPair]
  refine key (n.threads ρ) ?_ σ
  intro m hm σ'
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp hm
  exact n.wellFormed_inner u n.innerBox ρ σ'

end Paralever.Lang
