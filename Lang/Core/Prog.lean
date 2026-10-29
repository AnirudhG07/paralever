import Lang.Core.Loop
import Paralever.Lib.Block
import Paralever.Lib.ArrRef
import Paralever.Theory.Sequentialize

/-! # A small imperative language with parallel blocks — syntax and metatheory

`ParM`'s effect nodes carry Lean *functions* as continuations, so a `ParM` term cannot be printed
past a `read` and the arithmetic a thread performs is invisible. This file makes the program *data
all the way down*: `ParProg` is first-order, `execPar` lowers it into `ParM`, and the three
properties that follow are what the rest of `Lang/` builds on —

* **it prints**, computations included (`Lang/Core/Notation.lean`);
* **its footprint is computed** by a fold (`footprintOf`, `execPar_accesses`);
* **its obligation is decidable** (`wfB`, `wfB_wellFormed`, `par_seq_eq`).

Registers are **thread-private**: a `parallel` block hands each thread a copy of the register file
and discards what the threads leave, so threads communicate through memory only. That is why the
independence obligation is about memory alone, and it matches how a GPU kernel is written.

Rationale: `docs/block-ir.md`. -/

namespace Paralever.Lang
open Paralever

/-! ## Syntax -/

/-- One thing a `print` statement names. `print` touches no memory and both interpreters erase it,
so this is the only place its content lives. -- ref: `docs/print.md` -/
inductive PrintItem where
  /-- `print "msg"` — a literal, so a line of output can say what it is. -/
  | text : String → PrintItem
  /-- `print %p`, `print 2 * %p` — an expression over the registers in scope. -/
  | exp  : AExp → PrintItem
  /-- `print k` — a whole buffer: its name, its shape, and its first cell. -/
  | buf  : String → List Nat → Loc → PrintItem
  /-- `print k[1]` — one cell: the name, the subscript, and the cell it resolves to. -/
  | cell : String → List Nat → Loc → PrintItem
  /-- `print A[%i]` — a cell chosen at run time, so the index is an expression and the address
  wraps on `A`'s length exactly as `loadAt` does. -/
  | at   : String → ArrRef → AExp → PrintItem
  deriving Repr, Inhabited, DecidableEq


/-- The program statements. Addresses are literals, which is what keeps `footprintOf` syntactic; a loop over
indices is written in Lean, producing one fully-instantiated thread per index. -/
inductive ParProg where
  /-- `t := M[l]` -/
  | load  : Reg → Loc → ParProg
  /-- `M[l] := e` -/
  | store : Loc → AExp → ParProg
  /-- `t := e` — pure arithmetic, touches no memory -/
  | set   : Reg → AExp → ParProg
  /-- `a ; b` -/
  | seq   : ParProg → ParProg → ParProg
  /-- `parallel { … }` with one thread per element -/
  | par   : List ParProg → ParProg
  /-- `s :: name` — a named region. Semantically transparent: `execPar` ignores it. It exists so a
  region can be *referred to*, proved about on its own, and found again inside a larger program. -/
  | label : String → ParProg → ParProg
  /-- `t := A[e]` — a **data-dependent** load. The index wraps on `A.len`, so the access is
  confined to `A` by construction (`ArrRef.addr_mem_cells`). -/
  | loadAt  : Reg → ArrRef → AExp → ParProg
  /-- `A[e] := e'` — a data-dependent store. -/
  | storeAt : ArrRef → AExp → AExp → ParProg
  /-- `if c then t else e`. `0` is false; the footprint is the union of both branches, since which
  one runs is not known statically. -/
  | ifElse : AExp → ParProg → ParProg → ParProg
  /-- `synchronize` — a barrier the parallelizer may not cross. A no-op at run time: `par` already
  joins its threads, so there is nothing left to wait for. Its content is the constraint it puts on
  `autoPar`, which plans each phase on its own. -- ref: `docs/autopar.md` § Synchronization -/
  | synchronize : ParProg
  /-- `print k` — output, and nothing else. It has no footprint and no effect on the heap: both
  interpreters erase it, so every theorem about a program is a theorem about the program with its
  prints removed. What it does carry is a barrier, exactly as `synchronize` does, so the parallelizer
  cannot move a statement across the point where its value was observed.
  -- ref: `docs/print.md` § Erased, and a barrier -/
  | print : List PrintItem → ParProg
  /-- `for`/`parfor`, **rolled**: the nest's trip counts stay numbers, so the term does not grow
  with them and the independence check is over the subscript maps rather than the iteration space.
  A leaf constructor — the body is a `List NestStmt`, not a `ParProg` — so nothing here recurses.
  -- ref: `docs/loops.md` -/
  | loop : LoopNest → ParProg
  deriving Repr, Inhabited

namespace ParProg

/-- `s₁ ; s₂ ; …` from a list, right-nested. -/
def block : List ParProg → ParProg
  | []      => .set 0 (.reg 0)        -- a no-op: assign a register to itself
  | [s]     => s
  | s :: ss => .seq s (block ss)

/-- `while c { body }`, for **at most** `n` iterations, the guard tested before each.

A derived form, not a constructor: `ParM` is inductive, so an unbounded `while` is unrepresentable
and the bound is permanent. Unrolled at elaboration into `ifElse`/`seq`, so nothing else needs new
cases. -- ref: `docs/block-ir.md` -/
def whileAtMost : Nat → AExp → ParProg → ParProg
  | 0,     _, _    => block []
  | n + 1, c, body => .ifElse c (.seq body (whileAtMost n c body)) (block [])

/-! ## Lowering into `ParM`

`execPar` is the interpreter; `execSeq` is the same interpreter with `parallel` read as
"left to right". They differ in exactly one constructor, which is the whole point. -/

mutual

/-- Lower a statement, threading the register file. A `parallel` block gives every thread the
*current* register file and keeps its own afterwards: register updates inside a thread are private
to it. -/
def execPar : ParProg → Regs → ParM Regs
  | .load r l,  ρ => ParM.bind (readAs l (0 : Int)) (fun v => .pure (ρ.set r v))
  | .store l e, ρ => ParM.bind (writeAs l (e.eval ρ)) (fun _ => .pure ρ)
  | .set r e,   ρ => .pure (ρ.set r (e.eval ρ))
  | .seq a b,   ρ => ParM.bind (execPar a ρ) (fun ρ' => execPar b ρ')
  | .par ss,    ρ => ParM.bind (ParM.parAll (execParAll ss ρ)) (fun _ => .pure ρ)
  | .label _ s, ρ => execPar s ρ
  | .loadAt r a e,  ρ => ParM.bind (readAs (a.addr (e.eval ρ)) (0 : Int))
                           (fun v => .pure (ρ.set r v))
  | .storeAt a e v, ρ => ParM.bind (writeAs (a.addr (e.eval ρ)) (v.eval ρ)) (fun _ => .pure ρ)
  | .ifElse c t e,  ρ => if c.eval ρ != 0 then execPar t ρ else execPar e ρ
  | .synchronize,     ρ => .pure ρ
  -- erased: output is not a memory effect
  | .print _,         ρ => .pure ρ
  -- one child per forked coordinate; each runs the sequential levels in order
  | .loop n,          ρ => ParM.bind (ParM.parAll (n.threads ρ)) (fun _ => .pure ρ)

/-- Each thread, lowered from the same starting register file. -/
def execParAll : List ParProg → Regs → List (ParM Regs)
  | [],      _ => []
  | s :: ss, ρ => execPar s ρ :: execParAll ss ρ

end

mutual

/-- The sequential reading: `parallel` means "in order". -/
def execSeq : ParProg → Regs → ParM Regs
  | .load r l,  ρ => ParM.bind (readAs l (0 : Int)) (fun v => .pure (ρ.set r v))
  | .store l e, ρ => ParM.bind (writeAs l (e.eval ρ)) (fun _ => .pure ρ)
  | .set r e,   ρ => .pure (ρ.set r (e.eval ρ))
  | .seq a b,   ρ => ParM.bind (execSeq a ρ) (fun ρ' => execSeq b ρ')
  | .par ss,    ρ => ParM.bind (ParM.seqAll (execSeqAll ss ρ)) (fun _ => .pure ρ)
  | .label _ s, ρ => execSeq s ρ
  | .loadAt r a e,  ρ => ParM.bind (readAs (a.addr (e.eval ρ)) (0 : Int))
                           (fun v => .pure (ρ.set r v))
  | .storeAt a e v, ρ => ParM.bind (writeAs (a.addr (e.eval ρ)) (v.eval ρ)) (fun _ => .pure ρ)
  | .ifElse c t e,  ρ => if c.eval ρ != 0 then execSeq t ρ else execSeq e ρ
  | .synchronize,     ρ => .pure ρ
  -- erased: output is not a memory effect
  | .print _,         ρ => .pure ρ
  | .loop n,          ρ => ParM.bind (ParM.seqAll (n.threads ρ)) (fun _ => .pure ρ)

def execSeqAll : List ParProg → Regs → List (ParM Regs)
  | [],      _ => []
  | s :: ss, ρ => execSeq s ρ :: execSeqAll ss ρ

end

/-! ## The footprint, computed

No state, no simulation, no proof per program: a fold over the syntax. -/

mutual

/-- Whether `footprintOf` is **exact** rather than a bound. Fails for a computed address
(`loadAt`, `storeAt`) and for a run-time branch (`ifElse`). Only `execPar_accesses` needs it;
soundness goes through `execPar_accesses_sub`. -/
def footprintExact : ParProg → Bool
  | .load _ _      => true
  | .store _ _     => true
  | .set _ _       => true
  | .seq a b       => footprintExact a && footprintExact b
  | .par ss        => footprintExactAll ss
  | .label _ s     => footprintExact s
  | .loadAt _ _ _  => false
  | .storeAt _ _ _ => false
  | .ifElse _ _ _  => false
  | .synchronize         => true
  | .print _             => true
  -- an empty box runs nothing, so the buffer bound is never exact
  | .loop _              => false

def footprintExactAll : List ParProg → Bool
  | []      => true
  | s :: ss => footprintExact s && footprintExactAll ss

end

mutual

def footprintOf : ParProg → Footprint
  | .load _ l  => ⟨[l], []⟩
  | .store l _ => ⟨[], [l]⟩
  | .set _ _   => .empty
  | .seq a b   => Footprint.union (footprintOf a) (footprintOf b)
  | .par ss    => footprintsOf ss
  | .label _ s => footprintOf s
  -- the index is a register expression, so the cell is unknown statically; the bound is the array
  | .loadAt _ a _  => ⟨a.cells, []⟩
  | .storeAt a _ _ => ⟨[], a.cells⟩
  -- only one branch runs, but which is not known until the run
  | .ifElse _ t e  => Footprint.union (footprintOf t) (footprintOf e)
  | .synchronize         => .empty
  | .print _             => .empty
  -- the buffers the nest can reach, since a concrete cell list cannot be had without enumerating
  -- the iteration space -- ref: `docs/loops.md`
  | .loop n              => n.footprint

def footprintsOf : List ParProg → Footprint
  | []      => .empty
  | s :: ss => Footprint.union (footprintOf s) (footprintsOf ss)

end

/-- Each thread's footprint on its own — what the independence check ranges over. -/
def threadFootprints : List ParProg → List Footprint
  | []      => []
  | s :: ss => footprintOf s :: threadFootprints ss

/-! ## Prints are erased

Both interpreters send a `print` to `.pure ρ`, which is the whole of "the proofs ignore those
lines". `dropPrints` states the consequence as a function — the program with its prints gone — and
`execPar_dropPrints` proves the two run the same, so a theorem about either is a theorem about both.
-- ref: `docs/print.md` § Erased, and a barrier -/

@[simp] theorem execPar_print (is : List PrintItem) (ρ : Regs) :
    execPar (.print is) ρ = .pure ρ := rfl

@[simp] theorem execSeq_print (is : List PrintItem) (ρ : Regs) :
    execSeq (.print is) ρ = .pure ρ := rfl

@[simp] theorem footprintOf_print (is : List PrintItem) :
    footprintOf (.print is) = Footprint.empty := rfl

mutual

/-- The program with every `print` removed, or `none` when nothing is left of it. A print inside a
`parallel` thread is refused by the lowering (`Diag.p106`), so the `par` case only has to rebuild
threads that had none. -/
def dropPrints? : ParProg → Option ParProg
  | .print _      => none
  | .seq a b      =>
      match dropPrints? a, dropPrints? b with
      | none,    none    => none
      | some a', none    => some a'
      | none,    some b' => some b'
      | some a', some b' => some (.seq a' b')
  | .label nm s   => (dropPrints? s).map (.label nm)
  | .par ss       => some (.par (dropPrintsAll ss))
  | .ifElse c t e => some (.ifElse c (dropPrints? t |>.getD .synchronize)
                                     (dropPrints? e |>.getD .synchronize))
  | s             => some s

def dropPrintsAll : List ParProg → List ParProg
  | []      => []
  | s :: ss => (dropPrints? s |>.getD .synchronize) :: dropPrintsAll ss

end

/-- The program with its prints removed. A program that was *only* prints becomes `synchronize`,
which is the other statement both interpreters send to `.pure ρ`. -/
def dropPrints (s : ParProg) : ParProg := (dropPrints? s).getD .synchronize

/-! ## The obligation, decided

`wfB` is Bernstein at every `parallel` block in the program, read straight off the syntax. -/

mutual

/-- Whether every `parallel` block in the statement has pairwise-independent threads. -/
def wfB : ParProg → Bool
  | .load _ _  => true
  | .store _ _ => true
  | .set _ _   => true
  | .seq a b   => wfB a && wfB b
  | .par ss    => indepAllB (threadFootprints ss) && wfAllB ss
  | .label _ s => wfB s
  | .loadAt _ _ _  => true
  | .storeAt _ _ _ => true
  -- either branch may run, so both must be well-formed
  | .ifElse _ t e  => wfB t && wfB e
  | .synchronize         => true
  | .print _             => true
  -- the certificate, O(accesses^2) and independent of the trip counts; `footprintOf` is not
  -- consulted, which is what lets a nest at PolyBench sizes be decided at all
  | .loop n              => Nest.nestIndepB n.sizes n.parDepth n.reads n.writes

def wfAllB : List ParProg → Bool
  | []      => true
  | s :: ss => wfB s && wfAllB ss

end

/-! ## Induction

`ParProg` nests inside `List`, so Lean's `induction` tactic refuses it for the same reason it refuses
`ParM` (`Core/ParM.lean`). The remedy is the same: one eliminator, proved once, whose `cons` case is
the step from one thread to many. -/

theorem mutualInduction
    {motive1 : ParProg → Prop} {motive2 : List ParProg → Prop}
    (hload  : ∀ r l, motive1 (.load r l))
    (hstore : ∀ l e, motive1 (.store l e))
    (hset   : ∀ r e, motive1 (.set r e))
    (hseq   : ∀ a b, motive1 a → motive1 b → motive1 (.seq a b))
    (hpar   : ∀ ss, motive2 ss → motive1 (.par ss))
    (hlabel : ∀ nm s, motive1 s → motive1 (.label nm s))
    (hloadAt  : ∀ r a e, motive1 (.loadAt r a e))
    (hstoreAt : ∀ a e v, motive1 (.storeAt a e v))
    (hifElse  : ∀ c t e, motive1 t → motive1 e → motive1 (.ifElse c t e))
    (hsynchronize : motive1 .synchronize)
    (hnil   : motive2 [])
    (hcons  : ∀ s ss, motive1 s → motive2 ss → motive2 (s :: ss))
    -- last, so adding `print` left every existing call site's goals in their original order
    (hprint : ∀ items, motive1 (.print items))
    -- and `loop` after it, for the same reason
    (hloop : ∀ n, motive1 (.loop n)) :
    (∀ s, motive1 s) ∧ (∀ ss, motive2 ss) := by
  have h1 : ∀ s, motive1 s := fun s =>
    ParProg.rec (motive_1 := motive1) (motive_2 := motive2)
      hload hstore hset (fun a b ia ib => hseq a b ia ib) (fun ss ih => hpar ss ih)
      (fun nm s ih => hlabel nm s ih) hloadAt hstoreAt
      (fun c t e it ie => hifElse c t e it ie) hsynchronize hprint hloop
      hnil (fun s ss i1 i2 => hcons s ss i1 i2) s
  refine ⟨h1, ?_⟩
  intro ss
  induction ss with
  | nil => exact hnil
  | cons s ss ih => exact hcons s ss (h1 s) ih

/-! ## The footprint is the one `accesses` computes

Proved once, for every register file and every heap. Downstream, a program's footprint is obtained
by `rfl` and its independence check by `decide`. -/

/-- **The footprint is bounded by the syntax**, at every register file and heap. Containment is all
the obligation needs: `Indep` is antitone componentwise (`Indep.of_sub`), and has no `R∩R` clause,
so widening a read set never manufactures a conflict. -- ref: `docs/block-ir.md` -/
theorem execPar_accesses_sub_all :
    (∀ s ρ σ, (accesses (execPar s ρ) σ).Sub (footprintOf s)) ∧
    (∀ ss ρ σ, (accesses (ParM.parAll (execParAll ss ρ)) σ).Sub (footprintsOf ss)) := by
  refine mutualInduction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro r l ρ σ
    refine Footprint.Sub.of_eq ?_
    show accesses (ParM.bind (readAs l (0 : Int)) _) σ = _
    rw [accesses_bind, readAs_accesses, readAs_runSeq]
    simp [accesses, Footprint.union, Footprint.empty, footprintOf]
  · intro l e ρ σ
    refine Footprint.Sub.of_eq ?_
    show accesses (ParM.bind (writeAs l _) _) σ = _
    rw [accesses_bind, writeAs_accesses, writeAs_runSeq]
    simp [accesses, Footprint.union, Footprint.empty, footprintOf]
  · intro r e ρ σ; exact Footprint.Sub.rfl' _
  · intro a b ia ib ρ σ
    show (accesses (ParM.bind (execPar a ρ) _) σ).Sub _
    rw [accesses_bind]
    exact Footprint.Sub.union (ia ρ σ) (ib _ _)
  · intro ss ih ρ σ
    show (accesses (ParM.bind (ParM.parAll (execParAll ss ρ)) _) σ).Sub _
    rw [accesses_bind]
    refine Footprint.Sub.trans (Footprint.Sub.union (ih ρ σ) (Footprint.Sub.rfl' _))
      (Footprint.Sub.of_eq ?_)
    simp [accesses, Footprint.union, Footprint.empty, footprintOf]
  · intro nm s ih ρ σ; exact ih ρ σ
  · intro r a e ρ σ
    have e1 : accesses (execPar (.loadAt r a e) ρ) σ = ⟨[a.addr (e.eval ρ)], []⟩ := by
      show accesses (ParM.bind (readAs (a.addr (e.eval ρ)) (0 : Int)) _) σ = _
      rw [accesses_bind, readAs_accesses, readAs_runSeq]
      simp [accesses, Footprint.union, Footprint.empty]
    rw [e1]
    refine ⟨fun l m => ?_, fun l m => (List.not_mem_nil m).elim⟩
    rw [List.mem_singleton] at m
    exact m ▸ a.addr_mem_cells (e.eval ρ)
  · intro a e v ρ σ
    have e1 : accesses (execPar (.storeAt a e v) ρ) σ = ⟨[], [a.addr (e.eval ρ)]⟩ := by
      show accesses (ParM.bind (writeAs (a.addr (e.eval ρ)) _) _) σ = _
      rw [accesses_bind, writeAs_accesses, writeAs_runSeq]
      simp [accesses, Footprint.union, Footprint.empty]
    rw [e1]
    refine ⟨fun l m => (List.not_mem_nil m).elim, fun l m => ?_⟩
    rw [List.mem_singleton] at m
    exact m ▸ a.addr_mem_cells (e.eval ρ)
  · intro c t e it ie ρ σ
    show (accesses (if c.eval ρ != 0 then execPar t ρ else execPar e ρ) σ).Sub _
    by_cases h : c.eval ρ != 0
    · rw [ite_eq_left h]
      exact Footprint.Sub.trans (it ρ σ) (Footprint.Sub.left _ _)
    · rw [ite_eq_right h]
      exact Footprint.Sub.trans (ie ρ σ) (Footprint.Sub.right _ _)
  · intro ρ σ; exact Footprint.Sub.rfl' _
  · intro ρ σ; exact Footprint.Sub.rfl' _
  · intro s ss i1 i2 ρ σ
    show (accesses (ParM.parAll (execPar s ρ :: execParAll ss ρ)) σ).Sub _
    rw [accesses_parAll_cons]
    exact Footprint.Sub.union (i1 ρ σ) (i2 _ _)
  · intro _ ρ σ; exact Footprint.Sub.rfl' _
  · -- the nest: `accesses_threads_sub` is the bound, proved once in `Lang/Core/Loop.lean`
    intro n ρ σ
    show (accesses (ParM.bind (ParM.parAll (n.threads ρ)) _) σ).Sub _
    rw [accesses_bind]
    refine Footprint.Sub.trans
      (Footprint.Sub.union (n.accesses_threads_sub ρ σ) (Footprint.Sub.rfl' _))
      (Footprint.Sub.of_eq ?_)
    simp [accesses, Footprint.union, Footprint.empty, footprintOf]

/-- `execPar_accesses_sub_all`, for one statement. -/
theorem execPar_accesses_sub (s : ParProg) (ρ : Regs) (σ : State) :
    (accesses (execPar s ρ) σ).Sub (footprintOf s) := execPar_accesses_sub_all.1 s ρ σ

/-- The children-block's footprint is bounded by the syntax too — `Sub` composes over `union`, so
this is the same fold. -/
theorem accessesChilds_sub : ∀ (ss : List ParProg) (ρ : Regs) (σ : State),
    (accessesChilds (ParM.childsOf (execParAll ss ρ)) σ).Sub (footprintsOf ss) := by
  intro ss
  induction ss with
  | nil => intro ρ σ; exact Footprint.Sub.rfl' _
  | cons s ss ih =>
      intro ρ σ
      show (Footprint.union (accesses (execPar s ρ) σ)
        (accessesChilds (ParM.childsOf (execParAll ss ρ)) _)).Sub _
      exact Footprint.Sub.union (execPar_accesses_sub s ρ σ) (ih ρ _)

/-- A thread's footprint is one of the list `wfB` compares. -/
theorem mem_threadFootprints : ∀ (ss : List ParProg) (t : ParProg), t ∈ ss →
    footprintOf t ∈ threadFootprints ss := by
  intro ss
  induction ss with
  | nil => intro t ht; simp at ht
  | cons u us ih =>
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (ih t ht'))

/-- Independence from every thread is independence from the block they make up. -/
theorem indep_footprintsOf {f : Footprint} : ∀ (ss : List ParProg),
    (∀ t ∈ ss, Indep f (footprintOf t)) → Indep f (footprintsOf ss) := by
  intro ss
  induction ss with
  | nil => intro _; exact Indep.empty_right f
  | cons s ss ih =>
      intro h
      exact Indep.union_right (h s (by simp)) (ih (fun t ht => h t (by simp [ht])))

/-- **The decidable check implies the real obligation, bound and all.** `wfB` compares the
*syntactic* footprints; `Indep.of_sub` carries that down to the footprints the lowered program
actually has, because `Indep` is antitone componentwise. No side condition on the addresses: a
data-dependent access contributes its whole array, which is a bound, and a bound is enough. -/
theorem indepAll_childFootprints : ∀ (ss : List ParProg), indepAllB (threadFootprints ss) = true →
    ∀ (ρ : Regs) (σ : State), IndepAll (childFootprints (ParM.childsOf (execParAll ss ρ)) σ) := by
  intro ss
  induction ss with
  | nil => intro _ ρ σ; trivial
  | cons s ss ih =>
      intro h ρ σ
      rw [threadFootprints, indepAllB, Bool.and_eq_true, List.all_eq_true] at h
      refine ⟨?_, ih h.2 ρ _⟩
      -- the head against the whole tail, then each tail element inside that
      have hblock : Indep (footprintOf s) (footprintsOf ss) :=
        indep_footprintsOf ss (fun t ht => by
          have := h.1 (footprintOf t) (mem_threadFootprints ss t ht)
          rwa [← indepB_iff])
      have hhead : Indep (accesses (execPar s ρ) σ)
          (accessesChilds (ParM.childsOf (execParAll ss ρ)) (runSeq (execPar s ρ) σ).2) :=
        Indep.of_sub (execPar_accesses_sub s ρ σ) (accessesChilds_sub ss ρ _) hblock
      intro g hg
      obtain ⟨hgr, hgw⟩ := childFootprint_subset (ParM.childsOf (execParAll ss ρ)) _ g hg
      exact Indep.mono_right hhead hgr hgw

/-- **…and on literal addresses the bound is exact.** The containment above is all soundness needs,
but this is the equality the decidable check rests on, and it still holds for the whole of the
language as it was before data-dependent addressing. -/
@[simp]
theorem execPar_accesses_all :
    (∀ s, footprintExact s = true → ∀ ρ σ, accesses (execPar s ρ) σ = footprintOf s) ∧
    (∀ ss, footprintExactAll ss = true → ∀ ρ σ,
      accesses (ParM.parAll (execParAll ss ρ)) σ = footprintsOf ss) := by
  refine mutualInduction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro r l _ ρ σ
    show accesses (ParM.bind (readAs l (0 : Int)) _) σ = _
    rw [accesses_bind, readAs_accesses, readAs_runSeq]
    simp [accesses, Footprint.union, Footprint.empty, footprintOf]
  · intro l e _ ρ σ
    show accesses (ParM.bind (writeAs l _) _) σ = _
    rw [accesses_bind, writeAs_accesses, writeAs_runSeq]
    simp [accesses, Footprint.union, Footprint.empty, footprintOf]
  · intro r e _ ρ σ; rfl
  · intro a b ia ib h ρ σ
    simp only [footprintExact, Bool.and_eq_true] at h
    show accesses (ParM.bind (execPar a ρ) _) σ = _
    rw [accesses_bind, ia h.1, ib h.2]
    rfl
  · intro ss ih h ρ σ
    show accesses (ParM.bind (ParM.parAll (execParAll ss ρ)) _) σ = _
    rw [accesses_bind, ih h]
    simp [accesses, Footprint.union, Footprint.empty, footprintOf]
  · intro nm s ih h ρ σ; exact ih h ρ σ
  · intro r a e h _ _; simp [footprintExact] at h
  · intro a e v h _ _; simp [footprintExact] at h
  · intro c t e _ _ h _ _; simp [footprintExact] at h
  · intro _ ρ σ; rfl
  · intro _ ρ σ; rfl
  · intro s ss i1 i2 h ρ σ
    simp only [footprintExactAll, Bool.and_eq_true] at h
    show accesses (ParM.parAll (execPar s ρ :: execParAll ss ρ)) σ = _
    rw [accesses_parAll_cons, i1 h.1, i2 h.2]
    rfl
  · intro _ _ ρ σ; rfl
  · intro n h _ _; simp [footprintExact] at h

/-- **The footprint is syntactic**, when the addresses are. -/
@[simp, grind .]
theorem execPar_accesses (s : ParProg) (h : footprintExact s = true) (ρ : Regs) (σ : State) :
    accesses (execPar s ρ) σ = footprintOf s := execPar_accesses_all.1 s h ρ σ

/-- The per-thread footprints `wfB` checks are the ones the lowered fork actually has. -/
@[simp, grind .]
theorem threadFootprints_eq : ∀ (ss : List ParProg), footprintExactAll ss = true →
    ∀ (ρ : Regs) (σ : State),
    childFootprints (ParM.childsOf (execParAll ss ρ)) σ = threadFootprints ss := by
  intro ss
  induction ss with
  | nil => intro _ ρ σ; rfl
  | cons s ss ih =>
      intro h ρ σ
      simp only [footprintExactAll, Bool.and_eq_true] at h
      show accesses (execPar s ρ) σ :: childFootprints (ParM.childsOf (execParAll ss ρ)) _ = _
      rw [execPar_accesses s h.1, ih h.2]
      rfl

/-! ## The obligation is decided

`wfB` is a `Bool`; this turns it into the hypothesis `par_seq_eq` wants. -/
@[simp]
theorem wfB_wellFormed_all :
    (∀ s, wfB s = true → ∀ ρ σ, WellFormed (execPar s ρ) σ) ∧
    (∀ ss, wfAllB ss = true → ∀ ρ σ, WellFormedChilds (ParM.childsOf (execParAll ss ρ)) σ) := by
  refine mutualInduction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro r l _ ρ σ; trivial
  · intro l e _ ρ σ; trivial
  · intro r e _ ρ σ; trivial
  · intro a b ia ib h ρ σ
    rw [wfB, Bool.and_eq_true] at h
    show WellFormed (ParM.bind (execPar a ρ) _) σ
    rw [WellFormed_bind]
    exact ⟨ia h.1 ρ σ, ib h.2 _ _⟩
  · intro ss ih h ρ σ
    rw [wfB, Bool.and_eq_true] at h
    show WellFormed (ParM.bind (ParM.parAll (execParAll ss ρ)) _) σ
    rw [WellFormed_bind]
    exact ⟨⟨indepAll_childFootprints ss h.1 ρ σ, ih h.2 ρ σ, trivial⟩, trivial⟩
  · intro nm s ih h ρ σ; exact ih h ρ σ
  · intro r a e _ ρ σ; trivial
  · intro a e v _ ρ σ; trivial
  · intro c t e it ie h ρ σ
    rw [wfB, Bool.and_eq_true] at h
    show WellFormed (if c.eval ρ != 0 then _ else _) σ
    by_cases hc : c.eval ρ != 0
    · rw [ite_eq_left hc]; exact it h.1 ρ σ
    · rw [ite_eq_right hc]; exact ie h.2 ρ σ
  · intro _ ρ σ; trivial
  · intro _ ρ σ; trivial
  · intro s ss i1 i2 h ρ σ
    rw [wfAllB, Bool.and_eq_true] at h
    exact ⟨i1 h.1 ρ σ, i2 h.2 ρ _⟩
  · intro _ _ ρ σ; trivial
  · -- the nest: the certificate, through `parAll_wellformed_of_indexed_rw`
    intro n h ρ σ
    simp only [wfB] at h
    show WellFormed (ParM.bind (ParM.parAll (n.threads ρ)) _) σ
    rw [WellFormed_bind]
    exact ⟨LoopNest.wellFormed_threads h ρ σ, trivial⟩

/-- **A decidable check discharges the obligation.** `wfB` is read off the syntax; this says the
lowered program is well-formed whenever it holds — provided the addresses are literal, so that the
footprints `wfB` compared are the ones the program actually has. -/
theorem wfB_wellFormed {s : ParProg} (h : wfB s = true) (ρ : Regs) (σ : State) :
    WellFormed (execPar s ρ) σ := wfB_wellFormed_all.1 s h ρ σ

/-! ## The equivalence, for the whole language -/

theorem execPar_runSeq_all :
    (∀ s ρ σ, runSeq (execPar s ρ) σ = runSeq (execSeq s ρ) σ) ∧
    (∀ ss ρ σ, runSeq (ParM.seqAll (execParAll ss ρ)) σ
             = runSeq (ParM.seqAll (execSeqAll ss ρ)) σ) := by
  refine mutualInduction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro r l ρ σ; rfl
  · intro l e ρ σ; rfl
  · intro r e ρ σ; rfl
  · intro a b ia ib ρ σ
    show runSeq (ParM.bind (execPar a ρ) _) σ = runSeq (ParM.bind (execSeq a ρ) _) σ
    rw [runSeq_bind, runSeq_bind, ia]
    exact ib _ _
  · intro ss ih ρ σ
    show runSeq (ParM.bind (ParM.parAll (execParAll ss ρ)) _) σ
       = runSeq (ParM.bind (ParM.seqAll (execSeqAll ss ρ)) _) σ
    rw [runSeq_bind, runSeq_bind, runSeq_parAll_eq_seqAll, ih]
  · intro nm s ih ρ σ; exact ih ρ σ
  · intro r a e ρ σ; rfl
  · intro a e v ρ σ; rfl
  · intro c t e it ie ρ σ
    show runSeq (if c.eval ρ != 0 then execPar t ρ else execPar e ρ) σ
       = runSeq (if c.eval ρ != 0 then execSeq t ρ else execSeq e ρ) σ
    by_cases hc : c.eval ρ != 0
    · rw [ite_eq_left hc, ite_eq_left hc]; exact it ρ σ
    · rw [ite_eq_right hc, ite_eq_right hc]; exact ie ρ σ
  · intro ρ σ; rfl
  · intro ρ σ; rfl
  · intro s ss i1 i2 ρ σ
    show runSeq (ParM.seqAll (execPar s ρ :: execParAll ss ρ)) σ
       = runSeq (ParM.seqAll (execSeq s ρ :: execSeqAll ss ρ)) σ
    simp only [ParM.seqAll, ParM.seqPair, runSeq_bind, i1]
    rw [i2]
  · intro _ ρ σ; rfl
  · -- the nest lowers to the *same* children both ways, so this is `runSeq_parAll_eq_seqAll`
    intro n ρ σ
    show runSeq (ParM.bind (ParM.parAll (n.threads ρ)) _) σ
       = runSeq (ParM.bind (ParM.seqAll (n.threads ρ)) _) σ
    rw [runSeq_bind, runSeq_bind, runSeq_parAll_eq_seqAll]

theorem wfB_wellFormedSeq_all :
    (∀ s, wfB s = true → ∀ ρ σ, WellFormed (execSeq s ρ) σ) ∧
    (∀ ss, wfAllB ss = true → ∀ ρ σ, WellFormed (ParM.seqAll (execSeqAll ss ρ)) σ) := by
  refine mutualInduction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro r l _ ρ σ; trivial
  · intro l e _ ρ σ; trivial
  · intro r e _ ρ σ; trivial
  · intro a b ia ib h ρ σ
    rw [wfB, Bool.and_eq_true] at h
    show WellFormed (ParM.bind (execSeq a ρ) _) σ
    rw [WellFormed_bind]
    exact ⟨ia h.1 ρ σ, ib h.2 _ _⟩
  · intro ss ih h ρ σ
    rw [wfB, Bool.and_eq_true] at h
    show WellFormed (ParM.bind (ParM.seqAll (execSeqAll ss ρ)) _) σ
    rw [WellFormed_bind]
    exact ⟨ih h.2 ρ σ, trivial⟩
  · intro nm s ih h ρ σ; exact ih h ρ σ
  · intro r a e _ ρ σ; trivial
  · intro a e v _ ρ σ; trivial
  · intro c t e it ie h ρ σ
    rw [wfB, Bool.and_eq_true] at h
    show WellFormed (if c.eval ρ != 0 then _ else _) σ
    by_cases hc : c.eval ρ != 0
    · rw [ite_eq_left hc]; exact it h.1 ρ σ
    · rw [ite_eq_right hc]; exact ie h.2 ρ σ
  · intro _ ρ σ; trivial
  · intro _ ρ σ; trivial
  · intro s ss i1 i2 h ρ σ
    rw [wfAllB, Bool.and_eq_true] at h
    show WellFormed (ParM.bind (ParM.seqPair (execSeq s ρ) (ParM.seqAll (execSeqAll ss ρ))) _) σ
    grind
  · intro _ _ ρ σ; trivial
  · intro n _ ρ σ
    show WellFormed (ParM.bind (ParM.seqAll (n.threads ρ)) _) σ
    rw [WellFormed_bind]
    exact ⟨n.wellFormed_seqAll ρ σ, trivial⟩

/-- **Write the program, check one `Bool`, get the theorem.** If every `parallel` block in `s` has
pairwise-independent threads and every address is a literal — one decidable check on the syntax —
then running it with all threads at once reaches exactly the outcomes running them in order does,
under every schedule.

Data-dependent addressing costs *precision*, not soundness: `A[e]`'s syntactic footprint is all of
`A`, so two threads indexing the same array are rejected even when their indices never meet. When
that matters, the exact per-heap check is `wellFormedB` (`Search/RaceSearch.lean`), which is both
sound and complete. -/
-- ANCHOR: site-wfb-par-seq-eq
@[simp, grind .]
theorem par_seq_eq {s : ParProg} (h : wfB s = true) (ρ : Regs) (σ : State) :
    ParSeqEq (execPar s ρ) (execSeq s ρ) σ := by
  exact parSeqEq_of_runSeq_eq _ _ σ (wfB_wellFormed h ρ σ)
    (wfB_wellFormedSeq_all.1 s h ρ σ) (execPar_runSeq_all.1 s ρ σ)
-- ANCHOR_END: site-wfb-par-seq-eq

/-! ## Composing a pipeline out of proved pieces

A pipeline is a `;`-chain of phases, and `wfB` on `seq`/`label` is definitional, so its obligation
is the *conjunction* of its phases': `wfB_of_parFree` for a phase with no `parallel` block, the
kernel's own lemma for a kernel, then `wfB_block` and `par_seq_eq`. -/

/-- **Removing the prints changes neither interpreter.** So "the proofs ignore those lines" is an
equation and not a convention: `par_seq_eq` about `dropPrints s` and about `s` are the same theorem.
The `seq` case is where the work is — a print on either side of a bind is an identity,
`bind_pure_left` and `bind_pure_right`. -/
theorem execPar_dropPrints_all :
    (∀ (s : ParProg) (ρ : Regs), execPar (dropPrints s) ρ = execPar s ρ) ∧
    (∀ (ss : List ParProg) (ρ : Regs), execParAll (dropPrintsAll ss) ρ = execParAll ss ρ) := by
  refine mutualInduction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro r l ρ; rfl
  · intro l e ρ; rfl
  · intro r e ρ; rfl
  · -- the four ways a chain can lose its prints
    intro a b ia ib ρ
    simp only [dropPrints] at ia ib ⊢
    show execPar ((dropPrints? (.seq a b)).getD _) ρ = ParM.bind (execPar a ρ) _
    rw [dropPrints?]
    cases ha : dropPrints? a <;> cases hb : dropPrints? b <;>
      simp only [ha, hb, Option.getD] at ia ib ⊢ <;>
      simp only [← ia, ← ib, execPar, ParM.bind_pure_left, ParM.bind_pure_right]
  · intro ss ih ρ
    show execPar (.par (dropPrintsAll ss)) ρ = _
    simp only [execPar, ih]
  · intro nm t ih ρ
    simp only [dropPrints] at ih ⊢
    show execPar ((dropPrints? t).map _ |>.getD _) ρ = execPar t ρ
    cases h : dropPrints? t <;> simp only [h, Option.map, Option.getD] at ih ⊢ <;>
      rw [← ih] <;> rfl
  · intro r a e ρ; rfl
  · intro a e v ρ; rfl
  · intro c t e it ie ρ
    simp only [dropPrints] at it ie ⊢
    show execPar (.ifElse c _ _) ρ = execPar (.ifElse c t e) ρ
    simp only [execPar, it, ie]
  · intro ρ; rfl
  · intro ρ; rfl
  · intro s ss i1 i2 ρ
    simp only [dropPrints] at i1
    simp only [dropPrintsAll, execParAll, i1, i2]
  · intro _ ρ; rfl
  · intro n ρ; rfl

theorem execPar_dropPrints (s : ParProg) (ρ : Regs) : execPar (dropPrints s) ρ = execPar s ρ :=
  execPar_dropPrints_all.1 s ρ

/-- The same, for the sequential reading. -/
theorem execSeq_dropPrints_all :
    (∀ (s : ParProg) (ρ : Regs), execSeq (dropPrints s) ρ = execSeq s ρ) ∧
    (∀ (ss : List ParProg) (ρ : Regs), execSeqAll (dropPrintsAll ss) ρ = execSeqAll ss ρ) := by
  refine mutualInduction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro r l ρ; rfl
  · intro l e ρ; rfl
  · intro r e ρ; rfl
  · -- the four ways a chain can lose its prints
    intro a b ia ib ρ
    simp only [dropPrints] at ia ib ⊢
    show execSeq ((dropPrints? (.seq a b)).getD _) ρ = ParM.bind (execSeq a ρ) _
    rw [dropPrints?]
    cases ha : dropPrints? a <;> cases hb : dropPrints? b <;>
      simp only [ha, hb, Option.getD] at ia ib ⊢ <;>
      simp only [← ia, ← ib, execSeq, ParM.bind_pure_left, ParM.bind_pure_right]
  · intro ss ih ρ
    show execSeq (.par (dropPrintsAll ss)) ρ = _
    simp only [execSeq, ih]
  · intro nm t ih ρ
    simp only [dropPrints] at ih ⊢
    show execSeq ((dropPrints? t).map _ |>.getD _) ρ = execSeq t ρ
    cases h : dropPrints? t <;> simp only [h, Option.map, Option.getD] at ih ⊢ <;>
      rw [← ih] <;> rfl
  · intro r a e ρ; rfl
  · intro a e v ρ; rfl
  · intro c t e it ie ρ
    simp only [dropPrints] at it ie ⊢
    show execSeq (.ifElse c _ _) ρ = execSeq (.ifElse c t e) ρ
    simp only [execSeq, it, ie]
  · intro ρ; rfl
  · intro ρ; rfl
  · intro s ss i1 i2 ρ
    simp only [dropPrints] at i1
    simp only [dropPrintsAll, execSeqAll, i1, i2]
  · intro _ ρ; rfl
  · intro n ρ; rfl

theorem execSeq_dropPrints (s : ParProg) (ρ : Regs) : execSeq (dropPrints s) ρ = execSeq s ρ :=
  execSeq_dropPrints_all.1 s ρ

/-- **The equivalence is the same statement with or without the prints.** Which is what licenses
`Examples/Language/Stripe.lean` to gate a hand-written program against a file that prints, and what
makes "erased" precise. -/
theorem parSeqEq_dropPrints_iff (s : ParProg) (ρ : Regs) (σ : State) :
    ParSeqEq (execPar (dropPrints s) ρ) (execSeq (dropPrints s) ρ) σ
      ↔ ParSeqEq (execPar s ρ) (execSeq s ρ) σ := by
  rw [execPar_dropPrints, execSeq_dropPrints]

/-- Whether a program contains a `parallel` block at all. -/
def hasPar : ParProg → Bool
  | .load _ _  => false
  | .store _ _ => false
  | .set _ _   => false
  | .seq a b   => hasPar a || hasPar b
  | .par _     => true
  | .label _ s => hasPar s
  | .loadAt _ _ _  => false
  | .storeAt _ _ _ => false
  | .ifElse _ t e  => hasPar t || hasPar e
  | .synchronize         => false
  | .print _             => false
  -- a nest forks over its outermost levels, so it is a parallel block
  | .loop _              => true

/-- **A program with no `parallel` block is trivially well-formed.** There is nothing to check,
because there is nothing running concurrently — the parallel and sequential readings coincide. -/
@[simp, grind .]
theorem wfB_of_parFree : ∀ s : ParProg, hasPar s = false → wfB s = true := by
  intro s
  induction s using ParProg.rec
    (motive_2 := fun ss => (ss.any hasPar) = false → wfAllB ss = true) with
  | load r l => intro _; rfl
  | store l e => intro _; rfl
  | set r e => intro _; rfl
  | seq a b ia ib =>
      intro h
      rw [hasPar, Bool.or_eq_false_iff] at h
      rw [wfB, Bool.and_eq_true]
      exact ⟨ia h.1, ib h.2⟩
  | par ss _ => intro h; rw [hasPar] at h; exact absurd h (by simp)
  | label nm t ih => intro h; rw [hasPar] at h; exact ih h
  | loadAt r a e => intro _; rfl
  | storeAt a e v => intro _; rfl
  | ifElse c t e it ie =>
      intro h
      rw [hasPar, Bool.or_eq_false_iff] at h
      rw [wfB, Bool.and_eq_true]
      exact ⟨it h.1, ie h.2⟩
  | synchronize => intro _; rfl
  | print items => intro _; rfl
  | loop n => intro h; rw [hasPar] at h; exact absurd h (by simp)
  | nil => rfl
  | cons t ts i1 i2 =>
      rename_i h
      simp only [List.any_cons, Bool.or_eq_false_iff] at h
      rw [wfAllB, Bool.and_eq_true]
      exact ⟨i1 h.1, i2 h.2⟩

/-- A chain has literal addresses when each of its phases does — the `footprintExact` analogue of
`wfB_block`. -/
@[simp, grind .]
theorem footprintExact_block : ∀ ss : List ParProg, (∀ s ∈ ss, footprintExact s = true) →
    footprintExact (block ss) = true := by
  intro ss
  induction ss with
  | nil => intro _; rfl
  | cons s ss ih =>
      intro h
      match ss with
      | []      => exact h s (by simp)
      | t :: ts =>
          show footprintExact (.seq s (block (t :: ts))) = true
          rw [footprintExact, Bool.and_eq_true]
          exact ⟨h s (by simp), ih (fun x hx => h x (by simp [hx]))⟩

@[simp] theorem wfB_seq (a b : ParProg) : wfB (.seq a b) = (wfB a && wfB b) := rfl
@[simp] theorem wfB_label (nm : String) (s : ParProg) : wfB (.label nm s) = wfB s := rfl

/-- **A chain is well-formed when each of its phases is.** The pipeline lemma: prove the kernels,
get the program. -/
@[simp, grind .]
theorem wfB_block : ∀ ss : List ParProg, (∀ s ∈ ss, wfB s = true) → wfB (block ss) = true := by
  intro ss
  induction ss with
  | nil => intro _; rfl
  | cons t ts ih =>
      intro h
      cases ts with
      | nil => exact h t List.mem_cons_self
      | cons u us =>
          show wfB (.seq t (block (u :: us))) = true
          rw [wfB_seq, Bool.and_eq_true]
          exact ⟨h t List.mem_cons_self,
                 ih (fun x hx => h x (List.mem_cons_of_mem t hx))⟩

/-- **Par = Seq for a whole pipeline, from its phases.** Supply, for each phase, either "it has no
`parallel` block" or "it is a kernel whose obligation is proved"; the pipeline's equivalence
follows with nothing else to do. -/
@[simp, grind .]
theorem pipeline_par_seq_eq (phases : List ParProg)
    (h : ∀ s ∈ phases, wfB s = true) (ρ : Regs) (σ : State) :
    ParSeqEq (execPar (block phases) ρ) (execSeq (block phases) ρ) σ :=
  par_seq_eq (wfB_block phases h) ρ σ
end ParProg

end Paralever.Lang
