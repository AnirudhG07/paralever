import Paralever.Lib.Loop
import Paralever.Lib.OpaqueOp

/-! # One task per item: assigning a list to threads

The shape almost every data-parallel program has, and the one the `Nat`-indexed validator in
`Lib/Loop.lean` makes you encode by hand: you hold a list — array cells, chunks of a
chunk plan, `(i,j)` grid coordinates — and you want one thread per element, with the same body
applied to each.

`parEach xs body` is that, as one `par` node with `xs.length` children. The validator
(`parEach_par_seq_eq`) is `parAll_par_seq_eq_of_indexed_rw` at key type `α` rather than `Nat`, so
nothing is linearised and no index arithmetic appears: two tasks are distinguished because they sit
at distinct *items*, not because `i ≠ j`.

Reads and writes are bounded separately, as everywhere else — tasks may share reads freely
(`broadcastPar` below is the extreme case, where every task reads the whole input).

Rationale: `docs/access.md`; the key-generic validator is `Lib/Loop.lean`. -/

namespace Paralever
open Paralever.Loop

variable {α β : Type}

/-! ### One task per item -/

/-- One task per element of `xs`, all forked at once. A single `par` node with `xs.length`
children. -/
def parEach (xs : List α) (body : α → ParM β) : ParM (List β) := ParM.parAll (xs.map body)

/-- The sequential counterpart: the same tasks, left to right. -/
def seqEach (xs : List α) (body : α → ParM β) : ParM (List β) := ParM.seqAll (xs.map body)

@[simp] theorem parEach_nil (body : α → ParM β) :
    parEach ([] : List α) body = ParM.parAll [] := rfl

@[simp] theorem parEach_cons (x : α) (xs : List α) (body : α → ParM β) :
    parEach (x :: xs) body = ParM.parAll (body x :: xs.map body) := rfl

/-- **One task per item is equivalent to one after another.** Say where each task's reads land and
where its writes land; then check two things between *distinct items*: their writes do not collide,
and one's writes do not meet another's reads. There is no read/read condition, so tasks may read the
same cells freely.

`hnodup` is what makes "distinct items" the right notion: with a repeated element the same task
would be forked twice, and `Pw` could not tell the copies apart. -/
theorem parEach_par_seq_eq (xs : List α) (body : α → ParM β)
    (Pr Pw : α → Loc → Prop) (hnodup : xs.Nodup)
    (hwf : ∀ x ∈ xs, ∀ σ, WellFormed (body x) σ)
    (hR : ∀ x ∈ xs, ∀ σ, ReadsWithin (accesses (body x) σ) (Pr x))
    (hW : ∀ x ∈ xs, ∀ σ, WritesWithin (accesses (body x) σ) (Pw x))
    (hww : ∀ x y, x ∈ xs → y ∈ xs → x ≠ y → ∀ l, Pw x l → Pw y l → False)
    (hwr : ∀ x y, x ∈ xs → y ∈ xs → x ≠ y → ∀ l, Pw x l → Pr y l → False) (σ : State) :
    ParSeqEq (parEach xs body) (seqEach xs body) σ :=
  parAll_par_seq_eq_of_indexed_rw xs body Pr Pw hnodup hwf hR hW hww hwr σ

/-- The common case: one region per task covering both its reads and its writes, so a single
disjointness fact suffices. Use `parEach_par_seq_eq` when tasks share reads. -/
theorem parEach_par_seq_eq_of_regions (xs : List α) (body : α → ParM β)
    (P : α → Loc → Prop) (hnodup : xs.Nodup)
    (hwf : ∀ x ∈ xs, ∀ σ, WellFormed (body x) σ)
    (hbody : ∀ x ∈ xs, ∀ σ, FootprintWithin (accesses (body x) σ) (P x))
    (hdisj : ∀ x y, x ∈ xs → y ∈ xs → x ≠ y → ∀ l, P x l → P y l → False) (σ : State) :
    ParSeqEq (parEach xs body) (seqEach xs body) σ :=
  parAll_par_seq_eq_of_indexed_footprint xs body P hnodup hwf hbody hdisj σ

/-! ### Shared input, private output

The pattern a GPU kernel usually has: hand every thread the *same* input region and let it write one
cell of its own. Reads overlap completely, which is exactly what Bernstein permits and
`∗`-disjointness does not. Only two facts are left to check, both about the output map. -/

/-- Read every cell of `src`, then write `f x vs` to `out x`. The task assigned to item `x`. -/
def readThenWrite (src : List Loc) (f : α → List Val → Val) (out : α → Loc) (x : α) : ParM Unit :=
  ParM.bind (readAll src) (fun vs => .write (out x) (f x vs) .pure)

@[simp, grind .]
theorem readThenWrite_accesses (src : List Loc) (f : α → List Val → Val) (out : α → Loc)
    (x : α) (σ : State) :
    accesses (readThenWrite src f out x) σ = ⟨src, [out x]⟩ := by
  simp only [readThenWrite, accesses_bind, readAll_accesses, readAll_runSeq]
  simp [accesses, Footprint.union, Footprint.empty]

@[simp, grind .]
theorem readThenWrite_wellformed (src : List Loc) (f : α → List Val → Val) (out : α → Loc)
    (x : α) (σ : State) : WellFormed (readThenWrite src f out x) σ := by
  simp only [readThenWrite]
  rw [WellFormed_bind]
  exact ⟨readAll_wellformed src σ, trivial⟩

/-- Every task reads the whole of `src`; task `x` writes `out x`. -/
def broadcastPar (xs : List α) (src : List Loc) (f : α → List Val → Val) (out : α → Loc) :
    ParM (List Unit) := parEach xs (readThenWrite src f out)

/-- Sequential counterpart of `broadcastPar`. -/
def broadcastSeq (xs : List α) (src : List Loc) (f : α → List Val → Val) (out : α → Loc) :
    ParM (List Unit) := seqEach xs (readThenWrite src f out)

/-- **Broadcast an input to every task.** Two obligations, both about the output map: distinct tasks
write distinct cells, and no task writes into the shared input. Nothing is required of `src`, of
`f`, or of how much the tasks' reads overlap --- they overlap totally, by construction. -/
theorem broadcast_par_seq_eq (xs : List α) (src : List Loc) (f : α → List Val → Val)
    (out : α → Loc) (hnodup : xs.Nodup)
    (hinj : ∀ x y, x ∈ xs → y ∈ xs → x ≠ y → out x ≠ out y)
    (hout : ∀ x ∈ xs, out x ∉ src) (σ : State) :
    ParSeqEq (broadcastPar xs src f out) (broadcastSeq xs src f out) σ := by
  refine parEach_par_seq_eq xs (readThenWrite src f out)
    (fun _ l => l ∈ src) (fun x l => l = out x) hnodup
    (fun x _ σ' => readThenWrite_wellformed src f out x σ') ?_ ?_ ?_ ?_ σ
  · intro x _ σ' l hl; rw [readThenWrite_accesses] at hl; exact hl
  · intro x _ σ' l hl
    rw [readThenWrite_accesses] at hl
    simpa using hl
  · intro x y hx hy hxy l hlx hly
    exact hinj x y hx hy hxy (hlx ▸ hly ▸ rfl)
  · intro x y hx _ _ l hlx hly
    exact hout x hx (hlx ▸ hly)

end Paralever
