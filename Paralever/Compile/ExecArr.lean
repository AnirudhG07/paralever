import Paralever.Compile.Exec

/-! # `execArr` — the same run, on a flat array

`Compile/Exec.lean` runs a program with `State = Loc → Val`, where `update` prepends a closure
frame. A write is O(1) and so is a read of a cell near the top, but a read of a cell that later
writes have buried costs one step per frame — which is matmul's shape, since `A` and `B` are never
written and every thread reads them past all of its own writes to `C`.

This module runs the same program on an `Array Val`, where a write is an in-place store and a read
is an index. `execArr_eq_execTask` is what makes it usable rather than merely fast: the two
executors agree on every program, racy or not, well-formed or not.

Nothing in `Core/` or `Theory/` imports `Compile/`, so none of the theory is touched by any of this.
Rationale: `docs/scale.md` § What would fix the rest. -/

namespace Paralever

/-! ## The array heap

One field, so Lean erases the wrapper and `Array.set!` updates in place whenever the array is
uniquely referenced. -/

structure AState where
  cells : Array Val
  deriving Inhabited

namespace AState

/-- A heap of `n` cells, all `.int 0` — the value `Layout` gives an address no buffer claims. -/
def zeros (n : Nat) : AState := ⟨Array.replicate n (.int 0)⟩

/-- Reading past the end gives `.int 0`, which is what makes `toState` agree with the function heap
on reads with no bound to assume. -/
def get (a : AState) (l : Loc) : Val := a.cells[l]?.getD (.int 0)

/-- Writing past the end is the one thing an array cannot do, which is why the correctness theorem
below carries a hypothesis about writes and none about reads. `setIfInBounds` rather than `set!`:
an out-of-range write is dropped rather than a panic, so a program that escapes its `Layout` gives a
wrong answer the theorem's hypothesis excludes instead of killing the process. -/
def set (a : AState) (l : Loc) (v : Val) : AState := ⟨a.cells.setIfInBounds l v⟩

def size (a : AState) : Nat := a.cells.size

/-- **The abstraction function.** Everything about `execArr` is proved through this and nothing
else. -/
def toState (a : AState) : State := fun l => a.get l

@[simp] theorem toState_apply (a : AState) (l : Loc) : a.toState l = a.get l := rfl

@[simp] theorem get_set_same (a : AState) (l : Loc) (v : Val) (h : l < a.size) :
    (a.set l v).get l = v := by
  simp only [get, set, size] at *
  rw [Array.getElem?_setIfInBounds_self_of_lt h]; rfl

@[simp] theorem get_set_other (a : AState) (l k : Loc) (v : Val) (h : k ≠ l) :
    (a.set l v).get k = a.get k := by
  simp only [get, set]
  rw [Array.getElem?_setIfInBounds_ne (Ne.symm h)]

@[simp] theorem size_set (a : AState) (l : Loc) (v : Val) : (a.set l v).size = a.size := by
  simp [set, size]

/-- The bridge: an array write is a function-heap update. -/
theorem toState_set (a : AState) (l : Loc) (v : Val) (h : l < a.size) :
    (a.set l v).toState = a.toState.update l v := by
  funext k
  by_cases hk : k = l
  · subst hk; simp [State.update, get_set_same a k v h]
  · simp [State.update, hk, get_set_other a l k v hk]

end AState

/-! ## The merge

Built with `Array.ofFn` rather than a fold, so one cell of the result is one `if` and the
correspondence with `joinStates` is an equation rather than an induction over an accumulator. -/

/-- Merge `child` over `rest`, judged against `base`: a cell the child changed wins. -/
def mergeInto (base child rest : AState) : AState :=
  ⟨Array.ofFn (n := base.size) fun i =>
      if child.get i.val == base.get i.val then rest.get i.val else child.get i.val⟩

/-- **The N-ary merge.** Folded *right*, so the first child that differs from the base wins at each
cell — which is what `joinStates` does, and is why `toState_joinArr` needs no independence
hypothesis. -/
def joinArr (base : AState) : List AState → AState
  | []      => base
  | c :: cs => mergeInto base c (joinArr base cs)

@[simp] theorem size_mergeInto (base child rest : AState) :
    (mergeInto base child rest).size = base.size := by
  simp [mergeInto, AState.size]

@[simp] theorem get_mergeInto (base child rest : AState) (l : Loc) (h : l < base.size) :
    (mergeInto base child rest).get l =
      if child.get l == base.get l then rest.get l else child.get l := by
  simp only [mergeInto, AState.get]
  rw [Array.getElem?_eq_getElem (by simpa using h)]
  simp

@[simp] theorem size_joinArr (base : AState) (cs : List AState) :
    (joinArr base cs).size = base.size := by
  cases cs <;> simp [joinArr]

theorem AState.get_oob (a : AState) (l : Loc) (h : a.size ≤ l) : a.get l = .int 0 := by
  simp only [get]
  rw [Array.getElem?_eq_none (by simpa [AState.size] using h)]
  rfl

/-- **The merge is `joinAllStates`.** No independence hypothesis: the right fold makes the first
differing child win on both sides, which is a definitional match rather than a consequence. -/
theorem toState_joinArr (base : AState) (cs : List AState)
    (hsz : ∀ c ∈ cs, c.size = base.size) :
    (joinArr base cs).toState = joinAllStates base.toState (cs.map AState.toState) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      have hc : c.size = base.size := hsz c (by simp)
      have ih' := ih (fun x hx => hsz x (by simp [hx]))
      funext l
      simp only [joinArr, List.map_cons, joinAllStates, joinStates, AState.toState_apply]
      by_cases h : l < base.size
      · rw [get_mergeInto base c _ l h]
        by_cases hv : c.get l = base.get l
        · simp [hv, ← ih']
        · simp [hv]
      · have hb : base.size ≤ l := Nat.le_of_not_lt h
        have h1 : c.get l = (.int 0 : Val) := AState.get_oob c l (by omega)
        have h2 : base.get l = (.int 0 : Val) := AState.get_oob base l hb
        have h4 : (mergeInto base c (joinArr base cs)).get l = (.int 0 : Val) :=
          AState.get_oob _ l (by simpa using hb)
        have h3 : joinAllStates base.toState (cs.map AState.toState) l = (.int 0 : Val) := by
          rw [← ih']; exact AState.get_oob _ l (by simpa using hb)
        simp [h1, h2, h3, h4]

/-! ## The executor

Mirrors `execTask` constructor for constructor. The `write` case consumes `σ` exactly once, which
is what lets `setIfInBounds` update in place: the array is uniquely referenced along a thread's run,
so no copy happens after the first. -/

/-- One task per child, with the result types still static — `Results`' shape, one level up.

This spine exists for a compiler reason rather than a semantic one. Spawning and joining in a
single pass over `Childs` puts the `Task.spawn` and the matching `Task.get` in one branch of a
match on an indexed family, and the spawn then happens only when its own `get` is about to block:
measured, 16 children ran at 99% CPU and the thread count was flat from 1 to 32. Splitting the pass
in two makes the spawn a *value the recursion returns*, which cannot be deferred past the join. -/
def ATaskChilds : List Type → Type
  | []      => Unit
  | α :: αs => Task (α × AState) × ATaskChilds αs

/-- Phase two: every child waited on, nothing spawned. -/
def collectArrChilds : {αs : List Type} → ATaskChilds αs → Results αs × List AState
  | [],     _       => ((), [])
  | _ :: _, (t, ts) =>
      let r := t.get
      let rest := collectArrChilds ts
      ((r.1, rest.1), r.2 :: rest.2)

mutual

def execArr {α : Type} : ParM α → AState → α × AState
  | .pure a,      σ => (a, σ)
  | .read l k,    σ => execArr (k (σ.get l)) σ
  | .write l v k, σ => execArr (k ()) (σ.set l v)
  | .par cs k,    σ =>
      let r := collectArrChilds (spawnArrChilds cs σ)
      execArr (k r.1) (joinArr σ r.2)

/-- Phase one: every child spawned, nothing waited on. A child shares `σ`'s array until its first
write, which copies once; after that the child owns its heap at refcount one. -/
def spawnArrChilds : {αs : List Type} → Childs ParM αs → AState → ATaskChilds αs
  | _, .nil,       _ => ()
  | _, .cons p ps, σ => (Task.spawn fun _ => execArr p σ, spawnArrChilds ps σ)

end

/-- All N children in flight, then all N joined. -/
def execArrChilds {αs : List Type} (cs : Childs ParM αs) (σ : AState) :
    Results αs × List AState :=
  collectArrChilds (spawnArrChilds cs σ)

/-- Run and read the heap back as a `State`, which is the form every theorem is stated in. -/
def runArr {α : Type} (p : ParM α) (a : AState) : α × State :=
  let r := execArr p a
  (r.1, r.2.toState)

/-! ## The join, in time proportional to the writes

`joinArr` compares every cell of the heap once per child, so a program with `f` forks of width `w`
over a heap of `c` cells pays `O(f · w · c)` in joins however little each thread does. Measured on
`Bench/Chaos.lean`'s thousand-line program, that term *is* the parallel run: `auto ms` tracks
`forks × cells` to within a few percent at every size, and because it grows with the heap while the
work saved grows with the threads, the parallel program never catches the sequential one.

`joinDelta` pays for the writes instead. Two facts make it exact rather than approximate:

* `joinAllStates` takes the **first** child whose value at a cell differs from the base, so the head
  child's heap is already the answer at every cell the tail children never wrote;
* a cell no child wrote holds the base's value in every child, so the fold returns the base there —
  which is what the head child's heap holds too.

The result is therefore the head child's heap, patched at the cells the *tail* wrote, and nothing
else is read or written. The write list may carry duplicates and cells stored back to their old
value; neither changes the answer, because the patch still compares values rather than trusting the
list. -/

/-- A child's heap together with the cells it stored into, newest first. -/
structure ADelta where
  heap  : AState
  dirty : List Loc

/-- The first child whose value at `l` differs from the base, else the base's own: `joinAllStates`
at a single cell, with the heaps already in hand. -/
def pickAt (base : AState) (l : Loc) : List AState → Val
  | []      => base.get l
  | c :: cs => if c.get l == base.get l then pickAt base l cs else c.get l

/-- The join, touching only the cells the tail children wrote. -/
def joinDelta (base : AState) : List ADelta → AState
  | []      => base
  | c :: cs =>
      (cs.flatMap ADelta.dirty).foldl
        (fun a l =>
          if c.heap.get l == base.get l then a.set l (pickAt base l (cs.map ADelta.heap)) else a)
        c.heap

/-- One task per child, carrying the write list back with the heap. -/
def DeltaChilds : List Type → Type
  | []      => Unit
  | α :: αs => Task (α × ADelta) × DeltaChilds αs

def collectDelta : {αs : List Type} → DeltaChilds αs → Results αs × List ADelta
  | [],     _       => ((), [])
  | _ :: _, (t, ts) =>
      let r := t.get
      let rest := collectDelta ts
      ((r.1, rest.1), r.2 :: rest.2)

/-! `execArr` with a write list threaded through it. A child is spawned with an empty list, so what
it hands back is exactly what it stored; a fork adds its children's lists to its own, so an outer
join sees the writes made inside an inner one. -/

mutual

def execArrD {α : Type} : ParM α → AState → List Loc → α × ADelta
  | .pure a,      σ, d => (a, ⟨σ, d⟩)
  | .read l k,    σ, d => execArrD (k (σ.get l)) σ d
  | .write l v k, σ, d => execArrD (k ()) (σ.set l v) (l :: d)
  | .par cs k,    σ, d =>
      let r := collectDelta (spawnDelta cs σ)
      execArrD (k r.1) (joinDelta σ r.2) (r.2.flatMap ADelta.dirty ++ d)

def spawnDelta : {αs : List Type} → Childs ParM αs → AState → DeltaChilds αs
  | _, .nil,       _ => ()
  | _, .cons p ps, σ => (Task.spawn fun _ => execArrD p σ [], spawnDelta ps σ)

end

/-- Run and read the heap back as a `State`. -/
def runArrD {α : Type} (p : ParM α) (a : AState) : α × State :=
  let r := execArrD p a []
  (r.1, r.2.heap.toState)

end Paralever
