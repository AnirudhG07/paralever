/-! # Facts about real `Task`-based parallelism

`Task.mapList` (`Init/Task.lean`) is the real fork-join combinator Lean ships — spawn one `Task`
per item, combine when all finish — and has zero lemmas anywhere in core, Batteries, or Mathlib,
including the one fact you need to reason about it (`docs/theory.md`, `papers.md`). Its internal
recursive helper is compiler-generated and inaccessible by name, so instead of fighting to alias
it, `combineTasks` here is a from-scratch definition with the *identical* three-case algorithm
(spawn on empty, `.map` on a singleton, `.bind` to recurse otherwise) — genuinely `Task.spawn`
under the hood, fully our own to reason about.

This is the "second model" from the discussion in the session: instead of `ParM`'s abstract
interleaving semantics (proved correct once, for *any* schedule, gated on `WellFormed`), this
model writes the parallel algorithm directly against Lean's real `Task` and proves it correct by
straight computation — no `WellFormed`, no `Indep`, no schedule quantification. It is strictly
**less powerful**: `Task.spawn`/`.map`/`.bind` are `rfl`-trivial in the logic
(`docs/program-model.md`), so this method is *blind* to interference — it can prove a race-free
program correct, but it cannot even state what a race would look like, let alone detect one. It
only works because there is nothing to race on: chunks close over a fully materialized, immutable
input value, never a shared mutable heap. In exchange it is complete and "calculatable" — every
instance below is discharged by literal computation (`rfl`/`decide`/`simp`), no per-program
independence proof to construct. -/

@[simp, grind .]
def combineTasks {α β : Type} (f : List α → β) (prio : Task.Priority) (sync : Bool) :
    List (Task α) → List α → Task β
  | [], as => if sync then .pure (f as.reverse) else Task.spawn (prio := prio) fun _ => f as.reverse
  | [t], as => t.map (fun a => f (a :: as).reverse) prio sync
  | t :: ts, as => t.bind (fun a => combineTasks f prio sync ts (a :: as)) prio sync

/-- General accumulator form — needed for the induction; `combineTasks_eq` below is the clean
`as = []` corollary actually used. -/
@[simp, grind .]
theorem combineTasks_eq_acc {α β : Type} (f : List α → β) (prio : Task.Priority) (sync : Bool) :
    ∀ (ts : List (Task α)) (as : List α),
    (combineTasks f prio sync ts as).get = f (as.reverse ++ ts.map Task.get) := by
  intro ts
  induction ts with
  | nil => intro as; unfold combineTasks; split <;> simp [Task.spawn]
  | cons t ts ih =>
      intro as
      cases ts with
      | nil => unfold combineTasks; simp [Task.map]
      | cons t' ts' =>
          grind [Task.bind, combineTasks]

/-- `Task.mapList_eq`'s content, for `combineTasks` in place of the inaccessible stdlib internals:
the parallel combine's result is exactly `f` applied to the list of each task's own result. Proved
by computation, not by any independence argument — this is the "lesser powerful" method's whole
proof obligation, and it is always this cheap. -/
@[simp, grind .]
theorem combineTasks_eq {α β : Type} (f : List α → β) (ts : List (Task α))
    (prio : Task.Priority := .default) (sync : Bool := false) :
    (combineTasks f prio sync ts []).get = f (ts.map Task.get) := by
  simp only [combineTasks_eq_acc, List.reverse_nil, List.nil_append]

/-- **Spawn `n` independent pure computations as real `Task`s, combine.** The one thing every
`_Task.lean` example (`SumArrayTask`, `SortTask`) does by hand, generalized so a new example only
supplies its `n` closures, not another `combineTasks` call site.

`SortTask.lean`'s subtlety applies here too, unconditionally: `works` must each only *read* shared
data and *return* a value — never write to a shared mutable `Array`/`IO.Ref`, since a `Ref`'s
read-modify-write is not atomic against other real OS threads even at disjoint indices. Any
assembly into a mutable structure happens sequentially, after `.get`, in the caller. -/
def parTasks {α β : Type} (f : List α → β) (works : List (Unit → α)) : Task β :=
  combineTasks f .default false (works.map Task.spawn) []

/-- Correctness by computation, unconditional on `works` — no `WellFormed`, no `Indep`, because
`parTasks` never touches shared mutable state for those to protect. -/
theorem parTasks_eq {α β : Type} (f : List α → β) (works : List (Unit → α)) :
    (parTasks f works).get = f (works.map (fun w => w ())) := by
  unfold parTasks
  rw [combineTasks_eq]
  congr 1
  rw [List.map_map]
  rfl
