
/-- Fork-join over a list of running `Task`s: wait for each, then apply `f` to all the results in
order. `as` is the reversed accumulator of results collected so far, so callers start it at `[]`.

Three cases, matching `Task.mapList`: spawn the final `f` when nothing is left, `.map` the last task,
`.bind` to recurse otherwise. `sync := true` skips the spawn and combines on the calling thread. -/
@[simp, grind .]
def combineTasks {α β : Type} (f : List α → β) (prio : Task.Priority) (sync : Bool) :
    List (Task α) → List α → Task β
  | [], as => if sync then .pure (f as.reverse) else Task.spawn (prio := prio) fun _ => f as.reverse
  | [t], as => t.map (fun a => f (a :: as).reverse) prio sync
  | t :: ts, as => t.bind (fun a => combineTasks f prio sync ts (a :: as)) prio sync

/-- `combineTasks`'s result with an arbitrary accumulator: `f` applied to the accumulated results
followed by each remaining task's own. The induction-strength form; `combineTasks_eq` is the `as = []`
corollary callers use. -/
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

/-- The parallel combine returns exactly `f` applied to the list of each task's result. The lemma
`Task.mapList` is missing, supplied for `combineTasks`.

Proved by computation; no independence argument appears, and none could — `Task.spawn`/`.map`/`.bind`
are `rfl`-trivial here, so this says what the program *computes* and nothing about concurrency. -/
@[simp, grind .]
theorem combineTasks_eq {α β : Type} (f : List α → β) (ts : List (Task α))
    (prio : Task.Priority := .default) (sync : Bool := false) :
    (combineTasks f prio sync ts []).get = f (ts.map Task.get) := by
  simp only [combineTasks_eq_acc, List.reverse_nil, List.nil_append]

/-- **Spawn each closure in `works` as a real `Task`, then combine the results with `f`.** The one
thing every `*Task.lean` example does by hand, so a new example supplies only its closures.

Each `w ∈ works` must *read* shared data and *return* a value — never write to a shared mutable
`Array` or `IO.Ref`, even at disjoint indices, because a `Ref`'s read-modify-write is not atomic
against other OS threads. Lean's type theory cannot see that violation and neither can `parTasks_eq`;
it is a discipline on the caller. Assembly into a mutable structure happens after `.get`,
sequentially. -/
def parTasks {α β : Type} (f : List α → β) (works : List (Unit → α)) : Task β :=
  combineTasks f .default false (works.map Task.spawn) []

/-- `parTasks` returns `f` applied to the results of calling each closure. Unconditional on `works` —
and notice how little that costs, which is the measure of how little it says: spawning is `rfl`-equal
to calling, so this holds whether or not the closures would race. -/
theorem parTasks_eq {α β : Type} (f : List α → β) (works : List (Unit → α)) :
    (parTasks f works).get = f (works.map (fun w => w ())) := by
  unfold parTasks
  rw [combineTasks_eq]
  congr 1
  rw [List.map_map]
  rfl
