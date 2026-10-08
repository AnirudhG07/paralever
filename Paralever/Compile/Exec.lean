import Paralever.Theory.Sequentialize
import Paralever.Compile.TaskFacts

/-! # `execTask` — running a `ParM` program on real threads

`runSeq` is the reference run and never forks. `execTask` spawns both branches of a `par` node and
merges their post-states; `execTask_get` proves it computes `runSeq`'s answer.

Nothing here proves anything about parallelism, and nothing can: `(Task.spawn f).get = f ()` holds
by `rfl`. Rationale: `Compile/TaskFacts.lean`, `docs/program-model.md`. -/

namespace Paralever

/-- The post-state of a fork, pairwise: at each location, take the branch that changed it.

Unambiguous because `Indep` forces disjoint write sets, and a branch that rewrote a cell's existing
value is indistinguishable from one that left it alone — so no footprint is needed. -/
def joinStates (σ σp σq : State) : State :=
  fun l => if σp l = σ l then σq l else σp l

/-- The post-state of an N-ary fork: fold the pairwise merge over every child's post-state. With
pairwise-disjoint write sets at most one child changed any given cell, so the order of the fold does
not matter. -/
def joinAllStates (σ : State) : List State → State
  | []      => σ
  | s :: ss => joinStates σ s (joinAllStates σ ss)

/-- **The merge is the sequential post-state**, for one child against the rest of the block. Two
cases, each one frame property: a cell the block wrote is untouched by the head, so the block's two
runs agree there (locality); a cell the block did not write keeps the head's value.
-- ref: `docs/semantics.md`, Brookes CONCUR'04 §5 -/
theorem joinStates_eq_childs {α : Type} {αs : List Type} (p : ParM α) (ps : Childs ParM αs)
    (σ : State) (h : Indep (accesses p σ) (accessesChilds ps (runSeq p σ).2)) :
    joinStates σ (runSeq p σ).2 (runChilds ps σ).2 = (runChilds ps (runSeq p σ).2).2 := by
  have hiso := accessesChilds_isolated p ps σ h
  have hF : FDisjoint (accesses p σ).writes (accessesChilds ps (runSeq p σ).2) := ⟨h.2.1, h.1⟩
  have hloc := accessesChilds_runChilds_locality ps (runSeq p σ).2 σ (accesses p σ).writes hF
    (fun l hl => runSeq_frame p σ l hl)
  funext l
  unfold joinStates
  by_cases hq : l ∈ (accessesChilds ps σ).writes
  · have hq1 : l ∈ (accessesChilds ps (runSeq p σ).2).writes := by rw [hiso.1]; exact hq
    have hp : l ∉ (accesses p σ).writes := fun hp => h.1 l hp hq1
    simp [runSeq_frame p σ l hp, (hloc.2.2 l hp).symm]
  · have hq1 : l ∉ (accessesChilds ps (runSeq p σ).2).writes := by rw [hiso.1]; exact hq
    rw [runChilds_frame ps (runSeq p σ).2 l hq1, runChilds_frame ps σ l hq]
    by_cases hc : (runSeq p σ).2 l = σ l <;> simp [hc]

mutual

/-- Run `p`, forking at every `par` node. Every child is spawned before any is waited on, and all
start from the same `σ` — `State` is a function, so that is sharing, not aliasing. -/
def execTask {α : Type} : ParM α → State → Task (α × State)
  | .pure a,      σ => .pure (a, σ)
  | .read l k,    σ => execTask (k (σ l)) σ
  | .write l v k, σ => execTask (k ()) (σ.update l v)
  | .par cs k,    σ =>
      let r := execChilds cs σ
      execTask (k r.1) (joinAllStates σ r.2)

/-- Spawn every child from `σ`, collecting their results and their post-states. The spawn happens
before the recursive call's `get`, so all N children are in flight together. -/
def execChilds {αs : List Type} : Childs ParM αs → State → Results αs × List State
  | .nil,       _ => ((), [])
  | .cons p ps, σ =>
      let t := Task.spawn fun _ => (execTask p σ).get
      let rest := execChilds ps σ
      let r := t.get
      ((r.1, rest.1), r.2 :: rest.2)

end

/-- `execTask` at a fork, with the spawns discharged. -/
theorem execTask_par {β : Type} {αs : List Type} (cs : Childs ParM αs)
    (k : Results αs → ParM β) (σ : State) :
    execTask (.par cs k) σ
      = execTask (k (execChilds cs σ).1) (joinAllStates σ (execChilds cs σ).2) := rfl

/-- **The forked program computes the sequential answer.** The children-level half says the N spawns
produce the block's canonical results and that the fold of their post-states is the block's canonical
post-state; `joinStates_eq_childs` is the `cons` step. -/
theorem execTask_get_all :
    (∀ {τ : Type} (P : ParM τ), ∀ σ, WellFormed P σ → (execTask P σ).get = runSeq P σ) ∧
    (∀ {αs : List Type} (cs : Childs ParM αs), ∀ σ, WellFormedChilds cs σ →
        IndepAll (childFootprints cs σ) →
        (execChilds cs σ).1 = (runChilds cs σ).1 ∧
        joinAllStates σ (execChilds cs σ).2 = (runChilds cs σ).2) := by
  refine ParM.mutualInduction ?_ ?_ ?_ ?_ ?_ ?_
  · intro α a σ _; rfl
  · intro α l k ih σ h; exact ih (σ l) σ h
  · intro α l v k ih σ h; exact ih () (σ.update l v) h
  · intro β αs cs k ih2 ihk σ hwf
    obtain ⟨hind, hwfcs, hwfk⟩ := hwf
    obtain ⟨e1, e2⟩ := ih2 σ hwfcs hind
    rw [execTask_par, e1, e2]
    exact ihk _ _ hwfk
  · intro σ _ _; exact ⟨rfl, rfl⟩
  · -- **the 2-to-N step**: the head's own result, then the tail's — but the tail really ran from `σ`
    -- while `runChilds` measures it after the head, so isolation reconciles the two
    intro α αs p ps ihp ihps σ hwf hind
    have hheadtail : Indep (accesses p σ) (accessesChilds ps (runSeq p σ).2) :=
      indep_accessesChilds ps (accesses p σ) (runSeq p σ).2 hind.1
    have hFw : FDisjoint (accesses p σ).writes (accessesChilds ps (runSeq p σ).2) :=
      ⟨hheadtail.2.1, hheadtail.1⟩
    have hfrm := fun l hl => runSeq_frame p σ l hl
    have hwftail0 : WellFormedChilds ps σ :=
      (WellFormedChilds_locality ps (runSeq p σ).2 σ (accesses p σ).writes hFw hfrm).mp hwf.2
    have hindtail0 : IndepAll (childFootprints ps σ) := by
      rw [← childFootprints_locality ps (runSeq p σ).2 σ (accesses p σ).writes hFw hfrm]
      exact hind.2
    obtain ⟨hiso1, hiso2⟩ := accessesChilds_isolated p ps σ hheadtail
    have hp : (execTask p σ).get = runSeq p σ := ihp σ hwf.1
    obtain ⟨t1, t2⟩ := ihps σ hwftail0 hindtail0
    refine ⟨?_, ?_⟩
    · show ((execTask p σ).get.1, (execChilds ps σ).1) = _
      rw [hp, t1, ← hiso2]
      rfl
    · show joinStates σ (execTask p σ).get.2 (joinAllStates σ (execChilds ps σ).2) = _
      rw [hp, t2]
      exact joinStates_eq_childs p ps σ hheadtail

theorem execTask_get {α : Type} (p : ParM α) (σ : State) (h : WellFormed p σ) :
    (execTask p σ).get = runSeq p σ :=
  execTask_get_all.1 p σ h

theorem execChilds_get {αs : List Type} (cs : Childs ParM αs) (σ : State)
    (hwf : WellFormedChilds cs σ) (hind : IndepAll (childFootprints cs σ)) :
    (execChilds cs σ).1 = (runChilds cs σ).1 ∧
    joinAllStates σ (execChilds cs σ).2 = (runChilds cs σ).2 :=
  execTask_get_all.2 cs σ hwf hind

theorem execTask_parPair_get {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (h : WellFormed (ParM.parPair p q) σ) :
    (execTask (ParM.parPair p q) σ).get = runSeq (ParM.seqPair p q) σ := by
  rw [execTask_get _ σ h, runSeq_parPair_eq_seqPair]

/-- `execTask_get` for the value, `par_seq_eq` for every schedule. -/
theorem execTask_parPair_spec {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (h : WellFormed (ParM.parPair p q) σ) :
    (execTask (ParM.parPair p q) σ).get = runSeq (ParM.seqPair p q) σ ∧
    ParSeqEq (ParM.parPair p q) (ParM.seqPair p q) σ :=
  ⟨execTask_parPair_get p q σ h, par_seq_eq p q σ h⟩

/-! ### N-ary

`parAll` is nested binary `par`, so `execTask` already forks `n` ways and the N-ary statement is a
corollary — the same reason `ParM` needs no `parN` constructor. -/

theorem execTask_parAll_get {α : Type} (ps : List (ParM α)) (σ : State)
    (h : WellFormed (ParM.parAll ps) σ) :
    (execTask (ParM.parAll ps) σ).get = runSeq (ParM.seqAll ps) σ := by
  rw [execTask_get _ σ h, runSeq_parAll_eq_seqAll]

/-- Run `ps` on threads and keep only the final heap. -/
def runParAll {α : Type} (ps : List (ParM α)) (σ : State) : State :=
  (execTask (ParM.parAll ps) σ).get.2

@[simp, grind .] theorem runParAll_eq {α : Type} (ps : List (ParM α)) (σ : State)
    (h : WellFormed (ParM.parAll ps) σ) : runParAll ps σ = (runSeq (ParM.seqAll ps) σ).2 := by
  rw [runParAll, execTask_parAll_get ps σ h]

/-! ### Independent whole programs

`parAll` threads one heap through a single `ParM` tree. When the programs are separate runs that
share nothing to merge — each wanted for its own result — `execEach` spawns them side by side with
`parTasks` (`Compile/TaskFacts.lean`, standing in for the lemma-less `Task.mapList`). -/

/-- Spawn each program in `ps` from `σ` and collect every result and post-state. -/
def execEach {α : Type} (ps : List (ParM α)) (σ : State) : Task (List (α × State)) :=
  parTasks id (ps.map fun p _ => (execTask p σ).get)

/-- Each entry is that program's own canonical run. No independence between the `ps` is needed:
they never see each other's heap. -/
theorem execEach_get {α : Type} (ps : List (ParM α)) (σ : State)
    (h : ∀ p ∈ ps, WellFormed p σ) :
    (execEach ps σ).get = ps.map (fun p => runSeq p σ) := by
  rw [execEach, parTasks_eq, List.map_map]
  exact List.map_congr_left fun p hp => execTask_get p σ (h p hp)

/-! ### Building heaps for a run -/

/-- The heap mapping each listed location to its value, and everything else to `dflt`. -/
def State.ofList (ps : List (Loc × Val)) (dflt : Val := .int 0) : State :=
  fun l => (ps.find? (fun e => e.1 == l)).elim dflt Prod.snd

@[simp, grind .] theorem State.ofList_nil (dflt : Val) : State.ofList [] dflt = fun _ => dflt := rfl

/-- Run `p` on threads and keep only its value. -/
def evalPar {α : Type} (p : ParM α) (σ : State) : α := (execTask p σ).get.1

/-- Run `p` on threads and keep only the final heap. -/
def runPar {α : Type} (p : ParM α) (σ : State) : State := (execTask p σ).get.2

@[simp, grind .] theorem runPar_eq {α : Type} (p : ParM α) (σ : State) (h : WellFormed p σ) :
    runPar p σ = (runSeq p σ).2 := by rw [runPar, execTask_get p σ h]

@[simp, grind .] theorem evalPar_eq {α : Type} (p : ParM α) (σ : State) (h : WellFormed p σ) :
    evalPar p σ = (runSeq p σ).1 := by rw [evalPar, execTask_get p σ h]

/-- The `(location, value)` pairs the run leaves over `[lo, hi)`. What `#eval` wants. -/
def runParWindow {α : Type} (p : ParM α) (σ : State) (lo hi : Nat) : List (Loc × Val) :=
  (runPar p σ).window lo hi

end Paralever
