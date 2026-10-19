import Paralever.Lib.Notation

/-! # Cost: work, and time as a count of parallel rounds

`par_seq_eq` says the parallel program computes the same *output* as the sequential one. It says
nothing about being faster. This file supplies the other half.

* `work p σ` — how many memory operations execute in total
* `time p σ` — how many **parallel rounds** the program needs

How `time` is obtained is the design point. An earlier version of this file *defined* `time` by a fold
with `max` at the `par` node, which made "parallel is faster" true by construction: the theorem merely
unfolded a definition written to say so.

Instead `time` counts rounds of an operational relation, `pstep`, whose `par` case says only
**"advance both branches"**. The word `max` occurs nowhere in `pstep` or `ptime`. It has to be
*derived* — and the derivation is where independence earns its keep. `time_parPair_eq_max` is that
derivation, in general.

Rationale: `docs/cost.md`. -/

namespace Paralever

-- ref: docs/cost.md; calf/decalf (POPL'22 / OOPSLA'24) cost-as-effect; Blelloch for work/span

/-! ### Work: total operations

Nothing is stipulated here — operations genuinely add across a fork. -/

mutual

/-- The number of memory operations `p` performs along the canonical run from `σ`: one per `read`,
one per `write`, none for `pure` or for a join.

At a `par` node the three counts **add** — the left branch, the right branch measured from the heap
the left one left behind, and the continuation. Parallelism reorders operations; it does not remove
any, so `work` is the measure that stays fixed and `time` the one that shrinks. -/

@[simp, grind .]
def work {τ : Type} : ParM τ → State → Nat
  | .pure _,      _ => 0
  | .read l k,    σ => 1 + work (k (σ l)) σ
  | .write l v k, σ => 1 + work (k ()) (σ.update l v)
  | .par cs k,    σ =>
      let r := runChilds cs σ
      workChilds cs σ + work (k r.1) r.2

/-- Every child's operations, each measured from the heap the one before it left. -/
@[simp, grind .]
def workChilds {αs : List Type} : Childs ParM αs → State → Nat
  | .nil,       _ => 0
  | .cons p ps, σ => work p σ + workChilds ps (runSeq p σ).2

end

/-- Work adds across a `bind`: the left factor's operations, then the continuation's, measured from
the heap the left factor produced. -/
@[grind .]
theorem work_bind {α β : Type} (p : ParM α) (f : α → ParM β) (σ : State) :
    work (ParM.bind p f) σ = work p σ + work (f (runSeq p σ).1) (runSeq p σ).2 := by
  have H : ∀ {α : Type} (p : ParM α) (β : Type) (f : α → ParM β) (σ : State),
      work (ParM.bind p f) σ = work p σ + work (f (runSeq p σ).1) (runSeq p σ).2 := by
    intro α p
    induction p using ParM.inductionOn with
    | hpure a => intro β f σ; simp [ParM.bind, work]
    | hread l k ih => intro β f σ; simp only [ParM.bind, work, runSeq, ih]; omega
    | hwrite l v k ih => intro β f σ; simp only [ParM.bind, work, runSeq, ih]; omega
    | hpar cs k _ ihk => intro β f σ; simp only [ParM.bind, work, runSeq, ihk]; omega
  exact H p β f σ

/-- A parallel pair's work is the sum of its branches'. -/
@[grind .]
theorem work_parPair {α β : Type} (p : ParM α) (q : ParM β) (σ : State) :
    work (ParM.parPair p q) σ = work p σ + work q (runSeq p σ).2 := by
  simp [ParM.parPair, work, workChilds]

/-- A sequential pair's work is the sum of its components' — the same sum as `work_parPair`. -/
@[grind .]
theorem work_seqPair {α β : Type} (p : ParM α) (q : ParM β) (σ : State) :
    work (ParM.seqPair p q) σ = work p σ + work q (runSeq p σ).2 := by
  simp [ParM.seqPair, work_bind, work]

/-- **Parallelism does not reduce the work.** The same operations run either way — a chunked sum
still performs `n` additions. Conflating this with time is the usual mistake. -/
theorem work_par_eq_seq {α β : Type} (p : ParM α) (q : ParM β) (σ : State) :
    work (ParM.parPair p q) σ = work (ParM.seqPair p q) σ := by
  rw [work_parPair, work_seqPair]

/-- `work` is local in the same sense as `accesses`: two states agreeing outside a region the
program never touches give the same operation count. Same shape as `accesses_runSeq_locality`. -/
theorem work_locality_all :
    (∀ {τ : Type} (p : ParM τ), ∀ (σ σ' : State) (F : List Loc),
        FDisjoint F (accesses p σ) → (∀ l, l ∉ F → σ l = σ' l) → work p σ = work p σ') ∧
    (∀ {αs : List Type} (cs : Childs ParM αs), ∀ (σ σ' : State) (F : List Loc),
        FDisjoint F (accessesChilds cs σ) → (∀ l, l ∉ F → σ l = σ' l) →
        workChilds cs σ = workChilds cs σ') := by
  refine ParM.mutualInduction ?_ ?_ ?_ ?_ ?_ ?_
  · intro α a σ σ' F _ _; rfl
  · intro α l k ih σ σ' F hF hagree
    have hl : l ∉ F := fun hmem => hF.1 l hmem (by simp [accesses, Footprint.union])
    have hv : σ l = σ' l := hagree l hl
    have hFk : FDisjoint F (accesses (k (σ l)) σ) :=
      ⟨fun x hx hmem => hF.1 x hx (by simp [accesses, Footprint.union, hmem]),
       fun x hx hmem => hF.2 x hx (by simp [accesses, Footprint.union, hmem])⟩
    show 1 + work (k (σ l)) σ = 1 + work (k (σ' l)) σ'
    rw [← hv, ih (σ l) σ σ' F hFk hagree]
  · intro α l v k ih σ σ' F hF hagree
    have hFk : FDisjoint F (accesses (k ()) (σ.update l v)) :=
      ⟨fun x hx hmem => hF.1 x hx (by simp [accesses, Footprint.union, hmem]),
       fun x hx hmem => hF.2 x hx (by simp [accesses, Footprint.union, hmem])⟩
    have hagree' : ∀ x, x ∉ F → (σ.update l v) x = (σ'.update l v) x := by
      intro x hx
      by_cases hxl : x = l
      · subst hxl; simp [State.update]
      · simpa [State.update, hxl] using hagree x hx
    show 1 + work (k ()) (σ.update l v) = 1 + work (k ()) (σ'.update l v)
    rw [ih () (σ.update l v) (σ'.update l v) F hFk hagree']
  · intro β αs cs k ih2 ihk σ σ' F hF hagree
    have hFcs : FDisjoint F (accessesChilds cs σ) := hF.left
    obtain ⟨e1, e2, e3⟩ := accessesChilds_runChilds_locality cs σ σ' F hFcs hagree
    have hFk : FDisjoint F (accesses (k (runChilds cs σ).1) (runChilds cs σ).2) := hF.right
    show workChilds cs σ + work (k (runChilds cs σ).1) (runChilds cs σ).2
       = workChilds cs σ' + work (k (runChilds cs σ').1) (runChilds cs σ').2
    rw [ih2 σ σ' F hFcs hagree, ← e2,
        ihk (runChilds cs σ).1 (runChilds cs σ).2 (runChilds cs σ').2 F hFk e3]
  · intro σ σ' F _ _; rfl
  · -- **the 2-to-N step**: the head's count is local, and the tail's is local from where it starts
    intro α αs p ps ihp ihps σ σ' F hF hagree
    have hFp : FDisjoint F (accesses p σ) := hF.left
    obtain ⟨_, _, e3⟩ := accesses_runSeq_locality p σ σ' F hFp hagree
    have hFps : FDisjoint F (accessesChilds ps (runSeq p σ).2) := hF.right
    show work p σ + workChilds ps (runSeq p σ).2
       = work p σ' + workChilds ps (runSeq p σ').2
    rw [ihp σ σ' F hFp hagree, ihps (runSeq p σ).2 (runSeq p σ').2 F hFps e3]

theorem work_locality {τ : Type} (p : ParM τ) (σ σ' : State) (F : List Loc)
    (hF : FDisjoint F (accesses p σ)) (hagree : ∀ l, l ∉ F → σ l = σ' l) :
    work p σ = work p σ' :=
  work_locality_all.1 p σ σ' F hF hagree

theorem workChilds_locality {αs : List Type} (cs : Childs ParM αs) (σ σ' : State) (F : List Loc)
    (hF : FDisjoint F (accessesChilds cs σ)) (hagree : ∀ l, l ∉ F → σ l = σ' l) :
    workChilds cs σ = workChilds cs σ' :=
  work_locality_all.2 cs σ σ' F hF hagree

/-- `σ` with every write in the batch applied, left to right — how a round's collected writes land.

The order is fixed only to make this a definition. A round's batch comes from independent branches,
so its locations are pairwise distinct and any other order gives the same heap. -/
def applyAll (σ : State) : List (Loc × Val) → State
  | []           => σ
  | (l, v) :: ws => applyAll (σ.update l v) ws

mutual

/-- **One parallel round: every ready branch performs one operation.** Returns the residual program
together with the writes that round performed, batched; `none` means the program has finished and
there is no round to take.

Two details of the `par` case are load-bearing, and both were bugs in earlier drafts:

* The join charges **no** round, because joining performs no memory operation. Charging for it
  inflates every parallel cost by the nesting depth.
* The join fires when both branches are *finished*, which is **not** the same as being syntactically
  `.pure` — a nested `par` whose own work is exhausted is finished too. Testing for `.pure` instead
  skips the continuation entirely, so a program that writes reports zero rounds. The branch values
  are therefore taken from `runSeq`, which is exact here precisely because the branches are done.

`max` is written nowhere here; `ptime_parPair_eq_max` derives it. -- ref: docs/cost.md -/

@[simp, grind .]
def pstep {τ : Type} : ParM τ → State → Option (ParM τ × List (Loc × Val))
  | .pure _,      _ => none
  | .read l k,    σ => some (k (σ l), [])
  | .write l v k, _ => some (k (), [(l, v)])
  | .par cs k,    σ =>
      match pstepChilds cs σ with
      | some (cs', ws) => some (.par cs' k, ws)
      | none           => pstep (k (runChilds cs σ).1) σ  -- join: every child has finished

/-- Advance **every** ready child in one round, collecting all their writes. The N-ary form of "both
advance": a round costs one regardless of how many children move in it, which is what makes `time` a
span rather than a sum. -/
@[simp, grind .]
def pstepChilds {αs : List Type} :
    Childs ParM αs → State → Option (Childs ParM αs × List (Loc × Val))
  | .nil,       _ => none
  | .cons p ps, σ =>
      match pstep p σ, pstepChilds ps σ with
      | some (p', wp), some (ps', wq) => some (.cons p' ps', wp ++ wq)
      | some (p', wp), none           => some (.cons p' ps,  wp)
      | none,          some (ps', wq) => some (.cons p  ps',  wq)
      | none,          none           => none

end

/-- How many `pstep` rounds `p` takes from `σ`, counted under a fuel bound and returning `0` if the
fuel runs out before the program finishes.

Fuel rather than a termination argument because the recursion is on rounds, not on the term. Any
fuel exceeding `work p σ` gives the true count (`ptime_fuel_indep`, `ptime_eq_time`), which is why
`time` can simply pick `work p σ + 1`. -/
@[simp, grind .]
def ptime {τ : Type} : Nat → ParM τ → State → Nat
  | 0,     _, _ => 0
  | n + 1, p, σ =>
      match pstep p σ with
      | none          => 0
      | some (p', ws) => 1 + ptime n p' (applyAll σ ws)

/-- **The number of parallel rounds `p` needs from `σ`** — the span, as opposed to `work`'s total
operation count. This is the measure parallelism actually reduces.

A round performs at least one operation while the program is unfinished, so `work p σ` rounds always
suffice and the fuel is never the binding constraint; the `+ 1` is slack. Rounds are counted on an
idealised machine with unlimited cores and unit-cost operations — `docs/cost.md` says what that does
and does not claim about wall-clock time. -/
@[simp, grind .]
def time {τ : Type} (p : ParM τ) (σ : State) : Nat := ptime (work p σ + 1) p σ

/-! ### `max` is derived, not assumed — the narrow cases first

Special cases of `time_parPair_eq_max` below, kept because `simp` alone checks them, pinning the
definitions down independently of the general proof. -/

/-- Two single writes in parallel take `max 1 1` rounds. Checked by `simp` alone, so it pins the
definitions down independently of `ptime_parPair_eq_max`. -/
theorem ptime_parPair_single (a b : Loc) (va vb : Val) (σ : State) (n : Nat) :
    ptime (n + 2) (ParM.parPair (ParM.wr a va) (ParM.wr b vb)) σ
      = max (ptime (n + 2) (ParM.wr a va) σ) (ptime (n + 2) (ParM.wr b vb) σ) := by
  simp [ptime, pstep, ParM.wr, ParM.parPair]

/-- The same two writes in sequence take `1 + 1` rounds. Also by `simp` alone. -/
theorem ptime_seqPair_single (a b : Loc) (va vb : Val) (σ : State) (n : Nat) :
    ptime (n + 3) (ParM.seqPair (ParM.wr a va) (ParM.wr b vb)) σ
      = ptime (n + 3) (ParM.wr a va) σ + ptime (n + 3) (ParM.wr b vb) σ := by
  simp [ptime, pstep, ParM.wr, ParM.seqPair, ParM.bind]

/-- **Two writes run in parallel take strictly fewer rounds than in sequence** — `1 < 2`, derived
from the round semantics rather than stipulated. The smallest instance of `time_par_lt_seq`, and like
its neighbours above it is discharged by `simp` alone. -/
theorem time_par_lt_seq_single (a b : Loc) (va vb : Val) (σ : State) :
    time (ParM.parPair (ParM.wr a va) (ParM.wr b vb)) σ
      < time (ParM.seqPair (ParM.wr a va) (ParM.wr b vb)) σ := by
  simp [time, ptime, pstep, work, ParM.wr, ParM.parPair, ParM.seqPair, ParM.bind]

/-! ### The max law for straight-line write sequences, at arbitrary length

This is the first case where `max` is genuinely *derived* for unboundedly many operations: two
sequences of `m` and `n` writes take `max m n` rounds in parallel. `pstep` never mentions `max`. -/

/-- The program that performs the given writes one after another and returns `()`. A straight-line
test family of unbounded length, used only in this section. -/
def writeSeq : List (Loc × Val) → ParM Unit
  | []           => .pure ()
  | (l, v) :: ws => .write l v (fun _ => writeSeq ws)

/-- A sequence of `m` writes takes exactly `m` rounds — one round per write, given fuel to spare. -/
theorem ptime_writeSeq : ∀ (ws : List (Loc × Val)) (n : Nat) (σ : State),
    ws.length < n → ptime n (writeSeq ws) σ = ws.length := by
  intro ws
  induction ws with
  | nil =>
      grind only [= List.length_nil, = ptime.eq_def, = writeSeq.eq_def, ptime, pstep]
  | cons w ws ih =>
      grind [= ptime.eq_def, = writeSeq.eq_def]

/-- **`pstep` at a two-child fork, in binary form.** `parPair` is the `N = 2` case of `par`, and this
is what lets every binary-shaped cost proof below read `pstep` without unfolding the children spine.
-- ref: docs/cost.md -/
theorem pstep_parPair {α β : Type} (p : ParM α) (q : ParM β) (σ : State) :
    pstep (ParM.parPair p q) σ =
      (match pstep p σ, pstep q σ with
       | some (p', wp), some (q', wq) => some (ParM.parPair p' q', wp ++ wq)
       | some (p', wp), none          => some (ParM.parPair p' q,  wp)
       | none,          some (q', wq) => some (ParM.parPair p  q',  wq)
       | none,          none          =>
           pstep (ParM.pure ((runSeq p σ).1, (runSeq q (runSeq p σ).2).1)) σ) := by
  rcases hp : pstep p σ with _ | ⟨p', wp⟩ <;> rcases hq : pstep q σ with _ | ⟨q', wq⟩ <;>
    simp [ParM.parPair, pstep, pstepChilds, hp, hq]

/-! ### The max law for two write sequences of ARBITRARY length.
    Stated with `.par _ _ .pure` so nothing needs folding/unfolding mid-proof. -/

/-- **Two write sequences of lengths `m` and `n` run in parallel take `max m n` rounds.** The first
case where `max` is derived for unboundedly many operations, and it is proved by bare induction with
no appeal to independence — so it checks `pstep` against the intended cost model independently of
`ptime_parPair_eq_max`. -/
theorem ptime_par_writeSeq :
    ∀ (ws₁ ws₂ : List (Loc × Val)) (n : Nat) (σ : State),
      ws₁.length < n → ws₂.length < n →
      ptime n (ParM.parPair (writeSeq ws₁) (writeSeq ws₂)) σ
        = max ws₁.length ws₂.length := by
  intro ws₁
  induction ws₁ with
  | nil =>
      intro ws₂
      induction ws₂ with
      | nil => intro n σ _ _; cases n with
        | zero => rfl
        | succ m => simp [ptime, pstep_parPair, pstep, writeSeq]
      | cons w ws ih2 =>
          intro n σ h1 h2
          obtain ⟨l, v⟩ := w
          cases n with
          | zero => simp at h2
          | succ m =>
              simp only [ptime, pstep_parPair, pstep, writeSeq, applyAll,
                List.length_cons, List.length_nil]
              rw [show (ParM.pure () : ParM Unit) = writeSeq [] from rfl,
                  ih2 m (σ.update l v) (by simp at h2; simp; omega) (by simp at h2; omega)]
              simp; omega
  | cons w ws ih1 =>
      intro ws₂ n σ h1 h2
      obtain ⟨l, v⟩ := w
      cases ws₂ with
      | nil =>
          cases n with
          | zero => simp at h1
          | succ m =>
              simp only [ptime, pstep_parPair, pstep, writeSeq, applyAll,
                List.length_cons, List.length_nil]
              rw [show (ParM.pure () : ParM Unit) = writeSeq [] from rfl,
                  ih1 [] m (σ.update l v) (by simp at h1; omega) (by simp at h1; simp; omega)]
              simp; omega
      | cons w₂ ws₂' =>
          obtain ⟨l₂, v₂⟩ := w₂
          cases n with
          | zero => simp at h1
          | succ m =>
              simp only [ptime, pstep_parPair, pstep, writeSeq, List.length_cons]
              rw [ih1 ws₂' m (applyAll σ ([(l, v)] ++ [(l₂, v₂)]))
                    (by simp at h1; omega) (by simp at h2; omega)]
              omega

/-- The same two sequences composed with `bind` take `m + n` rounds. The sequential counterpart of
`ptime_par_writeSeq`, likewise proved directly. -/
theorem ptime_seq_writeSeq (ws₁ ws₂ : List (Loc × Val)) (n : Nat) (σ : State)
    (h1 : ws₁.length < n) (h2 : ws₂.length < n) (hsum : ws₁.length + ws₂.length < n) :
    ptime n (ParM.bind (writeSeq ws₁) (fun _ => writeSeq ws₂)) σ
      = ws₁.length + ws₂.length := by
  induction ws₁ generalizing n σ with
  | nil =>
      cases n with
      | zero => simp at h1
      | succ m => simpa [ptime, pstep, writeSeq, ParM.bind] using ptime_writeSeq ws₂ (m+1) σ h2
  | cons w ws ih =>
      obtain ⟨l, v⟩ := w
      cases n with
      | zero => simp at h1
      | succ m =>
          simp only [ptime, pstep, writeSeq, ParM.bind, applyAll, List.length_cons]
          rw [ih m (σ.update l v) (by simp at h1; omega) (by simp at hsum; omega) (by simp at hsum; omega)]
          omega

/-- A program with no round left to take has an empty footprint. Used throughout to conclude that a
finished branch leaves the heap exactly where it found it. -/
theorem pstep_none_accesses_all :
    (∀ {τ : Type} (p : ParM τ), ∀ σ, pstep p σ = none → accesses p σ = Footprint.empty) ∧
    (∀ {αs : List Type} (cs : Childs ParM αs), ∀ σ,
        pstepChilds cs σ = none → accessesChilds cs σ = Footprint.empty) := by
  refine ParM.mutualInduction ?_ ?_ ?_ ?_ ?_ ?_
  · intro α a σ _; rfl
  · intro α l k ih σ h; simp [pstep] at h
  · intro α l v k ih σ h; simp [pstep] at h
  · -- a fork with nothing to do: every child is finished, so the block touched nothing and the
    -- continuation ran from the untouched heap
    intro β αs cs k ih2 ihk σ h
    rcases hsc : pstepChilds cs σ with _ | ⟨cs', ws⟩
    · have hac : accessesChilds cs σ = Footprint.empty := ih2 σ hsc
      have hσ1 : (runChilds cs σ).2 = σ := by
        funext m; exact runChilds_frame cs σ m (by simp [hac, Footprint.empty])
      have hk : pstep (k (runChilds cs σ).1) σ = none := by
        simpa [pstep, hsc] using h
      have hak := ihk _ σ hk
      show accesses (ParM.par cs k) σ = Footprint.empty
      simp only [accesses, hσ1, hac, hak, Footprint.union, Footprint.empty]
      simp
    · simp [pstep, hsc] at h
  · intro σ _; rfl
  · -- **the 2-to-N step**: no round left means neither the head nor the tail has one
    intro α αs p ps ihp ihps σ h
    rcases hsp : pstep p σ with _ | ⟨p', wp⟩
    · rcases hsps : pstepChilds ps σ with _ | ⟨ps', ws⟩
      · have hap : accesses p σ = Footprint.empty := ihp σ hsp
        have hσ1 : (runSeq p σ).2 = σ := by
          funext m; exact runSeq_frame p σ m (by simp [hap, Footprint.empty])
        have haps : accessesChilds ps σ = Footprint.empty := ihps σ hsps
        show accessesChilds (Childs.cons p ps) σ = Footprint.empty
        simp only [accessesChilds, hσ1, hap, haps, Footprint.union, Footprint.empty]
        simp
      · simp [pstepChilds, hsp, hsps] at h
    · rcases hsps : pstepChilds ps σ with _ | ⟨ps', ws⟩ <;>
        simp [pstepChilds, hsp, hsps] at h

theorem pstep_none_accesses {τ : Type} :
    ∀ (p : ParM τ) (σ : State), pstep p σ = none → accesses p σ = Footprint.empty :=
  fun p σ h => pstep_none_accesses_all.1 p σ h

theorem pstepChilds_none_accesses {αs : List Type} :
    ∀ (cs : Childs ParM αs) (σ : State),
      pstepChilds cs σ = none → accessesChilds cs σ = Footprint.empty :=
  fun cs σ h => pstep_none_accesses_all.2 cs σ h

/-! ### Helpers about `applyAll` -/

/-- Applying a concatenated batch is applying the two halves in turn — how a `par` round's combined
batch is split back into the left branch's writes and the right's. -/
theorem applyAll_append (σ : State) : ∀ (ws₁ ws₂ : List (Loc × Val)),
    applyAll σ (ws₁ ++ ws₂) = applyAll (applyAll σ ws₁) ws₂ := by
  intro ws₁
  induction ws₁ generalizing σ with
  | nil => intro ws₂; rfl
  | cons w ws ih => intro ws₂; obtain ⟨l, v⟩ := w; simpa [applyAll] using ih (σ.update l v) ws₂

/-- A batch leaves every location it does not write alone. The frame rule for `applyAll`. -/
theorem applyAll_frame : ∀ (ws : List (Loc × Val)) (σ : State),
    ∀ l ∉ ws.map Prod.fst, applyAll σ ws l = σ l := by
  intro ws
  induction ws with
  | nil => intro σ l _; rfl
  | cons w ws ih =>
      intro σ l hl
      obtain ⟨l0, v0⟩ := w
      simp only [List.map_cons, List.mem_cons, not_or] at hl
      rw [applyAll, ih (σ.update l0 v0) l hl.2, State.update_other σ v0 hl.1]

/-- The right branch is already well formed in the *pre-fork* heap, not merely after the left branch
has run. `WellFormed` states `q`'s obligation at `(runSeq p σ).2`; independence makes the two heaps
indistinguishable to `q`, and every `par` case below opens with this move. -/
theorem wellFormed_branch_shift {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (hindep : Indep (accesses p σ) (accesses q (runSeq p σ).2))
    (hwfq1 : WellFormed q (runSeq p σ).2) : WellFormed q σ :=
  (WellFormed_locality q (runSeq p σ).2 σ (accesses p σ).writes
    ⟨hindep.2.1, hindep.1⟩ (runSeq_frame p σ)).mp hwfq1

/-- The children-block form of `wellFormed_branch_shift`: the tail really runs from `σ`, while
`WellFormedChilds` records it after the head. -/
theorem wellFormedChilds_branch_shift {α : Type} {αs : List Type} (p : ParM α)
    (ps : Childs ParM αs) (σ : State)
    (hindep : Indep (accesses p σ) (accessesChilds ps (runSeq p σ).2))
    (hwfps : WellFormedChilds ps (runSeq p σ).2) : WellFormedChilds ps σ :=
  (WellFormedChilds_locality ps (runSeq p σ).2 σ (accesses p σ).writes
    ⟨hindep.2.1, hindep.1⟩ (runSeq_frame p σ)).mp hwfps

/-- …and the same shift for the tail's independence. -/
theorem indepAll_branch_shift {α : Type} {αs : List Type} (p : ParM α) (ps : Childs ParM αs)
    (σ : State) (hindep : Indep (accesses p σ) (accessesChilds ps (runSeq p σ).2))
    (h : IndepAll (childFootprints ps (runSeq p σ).2)) : IndepAll (childFootprints ps σ) := by
  rw [← childFootprints_locality ps (runSeq p σ).2 σ (accesses p σ).writes
    ⟨hindep.2.1, hindep.1⟩ (runSeq_frame p σ)]
  exact h

/-- A round only writes inside the program's own write footprint. -/
theorem pstep_writes_subset_all :
    (∀ {τ : Type} (p : ParM τ), ∀ σ, WellFormed p σ → ∀ (p' : ParM τ) (ws : List (Loc × Val)),
        pstep p σ = some (p', ws) → ws.map Prod.fst ⊆ (accesses p σ).writes) ∧
    (∀ {αs : List Type} (cs : Childs ParM αs), ∀ σ, WellFormedChilds cs σ →
        IndepAll (childFootprints cs σ) → ∀ (cs' : Childs ParM αs) (ws : List (Loc × Val)),
        pstepChilds cs σ = some (cs', ws) → ws.map Prod.fst ⊆ (accessesChilds cs σ).writes) := by
  refine ParM.mutualInduction ?_ ?_ ?_ ?_ ?_ ?_
  · intro α a σ _ P' ws h; simp [pstep] at h
  · intro α l k ih σ _ P' ws h
    simp only [pstep, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; intro x hx; simp at hx
  · intro α l v k ih σ _ P' ws h
    simp only [pstep, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; intro x hx
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
    simp [accesses, Footprint.union, hx]
  · intro β αs cs k ih2 ihk σ hwf P' ws h
    rcases hsc : pstepChilds cs σ with _ | ⟨cs', wsc⟩
    · -- the join: the block is finished, so the round is the continuation's
      have hac : accessesChilds cs σ = Footprint.empty := pstepChilds_none_accesses cs σ hsc
      have hσ1 : (runChilds cs σ).2 = σ := by
        funext m; exact runChilds_frame cs σ m (by simp [hac, Footprint.empty])
      have hk : pstep (k (runChilds cs σ).1) σ = some (P', ws) := by
        simpa [pstep, hsc] using h
      have hwk : WellFormed (k (runChilds cs σ).1) σ := by
        have hw := hwf.2.2; rw [hσ1] at hw; exact hw
      have hsubk := ihk _ σ hwk P' ws hk
      intro x hx
      simp only [accesses, Footprint.union, List.mem_append, hσ1]
      exact Or.inr (hsubk hx)
    · -- a round of the children block
      simp only [pstep, hsc, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, hws⟩ := h
      have hsub := ih2 σ hwf.2.1 hwf.1 cs' wsc hsc
      intro x hx
      rw [← hws] at hx
      simp only [accesses, Footprint.union, List.mem_append]
      exact Or.inl (hsub hx)
  · intro σ _ _ cs' ws h; simp [pstepChilds] at h
  · -- **the 2-to-N step**: the head's batch lands in the head's writes, the tail's in the tail's
    intro α αs p ps ihp ihps σ hwf hind cs' ws h
    have hheadtail : Indep (accesses p σ) (accessesChilds ps (runSeq p σ).2) :=
      indep_accessesChilds ps (accesses p σ) (runSeq p σ).2 hind.1
    have hwfps0 : WellFormedChilds ps σ := wellFormedChilds_branch_shift p ps σ hheadtail hwf.2
    have hind0 : IndepAll (childFootprints ps σ) := indepAll_branch_shift p ps σ hheadtail hind.2
    obtain ⟨eacc, _⟩ := accessesChilds_isolated p ps σ hheadtail
    have hsub : (accessesChilds ps σ).writes ⊆ (accessesChilds ps (runSeq p σ).2).writes := by
      rw [eacc]; exact fun _ hx => hx
    rcases hsp : pstep p σ with _ | ⟨p', wp⟩
    · rcases hsps : pstepChilds ps σ with _ | ⟨ps', wq⟩
      · simp [pstepChilds, hsp, hsps] at h
      · simp only [pstepChilds, hsp, hsps, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, hws⟩ := h
        intro x hx
        rw [← hws] at hx
        simp only [accessesChilds, Footprint.union, List.mem_append]
        exact Or.inr (hsub (ihps σ hwfps0 hind0 ps' wq hsps hx))
    · rcases hsps : pstepChilds ps σ with _ | ⟨ps', wq⟩
      · simp only [pstepChilds, hsp, hsps, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, hws⟩ := h
        intro x hx
        rw [← hws] at hx
        simp only [accessesChilds, Footprint.union, List.mem_append]
        exact Or.inl (ihp σ hwf.1 p' wp hsp hx)
      · simp only [pstepChilds, hsp, hsps, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, hws⟩ := h
        intro x hx
        rw [← hws, List.map_append, List.mem_append] at hx
        simp only [accessesChilds, Footprint.union, List.mem_append]
        rcases hx with hx | hx
        · exact Or.inl (ihp σ hwf.1 p' wp hsp hx)
        · exact Or.inr (hsub (ihps σ hwfps0 hind0 ps' wq hsps hx))

theorem pstep_writes_subset {τ : Type} :
    ∀ (p : ParM τ) (σ : State), WellFormed p σ → ∀ (p' : ParM τ) (ws : List (Loc × Val)),
      pstep p σ = some (p', ws) → ws.map Prod.fst ⊆ (accesses p σ).writes :=
  fun p σ hwf p' ws h => pstep_writes_subset_all.1 p σ hwf p' ws h

theorem pstepChilds_writes_subset {αs : List Type} :
    ∀ (cs : Childs ParM αs) (σ : State), WellFormedChilds cs σ →
      IndepAll (childFootprints cs σ) → ∀ (cs' : Childs ParM αs) (ws : List (Loc × Val)),
      pstepChilds cs σ = some (cs', ws) → ws.map Prod.fst ⊆ (accessesChilds cs σ).writes :=
  fun cs σ hwf hind cs' ws h => pstep_writes_subset_all.2 cs σ hwf hind cs' ws h

/-! ### Towards the general law: locality of a round

`pstep_locality` is the keystone — two states that agree outside a region the program never touches
give *literally the same round*, residual program and write batch alike. -/

/-! ### Agreement survives a round: the same batch is applied to both states. -/

/-- Applying the *same* batch to two states that agree outside `F` leaves them agreeing outside `F`.
The induction step of `ptime_locality`. -/
theorem applyAll_agree (F : List Loc) :
    ∀ (ws : List (Loc × Val)) (σ σ' : State), (∀ l ∉ F, σ l = σ' l) →
      ∀ l ∉ F, applyAll σ ws l = applyAll σ' ws l := by
  intro ws
  induction ws with
  | nil => intro σ σ' h l hl; exact h l hl
  | cons w ws ih =>
      intro σ σ' h l hl
      obtain ⟨l0, v0⟩ := w
      refine ih (σ.update l0 v0) (σ'.update l0 v0) ?_ l hl
      grind

/-- **A round is local.** If `σ` and `σ'` agree outside a region `F` that `p` never touches, then `p`
takes *literally the same round* from both — same residual program, same write batch, on the nose
rather than up to equivalence. -/
theorem pstep_locality_all :
    (∀ {τ : Type} (p : ParM τ), ∀ (σ σ' : State) (F : List Loc), WellFormed p σ →
        FDisjoint F (accesses p σ) → (∀ l ∉ F, σ l = σ' l) → pstep p σ = pstep p σ') ∧
    (∀ {αs : List Type} (cs : Childs ParM αs), ∀ (σ σ' : State) (F : List Loc),
        WellFormedChilds cs σ → IndepAll (childFootprints cs σ) →
        FDisjoint F (accessesChilds cs σ) → (∀ l ∉ F, σ l = σ' l) →
        pstepChilds cs σ = pstepChilds cs σ') := by
  refine ParM.mutualInduction ?_ ?_ ?_ ?_ ?_ ?_
  · intro α a σ σ' F _ _ _; rfl
  · intro α l k ih σ σ' F _ hF hagree
    have hl : l ∉ F := fun hmem => hF.1 l hmem (by simp [accesses, Footprint.union])
    simp only [pstep, hagree l hl]
  · intro α l v k ih σ σ' F _ _ _; rfl
  · -- a fork: the children block takes the same round, and if it has none the join's continuation
    -- is reached from an untouched heap on both sides
    intro β αs cs k ih2 ihk σ σ' F hwf hF hagree
    obtain ⟨hind, hwfcs, hwfk⟩ := hwf
    have hFcs : FDisjoint F (accessesChilds cs σ) := hF.left
    have hcs' := ih2 σ σ' F hwfcs hind hFcs hagree
    obtain ⟨-, evcs, -⟩ := accessesChilds_runChilds_locality cs σ σ' F hFcs hagree
    rcases hsc : pstepChilds cs σ' with _ | ⟨cs'', ws⟩
    · -- the block is finished on both sides, so it moved neither heap
      simp only [pstep, hcs', hsc, evcs]
      have hac : accessesChilds cs σ = Footprint.empty :=
        pstepChilds_none_accesses cs σ (hcs'.trans hsc)
      have hσ1 : (runChilds cs σ).2 = σ := by
        funext m; exact runChilds_frame cs σ m (by simp [hac, Footprint.empty])
      refine ihk _ σ σ' F ?_ ?_ hagree
      · simpa [hσ1, ← evcs] using hwfk
      · simpa [hσ1, hac, Footprint.union, Footprint.empty, ← evcs] using hF.right
    · simp only [pstep, hcs', hsc]
  · intro σ σ' F _ _ _ _; rfl
  · -- **the 2-to-N step**: the head takes the same round by its own IH, and the tail by its, after
    -- isolation moves its hypotheses to `σ`
    intro α αs p ps ihp ihps σ σ' F hwf hind hF hagree
    have hheadtail : Indep (accesses p σ) (accessesChilds ps (runSeq p σ).2) :=
      indep_accessesChilds ps (accesses p σ) (runSeq p σ).2 hind.1
    have hwfps0 : WellFormedChilds ps σ := wellFormedChilds_branch_shift p ps σ hheadtail hwf.2
    have hind0 : IndepAll (childFootprints ps σ) := indepAll_branch_shift p ps σ hheadtail hind.2
    obtain ⟨eacc, _⟩ := accessesChilds_isolated p ps σ hheadtail
    have hFp : FDisjoint F (accesses p σ) := hF.left
    have hFps : FDisjoint F (accessesChilds ps σ) := eacc ▸ hF.right
    have hp' := ihp σ σ' F hwf.1 hFp hagree
    have hps' := ihps σ σ' F hwfps0 hind0 hFps hagree
    simp only [pstepChilds, hp', hps']

theorem pstep_locality {τ : Type} (p : ParM τ) (σ σ' : State) (F : List Loc)
    (hwf : WellFormed p σ)
    (hF : FDisjoint F (accesses p σ)) (hagree : ∀ l ∉ F, σ l = σ' l) :
    pstep p σ = pstep p σ' :=
  pstep_locality_all.1 p σ σ' F hwf hF hagree

theorem pstepChilds_locality {αs : List Type} (cs : Childs ParM αs) (σ σ' : State) (F : List Loc)
    (hwf : WellFormedChilds cs σ) (hind : IndepAll (childFootprints cs σ))
    (hF : FDisjoint F (accessesChilds cs σ)) (hagree : ∀ l ∉ F, σ l = σ' l) :
    pstepChilds cs σ = pstepChilds cs σ' :=
  pstep_locality_all.2 cs σ σ' F hwf hind hF hagree

/-- Two branches cannot race if their footprints are *contained* in an independent pair.
`no_race_of_indep` relaxed to subsets, which is the form needed once a branch has already advanced
some rounds and its remaining footprint has shrunk. -/
theorem no_race_of_sub {α β : Type} (p : ParM α) (q : ParM β) (σp σq : State) (fP fQ : Footprint)
    (hindep : Indep fP fQ)
    (hpr : (accesses p σp).reads ⊆ fP.reads) (hpw : (accesses p σp).writes ⊆ fP.writes)
    (hqr : (accesses q σq).reads ⊆ fQ.reads) (hqw : (accesses q σq).writes ⊆ fQ.writes) :
    ¬ racing (nextAccs p) (nextAccs q) = true := by
  refine no_race_contained _ _ fP fQ hindep ?_ ?_
  · intro lbl hl
    obtain ⟨h1, h2⟩ := nextAccs_subset_accesses p σp lbl hl
    exact ⟨fun h => hpw (h1 h), fun h => hpr (h2 h)⟩
  · intro lbl hl
    obtain ⟨h1, h2⟩ := nextAccs_subset_accesses q σq lbl hl
    exact ⟨fun h => hqw (h1 h), fun h => hqr (h2 h)⟩

/-- **A finished program reaches its canonical value, in the real semantics.** `pstep ... = none`
means no memory operation is left, but the program need not be syntactically `.pure`: nested `par`
nodes still have joins to perform. Those joins are real `step`s, so the sequential semantics walks
them out — leaving the state untouched, because a finished program's footprint is empty. -/
theorem pstep_none_reaches {τ : Type} :
    ∀ (p : ParM τ) (σ : State), WellFormed p σ → pstep p σ = none →
      Reaches (Conf.run p σ) (Conf.run (.pure (runSeq p σ).1) σ) := by
  have H : ∀ {τ : Type} (p : ParM τ), ∀ σ, WellFormed p σ → pstep p σ = none →
      Reaches (Conf.run p σ) (Conf.run (.pure (runSeq p σ).1) σ) := by
    intro τ p
    induction p using ParM.inductionOn with
    | hpure a => intro σ _ _; exact Reaches.refl
    | hread l k ih => intro σ _ h; simp [pstep] at h
    | hwrite l v k ih => intro σ _ h; simp [pstep] at h
    | hpar cs k _ ihk =>
        -- no children IH is needed: `reachesChilds_canonical` already runs every child out, and
        -- `reaches_par_of_reachesChilds` lifts that into the fork
        intro σ hwf h
        obtain ⟨hind, hwfcs, hwfk⟩ := hwf
        rcases hsc : pstepChilds cs σ with _ | ⟨cs', ws⟩
        · have hac : accessesChilds cs σ = Footprint.empty :=
            pstepChilds_none_accesses cs σ hsc
          have hσ1 : (runChilds cs σ).2 = σ := by
            funext m; exact runChilds_frame cs σ m (by simp [hac, Footprint.empty])
          have hk : pstep (k (runChilds cs σ).1) σ = none := by simpa [pstep, hsc] using h
          have hRc := reachesChilds_canonical cs σ hwfcs hind
          have hnr : ∀ cs'' σ'', ReachesChilds cs σ cs'' σ'' →
              racingAll (nextAccsChilds cs'') = false :=
            fun cs'' σ'' hR =>
              racingAll_of_indepAll cs'' σ'' (reachesChilds_preserves hR hwfcs hind).2
          have hRpar := reaches_par_of_reachesChilds k hRc hnr
          have hjoin : Conf.run (k (runChilds cs σ).1) (runChilds cs σ).2 ∈
              stepC (Conf.run (.par (pureChilds _ (runChilds cs σ).1) k) (runChilds cs σ).2) := by
            have hap := allPure_pureChilds _ (runChilds cs σ).1
            have hnr0 := hnr _ _ hRc
            simp only [stepC, step, hnr0, Bool.false_eq_true, ite_false, hap]
            simp
          have r4 := ihk _ σ (by rw [hσ1] at hwfk; exact hwfk) hk
          have he : runSeq (.par cs k) σ = runSeq (k (runChilds cs σ).1) σ := by
            simp only [runSeq, hσ1]
          rw [he]
          rw [hσ1] at hRpar hjoin
          exact (hRpar.tail hjoin).trans r4
        · simp [pstep, hsc] at h
  exact fun p σ => H p σ

/-- **A parallel round is a sequence of ordinary `step`s.** One `pstep` round — every ready branch
advancing at once — is realised in the real semantics by `p`'s move, then `q`'s, then whatever joins
fall due, and the round's batched writes land in exactly the state that schedule produces.

This is the bridge that makes the round semantics cheap: `runSeq_invariant_chain`,
`WellFormed_preserved` and `subset_chain` are already proved for arbitrary `Reaches` derivations, so
every invariant a round must preserve is inherited (`pstep_combined`) rather than re-proved by a
second induction over `pstep`. The proof is where `reaches_par_left`/`reaches_par_right` and their
non-racing side conditions get discharged. -- ref: docs/cost.md; Brookes CONCUR'04 §5 -/
theorem pstep_reaches_all :
    (∀ {τ : Type} (p : ParM τ), ∀ σ, WellFormed p σ → ∀ (p' : ParM τ) (ws : List (Loc × Val)),
        pstep p σ = some (p', ws) → Reaches (Conf.run p σ) (Conf.run p' (applyAll σ ws))) ∧
    (∀ {αs : List Type} (cs : Childs ParM αs), ∀ σ, WellFormedChilds cs σ →
        IndepAll (childFootprints cs σ) → ∀ (cs' : Childs ParM αs) (ws : List (Loc × Val)),
        pstepChilds cs σ = some (cs', ws) → ReachesChilds cs σ cs' (applyAll σ ws)) := by
  refine ParM.mutualInduction ?_ ?_ ?_ ?_ ?_ ?_
  · intro α a σ _ p' ws h; simp [pstep] at h
  · intro α l k ih σ _ p' ws h
    simp only [pstep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hp, hws⟩ := h
    rw [← hp, ← hws]
    exact Reaches.single (by simp [stepC, step, applyAll])
  · intro α l v k ih σ _ p' ws h
    simp only [pstep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hp, hws⟩ := h
    rw [← hp, ← hws]
    exact Reaches.single (by simp [stepC, step, applyAll])
  · -- a fork: either the children block took a round (lift it), or it is finished and the round is
    -- the continuation's (run the children out, join, then continue)
    intro β αs cs k ih2 ihk σ hwf p' ws h
    obtain ⟨hind, hwfcs, hwfk⟩ := hwf
    have hnr : ∀ cs'' σ'', ReachesChilds cs σ cs'' σ'' →
        racingAll (nextAccsChilds cs'') = false :=
      fun cs'' σ'' hR => racingAll_of_indepAll cs'' σ'' (reachesChilds_preserves hR hwfcs hind).2
    rcases hsc : pstepChilds cs σ with _ | ⟨cs₂, ws₂⟩
    · -- the join
      have hac : accessesChilds cs σ = Footprint.empty := pstepChilds_none_accesses cs σ hsc
      have hσ1 : (runChilds cs σ).2 = σ := by
        funext m; exact runChilds_frame cs σ m (by simp [hac, Footprint.empty])
      have hk : pstep (k (runChilds cs σ).1) σ = some (p', ws) := by simpa [pstep, hsc] using h
      have hRc := reachesChilds_canonical cs σ hwfcs hind
      have hRpar := reaches_par_of_reachesChilds k hRc hnr
      have hjoin : Conf.run (k (runChilds cs σ).1) (runChilds cs σ).2 ∈
          stepC (Conf.run (.par (pureChilds _ (runChilds cs σ).1) k) (runChilds cs σ).2) := by
        have hap := allPure_pureChilds _ (runChilds cs σ).1
        have hnr0 := hnr _ _ hRc
        simp only [stepC, step, hnr0, Bool.false_eq_true, ite_false, hap]
        simp
      rw [hσ1] at hRpar hjoin
      have r4 := ihk _ σ (by rw [hσ1] at hwfk; exact hwfk) p' ws hk
      exact (hRpar.tail hjoin).trans r4
    · -- the block took a round
      simp only [pstep, hsc, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hp, hws⟩ := h
      have hRc := ih2 σ hwfcs hind cs₂ ws₂ hsc
      rw [← hp, ← hws]
      exact reaches_par_of_reachesChilds k hRc hnr
  · intro σ _ _ cs' ws h; simp [pstepChilds] at h
  · -- **the 2-to-N step**: head alone, tail alone, or both — and for "both" the tail's round has to
    -- be replayed from after the head's writes, which `pstepChilds_locality` permits because the
    -- head's writes miss the tail entirely
    intro α αs p ps ihp ihps σ hwf hind cs' ws h
    have hheadtail : Indep (accesses p σ) (accessesChilds ps (runSeq p σ).2) :=
      indep_accessesChilds ps (accesses p σ) (runSeq p σ).2 hind.1
    have hwfps0 : WellFormedChilds ps σ := wellFormedChilds_branch_shift p ps σ hheadtail hwf.2
    have hind0 : IndepAll (childFootprints ps σ) := indepAll_branch_shift p ps σ hheadtail hind.2
    obtain ⟨eacc, _⟩ := accessesChilds_isolated p ps σ hheadtail
    have hindep0 : Indep (accesses p σ) (accessesChilds ps σ) := eacc ▸ hheadtail
    rcases hsp : pstep p σ with _ | ⟨p', wp⟩
    · rcases hsps : pstepChilds ps σ with _ | ⟨ps', wq⟩
      · simp [pstepChilds, hsp, hsps] at h
      · -- tail alone
        simp only [pstepChilds, hsp, hsps, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hcs, hws⟩ := h
        rw [← hcs, ← hws]
        exact reachesChilds_tail p (ihps σ hwfps0 hind0 ps' wq hsps)
    · rcases hsps : pstepChilds ps σ with _ | ⟨ps', wq⟩
      · -- head alone
        simp only [pstepChilds, hsp, hsps, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hcs, hws⟩ := h
        rw [← hcs, ← hws]
        rcases reachesChilds_head p ps σ _ (ihp σ hwf.1 p' wp hsp) with
          ⟨p'', σ'', heq, hlift⟩ | hwrong
        · obtain ⟨hp'', hσ''⟩ : p'' = p' ∧ σ'' = applyAll σ wp := by simpa using heq.symm
          rw [hp'', hσ''] at hlift; exact hlift
        · exact absurd hwrong (by simp)
      · -- both: the head's round, then the tail's replayed after the head's writes
        simp only [pstepChilds, hsp, hsps, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hcs, hws⟩ := h
        rw [← hcs, ← hws]
        -- leg 1: the head moves, the tail stands still
        have leg1 : ReachesChilds (Childs.cons p ps) σ (Childs.cons p' ps) (applyAll σ wp) := by
          rcases reachesChilds_head p ps σ _ (ihp σ hwf.1 p' wp hsp) with
            ⟨p'', σ'', heq, hlift⟩ | hwrong
          · obtain ⟨hp'', hσ''⟩ : p'' = p' ∧ σ'' = applyAll σ wp := by simpa using heq.symm
            rw [hp'', hσ''] at hlift; exact hlift
          · exact absurd hwrong (by simp)
        -- the head's writes miss the tail, so its round replays verbatim after them
        have hFps : FDisjoint (accesses p σ).writes (accessesChilds ps σ) :=
          ⟨hindep0.2.1, hindep0.1⟩
        have hagree : ∀ l ∉ (accesses p σ).writes, σ l = applyAll σ wp l := fun l hl =>
          (applyAll_frame wp σ l
            (fun hm => hl (pstep_writes_subset p σ hwf.1 p' wp hsp hm))).symm
        have hsps' : pstepChilds ps (applyAll σ wp) = some (ps', wq) :=
          (pstepChilds_locality ps σ (applyAll σ wp) _ hwfps0 hind0 hFps hagree).symm.trans hsps
        have hwfps1 : WellFormedChilds ps (applyAll σ wp) :=
          (WellFormedChilds_locality ps σ (applyAll σ wp) _ hFps hagree).mp hwfps0
        have hind1 : IndepAll (childFootprints ps (applyAll σ wp)) := by
          rw [← childFootprints_locality ps σ (applyAll σ wp) _ hFps hagree]; exact hind0
        -- leg 2: the tail moves, the head standing still
        have leg2 : ReachesChilds (Childs.cons p' ps) (applyAll σ wp)
            (Childs.cons p' ps') (applyAll (applyAll σ wp) wq) :=
          reachesChilds_tail p' (ihps (applyAll σ wp) hwfps1 hind1 ps' wq hsps')
        rw [applyAll_append]
        exact leg1.trans leg2

theorem pstep_reaches {τ : Type} :
    ∀ (p : ParM τ) (σ : State), WellFormed p σ → ∀ (p' : ParM τ) (ws : List (Loc × Val)),
      pstep p σ = some (p', ws) → Reaches (Conf.run p σ) (Conf.run p' (applyAll σ ws)) :=
  fun p σ hwf p' ws h => pstep_reaches_all.1 p σ hwf p' ws h

theorem pstepChilds_reaches {αs : List Type} :
    ∀ (cs : Childs ParM αs) (σ : State), WellFormedChilds cs σ →
      IndepAll (childFootprints cs σ) → ∀ (cs' : Childs ParM αs) (ws : List (Loc × Val)),
      pstepChilds cs σ = some (cs', ws) → ReachesChilds cs σ cs' (applyAll σ ws) :=
  fun cs σ hwf hind cs' ws h => pstep_reaches_all.2 cs σ hwf hind cs' ws h

/-- Everything a round preserves, in one package: the residual is still well formed, it still
computes the same canonical result and final heap, and its footprint has only shrunk. Inherited
wholesale from the `Reaches`-level chain lemmas through `pstep_reaches`; this is the lemma the
`ptime` proofs actually call. -/
theorem pstep_combined {τ : Type} (p : ParM τ) (σ : State) (hwf : WellFormed p σ)
    (p' : ParM τ) (ws : List (Loc × Val)) (h : pstep p σ = some (p', ws)) :
    WellFormed p' (applyAll σ ws) ∧ runSeq p' (applyAll σ ws) = runSeq p σ ∧
    (accesses p' (applyAll σ ws)).reads ⊆ (accesses p σ).reads ∧
    (accesses p' (applyAll σ ws)).writes ⊆ (accesses p σ).writes := by
  have hr := pstep_reaches p σ hwf p' ws h
  obtain ⟨hwf', heq⟩ := runSeq_invariant_chain p σ hwf _ hr p' (applyAll σ ws) rfl
  obtain ⟨hsr, hsw⟩ := subset_chain p σ hwf _ hr p' (applyAll σ ws) rfl
  exact ⟨hwf', heq, hsr, hsw⟩

/-- A program with no round left to take has zero work. The converse direction to `ptime_le_work`. -/
theorem pstep_none_work_all :
    (∀ {τ : Type} (p : ParM τ), ∀ σ, pstep p σ = none → work p σ = 0) ∧
    (∀ {αs : List Type} (cs : Childs ParM αs), ∀ σ,
        pstepChilds cs σ = none → workChilds cs σ = 0) := by
  refine ParM.mutualInduction ?_ ?_ ?_ ?_ ?_ ?_
  · intro α a σ _; rfl
  · intro α l k ih σ h; simp [pstep] at h
  · intro α l v k ih σ h; simp [pstep] at h
  · intro β αs cs k ih2 ihk σ h
    rcases hsc : pstepChilds cs σ with _ | ⟨cs', ws⟩
    · have hac : accessesChilds cs σ = Footprint.empty := pstepChilds_none_accesses cs σ hsc
      have hσ1 : (runChilds cs σ).2 = σ := by
        funext m; exact runChilds_frame cs σ m (by simp [hac, Footprint.empty])
      have hk : pstep (k (runChilds cs σ).1) σ = none := by simpa [pstep, hsc] using h
      show work (ParM.par cs k) σ = 0
      simp only [work, hσ1, ih2 σ hsc, ihk _ σ hk]
    · simp [pstep, hsc] at h
  · intro σ _; rfl
  · -- **the 2-to-N step**: no round left means neither side has work left
    intro α αs p ps ihp ihps σ h
    rcases hsp : pstep p σ with _ | ⟨p', wp⟩
    · rcases hsps : pstepChilds ps σ with _ | ⟨ps', wq⟩
      · have hap : accesses p σ = Footprint.empty := pstep_none_accesses p σ hsp
        have hσ1 : (runSeq p σ).2 = σ := by
          funext m; exact runSeq_frame p σ m (by simp [hap, Footprint.empty])
        show workChilds (Childs.cons p ps) σ = 0
        simp only [workChilds, hσ1, ihp σ hsp, ihps σ hsps]
      · simp [pstepChilds, hsp, hsps] at h
    · rcases hsps : pstepChilds ps σ with _ | ⟨ps', wq⟩ <;> simp [pstepChilds, hsp, hsps] at h

theorem pstep_none_work {τ : Type} :
    ∀ (p : ParM τ) (σ : State), pstep p σ = none → work p σ = 0 :=
  fun p σ h => pstep_none_work_all.1 p σ h

theorem pstepChilds_none_work {αs : List Type} :
    ∀ (cs : Childs ParM αs) (σ : State), pstepChilds cs σ = none → workChilds cs σ = 0 :=
  fun cs σ h => pstep_none_work_all.2 cs σ h

/-- A well-formed `par` node yields a well-formed `parPair` of its first two children when the fork
has exactly two: the independence and per-child obligations are the same, and `parPair`'s continuation
is a `pure`, whose obligation is `trivial`. -/
theorem wellFormed_parPair_of_par {α β γ : Type} (p : ParM α) (q : ParM β)
    (k : Results [α, β] → ParM γ) (σ : State)
    (hwf : WellFormed (ParM.par (Childs.cons p (Childs.cons q Childs.nil)) k) σ) :
    WellFormed (ParM.parPair p q) σ :=
  ⟨hwf.1, hwf.2.1, trivial⟩

/-- **The binary reading of `WellFormed (parPair p q) σ`.** `par` is N-ary, so the obligation is an
`IndepAll`/`WellFormedChilds` pair over a two-element spine; this projects out the three facts the
binary cost proofs quantify over. -- ref: docs/cost.md -/
theorem wellFormed_parPair_parts {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (hwf : WellFormed (ParM.parPair p q) σ) :
    Indep (accesses p σ) (accesses q (runSeq p σ).2) ∧ WellFormed p σ ∧
      WellFormed q (runSeq p σ).2 :=
  ⟨hwf.1.1 (accesses q (runSeq p σ).2) (by simp), hwf.2.1.1, hwf.2.1.2.1⟩

/-- The children's canonical run is invariant along a whole children-level run — `stepChilds_combined`
iterated. What lets a round's residual fork keep the same continuation state. -/
theorem reachesChilds_runChilds {αs : List Type} {cs cs' : Childs ParM αs} {σ σ' : State}
    (h : ReachesChilds cs σ cs' σ') (hwf : WellFormedChilds cs σ)
    (hind : IndepAll (childFootprints cs σ)) : runChilds cs' σ' = runChilds cs σ := by
  induction h with
  | refl => rfl
  | @tail a' σa' a'' σa'' hreach hmem ih =>
      obtain ⟨hwf', hind'⟩ := reachesChilds_preserves hreach hwf hind
      obtain ⟨e, _⟩ := stepChilds_combined a' σa' hwf' hind' a'' σa'' hmem
      exact e.trans ih

/-- The children-block footprint only shrinks along a children-level run — `stepChilds_subset_rw`
iterated, the `ReachesChilds` analogue of `subset_chain`. -/
theorem reachesChilds_subset {αs : List Type} {cs cs' : Childs ParM αs} {σ σ' : State}
    (h : ReachesChilds cs σ cs' σ') (hwf : WellFormedChilds cs σ)
    (hind : IndepAll (childFootprints cs σ)) :
    (accessesChilds cs' σ').reads ⊆ (accessesChilds cs σ).reads ∧
    (accessesChilds cs' σ').writes ⊆ (accessesChilds cs σ).writes := by
  induction h with
  | refl => exact ⟨fun _ hx => hx, fun _ hx => hx⟩
  | @tail a' σa' a'' σa'' hreach hmem ih =>
      obtain ⟨hwf', hind'⟩ := reachesChilds_preserves hreach hwf hind
      obtain ⟨-, hr, hw⟩ := stepChilds_subset_rw a' σa' hwf' hind' a'' σa'' hmem
      exact ⟨fun _ hx => ih.1 (hr hx), fun _ hx => ih.2 (hw hx)⟩

/-- The children-level `pstep_combined`: everything a children-block round preserves, in one
package — well-formedness, pairwise independence, the canonical run, and footprint containment. -/
theorem pstepChilds_combined {αs : List Type} (cs : Childs ParM αs) (σ : State)
    (hwf : WellFormedChilds cs σ) (hind : IndepAll (childFootprints cs σ))
    (cs' : Childs ParM αs) (ws : List (Loc × Val)) (h : pstepChilds cs σ = some (cs', ws)) :
    WellFormedChilds cs' (applyAll σ ws) ∧
    IndepAll (childFootprints cs' (applyAll σ ws)) ∧
    runChilds cs' (applyAll σ ws) = runChilds cs σ ∧
    (accessesChilds cs' (applyAll σ ws)).reads ⊆ (accessesChilds cs σ).reads ∧
    (accessesChilds cs' (applyAll σ ws)).writes ⊆ (accessesChilds cs σ).writes := by
  have hr := pstepChilds_reaches cs σ hwf hind cs' ws h
  obtain ⟨hwf', hind'⟩ := reachesChilds_preserves hr hwf hind
  obtain ⟨hsr, hsw⟩ := reachesChilds_subset hr hwf hind
  exact ⟨hwf', hind', reachesChilds_runChilds hr hwf hind, hsr, hsw⟩

/-- **A round strictly reduces the remaining work.** This is what makes `time`'s fuel sufficient:
`work p σ` rounds always finish the program. The `par` case cancels the continuation's work exactly,
by reading the join state off `pstepChilds_combined` — a round of the children block leaves their
canonical run, and hence the continuation's own work, untouched. -/
theorem work_pstep_lt_all :
    (∀ {τ : Type} (p : ParM τ), ∀ σ, WellFormed p σ → ∀ (p' : ParM τ) (ws : List (Loc × Val)),
        pstep p σ = some (p', ws) → work p' (applyAll σ ws) < work p σ) ∧
    (∀ {αs : List Type} (cs : Childs ParM αs), ∀ σ, WellFormedChilds cs σ →
        IndepAll (childFootprints cs σ) → ∀ (cs' : Childs ParM αs) (ws : List (Loc × Val)),
        pstepChilds cs σ = some (cs', ws) → workChilds cs' (applyAll σ ws) < workChilds cs σ) := by
  refine ParM.mutualInduction ?_ ?_ ?_ ?_ ?_ ?_
  · intro α a σ _ p' ws h; simp [pstep] at h
  · intro α l k ih σ _ p' ws h
    simp only [pstep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [work, applyAll]
  · intro α l v k ih σ _ p' ws h
    simp only [pstep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [work, applyAll]
  · intro β αs cs k ih2 ihk σ hwf P' ws h
    obtain ⟨hind, hwfcs, hwfk⟩ := hwf
    rcases hsc : pstepChilds cs σ with _ | ⟨cs', wsc⟩
    · -- the join: the block is finished, so the whole node's work is the continuation's
      have hac : accessesChilds cs σ = Footprint.empty := pstepChilds_none_accesses cs σ hsc
      have hσ1 : (runChilds cs σ).2 = σ := by
        funext m; exact runChilds_frame cs σ m (by simp [hac, Footprint.empty])
      have hw0 : workChilds cs σ = 0 := pstepChilds_none_work cs σ hsc
      have hk : pstep (k (runChilds cs σ).1) σ = some (P', ws) := by simpa [pstep, hsc] using h
      have hlt := ihk _ σ (by rw [hσ1] at hwfk; exact hwfk) P' ws hk
      show work P' (applyAll σ ws) < work (ParM.par cs k) σ
      simp only [work, hσ1, hw0]
      omega
    · -- the block took a round: the continuation's work is literally unchanged
      simp only [pstep, hsc, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨-, -, hrc, -, -⟩ := pstepChilds_combined cs σ hwfcs hind cs' wsc hsc
      have hlt := ih2 σ hwfcs hind cs' wsc hsc
      show work (ParM.par cs' k) (applyAll σ wsc) < work (ParM.par cs k) σ
      simp only [work, hrc]
      omega
  · intro σ _ _ cs' ws h; simp [pstepChilds] at h
  · -- **the 2-to-N step**: head alone, tail alone, or both
    intro α αs p ps ihp ihps σ hwf hind cs' ws h
    have hheadtail : Indep (accesses p σ) (accessesChilds ps (runSeq p σ).2) :=
      indep_accessesChilds ps (accesses p σ) (runSeq p σ).2 hind.1
    have hwfps0 : WellFormedChilds ps σ := wellFormedChilds_branch_shift p ps σ hheadtail hwf.2
    have hind0 : IndepAll (childFootprints ps σ) := indepAll_branch_shift p ps σ hheadtail hind.2
    obtain ⟨eacc, _⟩ := accessesChilds_isolated p ps σ hheadtail
    have hindep0 : Indep (accesses p σ) (accessesChilds ps σ) := eacc ▸ hheadtail
    have ework : workChilds ps (runSeq p σ).2 = workChilds ps σ :=
      workChilds_locality ps (runSeq p σ).2 σ (accesses p σ).writes
        ⟨hheadtail.2.1, hheadtail.1⟩ (runSeq_frame p σ)
    rcases hsp : pstep p σ with _ | ⟨p', wp⟩
    · rcases hsps : pstepChilds ps σ with _ | ⟨ps', wq⟩
      · simp [pstepChilds, hsp, hsps] at h
      · -- tail alone: the head is finished, so it neither works nor moves the heap
        simp only [pstepChilds, hsp, hsps, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hwp : work p σ = 0 := pstep_none_work p σ hsp
        have hap : accesses p σ = Footprint.empty := pstep_none_accesses p σ hsp
        have hFp : FDisjoint (accessesChilds ps σ).writes (accesses p σ) := by
          rw [hap]
          exact ⟨fun l _ hm => by simp [Footprint.empty] at hm,
            fun l _ hm => by simp [Footprint.empty] at hm⟩
        have hagree : ∀ l ∉ (accessesChilds ps σ).writes, σ l = applyAll σ wq l := fun l hl =>
          (applyAll_frame wq σ l
            (fun hm => hl (pstepChilds_writes_subset ps σ hwfps0 hind0 ps' wq hsps hm))).symm
        have hwp' : work p (applyAll σ wq) = 0 := by
          rw [← work_locality p σ (applyAll σ wq) _ hFp hagree]; exact hwp
        obtain ⟨eapq, -, -⟩ := accesses_runSeq_locality p σ (applyAll σ wq) _ hFp hagree
        have hσq1 : (runSeq p (applyAll σ wq)).2 = applyAll σ wq := by
          funext m
          exact runSeq_frame p (applyAll σ wq) m (by rw [← eapq, hap]; simp [Footprint.empty])
        have hlt := ihps σ hwfps0 hind0 ps' wq hsps
        show work p (applyAll σ wq) + workChilds ps' (runSeq p (applyAll σ wq)).2
            < work p σ + workChilds ps (runSeq p σ).2
        rw [hwp', hwp, hσq1, ework]
        omega
    · rcases hsps : pstepChilds ps σ with _ | ⟨ps', wq⟩
      · -- head alone: the head's round leaves the canonical run, hence the tail's term, unchanged
        simp only [pstepChilds, hsp, hsps, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨-, hrsp, -, -⟩ := pstep_combined p σ hwf.1 p' wp hsp
        have hlt := ihp σ hwf.1 p' wp hsp
        show work p' (applyAll σ wp) + workChilds ps (runSeq p' (applyAll σ wp)).2
            < work p σ + workChilds ps (runSeq p σ).2
        rw [hrsp]
        omega
      · -- both: compose the two decreases, the tail's replayed after the head's writes
        simp only [pstepChilds, hsp, hsps, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨-, hrsp, hsubpr, hsubpw⟩ := pstep_combined p σ hwf.1 p' wp hsp
        obtain ⟨-, -, -, hsubqr, hsubqw⟩ := pstepChilds_combined ps σ hwfps0 hind0 ps' wq hsps
        have hltp := ihp σ hwf.1 p' wp hsp
        have hltq := ihps σ hwfps0 hind0 ps' wq hsps
        have hWpq : applyAll σ (wp ++ wq) = applyAll (applyAll σ wp) wq := applyAll_append σ wp wq
        -- ① the head's residual is undisturbed by the tail's batch
        have hFp : FDisjoint (accessesChilds ps σ).writes (accesses p' (applyAll σ wp)) :=
          ⟨fun l hl hm => hindep0.2.2 l hl (hsubpr hm),
           fun l hl hm => hindep0.1 l (hsubpw hm) hl⟩
        have hagree1 : ∀ l ∉ (accessesChilds ps σ).writes,
            applyAll σ wp l = applyAll σ (wp ++ wq) l := by
          intro l hl
          rw [hWpq]
          exact (applyAll_frame wq (applyAll σ wp) l
            (fun hm => hl (pstepChilds_writes_subset ps σ hwfps0 hind0 ps' wq hsps hm))).symm
        have eA : work p' (applyAll σ wp) = work p' (applyAll σ (wp ++ wq)) :=
          work_locality p' (applyAll σ wp) _ _ hFp hagree1
        obtain ⟨eaccp', -, -⟩ := accesses_runSeq_locality p' (applyAll σ wp) _ _ hFp hagree1
        -- ② the tail's residual is undisturbed by the head's batch, nor by the head finishing
        have hFq : FDisjoint (accesses p σ).writes (accessesChilds ps' (applyAll σ wq)) :=
          ⟨fun l hl hm => hindep0.2.1 l hl (hsubqr hm),
           fun l hl hm => hindep0.1 l hl (hsubqw hm)⟩
        have hagree2 : ∀ l ∉ (accesses p σ).writes,
            applyAll σ wq l = (runSeq p' (applyAll σ (wp ++ wq))).2 l := by
          intro l hl
          have h1 : (runSeq p' (applyAll σ (wp ++ wq))).2 l = applyAll σ (wp ++ wq) l := by
            refine runSeq_frame p' _ l ?_
            rw [← eaccp']
            exact fun hm => hl (hsubpw hm)
          have h2 : applyAll σ (wp ++ wq) l = applyAll σ wq l := by
            rw [hWpq]
            refine applyAll_agree (accesses p σ).writes wq (applyAll σ wp) σ ?_ l hl
            intro m hm
            exact applyAll_frame wp σ m
              (fun hmm => hm (pstep_writes_subset p σ hwf.1 p' wp hsp hmm))
          rw [h1, h2]
        have eC : workChilds ps' (applyAll σ wq)
            = workChilds ps' (runSeq p' (applyAll σ (wp ++ wq))).2 :=
          workChilds_locality ps' (applyAll σ wq) _ _ hFq hagree2
        show work p' (applyAll σ (wp ++ wq))
            + workChilds ps' (runSeq p' (applyAll σ (wp ++ wq))).2
            < work p σ + workChilds ps (runSeq p σ).2
        rw [← eA, ← eC, ework]
        omega

theorem work_pstep_lt {τ : Type} :
    ∀ (p : ParM τ) (σ : State), WellFormed p σ → ∀ (p' : ParM τ) (ws : List (Loc × Val)),
      pstep p σ = some (p', ws) → work p' (applyAll σ ws) < work p σ :=
  fun p σ hwf p' ws h => work_pstep_lt_all.1 p σ hwf p' ws h

theorem workChilds_pstepChilds_lt {αs : List Type} :
    ∀ (cs : Childs ParM αs) (σ : State), WellFormedChilds cs σ →
      IndepAll (childFootprints cs σ) → ∀ (cs' : Childs ParM αs) (ws : List (Loc × Val)),
      pstepChilds cs σ = some (cs', ws) → workChilds cs' (applyAll σ ws) < workChilds cs σ :=
  fun cs σ hwf hind cs' ws h => work_pstep_lt_all.2 cs σ hwf hind cs' ws h

/-! ### `ptime`'s two equations, as rewrite rules

`ptime` is a fuel-recursive `match` on `pstep p σ`. `simp [ptime]` unfolds one level too far: it
rewrites under the scrutinee and leaves an unreduced `match` that nothing then fires on. These two
lemmas give the exact step instead, and every proof below rewrites with them rather than unfolding. -/

/-- A finished program takes no rounds. One of the two `ptime` step rules; use it in place of
`simp [ptime]`. -/
@[grind .]
theorem ptime_succ_none {τ : Type} (n : Nat) (p : ParM τ) (σ : State) (h : pstep p σ = none) :
    ptime (n + 1) p σ = 0 := by
  have e : ptime (n + 1) p σ =
      match pstep p σ with
      | none          => 0
      | some (p', ws) => 1 + ptime n p' (applyAll σ ws) := rfl
  rw [e, h]

/-- A program that takes a round costs that round plus the residual's rounds, counted from the heap
the round's writes produce. The other `ptime` step rule. -/
@[grind .]
theorem ptime_succ_some {τ : Type} (n : Nat) (p : ParM τ) (σ : State) (p' : ParM τ)
    (ws : List (Loc × Val)) (h : pstep p σ = some (p', ws)) :
    ptime (n + 1) p σ = 1 + ptime n p' (applyAll σ ws) := by
  have e : ptime (n + 1) p σ =
      match pstep p σ with
      | none           => 0
      | some (p'', ws') => 1 + ptime n p'' (applyAll σ ws') := rfl
  rw [e, h]

/-- `ptime_succ_none` at *any* fuel, including `0`. -/
theorem ptime_zero_of_none {τ : Type} (n : Nat) (p : ParM τ) (σ : State)
    (h : pstep p σ = none) : ptime n p σ = 0 := by
  cases n with
  | zero => rfl
  | succ n => exact ptime_succ_none n p σ h

/-- **Rounds never exceed operations**, at any fuel. Since each round performs at least one operation
(`work_pstep_lt`), `work p σ` rounds always suffice and `time`'s fuel is never the binding
constraint. -/
theorem ptime_le_work {τ : Type} : ∀ (n : Nat) (p : ParM τ) (σ : State), WellFormed p σ →
    ptime n p σ ≤ work p σ := by
  intro n
  induction n with
  | zero => intro p σ _; simp only [ptime]; omega
  | succ n ih =>
      intro p σ hwf
      rcases hs : pstep p σ with _ | ⟨p', ws⟩
      · rw [ptime_succ_none n p σ hs]; omega
      · have h1 := ih p' (applyAll σ ws) (pstep_combined p σ hwf p' ws hs).1
        have h2 := work_pstep_lt p σ hwf p' ws hs
        rw [ptime_succ_some n p σ _ _ hs]
        omega

/-- One extra unit of fuel changes nothing once the fuel already covers the work. -/
theorem ptime_succ_eq {τ : Type} : ∀ (n : Nat) (p : ParM τ) (σ : State), WellFormed p σ →
    work p σ ≤ n → ptime (n + 1) p σ = ptime n p σ := by
  intro n
  induction n with
  | zero =>
      intro p σ hwf hw
      rcases hs : pstep p σ with _ | ⟨p', ws⟩
      · rw [ptime_succ_none 0 p σ hs]; rfl
      · have := work_pstep_lt p σ hwf p' ws hs; omega
  | succ n ih =>
      intro p σ hwf hw
      rcases hs : pstep p σ with _ | ⟨p', ws⟩
      · rw [ptime_succ_none (n + 1) p σ hs, ptime_succ_none n p σ hs]
      · have hlt := work_pstep_lt p σ hwf p' ws hs
        have hrec := ih p' (applyAll σ ws) (pstep_combined p σ hwf p' ws hs).1 (by omega)
        rw [ptime_succ_some (n + 1) p σ _ _ hs, ptime_succ_some n p σ _ _ hs, hrec]

/-- `ptime` is insensitive to any surplus fuel: once the fuel covers the work, adding more leaves the
count alone. `ptime_succ_eq` iterated. -/
theorem ptime_fuel_indep {τ : Type} : ∀ (d n : Nat) (p : ParM τ) (σ : State), WellFormed p σ →
    work p σ ≤ n → ptime (n + d) p σ = ptime n p σ := by
  intro d
  induction d with
  | zero => intro n p σ _ _; rfl
  | succ d ih =>
      intro n p σ hwf hw
      have e : n + (d + 1) = (n + d) + 1 := by omega
      rw [e, ptime_succ_eq (n + d) p σ hwf (by omega), ih n p σ hwf hw]

/-- Any fuel strictly past the work computes `time`. This is how a `ptime` result at a convenient
shared fuel is converted into a statement about `time`, whose own fuel is `work p σ + 1`. -/
theorem ptime_eq_time {τ : Type} (p : ParM τ) (σ : State) (hwf : WellFormed p σ) (n : Nat)
    (hn : work p σ < n) : ptime n p σ = time p σ := by
  have e : n = (work p σ + 1) + (n - (work p σ + 1)) := by omega
  rw [e, ptime_fuel_indep _ _ p σ hwf (by omega)]
  rfl

/-- **A program's round count does not depend on memory it never touches.** `pstep_locality` gives the
first round; `pstep_combined` re-establishes `WellFormed` and footprint containment for the residual,
so the argument iterates over the fuel.

This is the one place where independence is actually spent in deriving `max`: it is what says a
branch's remaining rounds come out the same whether or not the *other* branch's writes from the same
round have already landed. It is false for interfering branches — see the `RacyCost` section. -/
theorem ptime_locality {τ : Type} : ∀ (n : Nat) (p : ParM τ) (σ σ' : State) (F : List Loc),
    WellFormed p σ → FDisjoint F (accesses p σ) → (∀ l ∉ F, σ l = σ' l) →
    ptime n p σ = ptime n p σ' := by
  intro n
  induction n with
  | zero => intro p σ σ' F _ _ _; rfl
  | succ n ih =>
      intro p σ σ' F hwf hF hagree
      have hstep : pstep p σ = pstep p σ' := pstep_locality p σ σ' F hwf hF hagree
      rcases hs : pstep p σ with _ | ⟨p', ws⟩
      · rw [ptime_succ_none n p σ hs, ptime_succ_none n p σ' (hstep.symm.trans hs)]
      · obtain ⟨hwf', -, hsr, hsw⟩ := pstep_combined p σ hwf p' ws hs
        have hrec : ptime n p' (applyAll σ ws) = ptime n p' (applyAll σ' ws) :=
          ih p' (applyAll σ ws) (applyAll σ' ws) F hwf'
            ⟨fun l hl hm => hF.1 l hl (hsr hm), fun l hl hm => hF.2 l hl (hsw hm)⟩
            (applyAll_agree F ws σ σ' hagree)
        rw [ptime_succ_some n p σ _ _ hs,
          ptime_succ_some n p σ' _ _ (hstep.symm.trans hs), hrec]

/-! ### The general law: a fork's span is a fold of `max` over its children

`max` appears nowhere in `pstep`; round-counting forces it, via `ptime_locality` — which is why the
law needs `WellFormed`. N-ary, so `List.foldr max 0` over `ptimeChilds`; binary `max` is the
two-child case. -- ref: docs/cost.md; Blelloch & Greiner ICFP'96 (where `max` is stipulated) -/

/-- Each child's own round count, measured from the **pre-fork** heap. Nothing is staggered here,
unlike `workChilds`: children run concurrently, and under `Indep` it makes no difference. -/
def ptimes {αs : List Type} : Nat → Childs ParM αs → State → List Nat
  | _, .nil,       _ => []
  | n, .cons p ps, σ => ptime n p σ :: ptimes n ps σ

/-- **The children block's rounds: the slowest child's count.** A `List.foldr max 0`, which is the
whole of the design decision — one round advances every ready child, so a block costs the maximum and
not the sum. For two children it is `max a (max b 0) = max a b`. -/
def ptimeChilds {αs : List Type} (n : Nat) (cs : Childs ParM αs) (σ : State) : Nat :=
  (ptimes n cs σ).foldr max 0

@[simp] theorem ptimeChilds_nil (n : Nat) (σ : State) :
    ptimeChilds n (Childs.nil : Childs ParM []) σ = 0 := rfl

@[simp] theorem ptimeChilds_cons {α : Type} {αs : List Type} (n : Nat) (p : ParM α)
    (ps : Childs ParM αs) (σ : State) :
    ptimeChilds n (Childs.cons p ps) σ = max (ptime n p σ) (ptimeChilds n ps σ) := rfl

/-- No fuel, no rounds — the base case of every fuel induction below. -/
@[simp] theorem ptimeChilds_zero {αs : List Type} (cs : Childs ParM αs) (σ : State) :
    ptimeChilds 0 cs σ = 0 := by
  induction cs with
  | nil => rfl
  | cons p ps ih => rw [ptimeChilds_cons, ih]; simp [ptime]

/-- A children block with no round left costs nothing: every child is finished. -/
theorem ptimeChilds_zero_of_none {αs : List Type} (cs : Childs ParM αs) :
    ∀ (n : Nat) (σ : State), pstepChilds cs σ = none → ptimeChilds n cs σ = 0 := by
  induction cs with
  | nil => intro n σ _; rfl
  | cons p ps ih =>
      intro n σ h
      rcases hsp : pstep p σ with _ | ⟨p', wp⟩
      · rcases hsps : pstepChilds ps σ with _ | ⟨ps', wq⟩
        · rw [ptimeChilds_cons, ptime_zero_of_none n p σ hsp, ih n σ hsps]; omega
        · simp [pstepChilds, hsp, hsps] at h
      · rcases hsps : pstepChilds ps σ with _ | ⟨ps', wq⟩ <;> simp [pstepChilds, hsp, hsps] at h

/-- **A children block's round count is local** — the children-level `ptime_locality`. -/
theorem ptimeChilds_locality {αs : List Type} (cs : Childs ParM αs) :
    ∀ (n : Nat) (σ σ' : State) (F : List Loc), WellFormedChilds cs σ →
      IndepAll (childFootprints cs σ) → FDisjoint F (accessesChilds cs σ) →
      (∀ l ∉ F, σ l = σ' l) → ptimeChilds n cs σ = ptimeChilds n cs σ' := by
  induction cs with
  | nil => intro n σ σ' F _ _ _ _; rfl
  | cons p ps ih =>
      intro n σ σ' F hwf hind hF hagree
      have hheadtail : Indep (accesses p σ) (accessesChilds ps (runSeq p σ).2) :=
        indep_accessesChilds ps (accesses p σ) (runSeq p σ).2 hind.1
      have hwfps0 : WellFormedChilds ps σ := wellFormedChilds_branch_shift p ps σ hheadtail hwf.2
      have hind0 : IndepAll (childFootprints ps σ) := indepAll_branch_shift p ps σ hheadtail hind.2
      obtain ⟨eacc, _⟩ := accessesChilds_isolated p ps σ hheadtail
      have hFp : FDisjoint F (accesses p σ) := hF.left
      have hFps : FDisjoint F (accessesChilds ps σ) := eacc ▸ hF.right
      rw [ptimeChilds_cons, ptimeChilds_cons, ptime_locality n p σ σ' F hwf.1 hFp hagree,
        ih n σ σ' F hwfps0 hind0 hFps hagree]

/-- **One round costs the block exactly one.** The N-ary heart of the span law: a round advances
*every* ready child at once, so the block's count drops by one whichever children moved. `Indep` is
spent here, through `ptime_locality`/`ptimeChilds_locality` — a child that moved must take the same
remaining rounds whether or not its siblings' writes from this same round have already landed. -/
theorem ptimeChilds_succ_some {αs : List Type} (cs : Childs ParM αs) :
    ∀ (n : Nat) (σ : State), WellFormedChilds cs σ → IndepAll (childFootprints cs σ) →
      ∀ (cs' : Childs ParM αs) (ws : List (Loc × Val)), pstepChilds cs σ = some (cs', ws) →
      ptimeChilds (n + 1) cs σ = 1 + ptimeChilds n cs' (applyAll σ ws) := by
  induction cs with
  | nil => intro n σ _ _ cs' ws h; simp [pstepChilds] at h
  | cons p ps ih =>
      intro n σ hwf hind cs' ws h
      have hheadtail : Indep (accesses p σ) (accessesChilds ps (runSeq p σ).2) :=
        indep_accessesChilds ps (accesses p σ) (runSeq p σ).2 hind.1
      have hwfps0 : WellFormedChilds ps σ := wellFormedChilds_branch_shift p ps σ hheadtail hwf.2
      have hind0 : IndepAll (childFootprints ps σ) := indepAll_branch_shift p ps σ hheadtail hind.2
      obtain ⟨eacc, _⟩ := accessesChilds_isolated p ps σ hheadtail
      have hindep0 : Indep (accesses p σ) (accessesChilds ps σ) := eacc ▸ hheadtail
      rcases hsp : pstep p σ with _ | ⟨p', wp⟩
      · rcases hsps : pstepChilds ps σ with _ | ⟨ps', wq⟩
        · simp [pstepChilds, hsp, hsps] at h
        · -- tail alone: the head is finished and stays finished after the tail's writes
          simp only [pstepChilds, hsp, hsps, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hap : accesses p σ = Footprint.empty := pstep_none_accesses p σ hsp
          have hFp : FDisjoint (accessesChilds ps σ).writes (accesses p σ) := by
            rw [hap]
            exact ⟨fun l _ hm => by simp [Footprint.empty] at hm,
              fun l _ hm => by simp [Footprint.empty] at hm⟩
          have hagree : ∀ l ∉ (accessesChilds ps σ).writes, σ l = applyAll σ wq l := fun l hl =>
            (applyAll_frame wq σ l
              (fun hm => hl (pstepChilds_writes_subset ps σ hwfps0 hind0 ps' wq hsps hm))).symm
          have hnone : pstep p (applyAll σ wq) = none :=
            (pstep_locality p σ (applyAll σ wq) _ hwf.1 hFp hagree).symm.trans hsp
          rw [ptimeChilds_cons, ptimeChilds_cons, ptime_zero_of_none (n + 1) p σ hsp,
            ptime_zero_of_none n p (applyAll σ wq) hnone, ih n σ hwfps0 hind0 ps' wq hsps]
          omega
      · rcases hsps : pstepChilds ps σ with _ | ⟨ps', wq⟩
        · -- head alone: the tail is finished and stays finished after the head's writes
          simp only [pstepChilds, hsp, hsps, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hFps : FDisjoint (accesses p σ).writes (accessesChilds ps σ) :=
            ⟨hindep0.2.1, hindep0.1⟩
          have hagree : ∀ l ∉ (accesses p σ).writes, σ l = applyAll σ wp l := fun l hl =>
            (applyAll_frame wp σ l
              (fun hm => hl (pstep_writes_subset p σ hwf.1 p' wp hsp hm))).symm
          have hnone : pstepChilds ps (applyAll σ wp) = none :=
            (pstepChilds_locality ps σ (applyAll σ wp) _ hwfps0 hind0 hFps hagree).symm.trans hsps
          rw [ptimeChilds_cons, ptimeChilds_cons, ptime_succ_some n p σ p' wp hsp,
            ptimeChilds_zero_of_none ps (n + 1) σ hsps,
            ptimeChilds_zero_of_none ps n (applyAll σ wp) hnone]
          omega
        · -- both move in the same round — this is where the fold's `max` is born
          simp only [pstepChilds, hsp, hsps, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hwfp', -, hsubpr, hsubpw⟩ := pstep_combined p σ hwf.1 p' wp hsp
          obtain ⟨hwfps', hindps', -, hsubqr, hsubqw⟩ :=
            pstepChilds_combined ps σ hwfps0 hind0 ps' wq hsps
          have hWpq : applyAll σ (wp ++ wq) = applyAll (applyAll σ wp) wq := applyAll_append σ wp wq
          -- the head's remaining rounds do not notice the tail's batch …
          have hFp : FDisjoint (accessesChilds ps σ).writes (accesses p' (applyAll σ wp)) :=
            ⟨fun l hl hm => hindep0.2.2 l hl (hsubpr hm),
             fun l hl hm => hindep0.1 l (hsubpw hm) hl⟩
          have hagree1 : ∀ l ∉ (accessesChilds ps σ).writes,
              applyAll σ wp l = applyAll σ (wp ++ wq) l := by
            intro l hl
            rw [hWpq]
            exact (applyAll_frame wq (applyAll σ wp) l
              (fun hm => hl (pstepChilds_writes_subset ps σ hwfps0 hind0 ps' wq hsps hm))).symm
          have eP : ptime n p' (applyAll σ wp) = ptime n p' (applyAll σ (wp ++ wq)) :=
            ptime_locality n p' (applyAll σ wp) _ _ hwfp' hFp hagree1
          -- … and the tail's do not notice the head's
          have hFq : FDisjoint (accesses p σ).writes (accessesChilds ps' (applyAll σ wq)) :=
            ⟨fun l hl hm => hindep0.2.1 l hl (hsubqr hm),
             fun l hl hm => hindep0.1 l hl (hsubqw hm)⟩
          have hagree2 : ∀ l ∉ (accesses p σ).writes,
              applyAll σ wq l = applyAll σ (wp ++ wq) l := by
            intro l hl
            rw [hWpq]
            refine (applyAll_agree (accesses p σ).writes wq (applyAll σ wp) σ ?_ l hl).symm
            intro m hm
            exact applyAll_frame wp σ m
              (fun hmm => hm (pstep_writes_subset p σ hwf.1 p' wp hsp hmm))
          have eQ : ptimeChilds n ps' (applyAll σ wq)
              = ptimeChilds n ps' (applyAll σ (wp ++ wq)) :=
            ptimeChilds_locality ps' n (applyAll σ wq) _ _ hwfps' hindps' hFq hagree2
          rw [ptimeChilds_cons, ptimeChilds_cons, ptime_succ_some n p σ p' wp hsp,
            ih n σ hwfps0 hind0 ps' wq hsps, eP, eQ]
          omega

/-- **A fork's rounds are the fold of `max` over its children's.** The span law, N-ary.

Stated for a fork whose continuation is a `pure`, which is the shape of both `parPair` and `parAll`
and the only shape where "the fork's rounds" is the children's span with nothing after the join. The
fuel is arbitrary: the law is uniform in the bound, as it must be to transport to `time`. -/
theorem ptime_par_pure {β : Type} {αs : List Type} (f : Results αs → β) :
    ∀ (n : Nat) (cs : Childs ParM αs) (σ : State),
      WellFormed (ParM.par cs (fun r => ParM.pure (f r))) σ →
      ptime n (ParM.par cs (fun r => ParM.pure (f r))) σ = ptimeChilds n cs σ := by
  intro n
  induction n with
  | zero => intro cs σ _; rw [ptimeChilds_zero]; rfl
  | succ n ih =>
      intro cs σ hwf
      obtain ⟨hind, hwfcs, -⟩ := hwf
      rcases hsc : pstepChilds cs σ with _ | ⟨cs', ws⟩
      · have hnone : pstep (ParM.par cs (fun r => ParM.pure (f r))) σ = none := by
          simp [pstep, hsc]
        rw [ptime_succ_none n _ σ hnone, ptimeChilds_zero_of_none cs (n + 1) σ hsc]
      · have hsome : pstep (ParM.par cs (fun r => ParM.pure (f r))) σ
            = some (ParM.par cs' (fun r => ParM.pure (f r)), ws) := by
          simp [pstep, hsc]
        obtain ⟨hwfcs', hindcs', -, -, -⟩ := pstepChilds_combined cs σ hwfcs hind cs' ws hsc
        have hwf' : WellFormed (ParM.par cs' (fun r => ParM.pure (f r))) (applyAll σ ws) :=
          ⟨hindcs', hwfcs', trivial⟩
        rw [ptime_succ_some n _ σ _ _ hsome, ih cs' (applyAll σ ws) hwf',
          ptimeChilds_succ_some cs n σ hwfcs hind cs' ws hsc]

/-- **Two independent branches run in parallel take as many rounds as the slower one** — at every
fuel `n`, so the statement is uniform in the bound.

The two-child case of `ptime_par_pure`: `foldr max 0 [a, b] = max a (max b 0) = max a b`. There is no
separate binary argument any more, which is the point — `parPair` is the `N = 2` instance of `par`. -/
theorem ptime_parPair_eq_max {α β : Type} (n : Nat) (p : ParM α) (q : ParM β) (σ : State)
    (hwf : WellFormed (ParM.parPair p q) σ) :
    ptime n (ParM.parPair p q) σ = max (ptime n p σ) (ptime n q σ) := by
  have h := ptime_par_pure (fun r : Results [α, β] => (r.1, r.2.1)) n
    (Childs.cons p (Childs.cons q Childs.nil)) σ hwf
  show ptime n (ParM.par (Childs.cons p (Childs.cons q Childs.nil))
      (fun r => ParM.pure (r.1, r.2.1))) σ = max (ptime n p σ) (ptime n q σ)
  rw [h, ptimeChilds_cons, ptimeChilds_cons, ptimeChilds_nil]
  omega

/-- **The max law.** The time of a parallel pair is the `max` of its branches' times —
`ptime_parPair_eq_max` transported to `time`'s own fuel.

`max` is a *consequence* of round-counting, never stipulated, and `WellFormed` is the hypothesis that
earns it: it is spent at exactly one point, `ptime_locality`. Dropping it breaks the conclusion, not
just the proof (`RacyCost`). -/
theorem time_parPair_eq_max {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (hwf : WellFormed (ParM.parPair p q) σ) :
    time (ParM.parPair p q) σ = max (time p σ) (time q σ) := by
  obtain ⟨hindep, hwfp, hwfq1⟩ := wellFormed_parPair_parts p q σ hwf
  have hwfq : WellFormed q σ := wellFormed_branch_shift p q σ hindep hwfq1
  have eW : work (ParM.parPair p q) σ = work p σ + work q σ := by
    rw [work_parPair]
    exact congrArg _ (work_locality q (runSeq p σ).2 σ _ ⟨hindep.2.1, hindep.1⟩ (runSeq_frame p σ))
  have h := ptime_parPair_eq_max (work (ParM.parPair p q) σ + 1) p q σ hwf
  rw [ptime_eq_time p σ hwfp _ (by omega), ptime_eq_time q σ hwfq _ (by omega)] at h
  exact h

/-! ### Sequential composition sums; only `par` takes the max

`bind` *is* sequential composition, so its rounds add. With the max law above, that is what makes
"parallel is faster" a comparison rather than a definition. -/

/-- A round of a `bind` is a round of its left factor, until that factor is finished — at which point
the state is unchanged (a finished program's footprint is empty) and the round belongs to the
continuation. `bind` grafts, so no case analysis on the continuation is needed. -/
theorem pstep_bind {α β : Type} :
    ∀ (p : ParM α) (f : α → ParM β) (σ : State),
      pstep (ParM.bind p f) σ =
        match pstep p σ with
        | some (p', ws) => some (ParM.bind p' f, ws)
        | none          => pstep (f (runSeq p σ).1) σ := by
  have H : ∀ {α : Type} (p : ParM α), ∀ (β : Type) (f : α → ParM β) (σ : State),
      pstep (ParM.bind p f) σ =
        match pstep p σ with
        | some (p', ws) => some (ParM.bind p' f, ws)
        | none          => pstep (f (runSeq p σ).1) σ := by
    intro α p
    induction p using ParM.inductionOn with
    | hpure a => intro β f σ; rfl
    | hread l k ih => intro β f σ; simp only [ParM.bind, pstep]
    | hwrite l v k ih => intro β f σ; simp only [ParM.bind, pstep]
    | hpar cs k _ ihk =>
        intro β f σ
        rcases hsc : pstepChilds cs σ with _ | ⟨cs', ws⟩
        · -- the block is finished, so the round belongs to the grafted continuation
          have hac : accessesChilds cs σ = Footprint.empty := pstepChilds_none_accesses cs σ hsc
          have hσ1 : (runChilds cs σ).2 = σ := by
            funext m; exact runChilds_frame cs σ m (by simp [hac, Footprint.empty])
          show pstep (ParM.par cs (fun r => ParM.bind (k r) f)) σ =
            match pstep (ParM.par cs k) σ with
            | some (p', ws) => some (ParM.bind p' f, ws)
            | none          => pstep (f (runSeq (ParM.par cs k) σ).1) σ
          simp only [pstep, hsc, ihk _ β f σ, runSeq, hσ1]
        · show pstep (ParM.par cs (fun r => ParM.bind (k r) f)) σ =
            match pstep (ParM.par cs k) σ with
            | some (p', ws) => some (ParM.bind p' f, ws)
            | none          => pstep (f (runSeq (ParM.par cs k) σ).1) σ
          simp only [pstep, hsc, ParM.bind]
  exact fun p f σ => H p β f σ

/-- Once the left factor is finished, a `bind` and its continuation have literally the same rounds. -/
theorem ptime_bind_of_none {α β : Type} (n : Nat) (p : ParM α) (f : α → ParM β) (σ : State)
    (h : pstep p σ = none) :
    ptime n (ParM.bind p f) σ = ptime n (f (runSeq p σ).1) σ := by
  cases n with
  | zero => rfl
  | succ n =>
      have hb : pstep (ParM.bind p f) σ = pstep (f (runSeq p σ).1) σ := by
        rw [pstep_bind, h]
      rcases hs : pstep (f (runSeq p σ).1) σ with _ | ⟨P', ws⟩
      · rw [ptime_succ_none n _ σ (hb.trans hs), ptime_succ_none n _ σ hs]
      · rw [ptime_succ_some n _ σ _ _ (hb.trans hs), ptime_succ_some n _ σ _ _ hs]

/-- **Rounds add across a `bind`.** Sequential composition sums both work *and* time; only `par`
takes the max. The fuel bound is what makes the two sides comparable at the same `n`. -/
theorem ptime_bind_add {α β : Type} : ∀ (n : Nat) (p : ParM α) (f : α → ParM β) (σ : State),
    WellFormed (ParM.bind p f) σ → work (ParM.bind p f) σ ≤ n →
      ptime n (ParM.bind p f) σ =
        ptime n p σ + ptime n (f (runSeq p σ).1) (runSeq p σ).2 := by
  intro n
  induction n with
  | zero =>
      intro p f σ _ hw
      simp only [ptime]
  | succ n ih =>
      intro p f σ hwf hw
      have hwfp : WellFormed p σ := (WellFormed_bind p f σ).mp hwf |>.1
      have hwfc : WellFormed (f (runSeq p σ).1) (runSeq p σ).2 :=
        (WellFormed_bind p f σ).mp hwf |>.2
      have hwork : work (ParM.bind p f) σ =
          work p σ + work (f (runSeq p σ).1) (runSeq p σ).2 := work_bind p f σ
      rcases hsp : pstep p σ with _ | ⟨p', wp⟩
      · have hwp : work p σ = 0 := pstep_none_work p σ hsp
        have hap : accesses p σ = Footprint.empty := pstep_none_accesses p σ hsp
        have hσ1 : (runSeq p σ).2 = σ := by
          funext m; exact runSeq_frame p σ m (by simp [hap, Footprint.empty])
        rw [ptime_bind_of_none (n + 1) p f σ hsp, ptime_succ_none n p σ hsp, hσ1]
        omega
      · have hbs : pstep (ParM.bind p f) σ = some (ParM.bind p' f, wp) := by
          rw [pstep_bind, hsp]
        obtain ⟨hwfp', hrs, -, -⟩ := pstep_combined p σ hwfp p' wp hsp
        have hltp := work_pstep_lt p σ hwfp p' wp hsp
        have hwfb' : WellFormed (ParM.bind p' f) (applyAll σ wp) := by
          rw [WellFormed_bind]
          exact ⟨hwfp', by rw [hrs]; exact hwfc⟩
        have hworkb' : work (ParM.bind p' f) (applyAll σ wp) ≤ n := by
          rw [work_bind, hrs]
          omega
        have hrec := ih p' f (applyAll σ wp) hwfb' hworkb'
        have hcont : ptime (n + 1) (f (runSeq p σ).1) (runSeq p σ).2 =
            ptime n (f (runSeq p σ).1) (runSeq p σ).2 :=
          ptime_succ_eq n _ _ hwfc (by omega)
        rw [ptime_succ_some n _ σ _ _ hbs, ptime_succ_some n p σ _ _ hsp, hrec, hrs, hcont]
        omega

/-- **Rounds add across a `bind`**, with no independence hypothesis needed for the shape: `bind` *is*
sequential composition. Together with `time_parPair_eq_max` this is what makes "parallel is faster" a
comparison of two counts rather than a definition. -/
theorem time_bind_add {α β : Type} (p : ParM α) (f : α → ParM β) (σ : State)
    (hwf : WellFormed (ParM.bind p f) σ) :
    time (ParM.bind p f) σ = time p σ + time (f (runSeq p σ).1) (runSeq p σ).2 := by
  have hwfp : WellFormed p σ := (WellFormed_bind p f σ).mp hwf |>.1
  have hwfc : WellFormed (f (runSeq p σ).1) (runSeq p σ).2 :=
    (WellFormed_bind p f σ).mp hwf |>.2
  have hwork := work_bind p f σ
  have h := ptime_bind_add (work (ParM.bind p f) σ + 1) p f σ hwf (by omega)
  rw [ptime_eq_time p σ hwfp _ (by omega),
    ptime_eq_time _ _ hwfc _ (by omega)] at h
  exact h

/-- **The sequential counterpart.** `seqPair` is a `bind` chain, so its rounds are the *sum*. -/
theorem time_seqPair_eq_add {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (hwf : WellFormed (ParM.seqPair p q) σ) :
    time (ParM.seqPair p q) σ = time p σ + time q (runSeq p σ).2 := by
  have hwfp : WellFormed p σ := (WellFormed_bind _ _ σ).mp hwf |>.1
  have hwfc := (WellFormed_bind _ _ σ).mp hwf |>.2
  rw [ParM.seqPair, time_bind_add p _ σ hwf, time_bind_add q _ _ hwfc]
  have : time (ParM.pure ((runSeq p σ).1, (runSeq q (runSeq p σ).2).1))
      (runSeq q (runSeq p σ).2).2 = 0 := rfl
  rw [this]
  omega

/-- The right branch's rounds do not depend on whether the left one has already written: the two are
independent at the `par` node, so `ptime_locality` applies. What makes `time_parPair_eq_max`'s `max`
(both branches measured at `σ`) comparable with `time_seqPair_eq_add`'s sum (the right branch
measured after the left). -/
theorem time_parPair_shift {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (hwf : WellFormed (ParM.parPair p q) σ) :
    time q (runSeq p σ).2 = time q σ := by
  obtain ⟨hindep, -, hwfq1⟩ := wellFormed_parPair_parts p q σ hwf
  have hF : FDisjoint (accesses p σ).writes (accesses q (runSeq p σ).2) :=
    ⟨hindep.2.1, hindep.1⟩
  have hw : work q (runSeq p σ).2 = work q σ :=
    work_locality q (runSeq p σ).2 σ _ hF (runSeq_frame p σ)
  show ptime (work q (runSeq p σ).2 + 1) q (runSeq p σ).2 = ptime (work q σ + 1) q σ
  rw [hw]
  exact ptime_locality _ q (runSeq p σ).2 σ _ hwfq1 hF (runSeq_frame p σ)

/-- **Parallel is strictly faster.** Same work (`work_par_eq_seq`), strictly fewer rounds whenever
both branches actually do something. Both hypotheses are load-bearing: forking against a `pure` buys
nothing, and racing branches have no `WellFormed` derivation. -/
theorem time_par_lt_seq {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (hwf : WellFormed (ParM.parPair p q) σ)
    (hp : 0 < time p σ) (hq : 0 < time q σ) :
    time (ParM.parPair p q) σ < time (ParM.seqPair p q) σ := by
  have hwfs : WellFormed (ParM.seqPair p q) σ := wellFormed_of_seqPair p q σ hwf
  rw [time_parPair_eq_max p q σ hwf, time_seqPair_eq_add p q σ hwfs,
    time_parPair_shift p q σ hwf]
  omega

/-- The non-strict form, with no hypothesis on the branches. -/
theorem time_par_le_seq {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (hwf : WellFormed (ParM.parPair p q) σ) :
    time (ParM.parPair p q) σ ≤ time (ParM.seqPair p q) σ := by
  have hwfs : WellFormed (ParM.seqPair p q) σ := wellFormed_of_seqPair p q σ hwf
  rw [time_parPair_eq_max p q σ hwf, time_seqPair_eq_add p q σ hwfs,
    time_parPair_shift p q σ hwf]
  omega

/-- `time` is local, like `work` and `ptime` separately. -/
theorem time_locality {τ : Type} (p : ParM τ) (σ σ' : State) (F : List Loc)
    (hwf : WellFormed p σ) (hF : FDisjoint F (accesses p σ)) (hagree : ∀ l ∉ F, σ l = σ' l) :
    time p σ = time p σ' := by
  show ptime (work p σ + 1) p σ = ptime (work p σ' + 1) p σ'
  rw [← work_locality p σ σ' F hF hagree]
  exact ptime_locality _ p σ σ' F hwf hF hagree

/-- **Any program with an operation left to do costs at least one round.** For a program whose root
is a `.read` or a `.write`, `pstep … = some …` holds by `rfl`, so this is the one-liner that
discharges the `0 < time _ _` side conditions of the speedup laws. -/
theorem time_pos {τ : Type} (p : ParM τ) (σ : State) {p' : ParM τ} {ws : List (Loc × Val)}
    (h : pstep p σ = some (p', ws)) : 0 < time p σ := by
  show 0 < ptime (work p σ + 1) p σ
  rw [ptime_succ_some (work p σ) p σ p' ws h]
  omega

/-- A program whose root is a `.read` costs at least one round. -/
theorem time_read_pos {τ : Type} (l : Loc) (k : Val → ParM τ) (σ : State) :
    0 < time (ParM.read l k) σ := time_pos _ σ rfl

/-- A program whose root is a `.write` costs at least one round. -/
theorem time_write_pos {τ : Type} (l : Loc) (v : Val) (k : Unit → ParM τ) (σ : State) :
    0 < time (ParM.write l v k) σ := time_pos _ σ rfl

/-- No operations, no rounds. -/
theorem time_zero_of_work_zero {τ : Type} (p : ParM τ) (σ : State) (hwf : WellFormed p σ)
    (h : work p σ = 0) : time p σ = 0 :=
  Nat.le_zero.mp (h ▸ ptime_le_work _ p σ hwf)

/-! ### N-ary: `parAll` takes the max, `seqAll` the sum

`parAll ps` is **one** `par` node with a `pure` continuation, so `ptime_par_pure` applies to it
directly and the laws below are that span law read off one list element at a time. -/

/-- `parAll`'s footprint is its children block's: the continuation is a `pure`, which touches
nothing. -/
theorem accesses_parAll {τ : Type} (ps : List (ParM τ)) (σ : State) :
    accesses (ParM.parAll ps) σ = accessesChilds (ParM.childsOf ps) σ := by
  simp [ParM.parAll, Footprint.union, Footprint.empty]

/-- …and likewise its work. -/
theorem work_parAll {τ : Type} (ps : List (ParM τ)) (σ : State) :
    work (ParM.parAll ps) σ = workChilds (ParM.childsOf ps) σ := by
  simp [ParM.parAll]

/-- **`parAll`'s rounds are the fold of `max` over its elements'** — `ptime_par_pure` at
`parAll`'s own continuation. -/
theorem ptime_parAll {τ : Type} (n : Nat) (ps : List (ParM τ)) (σ : State)
    (hwf : WellFormed (ParM.parAll ps) σ) :
    ptime n (ParM.parAll ps) σ = ptimeChilds n (ParM.childsOf ps) σ :=
  ptime_par_pure (ParM.resultsToList ps) n (ParM.childsOf ps) σ hwf

/-- The binary reading of a `parAll` fork's obligation: the head, the tail as a `parAll` both after
the head and — by isolation — in the pre-fork heap, and the independence between them. -/
theorem wellFormed_parAll_parts {τ : Type} (p : ParM τ) (ps : List (ParM τ)) (σ : State)
    (hwf : WellFormed (ParM.parAll (p :: ps)) σ) :
    Indep (accesses p σ) (accesses (ParM.parAll ps) (runSeq p σ).2) ∧ WellFormed p σ ∧
      WellFormed (ParM.parAll ps) (runSeq p σ).2 ∧ WellFormed (ParM.parAll ps) σ := by
  obtain ⟨hind, hwfcs, -⟩ := hwf
  have hheadtail : Indep (accesses p σ) (accessesChilds (ParM.childsOf ps) (runSeq p σ).2) :=
    indep_accessesChilds (ParM.childsOf ps) (accesses p σ) (runSeq p σ).2 hind.1
  refine ⟨by rw [accesses_parAll]; exact hheadtail, hwfcs.1, ⟨hind.2, hwfcs.2, trivial⟩, ?_⟩
  exact ⟨indepAll_branch_shift p (ParM.childsOf ps) σ hheadtail hind.2,
    wellFormedChilds_branch_shift p (ParM.childsOf ps) σ hheadtail hwfcs.2, trivial⟩

/-- `parAll`'s work peels one element: the head's, plus the tail's from the head's post-state. -/
theorem work_parAll_cons {τ : Type} (p : ParM τ) (ps : List (ParM τ)) (σ : State) :
    work (ParM.parAll (p :: ps)) σ = work p σ + work (ParM.parAll ps) (runSeq p σ).2 := by
  rw [work_parAll, work_parAll]
  simp [ParM.childsOf]

/-- `parAll`'s work splits into the head's and the tail's, both measured from the **pre-fork** heap —
independence is what lets the tail's be read off `σ` rather than off the head's post-state. -/
theorem work_parAll_cons_shift {τ : Type} (p : ParM τ) (ps : List (ParM τ)) (σ : State)
    (hwf : WellFormed (ParM.parAll (p :: ps)) σ) :
    work (ParM.parAll (p :: ps)) σ = work p σ + work (ParM.parAll ps) σ := by
  obtain ⟨hindep, -, -, -⟩ := wellFormed_parAll_parts p ps σ hwf
  rw [work_parAll_cons, work_locality (ParM.parAll ps) (runSeq p σ).2 σ (accesses p σ).writes
    ⟨hindep.2.1, hindep.1⟩ (runSeq_frame p σ)]

/-- **Work is unchanged N-ary too**, with no hypothesis: the same operations run either way. -/
theorem work_parAll_eq_seqAll {τ : Type} : ∀ (ps : List (ParM τ)) (σ : State),
    work (ParM.parAll ps) σ = work (ParM.seqAll ps) σ := by
  intro ps
  induction ps with
  | nil => intro σ; rfl
  | cons p ps ih =>
      intro σ
      have hpar : work (ParM.parAll (p :: ps)) σ
          = work p σ + work (ParM.parAll ps) (runSeq p σ).2 := work_parAll_cons p ps σ
      have hseq : work (ParM.seqAll (p :: ps)) σ
          = work p σ + work (ParM.seqAll ps) (runSeq p σ).2 := by
        show work (ParM.bind (ParM.seqPair p (ParM.seqAll ps))
            (fun r => ParM.pure (r.1 :: r.2))) σ
          = work p σ + work (ParM.seqAll ps) (runSeq p σ).2
        rw [work_bind, work_seqPair]
        simp [work]
      rw [hpar, hseq, ih (runSeq p σ).2]

/-- `parAll` takes the `max` of its head and its tail — the span law read off one list element at a
time. Not a corollary of nesting: `parAll (p :: ps)` is a single `par` node, and this is
`ptime_par_pure`'s fold peeled once. -/
theorem time_parAll_cons {τ : Type} (p : ParM τ) (ps : List (ParM τ)) (σ : State)
    (hwf : WellFormed (ParM.parAll (p :: ps)) σ) :
    time (ParM.parAll (p :: ps)) σ = max (time p σ) (time (ParM.parAll ps) σ) := by
  obtain ⟨-, hwfp, -, hwfps⟩ := wellFormed_parAll_parts p ps σ hwf
  have eW : work (ParM.parAll (p :: ps)) σ = work p σ + work (ParM.parAll ps) σ :=
    work_parAll_cons_shift p ps σ hwf
  have h : ptime (work (ParM.parAll (p :: ps)) σ + 1) (ParM.parAll (p :: ps)) σ
      = max (ptime (work (ParM.parAll (p :: ps)) σ + 1) p σ)
            (ptime (work (ParM.parAll (p :: ps)) σ + 1) (ParM.parAll ps) σ) := by
    rw [ptime_parAll _ (p :: ps) σ hwf, ptime_parAll _ ps σ hwfps]
    rfl
  rw [ptime_eq_time p σ hwfp _ (by omega),
    ptime_eq_time (ParM.parAll ps) σ hwfps _ (by omega)] at h
  exact h

/-- `seqAll` sums its head's rounds and its tail's, the tail measured from the heap the head left. -/
theorem time_seqAll_cons {τ : Type} (p : ParM τ) (ps : List (ParM τ)) (σ : State)
    (hwf : WellFormed (ParM.seqAll (p :: ps)) σ) :
    time (ParM.seqAll (p :: ps)) σ = time p σ + time (ParM.seqAll ps) (runSeq p σ).2 := by
  have hb : ParM.seqAll (p :: ps) =
      ParM.bind (ParM.seqPair p (ParM.seqAll ps)) (fun r => ParM.pure (r.1 :: r.2)) := rfl
  rw [hb, time_bind_add _ _ σ (hb ▸ hwf)]
  have hwfs : WellFormed (ParM.seqPair p (ParM.seqAll ps)) σ :=
    ((WellFormed_bind _ _ σ).mp (hb ▸ hwf)).1
  rw [time_seqPair_eq_add p (ParM.seqAll ps) σ hwfs]
  simp [time, ptime]

/-- The tail's rounds do not depend on whether the head has already written: the two are
independent at the `par` node, so `time_locality` applies. -/
theorem time_parAll_shift {τ : Type} (p : ParM τ) (ps : List (ParM τ)) (σ : State)
    (hwf : WellFormed (ParM.parAll (p :: ps)) σ) :
    time (ParM.parAll ps) σ = time (ParM.parAll ps) (runSeq p σ).2 := by
  obtain ⟨hindep, -, hwf1, -⟩ := wellFormed_parAll_parts p ps σ hwf
  exact (time_locality (ParM.parAll ps) (runSeq p σ).2 σ (accesses p σ).writes hwf1
    ⟨hindep.2.1, hindep.1⟩ (runSeq_frame p σ)).symm

/-- Running a list in parallel never takes more rounds than running it in sequence, for any list. The
non-strict N-ary speedup, with no hypothesis on the individual programs. -/
theorem time_parAll_le_seqAll {τ : Type} : ∀ (ps : List (ParM τ)) (σ : State),
    WellFormed (ParM.parAll ps) σ → time (ParM.parAll ps) σ ≤ time (ParM.seqAll ps) σ := by
  intro ps
  induction ps with
  | nil => intro σ _; exact Nat.le_refl _
  | cons p ps ih =>
      intro σ hwf
      have hwfs := wellFormed_of_seqAll (p :: ps) σ hwf
      obtain ⟨-, -, hwf1, -⟩ := wellFormed_parAll_parts p ps σ hwf
      have hrec := ih (runSeq p σ).2 hwf1
      rw [time_parAll_cons p ps σ hwf, time_seqAll_cons p ps σ hwfs,
        time_parAll_shift p ps σ hwf]
      omega

/-- **N-ary speedup.** If the head and the rest each have work to do, running the whole list in
parallel takes strictly fewer rounds than running it in sequence. -/
theorem time_parAll_lt_seqAll {τ : Type} (p : ParM τ) (ps : List (ParM τ)) (σ : State)
    (hwf : WellFormed (ParM.parAll (p :: ps)) σ)
    (hp : 0 < time p σ) (hps : 0 < time (ParM.parAll ps) σ) :
    time (ParM.parAll (p :: ps)) σ < time (ParM.seqAll (p :: ps)) σ := by
  have hwfs := wellFormed_of_seqAll (p :: ps) σ hwf
  obtain ⟨-, -, hwf1, -⟩ := wellFormed_parAll_parts p ps σ hwf
  have hle := time_parAll_le_seqAll ps (runSeq p σ).2 hwf1
  have hshift := time_parAll_shift p ps σ hwf
  rw [time_parAll_cons p ps σ hwf, time_seqAll_cons p ps σ hwfs]
  omega

/-- A `parAll` whose head has work to do costs at least one round. Discharges the `0 < time _ _` side
condition of `time_parAll_lt_seqAll` when recursing down a list. -/
theorem time_parAll_pos {τ : Type} (p : ParM τ) (ps : List (ParM τ)) (σ : State)
    (hwf : WellFormed (ParM.parAll (p :: ps)) σ) (hp : 0 < time p σ) :
    0 < time (ParM.parAll (p :: ps)) σ := by
  rw [time_parAll_cons p ps σ hwf]; omega

/-! ### Cost of a parallel region inside a sequential program

`par_seq_eq_region_of` (`Theory/Sequentialize.lean`) says substituting a region leaves the outcomes
alone. These say what it does to the span: nothing before or after the region changes, so the whole
program's saving is exactly the region's. -/

/-- The span of `pre ; r ; post` splits into its three phases. The phases after `pre` are measured
from the heap `pre` leaves, as they must be. -/
theorem time_region_split {α β δ : Type} (pre : ParM α) (r : ParM β) (post : β → ParM δ)
    (σ : State) (hwf : WellFormed (ParM.bind pre (fun _ => ParM.bind r post)) σ) :
    time (ParM.bind pre (fun _ => ParM.bind r post)) σ
      = time pre σ + time r (runSeq pre σ).2
        + time (post (runSeq r (runSeq pre σ).2).1) (runSeq r (runSeq pre σ).2).2 := by
  have hreg : WellFormed (ParM.bind r post) (runSeq pre σ).2 :=
    ((WellFormed_bind pre _ σ).mp hwf).2
  rw [time_bind_add pre _ σ hwf, time_bind_add r post (runSeq pre σ).2 hreg]
  omega

/-- **Parallelizing a region is no slower, whatever surrounds it.** The sequential phases contribute
the same count on both sides, because the two regions have the same canonical run. -/
theorem time_region_le {α τ' δ : Type} (pre : ParM α) (ps : List (ParM τ'))
    (post : List τ' → ParM δ) (σ : State)
    (hwf : WellFormed (ParM.bind pre (fun _ => ParM.bind (ParM.parAll ps) post)) σ) :
    time (ParM.bind pre (fun _ => ParM.bind (ParM.parAll ps) post)) σ
      ≤ time (ParM.bind pre (fun _ => ParM.bind (ParM.seqAll ps) post)) σ := by
  have hreg : WellFormed (ParM.bind (ParM.parAll ps) post) (runSeq pre σ).2 :=
    ((WellFormed_bind pre _ σ).mp hwf).2
  have hwfr : WellFormed (ParM.parAll ps) (runSeq pre σ).2 :=
    ((WellFormed_bind _ post (runSeq pre σ).2).mp hreg).1
  have hwfs : WellFormed (ParM.bind pre (fun _ => ParM.bind (ParM.seqAll ps) post)) σ := by
    rw [WellFormed_bind]
    refine ⟨((WellFormed_bind pre _ σ).mp hwf).1, ?_⟩
    exact wellFormed_bind_congr _ _ post (runSeq pre σ).2
      (wellFormed_of_seqAll ps (runSeq pre σ).2 hwfr)
      (runSeq_parAll_eq_seqAll ps (runSeq pre σ).2) hreg
  rw [time_region_split pre _ post σ hwf, time_region_split pre _ post σ hwfs,
    runSeq_parAll_eq_seqAll ps (runSeq pre σ).2]
  have := time_parAll_le_seqAll ps (runSeq pre σ).2 hwfr
  omega

/-- **Parallelizing a region is strictly faster** when at least two of its iterations have work to
do, however much sequential code surrounds it. -/
theorem time_region_lt {α τ' δ : Type} (pre : ParM α) (p : ParM τ') (ps : List (ParM τ'))
    (post : List τ' → ParM δ) (σ : State)
    (hwf : WellFormed (ParM.bind pre (fun _ => ParM.bind (ParM.parAll (p :: ps)) post)) σ)
    (hp : 0 < time p (runSeq pre σ).2)
    (hps : 0 < time (ParM.parAll ps) (runSeq pre σ).2) :
    time (ParM.bind pre (fun _ => ParM.bind (ParM.parAll (p :: ps)) post)) σ
      < time (ParM.bind pre (fun _ => ParM.bind (ParM.seqAll (p :: ps)) post)) σ := by
  have hreg : WellFormed (ParM.bind (ParM.parAll (p :: ps)) post) (runSeq pre σ).2 :=
    ((WellFormed_bind pre _ σ).mp hwf).2
  have hwfr : WellFormed (ParM.parAll (p :: ps)) (runSeq pre σ).2 :=
    ((WellFormed_bind _ post (runSeq pre σ).2).mp hreg).1
  have hwfs : WellFormed (ParM.bind pre (fun _ => ParM.bind (ParM.seqAll (p :: ps)) post)) σ := by
    rw [WellFormed_bind]
    refine ⟨((WellFormed_bind pre _ σ).mp hwf).1, ?_⟩
    exact wellFormed_bind_congr _ _ post (runSeq pre σ).2
      (wellFormed_of_seqAll (p :: ps) (runSeq pre σ).2 hwfr)
      (runSeq_parAll_eq_seqAll (p :: ps) (runSeq pre σ).2) hreg
  obtain ⟨-, -, hwf1, -⟩ := wellFormed_parAll_parts p ps (runSeq pre σ).2 hwfr
  rw [time_region_split pre _ post σ hwf, time_region_split pre _ post σ hwfs,
    runSeq_parAll_eq_seqAll (p :: ps) (runSeq pre σ).2]
  have := time_parAll_lt_seqAll p ps (runSeq pre σ).2 hwfr hp hps
  omega

/-! ### Anti-vacuity: the law fails for racing branches

`racyQ` writes `0`; `racyP` reads it a round later and branches. Alone it takes two rounds, in
parallel three — so `max` is wrong here, and `time_parPair_eq_max` refuses to apply because `0` is
in `racyQ`'s writes and `racyP`'s reads. -/

namespace RacyCost

/-- Reads location `5`, then reads location `0` and branches on it: stops at `int 0`, writes otherwise.
The branch whose round count depends on what the *other* branch has written. -/
def racyP : ParM Unit :=
  .read 5 (fun _ => .read 0 (fun v =>
    match v with
    | .int 0 => .pure ()
    | _      => .write 6 (.int 9) (fun _ => .pure ())))

/-- Writes `int 1` to location `0` — the cell `racyP` reads one round later. One write, one round, so
it lands in time to change `racyP`'s decision. -/
def racyQ : ParM Unit := .write 0 (.int 1) (fun _ => .pure ())

/-- The all-zero heap these examples start from. -/
def σz : State := fun _ => .int 0

/-- Each branch alone. -/
example : (time racyP σz, time racyQ σz) = (2, 1) := rfl

/-- In parallel: **three** rounds, not `max 2 1 = 2`. -/
example : time (ParM.parPair racyP racyQ) σz = 3 := rfl

example : time (ParM.parPair racyP racyQ) σz ≠ max (time racyP σz) (time racyQ σz) := by decide

/-- …and the reason: Bernstein's second condition is violated. -/
example : ¬ Indep (accesses racyP σz) (accesses racyQ (runSeq racyP σz).2) := by
  rw [← indepB_iff]; decide

end RacyCost

/-! ### `TimeM`

`bind` sums both components, which is right because `bind` *is* sequential composition. The
parallelism lives in `par`, a constructor of `ParM`, so the monad never needs to know about it. -/

/-- The two measures of a run, carried together: total operations and parallel rounds. -/
structure Cost where
  /-- Total memory operations — `work`. -/
  work : Nat
  /-- Parallel rounds — `time`, the span. -/
  time : Nat
  deriving Repr, DecidableEq, Inhabited

/-- A value paired with the cost of producing it — the cost-annotated writer monad. -/
def TimeM (α : Type) : Type := α × Cost

/-- Sequential composition: `bind` **sums** both components, and `pure` costs nothing.

Summing is correct rather than a simplification — `bind` is sequential composition, and
`time_bind_add` proves rounds really do add across it. The `max` belongs to `par`, which is a
constructor of `ParM` and not a bind, so the monad never has to know about parallelism. -/
instance : Monad TimeM where
  pure a   := (a, ⟨0, 0⟩)
  bind x f := let (b, c) := f x.1; (b, ⟨x.2.work + c.work, x.2.time + c.time⟩)

/-- Both costs of running `p` from `σ`, in one record. Another interpreter of a `ParM` term, alongside
`run`, `runSeq`, `accesses` and `render` — see `docs/program-model.md`. -/
def costOf {τ : Type} (p : ParM τ) (σ : State) : Cost := ⟨work p σ, time p σ⟩

/-- `costOf`'s first projection is `work`. -/
@[simp, grind .] theorem costOf_work {τ : Type} (p : ParM τ) (σ : State) :
    (costOf p σ).work = work p σ := rfl
/-- `costOf`'s second projection is `time`. -/
@[simp, grind .] theorem costOf_time {τ : Type} (p : ParM τ) (σ : State) :
    (costOf p σ).time = time p σ := rfl

end Paralever
