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
  | .par p q k,   σ =>
      let (a, σ₁) := runSeq p σ
      let (b, σ₂) := runSeq q σ₁
      work p σ + work q σ₁ + work (k (a, b)) σ₂

/-- Work adds across a `bind`: the left factor's operations, then the continuation's, measured from
the heap the left factor produced. -/
@[grind .]
theorem work_bind {α β : Type} (p : ParM α) (f : α → ParM β) (σ : State) :
    work (ParM.bind p f) σ = work p σ + work (f (runSeq p σ).1) (runSeq p σ).2 := by
  induction p generalizing σ with
  | pure a => simp [ParM.bind, work]
  | read l k ih => simp only [ParM.bind, work, runSeq, ih]; omega
  | write l v k ih => simp only [ParM.bind, work, runSeq, ih]; omega
  | par p q k ihp ihq ihk => simp only [ParM.bind, work, runSeq, ihk]; omega

/-- A parallel pair's work is the sum of its branches'. -/
@[grind .]
theorem work_parPair {α β : Type} (p : ParM α) (q : ParM β) (σ : State) :
    work (ParM.parPair p q) σ = work p σ + work q (runSeq p σ).2 := by
  simp [ParM.parPair, work]

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
theorem work_locality {τ : Type} (p : ParM τ) (σ σ' : State) (F : List Loc)
    (hF : FDisjoint F (accesses p σ)) (hagree : ∀ l, l ∉ F → σ l = σ' l) :
    work p σ = work p σ' := by
  induction p generalizing σ σ' with
  | pure a => rfl
  | read l k ih =>
      grind only [work, FDisjoint, = accesses.eq_2, = Disjoint.eq_1, = Footprint.union.eq_1,
        = List.cons_append, = List.mem_cons, = List.mem_append]
  | write l v k ih =>
      grind only [work, accesses, FDisjoint, Footprint.union, = Disjoint.eq_1, = List.cons_append,
        State.update_other, State.update_same, = List.mem_append, ← List.not_mem_nil]
  | par p q k ihp ihq ihk =>
      have hFp : FDisjoint F (accesses p σ) := hF.left
      obtain ⟨ep1, ep2, ep3⟩ := accesses_runSeq_locality p σ σ' F hFp hagree
      have hFq : FDisjoint F (accesses q (runSeq p σ).2) := hF.right.left
      obtain ⟨eq1, eq2, eq3⟩ :=
        accesses_runSeq_locality q (runSeq p σ).2 (runSeq p σ').2 F hFq ep3
      have e1 : work p σ = work p σ' := ihp σ σ' hFp hagree
      have e2 : work q (runSeq p σ).2 = work q (runSeq p σ').2 := ihq _ _ hFq ep3
      have e3 : work (k ((runSeq p σ).1, (runSeq q (runSeq p σ).2).1))
            (runSeq q (runSeq p σ).2).2 =
          work (k ((runSeq p σ').1, (runSeq q (runSeq p σ').2).1))
            (runSeq q (runSeq p σ').2).2 := by
        rw [← ep2, ← eq2]
        exact ihk _ _ _ hF.right.right eq3
      simp only [work]
      omega

/-! ### Time: rounds of a parallel-round semantics

In one round, *every* ready branch performs one operation. A round's writes are collected and applied
together; under `Indep` they land on disjoint cells, so the order inside a batch is immaterial. -/

/-- `σ` with every write in the batch applied, left to right — how a round's collected writes land.

The order is fixed only to make this a definition. A round's batch comes from independent branches,
so its locations are pairwise distinct and any other order gives the same heap. -/
def applyAll (σ : State) : List (Loc × Val) → State
  | []           => σ
  | (l, v) :: ws => applyAll (σ.update l v) ws

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
  | .par p q k,   σ =>
      match pstep p σ, pstep q σ with
      | some (p', wp), some (q', wq) => some (.par p' q' k, wp ++ wq)   -- BOTH advance
      | some (p', wp), none          => some (.par p' q  k, wp)
      | none,          some (q', wq) => some (.par p  q' k, wq)
      | none,          none          => pstep (k ((runSeq p σ).1, (runSeq q σ).1)) σ  -- join

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

Special cases of `time_parPair_eq_max` below, kept because they are checked by `simp` alone and so
pin the definitions down independently of the general proof. For branches that each take one
operation, round-counting *yields* `max` on the parallel composition and `+` on the sequential one.
Neither word appears in `pstep`. -/

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

/-! ### The max law for two write sequences of ARBITRARY length.
    Stated with `.par _ _ .pure` so nothing needs folding/unfolding mid-proof. -/

/-- **Two write sequences of lengths `m` and `n` run in parallel take `max m n` rounds.** The first
case where `max` is derived for unboundedly many operations, and it is proved by bare induction with
no appeal to independence — so it checks `pstep` against the intended cost model independently of
`ptime_parPair_eq_max`. -/
theorem ptime_par_writeSeq :
    ∀ (ws₁ ws₂ : List (Loc × Val)) (n : Nat) (σ : State),
      ws₁.length < n → ws₂.length < n →
      ptime n (ParM.par (writeSeq ws₁) (writeSeq ws₂) ParM.pure) σ
        = max ws₁.length ws₂.length := by
  intro ws₁
  induction ws₁ with
  | nil =>
      intro ws₂
      induction ws₂ with
      | nil => intro n σ _ _; cases n with
        | zero => rfl
        | succ m => simp [ptime, pstep, writeSeq]
      | cons w ws ih2 =>
          intro n σ h1 h2
          obtain ⟨l, v⟩ := w
          cases n with
          | zero => simp at h2
          | succ m =>
              simp only [ptime, pstep, writeSeq, applyAll, List.length_cons, List.length_nil]
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
              simp only [ptime, pstep, writeSeq, applyAll, List.length_cons, List.length_nil]
              rw [show (ParM.pure () : ParM Unit) = writeSeq [] from rfl,
                  ih1 [] m (σ.update l v) (by simp at h1; omega) (by simp at h1; simp; omega)]
              simp; omega
      | cons w₂ ws₂' =>
          obtain ⟨l₂, v₂⟩ := w₂
          cases n with
          | zero => simp at h1
          | succ m =>
              simp only [ptime, pstep, writeSeq, List.length_cons]
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
theorem pstep_none_accesses {τ : Type} :
    ∀ (p : ParM τ) (σ : State), pstep p σ = none → accesses p σ = Footprint.empty := by
  intro p
  induction p with
  | pure a => intro σ _; rfl
  | read l k ih => intro σ h; simp [pstep] at h
  | write l v k ih => intro σ h; simp [pstep] at h
  | par p q k ihp ihq ihk =>
      intro σ h
      rcases hsp : pstep p σ with _ | ⟨p', wp⟩
      · rcases hsq : pstep q σ with _ | ⟨q', wq⟩
        · -- both done, so the join ran and also returned none
          have hap : accesses p σ = Footprint.empty := ihp σ hsp
          have haq : accesses q σ = Footprint.empty := ihq σ hsq
          have hσ1 : (runSeq p σ).2 = σ := by
            funext m; exact runSeq_frame p σ m (by simp [hap, Footprint.empty])
          have hk : pstep (k ((runSeq p σ).1, (runSeq q σ).1)) σ = none := by
            simpa [pstep, hsp, hsq] using h
          have hak := ihk _ σ hk
          have hσ2 : (runSeq q σ).2 = σ := by
            funext m; exact runSeq_frame q σ m (by simp [haq, Footprint.empty])
          show accesses (ParM.par p q k) σ = Footprint.empty
          simp only [accesses, hσ1, hσ2, hap, haq, hak, Footprint.union, Footprint.empty]
          simp
        · simp [pstep, hsp, hsq] at h
      · rcases hsq : pstep q σ with _ | ⟨q', wq⟩
        · simp [pstep, hsp, hsq] at h
        · simp [pstep, hsp, hsq] at h

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

/-- A round only writes inside the program's own write footprint. -/
theorem pstep_writes_subset {τ : Type} :
    ∀ (p : ParM τ) (σ : State), WellFormed p σ → ∀ (p' : ParM τ) (ws : List (Loc × Val)),
      pstep p σ = some (p', ws) → ws.map Prod.fst ⊆ (accesses p σ).writes := by
  intro p
  induction p with
  | pure a => grind
  | read l k ih => grind
  | write l v k ih => grind
  | par p q k ihp ihq ihk =>
      intro σ hwf P' ws h
      obtain ⟨hindep, hwfp, hwfq1, hwfk⟩ := hwf
      obtain ⟨eacc_q, eval_q⟩ := accesses_runSeq_isolated p q σ hindep
      have hwfq : WellFormed q σ := wellFormed_branch_shift p q σ hindep hwfq1
      have hW : (accesses (ParM.par p q k) σ).writes =
          (accesses p σ).writes ++ (accesses q (runSeq p σ).2).writes ++
            (accesses (k ((runSeq p σ).1, (runSeq q (runSeq p σ).2).1))
              (runSeq q (runSeq p σ).2).2).writes := by
        simp [accesses, Footprint.union, List.append_assoc]
      rcases hsp : pstep p σ with _ | ⟨p', wp⟩
      · rcases hsq : pstep q σ with _ | ⟨q', wq⟩

        · -- join: both branches finished, so neither moved the state
          have hap : accesses p σ = Footprint.empty := pstep_none_accesses p σ hsp
          have haq : accesses q σ = Footprint.empty := pstep_none_accesses q σ hsq
          have hσ1 : (runSeq p σ).2 = σ := by
            funext m; exact runSeq_frame p σ m (by simp [hap, Footprint.empty])
          have hσ2 : (runSeq q σ).2 = σ := by
            funext m; exact runSeq_frame q σ m (by simp [haq, Footprint.empty])
          grind
        · -- only q advanced
          grind
      · rcases hsq : pstep q σ with _ | ⟨q', wq⟩
        · -- only p advanced
          grind
        · -- both advanced
          grind

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
theorem pstep_locality {τ : Type} (p : ParM τ) (σ σ' : State) (F : List Loc)
    (hwf : WellFormed p σ)
    (hF : FDisjoint F (accesses p σ)) (hagree : ∀ l ∉ F, σ l = σ' l) :
    pstep p σ = pstep p σ' := by
  induction p generalizing σ σ' with
  | pure a => rfl
  | read l k ih => grind
  | write l v k ih => rfl
  | par p q k ihp ihq ihk =>
      -- destructure WellFormed at the par node
      obtain ⟨hindep, hwfp, hwfq1, hwfk⟩ := hwf
      -- q's footprint is the same measured at σ or at σ₁, because the branches are independent
      obtain ⟨eacc_q, _⟩ := accesses_runSeq_isolated p q σ hindep
      -- and q's well-formedness transfers from σ₁ down to σ
      have hwfq : WellFormed q σ := by
        refine (WellFormed_locality q (runSeq p σ).2 σ (accesses p σ).writes ?_ ?_).mp hwfq1
        · exact ⟨hindep.2.1, hindep.1⟩
        · exact runSeq_frame p σ
      have hFp : FDisjoint F (accesses p σ) := hF.left
      have hFq : FDisjoint F (accesses q σ) := eacc_q ▸ hF.right.left
      have hp' := ihp σ σ' hwfp hFp hagree
      have hq' := ihq σ σ' hwfq hFq hagree
      -- the branch RESULTS also agree, which the join case needs
      obtain ⟨-, evp, -⟩ := accesses_runSeq_locality p σ σ' F hFp hagree
      obtain ⟨-, evq, -⟩ := accesses_runSeq_locality q σ σ' F hFq hagree
      rcases hsp : pstep p σ' with _ | ⟨p'', wp⟩
      · rcases hsq : pstep q σ' with _ | ⟨q'', wq⟩
        · -- both branches finished: the join runs the continuation, in the same round
          simp only [pstep, hp', hq', hsp, hsq, evp, evq]
          -- both branches are finished, so neither moved the state: σ₁ = σ₂ = σ
          have hap : accesses p σ = Footprint.empty := pstep_none_accesses p σ (hp'.trans hsp)
          have haq : accesses q σ = Footprint.empty := pstep_none_accesses q σ (hq'.trans hsq)
          have hσ1 : (runSeq p σ).2 = σ := by
            funext m; exact runSeq_frame p σ m (by simp [hap, Footprint.empty])
          have hσ2 : (runSeq q σ).2 = σ := by
            funext m; exact runSeq_frame q σ m (by simp [haq, Footprint.empty])
          refine ihk _ σ σ' ?_ ?_ hagree
          · simpa [hσ1, hσ2, ← evp, ← evq] using hwfk
          · simpa [hσ1, hσ2, hap, haq, Footprint.union, Footprint.empty, ← evp, ← evq]
              using hF.right.right
        · simp only [pstep, hp', hq', hsp, hsq]
      · rcases hsq : pstep q σ' with _ | ⟨q'', wq⟩
        · simp only [pstep, hp', hq', hsp, hsq]
        · simp only [pstep, hp', hq', hsp, hsq]

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
  intro p
  induction p with
  | pure a => intro σ _ _; exact Reaches.refl
  | read l k ih => intro σ _ h; simp [pstep] at h
  | write l v k ih => intro σ _ h; simp [pstep] at h
  | par p q k ihp ihq ihk =>
      intro σ hwf h
      obtain ⟨hindep, hwfp, hwfq1, hwfk⟩ := hwf
      obtain ⟨eacc_q, eval_q⟩ := accesses_runSeq_isolated p q σ hindep
      have hwfq : WellFormed q σ := wellFormed_branch_shift p q σ hindep hwfq1
      have hindep0 : Indep (accesses p σ) (accesses q σ) := eacc_q ▸ hindep
      rcases hsp : pstep p σ with _ | ⟨p', wp⟩
      · rcases hsq : pstep q σ with _ | ⟨q', wq⟩
        · have hap : accesses p σ = Footprint.empty := pstep_none_accesses p σ hsp
          have haq : accesses q σ = Footprint.empty := pstep_none_accesses q σ hsq
          have hσ1 : (runSeq p σ).2 = σ := by
            funext m; exact runSeq_frame p σ m (by simp [hap, Footprint.empty])
          have hσ2 : (runSeq q σ).2 = σ := by
            funext m; exact runSeq_frame q σ m (by simp [haq, Footprint.empty])
          have hk : pstep (k ((runSeq p σ).1, (runSeq q σ).1)) σ = none := by
            simpa [pstep, hsp, hsq] using h
          -- ① run `p` out to its value, inside the `par` context
          have r1 := ihp σ hwfp hsp
          have hnr1 : ∀ p'' σ'', Reaches (Conf.run p σ) (Conf.run p'' σ'') →
              ¬ racing (nextAccs p'') (nextAccs q) = true := by
            intro p'' σ'' hc
            obtain ⟨hr, hw⟩ := subset_chain p σ hwfp _ hc p'' σ'' rfl
            exact no_race_of_sub p'' q σ'' σ _ _ hindep0 hr hw (fun _ h => h) (fun _ h => h)
          obtain ⟨p2, σ2, heq2, lift1⟩ | hwrong :=
            reaches_par_left p q k σ _ r1 hnr1
          · obtain ⟨hp2, hs2⟩ : p2 = .pure (runSeq p σ).1 ∧ σ2 = σ := by
              simpa using heq2.symm
            rw [hp2, hs2] at lift1
            -- ② then run `q` out, with `p` already a value
            have r2 := ihq σ hwfq hsq
            obtain ⟨q2, σ3, heq3, lift2⟩ | hwrong :=
              reaches_par_right (ParM.pure (runSeq p σ).1) q k σ _ r2 (by simp [racing])
            · obtain ⟨hq2, hs3⟩ : q2 = .pure (runSeq q σ).1 ∧ σ3 = σ := by
                simpa using heq3.symm
              rw [hq2, hs3] at lift2
              -- ③ the join step, then ④ the continuation
              have join : Conf.run (k ((runSeq p σ).1, (runSeq q σ).1)) σ ∈
                  stepC (Conf.run (ParM.par (.pure (runSeq p σ).1) (.pure (runSeq q σ).1) k) σ) := by
                simp [stepC, step, racing]
              have r4 := ihk _ σ (by rw [hσ1, hσ2] at hwfk; exact hwfk) hk
              have : runSeq (ParM.par p q k) σ = runSeq (k ((runSeq p σ).1, (runSeq q σ).1)) σ := by
                simp only [runSeq, hσ1, hσ2]
              rw [this]
              exact ((lift1.trans lift2).tail join).trans r4
            · exact absurd hwrong (by simp)
          · exact absurd hwrong (by simp)
        · simp [pstep, hsp, hsq] at h
      · rcases hsq : pstep q σ with _ | ⟨q', wq⟩
        · simp [pstep, hsp, hsq] at h
        · simp [pstep, hsp, hsq] at h

/-- **A parallel round is a sequence of ordinary `step`s.** One `pstep` round — every ready branch
advancing at once — is realised in the real semantics by `p`'s move, then `q`'s, then whatever joins
fall due, and the round's batched writes land in exactly the state that schedule produces.

This is the bridge that makes the round semantics cheap: `runSeq_invariant_chain`,
`WellFormed_preserved` and `subset_chain` are already proved for arbitrary `Reaches` derivations, so
every invariant a round must preserve is inherited (`pstep_combined`) rather than re-proved by a
second induction over `pstep`. The proof is where `reaches_par_left`/`reaches_par_right` and their
non-racing side conditions get discharged. -- ref: docs/cost.md; Brookes CONCUR'04 §5 -/
theorem pstep_reaches {τ : Type} :
    ∀ (p : ParM τ) (σ : State), WellFormed p σ → ∀ (p' : ParM τ) (ws : List (Loc × Val)),
      pstep p σ = some (p', ws) → Reaches (Conf.run p σ) (Conf.run p' (applyAll σ ws)) := by
  intro p
  induction p with
  | pure a => intro σ _ p' ws h; simp [pstep] at h
  | read l k ih =>
      intro σ _ p' ws h
      simp only [pstep, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Reaches.single (by simp [stepC, step, applyAll])
  | write l v k ih =>
      intro σ _ p' ws h
      simp only [pstep, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Reaches.single (by simp [stepC, step, applyAll])
  | par p q k ihp ihq ihk =>
      intro σ hwf P' ws h
      obtain ⟨hindep, hwfp, hwfq1, hwfk⟩ := hwf
      obtain ⟨eacc_q, eval_q⟩ := accesses_runSeq_isolated p q σ hindep
      have hwfq : WellFormed q σ := wellFormed_branch_shift p q σ hindep hwfq1
      have hindep0 : Indep (accesses p σ) (accesses q σ) := eacc_q ▸ hindep
      rcases hsp : pstep p σ with _ | ⟨p', wp⟩
      · rcases hsq : pstep q σ with _ | ⟨q', wq⟩
        · -- ─── join: both branches finished, so the round is the continuation's round ───
          have hap : accesses p σ = Footprint.empty := pstep_none_accesses p σ hsp
          have haq : accesses q σ = Footprint.empty := pstep_none_accesses q σ hsq
          have hσ1 : (runSeq p σ).2 = σ := by
            funext m; exact runSeq_frame p σ m (by simp [hap, Footprint.empty])
          have hσ2 : (runSeq q σ).2 = σ := by
            funext m; exact runSeq_frame q σ m (by simp [haq, Footprint.empty])
          have hk : pstep (k ((runSeq p σ).1, (runSeq q σ).1)) σ = some (P', ws) := by
            simpa [pstep, hsp, hsq] using h
          have r1 := pstep_none_reaches p σ hwfp hsp
          have hnr1 : ∀ p'' σ'', Reaches (Conf.run p σ) (Conf.run p'' σ'') →
              ¬ racing (nextAccs p'') (nextAccs q) = true := by
            intro p'' σ'' hc
            obtain ⟨hr, hw⟩ := subset_chain p σ hwfp _ hc p'' σ'' rfl
            exact no_race_of_sub p'' q σ'' σ _ _ hindep0 hr hw (fun _ h => h) (fun _ h => h)
          obtain ⟨p2, σ2, heq2, lift1⟩ | hwrong := reaches_par_left p q k σ _ r1 hnr1
          · obtain ⟨hp2, hs2⟩ : p2 = .pure (runSeq p σ).1 ∧ σ2 = σ := by simpa using heq2.symm
            rw [hp2, hs2] at lift1
            have r2 := pstep_none_reaches q σ hwfq hsq
            obtain ⟨q2, σ3, heq3, lift2⟩ | hwrong :=
              reaches_par_right (ParM.pure (runSeq p σ).1) q k σ _ r2 (by simp [racing])
            · obtain ⟨hq2, hs3⟩ : q2 = .pure (runSeq q σ).1 ∧ σ3 = σ := by simpa using heq3.symm
              rw [hq2, hs3] at lift2
              have join : Conf.run (k ((runSeq p σ).1, (runSeq q σ).1)) σ ∈
                  stepC (Conf.run (ParM.par (.pure (runSeq p σ).1) (.pure (runSeq q σ).1) k) σ) := by
                simp [stepC, step, racing]
              have r4 := ihk _ σ (by rw [hσ1, hσ2] at hwfk; exact hwfk) P' ws hk
              exact ((lift1.trans lift2).tail join).trans r4
            · exact absurd hwrong (by simp)
          · exact absurd hwrong (by simp)
        · -- ─── only `q` advanced ───
          simp only [pstep, hsp, hsq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have r2 := ihq σ hwfq q' wq hsq
          have hnr2 : ∀ q'' σ'', Reaches (Conf.run q σ) (Conf.run q'' σ'') →
              ¬ racing (nextAccs p) (nextAccs q'') = true := by
            intro q'' σ'' hc
            obtain ⟨hr, hw⟩ := subset_chain q σ hwfq _ hc q'' σ'' rfl
            exact no_race_of_sub p q'' σ σ'' _ _ hindep0 (fun _ h => h) (fun _ h => h) hr hw
          obtain ⟨q2, σ3, heq3, lift2⟩ | hwrong := reaches_par_right p q k σ _ r2 hnr2
          · obtain ⟨hq2, hs3⟩ : q2 = q' ∧ σ3 = applyAll σ wq := by simpa using heq3.symm
            rw [hq2, hs3] at lift2; exact lift2
          · exact absurd hwrong (by simp)
      · rcases hsq : pstep q σ with _ | ⟨q', wq⟩
        · -- ─── only `p` advanced ───
          simp only [pstep, hsp, hsq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have r1 := ihp σ hwfp p' wp hsp
          have hnr1 : ∀ p'' σ'', Reaches (Conf.run p σ) (Conf.run p'' σ'') →
              ¬ racing (nextAccs p'') (nextAccs q) = true := by
            intro p'' σ'' hc
            obtain ⟨hr, hw⟩ := subset_chain p σ hwfp _ hc p'' σ'' rfl
            exact no_race_of_sub p'' q σ'' σ _ _ hindep0 hr hw (fun _ h => h) (fun _ h => h)
          obtain ⟨p2, σ2, heq2, lift1⟩ | hwrong := reaches_par_left p q k σ _ r1 hnr1
          · obtain ⟨hp2, hs2⟩ : p2 = p' ∧ σ2 = applyAll σ wp := by simpa using heq2.symm
            rw [hp2, hs2] at lift1; exact lift1
          · exact absurd hwrong (by simp)
        · -- ─── both advanced: `p`'s step, then `q`'s, replayed from after `p`'s write ───
          simp only [pstep, hsp, hsq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have r1 := ihp σ hwfp p' wp hsp
          have hnr1 : ∀ p'' σ'', Reaches (Conf.run p σ) (Conf.run p'' σ'') →
              ¬ racing (nextAccs p'') (nextAccs q) = true := by
            intro p'' σ'' hc
            obtain ⟨hr, hw⟩ := subset_chain p σ hwfp _ hc p'' σ'' rfl
            exact no_race_of_sub p'' q σ'' σ _ _ hindep0 hr hw (fun _ h => h) (fun _ h => h)
          obtain ⟨p2, σ2, heq2, lift1⟩ | hwrong := reaches_par_left p q k σ _ r1 hnr1
          · obtain ⟨hp2, hs2⟩ : p2 = p' ∧ σ2 = applyAll σ wp := by simpa using heq2.symm
            rw [hp2, hs2] at lift1
            -- transport `q`'s round from `σ` to `applyAll σ wp`: `p`'s writes miss `q` entirely
            have hFq : FDisjoint (accesses p σ).writes (accesses q σ) := ⟨hindep0.2.1, hindep0.1⟩
            have hagree : ∀ l ∉ (accesses p σ).writes, σ l = applyAll σ wp l := by
              intro l hl
              exact (applyAll_frame wp σ l
                (fun hm => hl (pstep_writes_subset p σ hwfp p' wp hsp hm))).symm
            have hwfq_p : WellFormed q (applyAll σ wp) :=
              (WellFormed_locality q σ (applyAll σ wp) _ hFq hagree).mp hwfq
            have hsq_p : pstep q (applyAll σ wp) = some (q', wq) :=
              (pstep_locality q σ (applyAll σ wp) _ hwfq hFq hagree).symm.trans hsq
            obtain ⟨eaccq_p, -, -⟩ :=
              accesses_runSeq_locality q σ (applyAll σ wp) _ hFq hagree
            have r2 := ihq (applyAll σ wp) hwfq_p q' wq hsq_p
            obtain ⟨hsubp_r, hsubp_w⟩ := subset_chain p σ hwfp _ r1 p' (applyAll σ wp) rfl
            have hnr2 : ∀ q'' σ'', Reaches (Conf.run q (applyAll σ wp)) (Conf.run q'' σ'') →
                ¬ racing (nextAccs p') (nextAccs q'') = true := by
              intro q'' σ'' hc
              obtain ⟨hr, hw⟩ := subset_chain q (applyAll σ wp) hwfq_p _ hc q'' σ'' rfl
              exact no_race_of_sub p' q'' (applyAll σ wp) σ'' _ _ hindep0 hsubp_r hsubp_w
                (fun l hl => eaccq_p ▸ hr hl) (fun l hl => eaccq_p ▸ hw hl)
            obtain ⟨q2, σ3, heq3, lift2⟩ | hwrong :=
              reaches_par_right p' q k (applyAll σ wp) _ r2 hnr2
            · obtain ⟨hq2, hs3⟩ : q2 = q' ∧ σ3 = applyAll (applyAll σ wp) wq := by
                simpa using heq3.symm
              rw [hq2, hs3] at lift2
              rw [applyAll_append]
              exact lift1.trans lift2
            · exact absurd hwrong (by simp)
          · exact absurd hwrong (by simp)

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
theorem pstep_none_work {τ : Type} :
    ∀ (p : ParM τ) (σ : State), pstep p σ = none → work p σ = 0 := by
  intro p
  induction p with
  | pure a => intro σ _; rfl
  | read l k ih => intro σ h; simp [pstep] at h
  | write l v k ih => intro σ h; simp [pstep] at h
  | par p q k ihp ihq ihk =>
      intro σ h
      rcases hsp : pstep p σ with _ | ⟨p', wp⟩
      · rcases hsq : pstep q σ with _ | ⟨q', wq⟩
        · have hap : accesses p σ = Footprint.empty := pstep_none_accesses p σ hsp
          have haq : accesses q σ = Footprint.empty := pstep_none_accesses q σ hsq
          have hσ1 : (runSeq p σ).2 = σ := by
            funext m; exact runSeq_frame p σ m (by simp [hap, Footprint.empty])
          have hσ2 : (runSeq q σ).2 = σ := by
            funext m; exact runSeq_frame q σ m (by simp [haq, Footprint.empty])
          have hk : pstep (k ((runSeq p σ).1, (runSeq q σ).1)) σ = none := by
            simpa [pstep, hsp, hsq] using h
          have e1 := ihp σ hsp
          have e2 := ihq σ hsq
          have e3 := ihk _ σ hk
          show work (ParM.par p q k) σ = 0
          simp only [work, hσ1, hσ2, e1, e2, e3]
        · simp [pstep, hsp, hsq] at h
      · rcases hsq : pstep q σ with _ | ⟨q', wq⟩
        · simp [pstep, hsp, hsq] at h
        · simp [pstep, hsp, hsq] at h

/-- A well-formed `par` node yields a well-formed `parPair` of its branches: the independence and
per-branch obligations are the same, and `parPair`'s continuation is a `pure`, whose obligation is
`trivial`. Lets a proof about a `par` node read its join state off `parPair`'s canonical run. -/
theorem wellFormed_parPair_of_par {α β γ : Type} (p : ParM α) (q : ParM β) (k : α × β → ParM γ)
    (σ : State) (hwf : WellFormed (ParM.par p q k) σ) : WellFormed (ParM.parPair p q) σ :=
  ⟨hwf.1, hwf.2.1, hwf.2.2.1, trivial⟩

/-- **A round strictly reduces the remaining work.** This is what makes `time`'s fuel sufficient:
`work p σ` rounds always finish the program. The `par` case cancels the continuation's work exactly,
by reading the join state off `pstep_combined` applied to `parPair p q` — whose canonical run *is*
the pair of branch values together with the post-join state. -/
theorem work_pstep_lt {τ : Type} :
    ∀ (p : ParM τ) (σ : State), WellFormed p σ → ∀ (p' : ParM τ) (ws : List (Loc × Val)),
      pstep p σ = some (p', ws) → work p' (applyAll σ ws) < work p σ := by
  intro p
  induction p with
  | pure a => intro σ _ p' ws h; simp [pstep] at h
  | read l k ih =>
      intro σ _ p' ws h
      simp only [pstep, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [work, applyAll]
  | write l v k ih =>
      intro σ _ p' ws h
      simp only [pstep, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [work, applyAll]
  | par p q k ihp ihq ihk =>
      intro σ hwf P' ws h
      have hwfpp : WellFormed (ParM.parPair p q) σ := wellFormed_parPair_of_par p q k σ hwf
      obtain ⟨hindep, hwfp, hwfq1, hwfk⟩ := hwf
      obtain ⟨eacc_q, eval_q⟩ := accesses_runSeq_isolated p q σ hindep
      have hwfq : WellFormed q σ := wellFormed_branch_shift p q σ hindep hwfq1
      have hindep0 : Indep (accesses p σ) (accesses q σ) := eacc_q ▸ hindep
      have hFq1 : FDisjoint (accesses p σ).writes (accesses q (runSeq p σ).2) :=
        ⟨hindep.2.1, hindep.1⟩
      have ework_q : work q (runSeq p σ).2 = work q σ :=
        work_locality q (runSeq p σ).2 σ _ hFq1 (runSeq_frame p σ)
      rcases hsp : pstep p σ with _ | ⟨p', wp⟩
      · rcases hsq : pstep q σ with _ | ⟨q', wq⟩
        · -- join: branches are done, so the whole node's work is the continuation's
          have hwp : work p σ = 0 := pstep_none_work p σ hsp
          have hwq : work q σ = 0 := pstep_none_work q σ hsq
          have hap : accesses p σ = Footprint.empty := pstep_none_accesses p σ hsp
          have haq : accesses q σ = Footprint.empty := pstep_none_accesses q σ hsq
          have hσ1 : (runSeq p σ).2 = σ := by
            funext m; exact runSeq_frame p σ m (by simp [hap, Footprint.empty])
          have hσ2 : (runSeq q σ).2 = σ := by
            funext m; exact runSeq_frame q σ m (by simp [haq, Footprint.empty])
          have hk : pstep (k ((runSeq p σ).1, (runSeq q σ).1)) σ = some (P', ws) := by
            simpa [pstep, hsp, hsq] using h
          have := ihk _ σ (by rw [hσ1, hσ2] at hwfk; exact hwfk) P' ws hk
          show work P' (applyAll σ ws) < work (ParM.par p q k) σ
          simp only [work, hσ1, hσ2, hwp, hwq]
          omega
        · -- only `q` advanced
          simp only [pstep, hsp, hsq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hwp : work p σ = 0 := pstep_none_work p σ hsp
          have hap : accesses p σ = Footprint.empty := pstep_none_accesses p σ hsp
          -- `p` never moves the state, nor is it disturbed by `q`'s writes
          have hFp : FDisjoint (accesses q σ).writes (accesses p σ) := by
            rw [hap]; exact ⟨fun l _ hm => by simp [Footprint.empty] at hm,
              fun l _ hm => by simp [Footprint.empty] at hm⟩
          have hagree : ∀ l ∉ (accesses q σ).writes, σ l = applyAll σ wq l := fun l hl =>
            (applyAll_frame wq σ l
              (fun hm => hl (pstep_writes_subset q σ hwfq q' wq hsq hm))).symm
          have hwp' : work p (applyAll σ wq) = 0 := by
            rw [← work_locality p σ (applyAll σ wq) _ hFp hagree]; exact hwp
          obtain ⟨eapq, -, -⟩ := accesses_runSeq_locality p σ (applyAll σ wq) _ hFp hagree
          have hσq1 : (runSeq p (applyAll σ wq)).2 = applyAll σ wq := by
            funext m
            exact runSeq_frame p (applyAll σ wq) m (by rw [← eapq, hap]; simp [Footprint.empty])
          have hlt := ihq σ hwfq q' wq hsq
          -- the continuation's work is unchanged: read the join state off `parPair`
          have hpp : pstep (ParM.parPair p q) σ = some (ParM.parPair p q', wq) := by
            simp [ParM.parPair, pstep, hsp, hsq]
          obtain ⟨-, hrs, -, -⟩ := pstep_combined (ParM.parPair p q) σ hwfpp _ _ hpp
          simp only [ParM.parPair, runSeq, Prod.mk.injEq] at hrs
          show work (ParM.par p q' k) (applyAll σ wq) < work (ParM.par p q k) σ
          simp only [work]
          rw [hrs.1.1, hrs.1.2, hrs.2, hσq1]
          omega
      · rcases hsq : pstep q σ with _ | ⟨q', wq⟩
        · -- only `p` advanced
          simp only [pstep, hsp, hsq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hlt := ihp σ hwfp p' wp hsp
          obtain ⟨-, hrsp, -, -⟩ := pstep_combined p σ hwfp p' wp hsp
          have hpp : pstep (ParM.parPair p q) σ = some (ParM.parPair p' q, wp) := by
            simp [ParM.parPair, pstep, hsp, hsq]
          obtain ⟨-, hrs, -, -⟩ := pstep_combined (ParM.parPair p q) σ hwfpp _ _ hpp
          simp only [ParM.parPair, runSeq, Prod.mk.injEq] at hrs
          show work (ParM.par p' q k) (applyAll σ wp) < work (ParM.par p q k) σ
          simp only [work]
          rw [hrs.1.1, hrs.1.2, hrs.2, hrsp]
          omega
        · -- both advanced
          simp only [pstep, hsp, hsq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨-, hrsp, hsubpr, hsubpw⟩ := pstep_combined p σ hwfp p' wp hsp
          obtain ⟨-, hrsq, hsubqr, hsubqw⟩ := pstep_combined q σ hwfq q' wq hsq
          have hltp := ihp σ hwfp p' wp hsp
          have hltq := ihq σ hwfq q' wq hsq
          have hWpq : applyAll σ (wp ++ wq) = applyAll (applyAll σ wp) wq := applyAll_append σ wp wq
          -- ① `p`'s residual is undisturbed by `q`'s batch
          have hFp : FDisjoint (accesses q σ).writes (accesses p' (applyAll σ wp)) :=
            ⟨fun l hl hm => hindep0.2.2 l hl (hsubpr hm),
             fun l hl hm => hindep0.1 l (hsubpw hm) hl⟩
          have hagree1 : ∀ l ∉ (accesses q σ).writes,
              applyAll σ wp l = applyAll σ (wp ++ wq) l := by
            intro l hl
            rw [hWpq]
            exact (applyAll_frame wq (applyAll σ wp) l
              (fun hm => hl (pstep_writes_subset q σ hwfq q' wq hsq hm))).symm
          have eA : work p' (applyAll σ wp) = work p' (applyAll σ (wp ++ wq)) :=
            work_locality p' (applyAll σ wp) _ _ hFp hagree1
          obtain ⟨eaccp', -, -⟩ :=
            accesses_runSeq_locality p' (applyAll σ wp) _ _ hFp hagree1
          -- ② `q`'s residual is undisturbed by `p`'s batch, nor by `p'` finishing
          have hFq : FDisjoint (accesses p σ).writes (accesses q' (applyAll σ wq)) :=
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
                (fun hmm => hm (pstep_writes_subset p σ hwfp p' wp hsp hmm))
            rw [h1, h2]
          have eC : work q' (applyAll σ wq) =
              work q' (runSeq p' (applyAll σ (wp ++ wq))).2 :=
            work_locality q' (applyAll σ wq) _ _ hFq hagree2
          -- ③ the continuation's work is unchanged: `parPair` pins the join state
          have hpp : pstep (ParM.parPair p q) σ = some (ParM.parPair p' q', wp ++ wq) := by
            simp [ParM.parPair, pstep, hsp, hsq]
          obtain ⟨-, hrs, -, -⟩ := pstep_combined (ParM.parPair p q) σ hwfpp _ _ hpp
          simp only [ParM.parPair, runSeq, Prod.mk.injEq] at hrs
          show work (ParM.par p' q' k) (applyAll σ (wp ++ wq)) < work (ParM.par p q k) σ
          simp only [work]
          rw [hrs.1.1, hrs.1.2, hrs.2]
          omega

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

/-! ### The general law

`max` is written nowhere in `pstep` or `ptime`. It is forced by round-counting, and the proof needs
`Indep` at exactly one point: a branch's remaining rounds must come out the same whether or not the
*other* branch's writes from this round have already landed. That is `ptime_locality`, and it fails
for racing branches — which is why the law is stated under `WellFormed`. -/

/-- **Two independent branches run in parallel take as many rounds as the slower one** — at every
fuel `n`, so the statement is uniform in the bound.

`max` appears in neither `pstep` nor `ptime`; it is *derived* here. The proof is a fuel induction with
four cases at the `par` node — both branches step, only `p`, only `q`, neither — whose arithmetic is
trivial. All the content sits in `ptime_locality`, which is the single point where the `WellFormed`
hypothesis is used. -- ref: docs/cost.md; Blelloch & Greiner ICFP'96 (where `max` is stipulated) -/
theorem ptime_parPair_eq_max {α β : Type} : ∀ (n : Nat) (p : ParM α) (q : ParM β) (σ : State),
    WellFormed (ParM.parPair p q) σ →
      ptime n (ParM.parPair p q) σ = max (ptime n p σ) (ptime n q σ) := by
  intro n
  induction n with
  | zero => intro p q σ _; simp only [ptime]; omega
  | succ n ih =>
      intro p q σ hwf
      have hwfpp := hwf
      obtain ⟨hindep, hwfp, hwfq1, -⟩ := hwf
      obtain ⟨eacc_q, eval_q⟩ := accesses_runSeq_isolated p q σ hindep
      have hwfq : WellFormed q σ := wellFormed_branch_shift p q σ hindep hwfq1
      have hindep0 : Indep (accesses p σ) (accesses q σ) := eacc_q ▸ hindep
      rcases hsp : pstep p σ with _ | ⟨p', wp⟩
      · rcases hsq : pstep q σ with _ | ⟨q', wq⟩
        · -- neither branch has work left: the join is a `.pure`, so there is no round at all
          have hpp : pstep (ParM.parPair p q) σ = none := by
            simp [ParM.parPair, pstep, hsp, hsq]
          rw [ptime_succ_none n _ σ hpp, ptime_succ_none n p σ hsp, ptime_succ_none n q σ hsq]
          omega
        · -- only `q` has work left
          have hpp : pstep (ParM.parPair p q) σ = some (ParM.parPair p q', wq) := by
            simp [ParM.parPair, pstep, hsp, hsq]
          obtain ⟨hwf', -, -, -⟩ := pstep_combined (ParM.parPair p q) σ hwfpp _ _ hpp
          have hap : accesses p σ = Footprint.empty := pstep_none_accesses p σ hsp
          have hFp : FDisjoint (accesses q σ).writes (accesses p σ) := by
            rw [hap]
            exact ⟨fun l _ hm => by simp [Footprint.empty] at hm,
              fun l _ hm => by simp [Footprint.empty] at hm⟩
          have hagree : ∀ l ∉ (accesses q σ).writes, σ l = applyAll σ wq l := fun l hl =>
            (applyAll_frame wq σ l
              (fun hm => hl (pstep_writes_subset q σ hwfq q' wq hsq hm))).symm
          have hnone : pstep p (applyAll σ wq) = none :=
            (pstep_locality p σ (applyAll σ wq) _ hwfp hFp hagree).symm.trans hsp
          rw [ptime_succ_some n _ σ _ _ hpp, ptime_succ_none n p σ hsp,
            ptime_succ_some n q σ _ _ hsq, ih p q' (applyAll σ wq) hwf',
            ptime_zero_of_none n p _ hnone]
          omega
      · rcases hsq : pstep q σ with _ | ⟨q', wq⟩
        · -- only `p` has work left
          have hpp : pstep (ParM.parPair p q) σ = some (ParM.parPair p' q, wp) := by
            simp [ParM.parPair, pstep, hsp, hsq]
          obtain ⟨hwf', -, -, -⟩ := pstep_combined (ParM.parPair p q) σ hwfpp _ _ hpp
          have hFq : FDisjoint (accesses p σ).writes (accesses q σ) := ⟨hindep0.2.1, hindep0.1⟩
          have hagree : ∀ l ∉ (accesses p σ).writes, σ l = applyAll σ wp l := fun l hl =>
            (applyAll_frame wp σ l
              (fun hm => hl (pstep_writes_subset p σ hwfp p' wp hsp hm))).symm
          have hnone : pstep q (applyAll σ wp) = none :=
            (pstep_locality q σ (applyAll σ wp) _ hwfq hFq hagree).symm.trans hsq
          rw [ptime_succ_some n _ σ _ _ hpp, ptime_succ_some n p σ _ _ hsp,
            ptime_succ_none n q σ hsq, ih p' q (applyAll σ wp) hwf',
            ptime_zero_of_none n q _ hnone]
          omega
        · -- both advance in the same round — this is where `max` is born
          have hpp : pstep (ParM.parPair p q) σ = some (ParM.parPair p' q', wp ++ wq) := by
            simp [ParM.parPair, pstep, hsp, hsq]
          obtain ⟨hwf', -, -, -⟩ := pstep_combined (ParM.parPair p q) σ hwfpp _ _ hpp
          obtain ⟨hwfp', -, hsubpr, hsubpw⟩ := pstep_combined p σ hwfp p' wp hsp
          obtain ⟨hwfq', -, hsubqr, hsubqw⟩ := pstep_combined q σ hwfq q' wq hsq
          have hWpq : applyAll σ (wp ++ wq) = applyAll (applyAll σ wp) wq := applyAll_append σ wp wq
          -- `p`'s remaining rounds do not notice `q`'s batch …
          have hFp : FDisjoint (accesses q σ).writes (accesses p' (applyAll σ wp)) :=
            ⟨fun l hl hm => hindep0.2.2 l hl (hsubpr hm),
             fun l hl hm => hindep0.1 l (hsubpw hm) hl⟩
          have hagree1 : ∀ l ∉ (accesses q σ).writes,
              applyAll σ wp l = applyAll σ (wp ++ wq) l := by
            intro l hl
            rw [hWpq]
            exact (applyAll_frame wq (applyAll σ wp) l
              (fun hm => hl (pstep_writes_subset q σ hwfq q' wq hsq hm))).symm
          have eP : ptime n p' (applyAll σ wp) = ptime n p' (applyAll σ (wp ++ wq)) :=
            ptime_locality n p' (applyAll σ wp) _ _ hwfp' hFp hagree1
          -- … and `q`'s remaining rounds do not notice `p`'s
          have hFq : FDisjoint (accesses p σ).writes (accesses q' (applyAll σ wq)) :=
            ⟨fun l hl hm => hindep0.2.1 l hl (hsubqr hm),
             fun l hl hm => hindep0.1 l hl (hsubqw hm)⟩
          have hagree2 : ∀ l ∉ (accesses p σ).writes,
              applyAll σ wq l = applyAll σ (wp ++ wq) l := by
            intro l hl
            rw [hWpq]
            refine (applyAll_agree (accesses p σ).writes wq (applyAll σ wp) σ ?_ l hl).symm
            intro m hm
            exact applyAll_frame wp σ m
              (fun hmm => hm (pstep_writes_subset p σ hwfp p' wp hsp hmm))
          have eQ : ptime n q' (applyAll σ wq) = ptime n q' (applyAll σ (wp ++ wq)) :=
            ptime_locality n q' (applyAll σ wq) _ _ hwfq' hFq hagree2
          rw [ptime_succ_some n _ σ _ _ hpp, ptime_succ_some n p σ _ _ hsp,
            ptime_succ_some n q σ _ _ hsq, ih p' q' (applyAll σ (wp ++ wq)) hwf', ← eP, ← eQ]
          omega

/-- **The max law.** The time of a parallel pair is the `max` of its branches' times —
`ptime_parPair_eq_max` transported to `time`'s own fuel.

`max` is a *consequence* of round-counting, never stipulated, and `WellFormed` is the hypothesis that
earns it: it is spent at exactly one point, `ptime_locality`. Dropping it breaks the conclusion, not
just the proof (`RacyCost`). -/
theorem time_parPair_eq_max {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (hwf : WellFormed (ParM.parPair p q) σ) :
    time (ParM.parPair p q) σ = max (time p σ) (time q σ) := by
  have hwfp : WellFormed p σ := hwf.2.1
  have hwfq : WellFormed q σ := wellFormed_branch_shift p q σ hwf.1 hwf.2.2.1
  have eW : work (ParM.parPair p q) σ = work p σ + work q σ := by
    rw [work_parPair]
    exact congrArg _ (work_locality q (runSeq p σ).2 σ _ ⟨hwf.1.2.1, hwf.1.1⟩ (runSeq_frame p σ))
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
  intro p
  induction p with
  | pure a => intro f σ; rfl
  | read l k ih => intro f σ; simp only [ParM.bind, pstep]
  | write l v k ih => intro f σ; simp only [ParM.bind, pstep]
  | par p q k ihp ihq ihk =>
      intro f σ
      rcases hsp : pstep p σ with _ | ⟨p', wp⟩
      · rcases hsq : pstep q σ with _ | ⟨q', wq⟩
        · have hap : accesses p σ = Footprint.empty := pstep_none_accesses p σ hsp
          have haq : accesses q σ = Footprint.empty := pstep_none_accesses q σ hsq
          have hσ1 : (runSeq p σ).2 = σ := by
            funext m; exact runSeq_frame p σ m (by simp [hap, Footprint.empty])
          have hσ2 : (runSeq q σ).2 = σ := by
            funext m; exact runSeq_frame q σ m (by simp [haq, Footprint.empty])
          show pstep (ParM.par p q (fun r => ParM.bind (k r) f)) σ = _
          simp only [pstep, hsp, hsq, ihk _ f σ, runSeq, hσ1, hσ2]
        · show pstep (ParM.par p q (fun r => ParM.bind (k r) f)) σ = _
          simp only [pstep, hsp, hsq, ParM.bind]
      · rcases hsq : pstep q σ with _ | ⟨q', wq⟩
        · show pstep (ParM.par p q (fun r => ParM.bind (k r) f)) σ = _
          simp only [pstep, hsp, hsq, ParM.bind]
        · show pstep (ParM.par p q (fun r => ParM.bind (k r) f)) σ = _
          simp only [pstep, hsp, hsq, ParM.bind]

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

/-- **Parallel is strictly faster.** Same work (`work_par_eq_seq`), strictly fewer rounds whenever
both branches actually do something. Both hypotheses are load-bearing: forking against a `pure` buys
nothing, and racing branches have no `WellFormed` derivation. -/
theorem time_par_lt_seq {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (hwf : WellFormed (ParM.parPair p q) σ)
    (hp : 0 < time p σ) (hq : 0 < time q σ) :
    time (ParM.parPair p q) σ < time (ParM.seqPair p q) σ := by
  have hwfs : WellFormed (ParM.seqPair p q) σ := by
    rw [ParM.seqPair, WellFormed_bind]
    refine ⟨hwf.2.1, ?_⟩
    rw [WellFormed_bind]
    exact ⟨hwf.2.2.1, trivial⟩
  have eq : time q (runSeq p σ).2 = time q σ := by
    have hF : FDisjoint (accesses p σ).writes (accesses q (runSeq p σ).2) :=
      ⟨hwf.1.2.1, hwf.1.1⟩
    have hw : work q (runSeq p σ).2 = work q σ :=
      work_locality q (runSeq p σ).2 σ _ hF (runSeq_frame p σ)
    have hwfq1 : WellFormed q (runSeq p σ).2 := hwf.2.2.1
    show ptime (work q (runSeq p σ).2 + 1) q (runSeq p σ).2 = ptime (work q σ + 1) q σ
    rw [hw]
    exact ptime_locality _ q (runSeq p σ).2 σ _ hwfq1 hF (runSeq_frame p σ)
  rw [time_parPair_eq_max p q σ hwf, time_seqPair_eq_add p q σ hwfs, eq]
  omega

/-- The non-strict form, with no hypothesis on the branches. -/
theorem time_par_le_seq {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (hwf : WellFormed (ParM.parPair p q) σ) :
    time (ParM.parPair p q) σ ≤ time (ParM.seqPair p q) σ := by
  have hwfs : WellFormed (ParM.seqPair p q) σ := by
    rw [ParM.seqPair, WellFormed_bind]
    refine ⟨hwf.2.1, ?_⟩
    rw [WellFormed_bind]
    exact ⟨hwf.2.2.1, trivial⟩
  have eq : time q (runSeq p σ).2 = time q σ := by
    have hF : FDisjoint (accesses p σ).writes (accesses q (runSeq p σ).2) :=
      ⟨hwf.1.2.1, hwf.1.1⟩
    have hw : work q (runSeq p σ).2 = work q σ :=
      work_locality q (runSeq p σ).2 σ _ hF (runSeq_frame p σ)
    show ptime (work q (runSeq p σ).2 + 1) q (runSeq p σ).2 = ptime (work q σ + 1) q σ
    rw [hw]
    exact ptime_locality _ q (runSeq p σ).2 σ _ hwf.2.2.1 hF (runSeq_frame p σ)
  rw [time_parPair_eq_max p q σ hwf, time_seqPair_eq_add p q σ hwfs, eq]
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

/-- **Work is unchanged N-ary too**, with no hypothesis: the same operations run either way. -/
theorem work_parAll_eq_seqAll {τ : Type} : ∀ (ps : List (ParM τ)) (σ : State),
    work (ParM.parAll ps) σ = work (ParM.seqAll ps) σ := by
  intro ps
  induction ps with
  | nil => intro σ; rfl
  | cons p ps ih =>
      intro σ
      show work (ParM.bind (ParM.parPair p (ParM.parAll ps)) _) σ
        = work (ParM.bind (ParM.seqPair p (ParM.seqAll ps)) _) σ
      rw [work_bind, work_bind, work_parPair, work_seqPair, ih (runSeq p σ).2]
      simp [work]

/-! ### N-ary: `parAll` takes the max, `seqAll` the sum -/

/-- `parAll` takes the `max` of its head and its tail. The N-ary max law, a corollary of the binary
one because `parAll` is built from `parPair` — there is no `parN` constructor. -/
theorem time_parAll_cons {τ : Type} (p : ParM τ) (ps : List (ParM τ)) (σ : State)
    (hwf : WellFormed (ParM.parAll (p :: ps)) σ) :
    time (ParM.parAll (p :: ps)) σ = max (time p σ) (time (ParM.parAll ps) σ) := by
  have hb : ParM.parAll (p :: ps) =
      ParM.bind (ParM.parPair p (ParM.parAll ps)) (fun r => ParM.pure (r.1 :: r.2)) := rfl
  rw [hb, time_bind_add _ _ σ (hb ▸ hwf)]
  have hwfp : WellFormed (ParM.parPair p (ParM.parAll ps)) σ :=
    ((WellFormed_bind _ _ σ).mp (hb ▸ hwf)).1
  rw [time_parPair_eq_max p (ParM.parAll ps) σ hwfp]
  rfl

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
  have hwfp : WellFormed (ParM.parPair p (ParM.parAll ps)) σ :=
    ((WellFormed_bind _ _ σ).mp hwf).1
  have hindep : Indep (accesses p σ) (accesses (ParM.parAll ps) (runSeq p σ).2) := hwfp.1
  have hwf1 : WellFormed (ParM.parAll ps) (runSeq p σ).2 := hwfp.2.2.1
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
      have hwfp : WellFormed (ParM.parPair p (ParM.parAll ps)) σ :=
        ((WellFormed_bind _ _ σ).mp hwf).1
      have hrec := ih (runSeq p σ).2 hwfp.2.2.1
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
  have hwfp : WellFormed (ParM.parPair p (ParM.parAll ps)) σ :=
    ((WellFormed_bind _ _ σ).mp hwf).1
  have hle := time_parAll_le_seqAll ps (runSeq p σ).2 hwfp.2.2.1
  have hshift := time_parAll_shift p ps σ hwf
  rw [time_parAll_cons p ps σ hwf, time_seqAll_cons p ps σ hwfs]
  omega

/-- A `parAll` whose head has work to do costs at least one round. Discharges the `0 < time _ _` side
condition of `time_parAll_lt_seqAll` when recursing down a list. -/
theorem time_parAll_pos {τ : Type} (p : ParM τ) (ps : List (ParM τ)) (σ : State)
    (hwf : WellFormed (ParM.parAll (p :: ps)) σ) (hp : 0 < time p σ) :
    0 < time (ParM.parAll (p :: ps)) σ := by
  rw [time_parAll_cons p ps σ hwf]; omega

/-! ### Anti-vacuity: the law fails for racing branches

Required by `CLAUDE.md`'s standing obligation — the `WellFormed` hypothesis must be doing work, not
decorating a theorem that would hold anyway.

`racyQ` writes location `0`; `racyP` reads it, one round later, and branches on what it finds. Run
alone from `σz` it sees `int 0` and stops after two rounds. Run in parallel it sees `racyQ`'s `int 1`
and takes a third. So `max` is *wrong* here, and `time_parPair_eq_max` correctly refuses to apply:
`Indep` fails, because `0` is in `racyQ`'s writes and `racyP`'s reads. -/

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
`run`, `accesses`, `compile` and `render` — see `docs/program-model.md`. -/
def costOf {τ : Type} (p : ParM τ) (σ : State) : Cost := ⟨work p σ, time p σ⟩

/-- `costOf`'s first projection is `work`. -/
@[simp, grind .] theorem costOf_work {τ : Type} (p : ParM τ) (σ : State) :
    (costOf p σ).work = work p σ := rfl
/-- `costOf`'s second projection is `time`. -/
@[simp, grind .] theorem costOf_time {τ : Type} (p : ParM τ) (σ : State) :
    (costOf p σ).time = time p σ := rfl

end Paralever
