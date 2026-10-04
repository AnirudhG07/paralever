import Paralever.Lib.Compose

/-! # Typed reads — eliminate Val case splits from proofs

Every `.read l k` in user code forces a 3-way `cases σ l` split in footprint and well-formedness
proofs. `readInt`/`readBool` wrap the read so all branches are `.pure`, making `accesses`
state-independent (`⟨[l], []⟩` by `rfl`) and `WellFormed` trivial. The Val dispatch still happens
at `runSeq` time, but proof obligations never see it.

Rationale: `docs/access.md` (footprints are reference-interpreter folds). -/

namespace Paralever

-- ref: Vafeiadis §3 — typed accessors as derived forms over untyped state

def readInt (l : Loc) (default : Int := 0) : ParM Int :=
  .read l (fun v => match v with | .int n => .pure n | _ => .pure default)

def readBool (l : Loc) (default : Bool := false) : ParM Bool :=
  .read l (fun v => match v with | .bool b => .pure b | _ => .pure default)

/-! ### Accesses: state-independent because every branch is `.pure` -/

@[simp, grind .]
theorem readInt_accesses (l : Loc) (d : Int) (σ : State) :
    accesses (readInt l d) σ = ⟨[l], []⟩ := by
  unfold readInt accesses
  cases σ l <;> simp [Footprint.union, Footprint.empty]

@[simp, grind .]
theorem readBool_accesses (l : Loc) (d : Bool) (σ : State) :
    accesses (readBool l d) σ = ⟨[l], []⟩ := by
  unfold readBool accesses
  cases σ l <;> simp [Footprint.union, Footprint.empty]

/-! ### WellFormed: trivially true (no `par` inside) -/

@[simp, grind .]
theorem readInt_wellformed (l : Loc) (d : Int) (σ : State) :
    WellFormed (readInt l d) σ := by
  unfold readInt WellFormed
  cases σ l <;> trivial

@[simp, grind .]
theorem readBool_wellformed (l : Loc) (d : Bool) (σ : State) :
    WellFormed (readBool l d) σ := by
  unfold readBool WellFormed
  cases σ l <;> trivial

/-! ### runSeq: the only place Val dispatch matters -/

@[simp, grind .]
theorem readInt_runSeq (l : Loc) (d : Int) (σ : State) :
    runSeq (readInt l d) σ = (match σ l with | .int n => n | _ => d, σ) := by
  unfold readInt runSeq
  cases σ l <;> rfl

@[simp, grind .]
theorem readBool_runSeq (l : Loc) (d : Bool) (σ : State) :
    runSeq (readBool l d) σ = (match σ l with | .bool b => b | _ => d, σ) := by
  unfold readBool runSeq
  cases σ l <;> rfl

/-! ### FootprintWithin: just needs `P l` -/

@[simp, grind .]
theorem readInt_footprintWithin (l : Loc) (d : Int) (σ : State) (P : Loc → Prop) (hl : P l) :
    FootprintWithin (accesses (readInt l d) σ) P := by
  rw [readInt_accesses]; exact ⟨Within.singleton hl, Within.empty P⟩

@[simp, grind .]
theorem readBool_footprintWithin (l : Loc) (d : Bool) (σ : State) (P : Loc → Prop) (hl : P l) :
    FootprintWithin (accesses (readBool l d) σ) P := by
  rw [readBool_accesses]; exact ⟨Within.singleton hl, Within.empty P⟩

@[simp, grind .]
theorem readInt_readsWithin (l : Loc) (d : Int) (σ : State) (P : Loc → Prop) (hl : P l) :
    ReadsWithin (accesses (readInt l d) σ) P := by
  rw [readInt_accesses]; exact Within.singleton hl

@[simp, grind .]
theorem readBool_readsWithin (l : Loc) (d : Bool) (σ : State) (P : Loc → Prop) (hl : P l) :
    ReadsWithin (accesses (readBool l d) σ) P := by
  rw [readBool_accesses]; exact Within.singleton hl

/-! ### Bind composition: readInt/readBool followed by any continuation

The user writes `bind (readInt l d) f` — these lemmas push the footprint bound through the bind
in one step, so the user supplies only `P l` and a footprint bound for `f`. -/

@[simp, grind .]
theorem readInt_bind_footprintWithin (l : Loc) (d : Int) (f : Int → ParM β)
    (σ : State) (P : Loc → Prop) (hl : P l)
    (hf : ∀ n, FootprintWithin (accesses (f n) σ) P) :
    FootprintWithin (accesses (ParM.bind (readInt l d) f) σ) P := by
  apply footprintWithin_bind
  · exact readInt_footprintWithin l d σ P hl
  · rw [readInt_runSeq]; cases σ l <;> exact hf _

@[simp, grind .]
theorem readBool_bind_footprintWithin (l : Loc) (d : Bool) (f : Bool → ParM β)
    (σ : State) (P : Loc → Prop) (hl : P l)
    (hf : ∀ b, FootprintWithin (accesses (f b) σ) P) :
    FootprintWithin (accesses (ParM.bind (readBool l d) f) σ) P := by
  apply footprintWithin_bind
  · exact readBool_footprintWithin l d σ P hl
  · rw [readBool_runSeq]; cases σ l <;> exact hf _

@[simp, grind .]
theorem readInt_bind_wellformed (l : Loc) (d : Int) (f : Int → ParM β)
    (σ : State)
    (hf : ∀ n, WellFormed (f n) σ) :
    WellFormed (ParM.bind (readInt l d) f) σ := by
  unfold readInt ParM.bind WellFormed
  cases σ l <;> simp [ParM.bind] <;> exact hf _

@[simp, grind .]
theorem readBool_bind_wellformed (l : Loc) (d : Bool) (f : Bool → ParM β)
    (σ : State)
    (hf : ∀ b, WellFormed (f b) σ) :
    WellFormed (ParM.bind (readBool l d) f) σ := by
  unfold readBool ParM.bind WellFormed
  cases σ l <;> simp [ParM.bind] <;> exact hf _

end Paralever
