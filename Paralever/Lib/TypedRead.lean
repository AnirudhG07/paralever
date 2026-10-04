import Paralever.Lib.Compose

/-! # Typed access — `Storable α`, for any `α` encodable in `Val`

The heap is `State := Loc → Val`, so a `.read` physically yields a `Val`; that is a property of the
memory model, not a restriction we chose. `Storable α` is the honest boundary: *any* type that can
be encoded into `Val` gets typed access, with every footprint lemma proved once, polymorphically.

The payoff over a hand-written `readInt`/`readBool` pair is not just deduplication. Writing the
decode *inside* `.pure` — `.read l (fun v => .pure (decode v))` rather than
`.read l (fun v => match v with | .int n => .pure n | _ => .pure d)` — means every branch is
syntactically the same `.pure` node, so `accesses` and `WellFormed` hold by `rfl` with **no `Val`
case analysis at all**. The match moved inside the value, where footprints cannot see it.

Rationale: `docs/access.md` (footprints are folds over the tree). -/

namespace Paralever

-- ref: docs/access.md; the encode/decode discipline is standard data refinement

/-- Types encodable in the heap's value universe. `decode_encode` is what makes `readAs` after
`writeAs` round-trip; nothing in the footprint theory needs it, but programs do. -/
class Storable (α : Type) where
  encode : α → Val
  decode : Val → Option α
  decode_encode : ∀ a : α, decode (encode a) = some a

instance : Storable Int where
  encode n := .int n
  decode | .int n => some n | _ => none
  decode_encode _ := rfl

instance : Storable Bool where
  encode b := .bool b
  decode | .bool b => some b | _ => none
  decode_encode _ := rfl

instance : Storable Unit where
  encode _ := .unit
  decode | .unit => some () | _ => none
  decode_encode _ := rfl

/-! ### Typed read and write -/

/-- Read `l` as an `α`, falling back to `dflt` if the cell holds something else. -/
def readAs {α : Type} [Storable α] (l : Loc) (dflt : α) : ParM α :=
  .read l (fun v => .pure ((Storable.decode v).getD dflt))

/-- Write `a : α` to `l`. -/
def writeAs {α : Type} [Storable α] (l : Loc) (a : α) : ParM Unit :=
  .write l (Storable.encode a) .pure

/-! ### Footprints — all by `rfl`, no case analysis

This is the whole point of pushing the decode inside `.pure`. -/

@[simp, grind .]
theorem readAs_accesses {α : Type} [Storable α] (l : Loc) (d : α) (σ : State) :
    accesses (readAs l d) σ = ⟨[l], []⟩ := rfl

@[simp, grind .]
theorem writeAs_accesses {α : Type} [Storable α] (l : Loc) (a : α) (σ : State) :
    accesses (writeAs l a) σ = ⟨[], [l]⟩ := rfl

@[simp, grind .]
theorem readAs_wellformed {α : Type} [Storable α] (l : Loc) (d : α) (σ : State) :
    WellFormed (readAs l d) σ := trivial

@[simp, grind .]
theorem writeAs_wellformed {α : Type} [Storable α] (l : Loc) (a : α) (σ : State) :
    WellFormed (writeAs l a) σ := trivial

@[simp, grind .]
theorem readAs_runSeq {α : Type} [Storable α] (l : Loc) (d : α) (σ : State) :
    runSeq (readAs l d) σ = ((Storable.decode (σ l)).getD d, σ) := rfl

@[simp, grind .]
theorem writeAs_runSeq {α : Type} [Storable α] (l : Loc) (a : α) (σ : State) :
    runSeq (writeAs l a) σ = ((), σ.update l (Storable.encode a)) := rfl

/-! ### Confinement -/

@[grind .]
theorem readAs_footprintWithin {α : Type} [Storable α] (l : Loc) (d : α) (σ : State)
    (P : Loc → Prop) (hl : P l) : FootprintWithin (accesses (readAs l d) σ) P :=
  ⟨Within.singleton hl, Within.empty P⟩

@[grind .]
theorem writeAs_footprintWithin {α : Type} [Storable α] (l : Loc) (a : α) (σ : State)
    (P : Loc → Prop) (hl : P l) : FootprintWithin (accesses (writeAs l a) σ) P :=
  ⟨Within.empty P, Within.singleton hl⟩

@[grind .]
theorem readAs_readsWithin {α : Type} [Storable α] (l : Loc) (d : α) (σ : State)
    (P : Loc → Prop) (hl : P l) : ReadsWithin (accesses (readAs l d) σ) P :=
  Within.singleton hl

@[grind .]
theorem readAs_no_writes {α : Type} [Storable α] (l : Loc) (d : α) (σ : State) :
    (accesses (readAs l d) σ).writes = [] := rfl

/-! ### Bind composition — the state is unchanged by a read, so the continuation sees `σ` -/

@[grind .]
theorem readAs_bind_footprintWithin {α β : Type} [Storable α] (l : Loc) (d : α)
    (f : α → ParM β) (σ : State) (P : Loc → Prop) (hl : P l)
    (hf : ∀ a : α, FootprintWithin (accesses (f a) σ) P) :
    FootprintWithin (accesses (ParM.bind (readAs l d) f) σ) P := by
  refine footprintWithin_bind _ _ _ _ (readAs_footprintWithin l d σ P hl) ?_
  rw [readAs_runSeq]; exact hf _

@[grind .]
theorem readAs_bind_wellformed {α β : Type} [Storable α] (l : Loc) (d : α)
    (f : α → ParM β) (σ : State) (hf : ∀ a : α, WellFormed (f a) σ) :
    WellFormed (ParM.bind (readAs l d) f) σ := by
  rw [WellFormed_bind]
  exact ⟨readAs_wellformed l d σ, by rw [readAs_runSeq]; exact hf _⟩

/-! ### The former `readInt`/`readBool`, now instances rather than duplicated code -/

abbrev readInt (l : Loc) (dflt : Int := 0) : ParM Int := readAs l dflt
abbrev readBool (l : Loc) (dflt : Bool := false) : ParM Bool := readAs l dflt

end Paralever
