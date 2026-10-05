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

/-- A type whose values fit in a heap cell: `encode` turns an `α` into a `Val` and `decode` tries to
read one back. `decode` is partial because a cell may hold a `Val` of another shape, and
`decode_encode` is what makes `readAs` after `writeAs` round-trip. The footprint theory never uses
`decode_encode`; programs reasoning about values do. -/
class Storable (α : Type) where
  encode : α → Val
  decode : Val → Option α
  decode_encode : ∀ a : α, decode (encode a) = some a

/-- `Int` is stored as `Val.int`. -/
instance : Storable Int where
  encode n := .int n
  decode | .int n => some n | _ => none
  decode_encode _ := rfl

/-- `Bool` is stored as `Val.bool`. -/
instance : Storable Bool where
  encode b := .bool b
  decode | .bool b => some b | _ => none
  decode_encode _ := rfl

/-- `Unit` is stored as `Val.unit`. -/
instance : Storable Unit where
  encode _ := .unit
  decode | .unit => some () | _ => none
  decode_encode _ := rfl

/-! ### Typed read and write -/

/-- Read `l` as an `α`, falling back to `dflt` when the cell holds a `Val` of another shape. A total
function, so there is no failure case for footprints to branch on. -/
def readAs {α : Type} [Storable α] (l : Loc) (dflt : α) : ParM α :=
  .read l (fun v => .pure ((Storable.decode v).getD dflt))

/-- Store `a : α` at `l`, encoded as a `Val`. -/
def writeAs {α : Type} [Storable α] (l : Loc) (a : α) : ParM Unit :=
  .write l (Storable.encode a) .pure

/-! ### Footprints — all by `rfl`, no case analysis

This is the whole point of pushing the decode inside `.pure`. -/

/-- A typed read touches exactly `l`, and only by reading it. -/
@[simp, grind .]
theorem readAs_accesses {α : Type} [Storable α] (l : Loc) (d : α) (σ : State) :
    accesses (readAs l d) σ = ⟨[l], []⟩ := rfl

/-- A typed write touches exactly `l`, and only by writing it. -/
@[simp, grind .]
theorem writeAs_accesses {α : Type} [Storable α] (l : Loc) (a : α) (σ : State) :
    accesses (writeAs l a) σ = ⟨[], [l]⟩ := rfl

/-- A typed read is well-formed: it contains no `par` node. -/
@[simp, grind .]
theorem readAs_wellformed {α : Type} [Storable α] (l : Loc) (d : α) (σ : State) :
    WellFormed (readAs l d) σ := trivial

/-- A typed write is well-formed: it contains no `par` node. -/
@[simp, grind .]
theorem writeAs_wellformed {α : Type} [Storable α] (l : Loc) (a : α) (σ : State) :
    WellFormed (writeAs l a) σ := trivial

/-- A typed read yields the decoded contents of `l` and leaves the heap alone. -/
@[simp, grind .]
theorem readAs_runSeq {α : Type} [Storable α] (l : Loc) (d : α) (σ : State) :
    runSeq (readAs l d) σ = ((Storable.decode (σ l)).getD d, σ) := rfl

/-- A typed write updates `l` to `encode a` and yields nothing. -/
@[simp, grind .]
theorem writeAs_runSeq {α : Type} [Storable α] (l : Loc) (a : α) (σ : State) :
    runSeq (writeAs l a) σ = ((), σ.update l (Storable.encode a)) := rfl

/-! ### Confinement — base cases for the `Within` combinators

A single typed access is confined to any location predicate its one location satisfies; these are the
leaves that `Theory/Intervals.lean`'s `union`/`mono` lemmas build larger bounds from. -/

/-- A typed read of `l` is confined to any `P` holding at `l`. -/
@[grind .]
theorem readAs_footprintWithin {α : Type} [Storable α] (l : Loc) (d : α) (σ : State)
    (P : Loc → Prop) (hl : P l) : FootprintWithin (accesses (readAs l d) σ) P :=
  ⟨Within.singleton hl, Within.empty P⟩

/-- A typed write to `l` is confined to any `P` holding at `l`. -/
@[grind .]
theorem writeAs_footprintWithin {α : Type} [Storable α] (l : Loc) (a : α) (σ : State)
    (P : Loc → Prop) (hl : P l) : FootprintWithin (accesses (writeAs l a) σ) P :=
  ⟨Within.empty P, Within.singleton hl⟩

/-- The reads-only bound, for when `P` confines reads but writes need a different predicate. -/
@[grind .]
theorem readAs_readsWithin {α : Type} [Storable α] (l : Loc) (d : α) (σ : State)
    (P : Loc → Prop) (hl : P l) : ReadsWithin (accesses (readAs l d) σ) P :=
  Within.singleton hl

/-- A typed read writes nothing — the base case for `no_writes_bind` and `indep_of_no_writes`. -/
@[grind .]
theorem readAs_no_writes {α : Type} [Storable α] (l : Loc) (d : α) (σ : State) :
    (accesses (readAs l d) σ).writes = [] := rfl

/-! ### Bind composition — the state is unchanged by a read, so the continuation sees `σ` -/

/-- A typed read followed by `f` is confined to `P` when `P l` holds and every `f a` is. The
continuation hypothesis is universally quantified over `a` because the decoded value depends on the
heap, and `σ` is the same on both sides since a read does not change it. -/
@[grind .]
theorem readAs_bind_footprintWithin {α β : Type} [Storable α] (l : Loc) (d : α)
    (f : α → ParM β) (σ : State) (P : Loc → Prop) (hl : P l)
    (hf : ∀ a : α, FootprintWithin (accesses (f a) σ) P) :
    FootprintWithin (accesses (ParM.bind (readAs l d) f) σ) P := by
  refine footprintWithin_bind _ _ _ _ (readAs_footprintWithin l d σ P hl) ?_
  rw [readAs_runSeq]; exact hf _

/-- A typed read followed by `f` is well-formed when every `f a` is — the step `Lib/Block.lean`'s
`load` case takes. -/
@[grind .]
theorem readAs_bind_wellformed {α β : Type} [Storable α] (l : Loc) (d : α)
    (f : α → ParM β) (σ : State) (hf : ∀ a : α, WellFormed (f a) σ) :
    WellFormed (ParM.bind (readAs l d) f) σ := by
  rw [WellFormed_bind]
  exact ⟨readAs_wellformed l d σ, by rw [readAs_runSeq]; exact hf _⟩

/-! ### The former `readInt`/`readBool`, now instances rather than duplicated code -/

/-- Read `l` as an `Int`, defaulting to `0`. An `abbrev`, so every `readAs` lemma applies unfolded. -/
abbrev readInt (l : Loc) (dflt : Int := 0) : ParM Int := readAs l dflt

/-- Read `l` as a `Bool`, defaulting to `false`. -/
abbrev readBool (l : Loc) (dflt : Bool := false) : ParM Bool := readAs l dflt

end Paralever
