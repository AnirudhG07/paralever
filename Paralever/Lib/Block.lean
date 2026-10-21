import Paralever.Lib.TypedRead
import Paralever.Lib.Notation
import Paralever.Lib.Cost

/-! # `Block` — a straight-line IR, so footprints are *computed* rather than proved

Writing programs as nested `ParM.bind` chains is writing in the monad by hand, and it forces a
per-program footprint induction. A compiler does not work that way: it lowers to an IR where every
memory operation is an explicit instruction, and the read/write set of a basic block is then a
*fold over the instruction list* — syntax, not analysis.

This file is that IR, at the smallest size that is still honest:

* `AExp` — pure arithmetic over a register file. No memory operand, so it contributes **nothing**
  to the footprint.
* `Instr` — exactly two memory operations, `load` and `store`.
* `Block := List Instr` — a straight-line basic block. Ordinary data.

The payoff is `exec_accesses`:

    accesses (exec b ρ) σ = footprintOf b

proved **once** by induction on the block. After it, every concrete program's footprint is `rfl`,
every independence check is `decide`, and no example writes a footprint induction again.

The register/memory split is exactly the one LLVM's `mem2reg` makes: a value in a register is
invisible to the footprint, a value in memory is not. Forcing every heap value through an explicit
`load` is what makes the extraction syntactic.

Rationale: `docs/block-ir.md`. -/

namespace Paralever

-- ref: docs/block-ir.md; register/memory split follows LLVM mem2reg

/-- A register name. Registers are not addressable, so a `Reg` is never a `Loc`. -/
abbrev Reg := Nat

/-- Arithmetic over registers and literals. Deliberately has **no** memory operand: every heap value
must come through an explicit `load` first, which is what keeps `footprintOf` syntactic and keeps
registers out of every footprint. -- ref: `docs/block-ir.md` -/
inductive AExp where
  | lit : Int → AExp
  | reg : Reg → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  /-- `min a b` and `max a b`. Present so a compare-exchange can be written **branch-free**: a
  sorting network never needs a conditional, so the language needs none and footprints stay exact.
  -- ref: `docs/block-ir.md` -/
  | min : AExp → AExp → AExp
  | max : AExp → AExp → AExp
  /-- Integer division, total: division by zero is `0`, as in Lean's `Int`. Present so a learning
  rate below one can be written without leaving the integers. -/
  | div : AExp → AExp → AExp
  deriving Repr, DecidableEq

/-- The two memory operations. `load r l` is `r := M[l]`; `store l e` is `M[l] := e`. -/
inductive Instr where
  | load  : Reg → Loc → Instr
  | store : Loc → AExp → Instr
  deriving Repr, DecidableEq

/-- A straight-line basic block: instructions in execution order, no branches and no loops. Ordinary
`List` data, so `footprintOf` can fold over it. -/
abbrev Block := List Instr

/-- The register file. Registers hold `Int`, are not memory, and never appear in a footprint. -/
abbrev Regs := Reg → Int

/-- `ρ` with register `r` holding `v`. -/
def Regs.set (ρ : Regs) (r : Reg) (v : Int) : Regs := fun r' => if r' = r then v else ρ r'

/-- The `Int` an expression denotes under the register file `ρ`. Total, and touches no memory. -/
@[simp, grind .]
def AExp.eval (ρ : Regs) : AExp → Int
  | .lit n   => n
  | .reg r   => ρ r
  | .add a b => a.eval ρ + b.eval ρ
  | .sub a b => a.eval ρ - b.eval ρ
  | .mul a b => a.eval ρ * b.eval ρ
  | .min a b => let x := a.eval ρ; let y := b.eval ρ; if x ≤ y then x else y
  | .max a b => let x := a.eval ρ; let y := b.eval ρ; if x ≤ y then y else x
  | .div a b => (a.eval ρ) / (b.eval ρ)

/-- `+` on `AExp`, so expressions are written as ordinary arithmetic. -/
instance : Add AExp := ⟨AExp.add⟩
/-- `-` on `AExp`. -/
instance : Sub AExp := ⟨AExp.sub⟩
/-- `*` on `AExp`. -/
instance : Mul AExp := ⟨AExp.mul⟩
/-- A numeric literal elaborates as `AExp.lit`, so `%0 * 2 + 1` is an `AExp`
(`%n` is surface syntax, `Prl/Lang/Notation.lean`). -/
instance : OfNat AExp n := ⟨AExp.lit (Int.ofNat n)⟩

/-! ### Lowering to `ParM`

The binds are generated here, once, rather than written by hand at every use site. -/

/-- Lower a block to a `ParM` program, starting from register file `ρ`: one `readAs` per `load`, one
`writeAs` per `store`, bound left to right. -/
def exec : Block → Regs → ParM Unit
  | [],                 _ => .pure ()
  | .load r l  :: rest, ρ => doₚ
      let v ← readAs l (0 : Int)
      exec rest (ρ.set r v)
  | .store l e :: rest, ρ => doₚ
      writeAs l (e.eval ρ)
      exec rest ρ

/-! ### The syntactic footprint — a fold, computable by `rfl` -/

/-- The block's read/write set, read straight off the instruction list: no state, no simulation.
Not written `Block.footprint`, because `Block` is an `abbrev` for `List` and dot-notation would
resolve to `List.footprint`. -/
@[simp, grind .]
def footprintOf : Block → Footprint
  | []                 => .empty
  | .load _ l  :: rest => Footprint.union ⟨[l], []⟩ (footprintOf rest)
  | .store l _ :: rest => Footprint.union ⟨[], [l]⟩ (footprintOf rest)

/-- **The theorem that makes this worthwhile.** The footprint `accesses` computes by simulating is
exactly the one read off the syntax — for every register file and every state. Proved once; every
program downstream gets its footprint by `rfl`. -/
theorem exec_accesses : ∀ (b : Block) (ρ : Regs) (σ : State),
    accesses (exec b ρ) σ = footprintOf b := by
  intro b
  induction b with
  | nil => intro ρ σ; rfl
  | cons i rest ih =>
      intro ρ σ
      cases i with
      | load r l =>
          show accesses (ParM.bind (readAs l (0 : Int)) _) σ = _
          rw [accesses_bind, readAs_accesses, readAs_runSeq, ih]
          rfl
      | store l e =>
          show accesses (ParM.bind (writeAs l (AExp.eval ρ e)) _) σ = _
          rw [accesses_bind, writeAs_accesses, writeAs_runSeq, ih]
          rfl

/-- A straight-line block has no `par` node, so it is well-formed unconditionally. -/
theorem exec_wellformed : ∀ (b : Block) (ρ : Regs) (σ : State), WellFormed (exec b ρ) σ := by
  intro b
  induction b with
  | nil => intro ρ σ; trivial
  | cons i rest ih =>
      intro ρ σ
      cases i with
      | load r l => exact readAs_bind_wellformed l 0 _ σ (fun _ => ih _ _)
      | store l e =>
          show WellFormed (ParM.bind (writeAs l (AExp.eval ρ e)) _) σ
          rw [WellFormed_bind]
          exact ⟨writeAs_wellformed _ _ σ, ih _ _⟩

/-! ### Link ②: a block runs as a plain interpreter

A `Block` is data, so its pure counterpart is an ordinary state transformer — no monad, no
footprints, registers and heap threaded by hand. `exec_eq_execPure` is the `Block` IR's half of the
pure bridge, exactly parallel to `exec_accesses`. See `docs/block-ir.md`, `docs/pure-bridge.md`. -/

/-- The `Int` a `load` observes — `readAs`'s decode, with its `0` fallback. -/
def loadVal (σ : State) (l : Loc) : Int := (Storable.decode (σ l)).getD (0 : Int)

/-- Run a block as a plain state transformer. Mirrors `exec` instruction for instruction. -/
def execPure : Block → Regs → State → Regs × State
  | [],                 ρ, σ => (ρ, σ)
  | .load r l  :: rest, ρ, σ => execPure rest (ρ.set r (loadVal σ l)) σ
  | .store l e :: rest, ρ, σ => execPure rest ρ (σ.update l (.int (e.eval ρ)))

/-- The lowering is faithful, for every block, register file and state. One induction; no example
repeats it. -/
theorem exec_eq_execPure : ∀ (bl : Block) (ρ : Regs) (σ : State),
    (runSeq (exec bl ρ) σ).2 = (execPure bl ρ σ).2 := by
  intro bl
  induction bl with
  | nil => intro ρ σ; rfl
  | cons i rest ih =>
      intro ρ σ
      cases i with
      | load r l =>
          show (runSeq (ParM.bind (readAs l (0 : Int)) _) σ).2 = _
          rw [runSeq_bind, readAs_runSeq]
          exact ih _ _
      | store l e =>
          show (runSeq (ParM.bind (writeAs l (AExp.eval ρ e)) _) σ).2 = _
          rw [runSeq_bind, writeAs_runSeq]
          exact ih _ _

/-- A block that starts with a memory instruction takes at least one round. -/
theorem exec_time_pos (i : Instr) (rest : Block) (ρ : Regs) (σ : State) :
    0 < time (exec (i :: rest) ρ) σ := by
  cases i with
  | load r l  => exact time_read_pos l _ σ
  | store l e => exact time_write_pos l _ _ σ

/-! ### Independence and the metatheorem, decided on syntax

`footprintOf` is a computation, so `Indep` between two concrete blocks is **decidable** — `by decide`
discharges it with no reasoning about states or interleavings. -/

/-- The whole `WellFormed` obligation for two blocks, decided on the instruction lists alone. Shared
by the equivalence result below and by the cost results in `Lib/Cost.lean`. -/
theorem block_wellformed_parPair (b₁ b₂ : Block) (ρ₁ ρ₂ : Regs) (σ : State)
    (h : Indep (footprintOf b₁) (footprintOf b₂)) :
    WellFormed (ParM.parPair (exec b₁ ρ₁) (exec b₂ ρ₂)) σ :=
  WellFormed_par_intro (by rw [exec_accesses, exec_accesses]; exact h)
    (exec_wellformed b₁ ρ₁ σ) (exec_wellformed b₂ ρ₂ _)

/-- Two blocks whose syntactic footprints are Bernstein-independent run in parallel exactly as they
run in sequence. The hypothesis mentions only the instruction lists. -/
theorem block_par_seq_eq (b₁ b₂ : Block) (ρ₁ ρ₂ : Regs) (σ : State)
    (h : Indep (footprintOf b₁) (footprintOf b₂)) :
    ParM.parPair (exec b₁ ρ₁) (exec b₂ ρ₂)
      ∥≡ ParM.seqPair (exec b₁ ρ₁) (exec b₂ ρ₂) from σ := by
  exact par_seq_eq _ _ σ (block_wellformed_parPair b₁ b₂ ρ₁ ρ₂ σ h)

/-- The `decide`-friendly form: for concrete blocks the whole obligation is one `by decide`. -/
theorem block_par_seq_eq_of_indepB (b₁ b₂ : Block) (ρ₁ ρ₂ : Regs) (σ : State)
    (h : indepB (footprintOf b₁) (footprintOf b₂) = true) :
    ParM.parPair (exec b₁ ρ₁) (exec b₂ ρ₂)
      ∥≡ ParM.seqPair (exec b₁ ρ₁) (exec b₂ ρ₂) from σ :=
  block_par_seq_eq b₁ b₂ ρ₁ ρ₂ σ ((indepB_iff _ _).mp h)

end Paralever
