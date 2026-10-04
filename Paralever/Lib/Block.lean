import Paralever.Lib.TypedRead
import Paralever.Lib.Notation

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

abbrev Reg := Nat

/-- Pure arithmetic over registers. Deliberately has no memory operand. -/
inductive AExp where
  | lit : Int → AExp
  | reg : Reg → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  deriving Repr, DecidableEq

/-- The two memory operations. `load r l` is `r := M[l]`; `store l e` is `M[l] := e`. -/
inductive Instr where
  | load  : Reg → Loc → Instr
  | store : Loc → AExp → Instr
  deriving Repr, DecidableEq

/-- A straight-line basic block. -/
abbrev Block := List Instr

/-- The register file. Registers hold `Int`, are not memory, and never appear in a footprint. -/
abbrev Regs := Reg → Int

def Regs.set (ρ : Regs) (r : Reg) (v : Int) : Regs := fun r' => if r' = r then v else ρ r'

/-- `R n` reads as a register operand inside an `AExp`. -/
abbrev R (n : Reg) : AExp := AExp.reg n

@[simp, grind .]
def AExp.eval (ρ : Regs) : AExp → Int
  | .lit n   => n
  | .reg r   => ρ r
  | .add a b => a.eval ρ + b.eval ρ
  | .sub a b => a.eval ρ - b.eval ρ
  | .mul a b => a.eval ρ * b.eval ρ

instance : Add AExp := ⟨AExp.add⟩
instance : Sub AExp := ⟨AExp.sub⟩
instance : Mul AExp := ⟨AExp.mul⟩
instance : OfNat AExp n := ⟨AExp.lit (Int.ofNat n)⟩

/-! ### Lowering to `ParM`

The binds are generated here, once, rather than written by hand at every use site. -/

/-- Interpret a block as a `ParM` program. -/
def exec : Block → Regs → ParM Unit
  | [],                 _ => .pure ()
  | .load r l  :: rest, ρ => ParM.bind (readAs l (0 : Int)) (fun v => exec rest (ρ.set r v))
  | .store l e :: rest, ρ => ParM.bind (writeAs l (e.eval ρ)) (fun _ => exec rest ρ)

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

/-! ### Independence and the metatheorem, decided on syntax

`footprintOf` is a computation, so `Indep` between two concrete blocks is **decidable** — `by decide`
discharges it with no reasoning about states or interleavings. -/

/-- Two blocks whose syntactic footprints are Bernstein-independent run in parallel exactly as they
run in sequence. The hypothesis mentions only the instruction lists. -/
theorem block_par_seq_eq (b₁ b₂ : Block) (ρ₁ ρ₂ : Regs) (σ : State)
    (h : Indep (footprintOf b₁) (footprintOf b₂)) :
    ParM.parPair (exec b₁ ρ₁) (exec b₂ ρ₂)
      ∥≡ ParM.seqPair (exec b₁ ρ₁) (exec b₂ ρ₂) from σ := by
  refine par_seq_eq _ _ σ (WellFormed_par_intro ?_ (exec_wellformed b₁ ρ₁ σ)
    (exec_wellformed b₂ ρ₂ _))
  rw [exec_accesses, exec_accesses]
  exact h

/-- The `decide`-friendly form: for concrete blocks the whole obligation is one `by decide`. -/
theorem block_par_seq_eq_of_indepB (b₁ b₂ : Block) (ρ₁ ρ₂ : Regs) (σ : State)
    (h : indepB (footprintOf b₁) (footprintOf b₂) = true) :
    ParM.parPair (exec b₁ ρ₁) (exec b₂ ρ₂)
      ∥≡ ParM.seqPair (exec b₁ ρ₁) (exec b₂ ρ₂) from σ :=
  block_par_seq_eq b₁ b₂ ρ₁ ρ₂ σ ((indepB_iff _ _).mp h)

end Paralever
