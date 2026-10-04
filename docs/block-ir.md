# `Block`: a straight-line IR, so footprints are computed

Rationale for `Paralever/Lib/Block.lean`. Code references this file as `docs/block-ir.md`.

## The complaint this answers

Writing a program as a nested `ParM.bind` chain is writing in the monad by hand. Worse, it forces a
*per-program footprint induction*: the previous `Examples/TwoProcesses.lean` spent nineteen lines on
two `footprintWithin_bind` chains, one per process, both entirely mechanical.

No compiler works that way. A compiler lowers to an IR in which every memory operation is an
explicit instruction, and then a basic block's read/write set is a **fold over the instruction
list** — syntax, not analysis. That is what this file does.

## The design

Three types, deliberately minimal:

```lean
inductive AExp  | lit | reg | add | sub | mul        -- pure arithmetic, NO memory operand
inductive Instr | load  : Reg → Loc → Instr          -- r := M[l]
                | store : Loc → AExp → Instr         -- M[l] := e
abbrev   Block  := List Instr                        -- a straight-line basic block
```

`exec : Block → Regs → ParM Unit` generates the binds, once. `footprintOf : Block → Footprint` reads
the answer off the list. The theorem that ties them together is the point of the file:

```lean
theorem exec_accesses : ∀ (b : Block) (ρ : Regs) (σ : State),
    accesses (exec b ρ) σ = footprintOf b
```

Quantified over **every** register file and **every** state, proved once by induction on the block.
Downstream, a concrete program's footprint is `rfl` and an independence check is `decide`.

## Why `AExp` has no memory operand

This is the load-bearing restriction. If `AExp` could contain `M[l]`, then an expression would have
a footprint, `footprintOf` would have to recurse into expressions, and the neat syntactic story would
start leaking. Forcing every heap value through an explicit `load` first means:

> registers are invisible to the footprint; memory is not.

That is precisely the split LLVM's `mem2reg` / SROA passes produce — promote every local whose
address is never taken into an SSA register, and whatever `load`/`store` traffic survives *is* the
footprint. The analogy is exact, and it is the reason the register file `Regs := Reg → Int` needs no
footprint reasoning at all: it is not addressable.

## What this does and does not buy

**Does:** eliminate per-program footprint proofs. `Examples/TwoProcesses.lean` went from 187 to 129
lines, and the nineteen lines of `footprintWithin_bind` plumbing became a single `by decide`. The
rendered `ParM` trees are byte-identical before and after, so the lowering is observably the same
program — the proof got cheaper, not the program weaker.

**Does:** make independence *decidable* for concrete blocks. `indepB (footprintOf b₁) (footprintOf b₂)`
is a computation on two lists, so `by decide` discharges the metatheorem's hypothesis with no
reasoning about states or interleavings.

**Does not** cover control flow. `Block` is *straight-line* only — no branches, no loops. A loop over
a parameterized block (`Nat → Block`) composes with `Pragma/ParallelFor.lean` for the iteration
dimension, but branching inside a block is unrepresentable. Adding it means `footprintOf` must
over-approximate by unioning both arms, which is sound and standard but a real extension.

**Does not** make addresses symbolic. `Instr.load` takes a concrete `Loc`. A block parameterized by
an index (`fun i => [.load 0 (a.loc i), …]`) works and keeps `footprintOf` symbolic in `i`, at which
point disjointness is `omega` rather than `decide` — the same affine bargain `docs/reductions.md`
describes.

**Does not** read Lean's own IR. See below.

## Why not reflect on Lean's `Expr` or LCNF

The tempting next step is to take an existing Lean function over `Array Int`, inspect its elaborated
`Expr` (or its LCNF, Lean's own compiler IR, which is already in A-normal form with explicit `let`s
for intermediates), recognize `Array.get`/`Array.set`, and emit a `Block` automatically. This was
considered and is **not** what this file does, for a reason that is not about effort:

**Lean has no heap.** `Array.set` is *functional* — it returns a new array. A pure Lean function over
arrays therefore has no aliasing, no shared mutable state, and no memory traffic to extract. The heap
is our construction, not Lean's.

So translating a Lean function into a `Block` is not syntax-walking; it requires

1. choosing a **layout** (this array lives at base `B`), which is a human decision, and
2. proving a **data refinement** — that the functional `Array` and the heap region `[B, B+n)` stay in
   correspondence across every `get`/`set`.

Step 2 is the real work, and no amount of `Expr` inspection removes it. A `Block` written directly
has no such gap, because the IR *is* the program rather than a model of one.

This is not a hypothetical difficulty: Lammich's Isabelle-LLVM Parallel (`papers.md` §6.1) does
exactly this refinement — a stepwise descent from a nondeterministic HOL specification down to
parallel LLVM — and needs fine-grained tracking of *pointer inequalities* specifically to justify
parallelizing over disjoint regions. That is an entire refinement calculus, and it is the honest
measure of what a reflective frontend here would cost.

The ordering, then: this file gives a user-facing program representation with no refinement gap and
no footprint proofs. A reflective frontend (`Expr`/LCNF → `Block` plus a generated refinement proof)
remains the ambitious version, and the refinement obligation — not the syntax walking — is the part
to design first.

## References

- Li, Liang, Feng, *Verified Validation for Affine Scheduling in Polyhedral Compilation*, TASE 2024
  (`papers.md` §2.3) — Bernstein's conditions checked against an instruction-level IR, *generically
  over the instruction language*. `exec_accesses` + `block_par_seq_eq` instantiate exactly that
  shape: a fixed instruction set, a syntactic effect function, one soundness theorem.
- Lammich, *Refinement of Parallel Algorithms down to LLVM*, ITP 2022 (`papers.md` §6.1) — the
  state of the art for descending to real LLVM, and the reason the "just read Lean's IR" route is
  scoped out above: it requires pointer-inequality tracking inside a refinement calculus.
- Bocchino, Adve et al., *A Type and Effect System for Deterministic Parallel Java*, OOPSLA 2009 §2 —
  effects declared structurally with the computation unconstrained; `AExp` is the unconstrained part.
- Reynolds, *Toward a Grainless Semantics for Shared-Variable Concurrency*, FSTTCS 2004 — why
  lowering to a coarse load/store granularity does not weaken the theorem.

Full list in [`../papers.md`](../papers.md).
