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
a parameterized block (`Nat → Block`) composes with `Lib/Loop.lean` for the iteration
dimension, but branching inside a block is unrepresentable. Adding it means `footprintOf` must
over-approximate by unioning both arms, which is sound and standard but a real extension.

**Does not** make addresses symbolic. `Instr.load` takes a concrete `Loc`. A block parameterized by
an index (`fun i => [.load 0 (a.loc i), …]`) works and keeps `footprintOf` symbolic in `i`, at which
point disjointness is `omega` rather than `decide` — the same affine bargain `docs/reductions.md`
describes.

**Does not** read Lean's own IR. See below.

## Data-dependent addresses

`load`/`store` take a `Loc` — a Lean `Nat`, fixed before the program is data — which is exactly what
makes `footprintOf` a fold and `wfB` a `decide`. `A[B[i]]` does not fit, so `Lang/Core/Prog.lean` adds two
constructors whose address is an expression:

```lean
| loadAt  : Reg → ArrRef → AExp → ParProg      -- t := A[e]
| storeAt : ArrRef → AExp → AExp → ParProg     -- A[e] := e'
```

The index is separated into a register first, as LLVM separates `getelementptr` from `load`. That
keeps `AExp` the only address arithmetic and keeps registers thread-private, so `A[%0]` in thread
*t* touches one cell determined by *t*'s own registers.

### The semantics needed nothing

`State = Loc → Val` is total and `accesses : ParM τ → State → Footprint` takes a heap and
*simulates*, so `WellFormed` was always able to talk about an address computed at run time. A raw
`ParM` program can scatter today, and `wellFormedB`/`raceSites` decide it exactly:

```text
accesses (indirect 100 1) σ  =  { reads := [100], writes := [3] }    -- B[100] = 3
wellFormedB (parPair …) σ    =  true                                  -- 3 ≠ 7
wellFormedB (parPair …) σ'   =  false                                 -- both index 5
```

`par_seq_eq` is untouched. What was missing was only the DSL's *syntactic* layer.

### Three tiers, and why the middle one is enough

| | holds for | decides the obligation? |
|---|---|---|
| `footprintOf` — syntactic, a **bound** | every heap | sound, not complete |
| `accesses p σ` / `wellFormedB p σ` | one heap | sound **and** complete (`raceSites_nil_iff`) |
| a bound hypothesis (`FootprintWithin`) | every heap | precise, but you prove it |

Static analysis of the *values* is not possible in general, so the syntactic tier reports a bound:
`footprintOf (.storeAt A e _) = ⟨[], A.cells⟩` — somewhere in `A`. Containment is proved once,

```lean
theorem execPar_accesses_sub (s : ParProg) (ρ : Regs) (σ : State) :
    (accesses (execPar s ρ) σ).Sub (footprintOf s)
```

and that is all the obligation needs, because **`Indep` is antitone componentwise**
(`Indep.of_sub`, built from `Indep.mono_left`/`mono_right`). So `wfB s = true → WellFormed` holds
with *no side condition on the addresses*: nothing downstream — `par_seq_eq`, the kernels, the cost
theorems — changed signature.

Two details make this the right approximation rather than a convenient one:

* **Bernstein has no `R∩R` clause**, so widening a *read* set can never manufacture a conflict.
  Shared reads survive the approximation, which is what keeps matmul parallel. A single-region
  bound per thread (`indep_of_footprint_subset`) would have lost them, which is why `Indep.of_sub`
  is the lemma used and not that one.
* **The index wraps** (`ArrRef.addr`), so `addr_mem_cells` holds unconditionally and there is no
  out-of-range case to exclude. An out-of-range index aliases *inside* its array rather than
  escaping it — deliberately unlike a raw `store l`, which addresses anywhere
  (`Examples/Races/Pointers.lean`). Indexed access trades exactness for confinement.

The cost is precision, and it is visible: two threads scattering into the same array are rejected
even when their indices never meet, because the syntax cannot tell them apart.

```text
wfB (par [scatter 0 1, scatter 1 2])        = false      -- both bounds cover all of A
wellFormedB (…execPar ρ) σ₀                 = true       -- indices 1 and 3 never meet
wellFormedB (…execPar ρ) σ₁                 = false      -- both scatter to A[2]
```

`Examples/Language/Scatter.lean` is that program. The route to an all-heaps proof is the third tier: an
injectivity hypothesis on the index map (`∀ i j, i ≠ j → B[i] ≠ B[j]`), which is a real obligation
and not a syntactic check.

`footprintExact` marks the sublanguage where the bound is *exact*, and `execPar_accesses` keeps the
equality there — so the claim this file opens with still holds for the language as it was.

## Control flow

`ifElse c t e` makes the *path* dynamic while every address stays literal — which is why the
predicate above is `footprintExact` and not `staticAddrs`. Its footprint is the union of the two
branches: only one runs, but which is not known statically.

The over-approximation is usually harmless, and that is the difference from a computed address. A
thread whose two branches both write the thread's own cell has a union naming only that cell, so
Bernstein still holds on the bounds and `par_seq_eq` applies with one `decide`
(`Examples/Language/ControlFlow.lean` §1). It bites only when the branches write *different* cells and two
threads' unions overlap (§3) — then the exact per-heap `wellFormedB` still accepts what the
syntactic check cannot.

`whileAtMost n c body` is a **derived form, not a constructor**:

```lean
def whileAtMost : Nat → AExp → ParProg → ParProg
  | 0,     _, _    => block []
  | n + 1, c, body => .ifElse c (.seq body (whileAtMost n c body)) (block [])
```

`ParM` is inductive, so only terminating programs exist and an unbounded `while` is unrepresentable
— the bound is permanent, not a TODO (`CLAUDE.md`). Given one, the recursion runs at elaboration and
the result is an ordinary tree of `ifElse`/`seq`, so `footprintOf`, `wfB` and `par_seq_eq` need no
new cases at all. What separates it from `for` is that the guard is re-read each round, so the loop
exits on the data rather than always running `n` times.

Surface syntax: `if (c) {…} else {…}` and `while (c) in n {…}`. The condition is parsed at
`term:max`, so a compound condition needs parentheses; `in` is reused rather than reserving a new
keyword, for the reason recorded in `CLAUDE.md`.

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
