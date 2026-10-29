# Two programs, one claim: `assert f(…) == g(…)`

A reader who has a sequential sort and a parallel one wants to ask whether **these two programs
compute the same thing**. `par_seq_eq` does not answer that. It answers a question about one
program — whether reading its `parallel` blocks in parallel reaches the outcomes reading them in
order does — and a program can pass that check while computing something entirely different from
its neighbour.

`assert` is the surface form of the second question, and `ParProg.AgreeOn`
(`Lang/Core/Agree.lean`) is what it means.

```prl
def bubble(A, n)  { … }        -- no parallel block at all
def oddeven(A, n) { … }        -- parfor + synchronize

buf A[8] = 5, 3, 8, 1, 7, 2, 6, 4
const n = 8

assert bubble(A, n) == oddeven(A, n) on A
```

## What the statement says

```lean
def AgreeOn (cells : List Loc) (p q : ParProg) (ρ : Regs) (σ : State) : Prop :=
  ∀ r₁ σ₁ r₂ σ₂,
    Reaches (.run (execPar p ρ) σ) (.run (.pure r₁) σ₁) →
    Reaches (.run (execPar q ρ) σ) (.run (.pure r₂) σ₂) →
    ∀ l ∈ cells, σ₁ l = σ₂ l
```

Every outcome either program reaches, under any schedule, holds the same values at `cells`. Three
things are deliberately absent.

| not compared | why |
|---|---|
| the register file | two programs need not name the same registers, and a register is private to its run — `Lib/Block.lean` proves footprints do not depend on one |
| termination | `ParM` is inductive, so every program in this language terminates. There is no divergence to preserve |
| what `print` wrote | output is erased from both interpreters and is not a memory effect (`docs/print.md`) |

The quantifier ranges over the outcomes a program *reaches*, so it says nothing about the
schedules that reach `wrong`. For a program whose every schedule races, the second premise is
unsatisfiable and `AgreeOn` holds vacuously. This is why both sides' well-formedness is a
hypothesis of the theorem and a condition of the report rather than a caveat on it: `claimParts`'
fourth branch refuses to state the claim when either side has a race, and `paralever prove` writes
the two refusals in place of a theorem.

Reflexivity is **not** free: `AgreeOn cells p p ρ σ` holds only once `p`'s own parallel reading is
well formed. `AgreeOn.refl_of_wellFormed` carries that hypothesis, and the witness that it cannot be
dropped is a fork whose conflict is never *simultaneously ready* — thread one writes `A[0]` after
reading an unrelated cell while thread two reads `A[0]` after reading another, so no step ever has
two conflicting heads, `wrong` is avoided on four of six schedules, and those four reach two
different values at `A[1]`. `wrong` catches an overlapping *instant*; `WellFormed` is the stronger
condition, which is Reynolds' grainless point in `docs/semantics.md`.

## How it is proved: the question factors

The two-program question splits into three, and only the first two are about parallelism.

```text
                  do p and q agree on cells, under every schedule?
                                     │
            ┌────────────────────────┼────────────────────────┐
            │                        │                        │
   p's schedules agree       q's schedules agree     p's and q's SEQUENTIAL
   with p's sequential       with q's sequential     readings agree on cells
   reading                   reading
            │                        │                        │
       wfB p = true             wfB q = true            agreeB cells p q
       (par_seq_eq)             (par_seq_eq)            (one run of each)
```

`reaches_iff_runSeq` is the step that makes this cheap. For a program whose parallel reading is
well formed at `σ`, `wellFormed_canonical` says the reachable outcomes are exactly the one the
reference run computes, and `execPar_runSeq_all` says that run may be taken on the *sequential*
reading — which has no fork to schedule. So each side collapses to a function of `σ`, and the
remaining obligation is an equality between two heaps:

```lean
def agreeB (cells : List Loc) (p q : ParProg) (ρ : Regs) (σ : State) : Bool :=
  let σ₁ := (runSeq (execSeq p ρ) σ).2
  let σ₂ := (runSeq (execSeq q ρ) σ).2
  cells.all (fun l => σ₁ l == σ₂ l)
```

`agreeOn_of_wfB` is then three `decide`s: `wfB p`, `wfB q`, and `agreeB`. Nothing about schedules
survives into the third.

**That third question is not ours.** Whether two sequential programs compute the same function is
the general program-equivalence problem; parallelism has left the room. What this project
contributes is that the first two questions are answered once and for all, so a reader comparing a
parallel program to a sequential one is left with exactly the obligation they would have had
comparing two sequential programs.

## What is decided, and what is not

`agreeB` runs both programs on **one heap**: the heap the file's `buf` initializers describe
(`Layout.state`). That is the program's own declared initial state, not a sample of it — the two
sides share one declaration prefix, so there is nothing else for them to start from. For a file
whose buffers are fully initialized this is the whole statement a reader wanted.

The register file is a parameter of `AgreeOn` and the decided instance fixes it at `fun _ => 0`,
which is what every run of a compiled file starts from (`runTaskSeq`, `evalTask`). That is not a
simplification we could drop: a register read before it is written takes the caller's value, so the
answer genuinely depends on `ρ`, and a claim quantified over every `ρ` would be a different and
undecidable statement. A program that assigns before it reads does not care, and nothing here
proves that it does not.

It is not the universally quantified claim. `∀ σ, AgreeOn cells p q ρ σ` is false as stated
(nothing stops a cell neither program initializes from differing on the way in) and undecidable
once restricted to the cells both programs read before writing. Two routes would close it, neither
taken here:

* **A symbolic run.** `Lang/Smt/Vc.lean` already substitutes registers away and emits a symbolic
  footprint per fork. The same walk could emit the two final *values* of each compared cell and ask
  a solver whether they are equal for every input. An `unsat` would be *discharged by* the solver
  and never a Lean proof, exactly as `docs/smt-vc.md` requires of the independence obligation.
* **A relational proof.** Writing the equivalence as a simulation and proving it per program pair.
  This is the honest version and the expensive one; it is also the one a reader can do by hand
  today, since `AgreeOn` is a plain `Prop` and nothing stops a hand-written proof of it at an
  arbitrary `σ`.

## What `assertParSeq` adds

`AgreeOn` compares the named cells of the final heap and nothing else. The register file is left out
because two programs need not name the same registers, and a register is private to its run. The
cost of leaving it out is a blind spot: a side can carry work that lands only in a register and
still agree at every cell. `regonly`-shaped pairs are the witness, and `Examples/Language/tally.prl`
is the one in the repository — two summations over the same fork, one of which peels the last
iteration out of its loop and forgets to increment the tally. Every cell agrees; `%cnt` is 2 on one
side and 1 on the other.

`assertParSeq` is the second keyword, and it states the stronger relation:

```lean
def AgreeParSeq (cells : List Loc) (regs : List Reg) (p q : ParProg) (ρ : Regs) (σ : State) : Prop :=
  ∀ r₁ σ₁ r₂ σ₂,
    Reaches (.run (execPar p ρ) σ) (.run (.pure r₁) σ₁) →
    Reaches (.run (execPar q ρ) σ) (.run (.pure r₂) σ₂) →
    (∀ l ∈ cells, σ₁ l = σ₂ l) ∧ (∀ k ∈ regs, r₁ k = r₂ k)
```

This is both components of the outcome `ParSeqEq` quantifies — the pair `(r, σ')`, since
`execPar : ParProg → Regs → ParM Regs` — where `AgreeOn` takes the heap half alone. Hence the name:
the claim is stated at the metatheorem's own strength rather than at a weakening of it.

The proof costs nothing new. `reaches_iff_runSeq` already pins the whole outcome as one equation
against the reference run, and `agreeOn_of_wellFormed` uses only `congrArg Prod.snd` of it;
`agreeParSeq_of_wellFormed` takes `congrArg Prod.fst` as well. `AgreeParSeq.toAgreeOn` is the first
projection, so the stronger claim never states less than the weaker one on the same cells.

### Why the registers are a list, and why the file does not name them

`Regs` is `Reg → Int`, a function, so equality on all of it is not decidable and `agreeB`'s
counterpart could not be a `Bool`. The registers are therefore a list, exactly as the cells are: a
register file is only as observable as the registers named.

The list is **derived**, not written. `Lang/Compile/Lower.lean`'s `claimRegs` takes both sides'
written registers from `regFootprint`, so a file cannot name the wrong set and `on` stays a list of
buffers. Two consequences are worth stating:

* **A fork's registers are not compared.** `regFootprint (.par ss) = ⟨reads, []⟩` — a `parallel`
  block writes no register the parent can see, because threads get a copy and it is discarded. So
  what `assertParSeq` compares is the registers either side leaves *outside* a fork. This is not a
  gap: a thread-local register is unobservable after the join by the semantics, not by the choice of
  comparison set.
* **The set is an over-approximation**, in the same sense and for the same reason `footprintOf` is
  (`docs/block-ir.md`). `ParProg.block [] = .set 0 (.reg 0)`, a semantic no-op that `regFootprint`
  nevertheless reports as a write to `%0`, so an empty `else` branch puts `%0` in the compared set.
  The error is in the safe direction — comparing more registers is a stronger claim, and the no-op
  leaves `%0` at whatever the program genuinely left there — but a report can name a register the
  file never mentions. Making `regFootprint` precise about the no-op is not free:
  `Lang/Core/AutoParSound.lean` depends on its definitional shape, and the change breaks two of its
  proofs.

### When each keyword is the right one

`assertParSeq` passes only when both sides write the same registers outside their forks. That makes
it the check for a **refactor** — two programs of the same shape, where the register file is part of
the answer — and the wrong check for a sequential program against a parallel one. `equiv.prl`'s
bubble sort and transposition network are the illustration: the network does its comparisons inside
a `parfor`, so it leaves `%x` and `%y` untouched while bubble sort leaves the last comparison in
them. As an `assertParSeq` that pair would be rejected for a difference no reader is asking about,
which is why `assert` is the default and the weaker relation is the one the examples mostly use.

A third reason to want the stronger form is coming: `docs/prl.md` defers `%r := f(…)`, a call with a
return value. Once a `def` can answer in a register, the register file *is* part of what a caller
compares, and `assertParSeq` is the claim that covers it.

## Why the surface form is two calls

A side of an `assert` is a call to a `def`, not an inline block.

* A call already has argument checking (`P112`), a name for a report to print, and a body whose
  statements are checked whether or not it is called (`docs/prl.md` § Functions). An inline block
  would duplicate all of that and leave the two sides unnamed.
* `def` is expanded rather than invoked, so each side **is** its body written out in place. The
  claim compares the file twice over: once with the left call's body there, once with the right's.
  Both compilations see the same declarations, hence the same `Layout` and the same initial heap.
* A reader who wants an inline block writes a `def` around it, which costs one line and gains a
  name.

Only one `assert` is allowed per file (`P114`), and only at the top level. A second claim would be
a third and fourth program, and the compiled file holds two. One nested inside a `for` or a
`parallel` block is refused by `P106`: each side is a whole program, not a statement that happens
at a point in a run.

### Why `on`

`on A, B` names the buffers compared; without it every live buffer is. The restriction is not a
convenience — a parallel version commonly needs scratch space its sequential counterpart does not
(partial sums, a merge buffer), and the two will leave that scratch holding different values while
agreeing on everything a reader cares about. Comparing all of memory would reject such a pair for a
difference that is not observable. `on` costs one reserved word, which is the stated price of a
keyword in this project (`CLAUDE.md` § Surface-syntax tokens are global).

## Why not a relational logic

`docs/papers.md` § 7 records why ReLoC and Simuliris are read and not used, and `assert` does not
change that answer. Their judgment is contextual refinement, proved by simulation under a
step-indexed model, because their programs are fine-grained, nonterminating, and compared in every
context. `AgreeOn` needs none of that: both programs terminate, both are compared from one state
on a fixed set of cells, and the comparison is a first-order statement about two reachability
relations. Its proof is five lines because the hard work is in `wellFormed_canonical`, which was
already done for one program.

## References

* Bernstein, *Analysis of Programs for Parallel Processing*, IEEE Trans. Electronic Computers 1966
  — the independence condition both sides' `wfB` decides.
* Pnueli, Siegel & Singerman, *Translation validation*, TACAS 1998 — the shape of what `assert`
  does: rather than verify a transformation in general, check **this** source against **this**
  target, and emit a certificate per pair. A hand-written parallelization is a translation whose
  translator is a person.
* Necula, *Translation validation for an optimizing compiler*, PLDI 2000 — the same idea scaled, and
  the precedent for the symbolic-run route above.
* Benton, *Simple Relational Correctness Proofs for Static Analyses and Program Transformations*,
  POPL 2004 — relational Hoare logic, the template if the per-heap statement is ever generalized.
* Li, Liang & Feng, *Verified Validation for Affine Scheduling in Polyhedral Compilation*, TASE 2024
  — the packaging this follows: one generic theorem, plus a decidable validator run per instance.
