# The verdict has two parts

A program with a computed address has two different answers, and for a long time the report printed
one of them and called the other situation `inconclusive`. This note says what the two questions are,
which of them is decided and how, and what the word `Inconclusive` is allowed to mean.

## The two questions

```text
                       ParSeqEq (execPar s ρ) (execSeq s ρ) σ
                                       │
              ┌────────────────────────┴────────────────────────┐
     at σ = layout.state                                 at every σ
     "this heap"                                         "any heap"
     decided exactly by raceSites                        decided by wfB when it accepts;
     (raceSites_nil_iff)                                 searched for a counterexample when it does not
```

**This heap** is the one the file's `buf` initializers describe. `raceSites p σ` is exact at the heap
it is given — `raceSites_nil_iff` says the list is empty exactly when `WellFormed p σ` — so this half
is always `Proved: Yes` or `RACE found`, never open.

**Any heap** is the universally quantified statement. `wfB` decides it when it accepts, because it
reads footprints off the syntax and so speaks for every heap and every register file. When `wfB`
refuses, the statement may still be true, may be false, and is not decided by anything in the
library — so `Lang/Core/Heaps.lean` goes looking for a counterexample.

The two are printed as one line when they agree and as two when they differ:

| `wfB` | this heap | any heap | printed |
|---|---|---|---|
| accepts | — | `Proved: Yes` | one line, `every heap` |
| refuses | `RACE found` | `RACE found` | one line, `every heap` — the declared heap *is* a heap |
| refuses | `Proved: Yes` | `RACE found` | two lines |
| refuses | `Proved: Yes` | `Inconclusive` | two lines |

## The search

The program reads values out of memory and turns them into addresses. A counterexample is therefore a
heap that differs from the declared one in those cells, and the search enumerates such heaps.

**Which cells.** The cells a `load` names (`ParProg.probeCells`). A `loadAt`'s own cell is computed,
so probing it would mean guessing a second index; those are left out rather than approximated.

**Which values.** `ArrRef.addr a i = a.base + i.toNat % max a.len 1` aliases exactly two ways, and
the probe set holds a witness to each: the `Int.toNat` clamp sends every negative index to cell `0`,
so `-1` is in the set; the `% max len 1` wrap sends `n` back to `0` and `n + 1` to `1`, so `n - 1`,
`n` and `n + 1` of each declared buffer are in it, along with `0` and `1`, which are in range for
every non-empty buffer.

**Which heaps, in what order.** The declared heap first — so the general search can never miss a race
the per-heap check finds — then every one-cell change, then every *uniform* assignment, then every
two-cell change, capped at `probeBudget`. The uniform pass is not redundant: a stride whose threads
alias only when both indices clamp needs both cells changed at once, and no single-cell change
reaches it.

Finding something is decisive. `raceSites` is exact at the heap it is handed, so a hit refutes
`∀ σ, ParSeqEq …` outright — it is a counterexample to the quantified statement, not a heuristic
warning. Whether that heap is one the program's own inputs can produce is a separate question the
report does not claim to answer.

## What `Inconclusive` means

It means: `wfB` refused, and a search of *n* heaps found no race. Both halves of that are in the
line, because neither alone is a reason:

```console
verdict   this heap   Proved: Yes — no two threads touch one cell here
          any heap    Inconclusive — wfB refuses over {A[0], A[1]}: a branch contributes both arms although only one runs
          no race found in 11 heap(s) probed over {c[0]}
```

The first clause is the proof checker's reason, in the program's own names: which cells `wfB` refused
over (`refusedAt`) and which constructor widened the footprint (`ParProg.widenedBy` — a computed
address, a branch, or both). The second is the search's: how far it looked, and at which cells. A
bounded search that finds nothing is `unknown`, never `proved`; the complete answer for every heap is
`wfB`, and this runs only when `wfB` has already said no.

`Examples/Language/branch.prl` is the witness. Two threads write mirror-image cells of one `if`, so
`par = seq` at every heap and the checker proves it at none of them — the one shape where the gap is
a branch rather than an index.

## What this settled about stripe

`Examples/Language/stripe.prl` writes `A[2 * %p]` against `A[2 * %q + 1]`, which are different cells
for every in-range pair of indices. `paralever vc` handed that to a solver, z3 answered `sat`, and the
report treated the `sat` as a solver artefact to be worked around with `--assume nonneg`.

The solver was right. At `k[1] = -1` the odd address `2 * (-1) + 1` clamps through `Int.toNat` onto
`A[0]`, where `2 * 0` already is, and both threads write it. The search finds that heap by changing
one cell:

```console
verdict   this heap   Proved: Yes — no two threads touch one cell here
          any heap    RACE found — with k[1] = -1: A[0] written by both threads
```

So the unrestricted `par_seq_eq` for stripe is not merely unproved — it is **false**, which is why no
tactic discharges it. What is true is the in-range statement, and
`Examples/Language/Stripe.lean`'s `par_seq_eq_of_inRange` proves it in Lean with no solver, from
`ArrRef.addr_ne`. See `docs/smt-vc.md` § *Lean closes the same arithmetic*.

The same search finds a counterexample for `scatter.prl`: `idx = 2, 0, 1` is a permutation, and
`idx[0] = -1` clamps thread 0 onto `dst[0]`, which thread 1 already owns.

## What would make the strong statement decidable

The clamp is why a stride abstraction for `footprintOf` would be unsound: if `A[2*e]` mapped to the
even cells and `A[2*e+1]` to the odd ones, a negative index would break both maps, since every
negative index lands on `A[0]`. Two changes would close it, and neither is made here:

- a way to state an index's range in the surface language, so `0 ≤ %p < 4` is syntax rather than a
  fact about the heap, after which a residue abstraction is sound and `wfB` accepts stripe by
  `decide`;
- or an address that traps out of range instead of wrapping, after which the bound is free.

Both change `Core/`, so both wait for a decision recorded here.

## Not in scope

- Deciding the quantified statement. `wfB` is the only complete answer and it is sound, not complete;
  the search is complete for nothing and says so.
- Reachability. A counterexample heap refutes `∀ σ`; whether a program's inputs can produce it is a
  question about the program's callers, which a `.prl` file does not have.
- Replaying a counterexample heap as an interleaving. `paralever race` does that for the declared
  heap; doing it for a probed heap needs the heap to be nameable on the command line.
