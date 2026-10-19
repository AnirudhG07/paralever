# Toward a Grainless Semantics for Shared-Variable Concurrency
John C. Reynolds (Carnegie Mellon University and Edinburgh University) · FSTTCS 2004 (LNCS 3328, pp35–48) · `reynolds-fsttcs04-grainless-semantics.pdf`

> The PDF is marked "This is a preprint of a paper that will appear in the Proceedings of the 24th Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2004), Chennai, India, December 16, 2004". A more preliminary version was presented at POPL 2004 (abstract only, ref [1]).

## One-line thesis
Remove the need to pick a default atomic grain by giving operations *duration* (a `start` and a separate `fin` action, between which other processes act) and declaring every overlap of two operations on the same location to be `wrong`, with `wrong` absorbing all other outcomes.

## The setting

**What "grainless" means.** The paper opens with the problem (§1): for `x := x × x ‖ x := x + 1`, the set of outcomes depends entirely on which level is taken to be atomic — whole assignments (2 outcomes), expression-evaluation-plus-store (more), individual loads and stores (more still), or, "say if x is a double-precision floating-point number, the atomic actions might be loads and stores of parts of the number representation, so that the possible outcomes would depend upon details of the machine representation of numbers." Reynolds: "there is no default level of atomicity that is natural for both user and implementor."

The three principles, verbatim from the abstract:

```text
  – Operations have duration and can overlap one another during execution.
  – If two overlapping operations touch the same location, the meaning of the
    program execution is "wrong".
  – If, from a given starting state, execution of a program can give "wrong", then
    no other possibilities need be considered.
```

and the slightly sharper §1 version:

```text
 – All operations, except locking and unlocking, have duration, and can overlap
   one another during execution.
 – If two overlapping operations lookup or set the same location, which may
   be either a variable or a pointer, then the meaning of program execution is
   wrong.
 – If, from a given starting state, execution of a program can give wrong, then
   no other possibilities need be considered.
```

**Language** (§3):

```text
<exp>     ::= <var> | <constant> | <exp> + <exp> | ··· | [<exp>]
<boolexp> ::= <exp> = <exp> | ··· | <boolexp> ∧ <boolexp> | ···
<comm>    ::= <var> := <exp> | skip | <comm> ; <comm>
            | if <boolexp> then <comm> else <comm>
            | while <boolexp> do <comm>
            | [<exp>] := <exp>
            | <comm> ‖ <comm>
            | with <lock> do <comm> | with <lock> when <boolexp> do <comm>
```

No variable or lock declarations, no allocation/deallocation — both are listed as future work in §6.

**States** (§3):

```text
Addresses = Integers
Locations = <var> ⊎ Addresses
States    = ⋃{ δ → Integers | δ ⊆fin Locations }
```

`σ ⌣ σ'` means *compatible* ("σ ∪ σ' is a function, or equivalently, σ and σ' agree on the intersection of their domains"); `σ ⊥ σ'` means `dom σ ⊥ dom σ'`.

**Judgment form.** None — this is a pure semantics paper, no logic, no triples. The meaning of a command is a **set of traces** `[[c]] ⊆ Traces`, and traces are *executed* by a small-step relation on configurations. The observable is `Exec(κ, σ, [[c]])`.

**Terminating programs only?** No. Traces may be infinite, `⊥` is an explicit terminal configuration for divergence, and `while` produces `(filter(b) ; [[c]])ω`.

**The key mechanism: footprints in the actions.** §2: "Notice that the states in the start and finish actions have the same domain, which is the footprint of the operation, i.e., the exact set of locations that are examined or set by the operation." A `start(σ')` *removes* `σ'` from the currently available state — marking those locations "busy" — and the matching `fin(σ'')` *returns* them. Reynolds's own gloss: "In essence, the effect of the start action is to check that x = 3 and then mark x 'busy' by removing [x: 3] from the current state. Then the effect of the finish action is to return x to the current state with a new value."

Expression meanings carry footprints too (§3): "The meaning `[[e]]` of an expression (or boolean expression) e is a set of pairs ⟨σ, n⟩ in which n is the value obtained by evaluating e in any state that is an extension of σ, and in which the domain of σ is the footprint of the evaluation, i.e., the set of locations that are actually examined during the evaluation."

## Main results, stated

**There are no numbered theorems, lemmas or definitions in this paper.** It is a semantics with worked examples and two unnumbered claimed properties. Everything below is reproduced at the level of precision the paper gives.

### Expression semantics (§3)

```text
[[<exp>]] ⊆ States × Integers

[[n]]      = {⟨[ ], n⟩}
[[v]]      = { ⟨[ v: n ], n⟩ | n ∈ Integers }
[[e + e']] = { ⟨σ ∪ σ', n + n'⟩ | ⟨σ,n⟩ ∈ [[e]], ⟨σ',n'⟩ ∈ [[e']], and σ ⌣ σ' }
[[[e]]]    = { ⟨σ ∪ [ n: n' ], n'⟩ | ⟨σ,n⟩ ∈ [[e]], n' ∈ Integers, and σ ⌣ [ n: n' ] }

[[<boolexp>]] ⊆ States × Bool

[[e = e']] = { ⟨σ ∪ σ', n = n'⟩ | ⟨σ,n⟩ ∈ [[e]], ⟨σ',n'⟩ ∈ [[e']], and σ ⌣ σ' }
[[b ∧ b']] = { ⟨σ, false⟩ | ⟨σ, false⟩ ∈ [[b]] }
           ∪ { ⟨σ ∪ σ', t'⟩ | ⟨σ, true⟩ ∈ [[b]], ⟨σ', t'⟩ ∈ [[b']], and σ ⌣ σ' }
```

Example: `[[x − x]] = { ⟨[ x: m ], 0⟩ | m ∈ Integers }`.

Totality (unnumbered, §3): "For all e and σ, there are σ' and n such that σ ⌣ σ' and ⟨σ', n⟩ ∈ [[e]]."

### Actions and traces (§4)

```text
<action> ::= start(<state>) | fin(<state>) | try(<lock>) | acq(<lock>) | rel(<lock>)
```

"a trace is a finite or infinite sequence of actions, or a finite sequence of actions followed by either `wrong` or `⊥`."

```text
τ1 ; τ2 =  τ1      if τ1 is infinite, or ends in wrong or ⊥,
           τ1 τ2   otherwise.

T ; T' = { τ ; τ' | τ ∈ T, τ' ∈ T' }
T⁰ = {ε};  T^{n+1} = T ; T^n;  T* = ⋃_{n=0}^∞ T^n
Tω = { τ0 ; τ1 ; ··· | ∀i ≥ 0. τi ∈ T }

filter(b) = { start(σ) fin(σ) | ⟨σ, true⟩ ∈ [[b]] }
```

The lock actions (§2): "`try(k)` : Try to acquire k, but find it is already locked. `acq(k)` : Succeed in acquiring k, and lock it. `rel(k)` : Unlock k (or signal 'impossible' if it is already unlocked)."

### Command semantics (§4)

```text
[[<comm>]] ⊆ Traces

[[v := e]]  = { start(σ ∪ [ v: n_old ]) fin([ σ | v: n ])
              | ⟨σ,n⟩ ∈ [[e]], σ ⌣ [ v: n_old ] }

[[[e] := e']] = { start(σ ∪ σ' ∪ [ n: n_old ]) fin([ σ ∪ σ' | n: n' ])
              | ⟨σ,n⟩ ∈ [[e]], ⟨σ',n'⟩ ∈ [[e']], σ ⌣ σ', (σ ∪ σ') ⌣ [ n: n_old ] }

[[skip]]    = {start[ ] fin[ ]}
[[c1 ; c2]] = [[c1]] ; [[c2]]
[[if b then c1 else c2]] = (filter(b) ; [[c1]]) ∪ (filter(¬b) ; [[c2]])
[[while b do c]] = ((filter(b) ; [[c]])* ; filter(¬b)) ∪ (filter(b) ; [[c]])ω
```

**Fair merge and concurrent composition** (§4). `τ` is a fair merge of `τ1` and `τ2` iff there are `φ1, φ2` with

```text
dom φ1 = dom τ1 and dom φ2 = dom τ2.
φ1 and φ2 are strictly monotone.
The ranges of φ1 and φ2 are a partition of dom τ.
For all i ∈ dom τ1, τ1(i) = τ(φ1(i)).
For all i ∈ dom τ2, τ2(i) = τ(φ2(i)).
```

```text
τ1 ‖ τ2 = { truncate(τ) | τ is a fair merge of τ1 and τ2 }

truncate(τ)          = τ          (when τ contains neither wrong nor ⊥)
truncate(τ wrong τ') = τ wrong
truncate(τ ⊥ τ')     = τ ⊥

[[c1 ‖ c2]] = ⋃ { τ1 ‖ τ2 | τ1 ∈ [[c1]], τ2 ∈ [[c2]] }
```

**Critical regions** (§4) — "Our semantics of critical regions follows closely that of Brookes [6]":

```text
[[with k do c]] = ({try(k)}* ; {acq(k)} ; [[c]] ; {rel(k)}) ∪ {try(k)}ω

[[with k when b do c]] =
   (wait* ; {try(k)}* ; {acq(k)} ; filter(b) ; [[c]] ; {rel(k)}) ∪ waitω,
where
   wait = ({try(k)}* ; {acq(k)} ; filter(¬b) ; {rel(k)}) ∪ {try(k)}ω.
```

**Totality properties** (§4, unnumbered):

```text
A set T of traces is said to be total whenever, if
       τ start(σ0) τ' ∈ T,
holds for some state σ0, then for every state σ there is a trace
       τ start(σ') τ'' ∈ T,
such that σ ⌣ σ'.

A set T of traces is lock-total whenever, if
       τ acq(k) τ' ∈ T,
then there is a trace
       τ try(k) τ'' ∈ T.

It can be shown that, for all commands c, [[c]] is total and lock-total.
```

(The proof is not given — `NOT FOUND IN PDF`.)

### ⭐ The execution relation (§5) — where `wrong` comes from

```text
Configurations =
     Finite Sets of Locks × States × Traces ∪ {wrong, impossible, ⊥}.
```

Informal meanings, verbatim (§5):

```text
 – "wrong" indicates that a start operation has tried to access a location that
   is not in the domain of the currently available state.
 – "impossible" indicates that a fin operation has tried to extend the current
   state at a location that is already in its domain, or that a rel has tried to
   open a lock that is not closed.
 – ⊥ indicates that the trace will execute forever without performing further
   actions.
```

The transition relation `→ ⊆ Nonterminal Configurations × Configurations`, "the least relation satisfying":

```text
                            ⎧ κ, σ − σ', τ    if σ' ⊆ σ
κ, σ, start(σ') τ  →        ⎨ wrong           if σ ⌣ σ' and σ' ⊄ σ
                            ⎩ no transition   if σ ⌣̸ σ'

κ, σ, fin(σ') τ    →        ⎧ κ, σ ∪ σ', τ    if σ' ⊥ σ
                            ⎩ impossible      otherwise

κ, σ, try(k) τ     →        ⎧ κ, σ, τ         if k ∈ κ
                            ⎩ no transition   if k ∉ κ

κ, σ, acq(k) τ     →        ⎧ κ ∪ {k}, σ, τ   if k ∉ κ
                            ⎩ no transition   if k ∈ κ

κ, σ, rel(k) τ     →        ⎧ κ − {k}, σ, τ   if k ∈ κ
                            ⎩ impossible      if k ∉ κ

κ, σ, wrong        →        wrong
κ, σ, ⊥            →        ⊥.
```

**Determinacy of a single trace** (§5): "Since → is a partial function, if Φ diverges, then there is no terminal Φ' such that Φ →* Φ', while if Φ does not diverge, then there is at most one Φ' such that Φ →* Φ'. In other words, the execution of a trace is always determinate." Nondeterminacy enters only at the level of trace *sets*.

**Irrelevant traces** (§5): "since → is not a total function, there are nonterminal Φ = κ, σ, τ such that Φ does not diverge and there is no terminal Φ' such that Φ →* Φ'. In this case, there is no execution of τ in κ, σ, and we say that τ is **irrelevant** to κ, σ." This is how traces whose `start` state disagrees with the actual state are discarded (`σ ⌣̸ σ'` ⟹ no transition) rather than producing `wrong`.

**"impossible" never arises** (§5, unnumbered, with a proof sketch): because in any trace of any command `acq`/`rel` and `start`/`fin` are balanced "in much the same sense as with parentheses", one can show

```text
For all commands c, traces τ ∈ [[c]], lock sets κ, and states σ:
                        κ, σ, τ ↛* impossible .
```

Reynolds flags the limit of this: "(which might not hold for a lower-level programming language)".

### ⭐ `Exec` and the absorbing `wrong` (§5)

```text
Exec(κ, σ, T) = { ⟨κ',σ'⟩ | ∃τ ∈ T. κ, σ, τ →* κ', σ' }
              ∪ if ∃τ ∈ T. κ, σ, τ →* wrong then Wrong else {}
              ∪ if ∃τ ∈ T. κ, σ, τ diverges then {⊥} else {},

where Wrong is the set of all terminal configurations, including "wrong". Since

                        Wrong ∪ S = Wrong,

for all sets S of terminal configurations, this captures the principle that Wrong
overrides other possible outcomes. It also captures the notion that Wrong can
be implemented arbitrarily.
```

"since command meanings are total and lock-total, `Exec(κ, σ, [[c]])` contains at least one terminal configuration for every command c, state σ, and finite lock set κ" (§5).

### Worked example: when two indirect assignments go wrong (§2)

```text
[[[x] := [x] × [x]]] = { start[ x: n1 | n1: n2 ] fin[ x: n1 | n1: n2 × n2 ] }
[[[y] := [y] + 1]]   = { start[ y: n3 | n3: n4 ] fin[ y: n3 | n3: n4 + 1 ] }
```

An overlapping interleaving in `[[[x] := [x] × [x] ‖ [y] := [y] + 1]]`:

```text
start[ x: n1 | n1: n2 ]  start[ y: n3 | n3: n4 ]
     fin[ y: n3 | n3: n4 + 1 ]  fin[ x: n1 | n1: n2 × n2 ]
```

When `n1 ≠ n3` it executes cleanly:

```text
[ x: n1 | n1: n2 | y: n3 | n3: n4 ]
  ↓  start[ x: n1 | n1: n2 ]
[ y: n3 | n3: n4 ]
  ↓  start[ y: n3 | n3: n4 ]
[ ]
  ↓  fin[ y: n3 | n3: n4 + 1 ]
[ y: n3 | n3: n4 + 1 ]
  ↓  fin[ x: n1 | n1: n2 × n2 ]
[ y: n3 | n3: n4 + 1 | x: n1 | n1: n2 × n2 ]
```

When `n1 = n3` and `n2 = n4` it goes wrong:

```text
[ x: n1 | n1: n2 | y: n1 ]
  ↓  start[ x: n1 | n1: n2 ]
[ y: n1 ]
  ↓  start[ y: n1 | n1: n2 ]
wrong
```

This is the mechanism in one picture: the first `start` removed `n1` from the available state, so the second `start`'s footprint is no longer a subset of it, and the second clause of the `start` rule fires.

## Proof technique
There is essentially none to report: the paper has no numbered results and gives no proofs. Two properties are asserted "it can be shown" / "one can show" — totality and lock-totality of `[[c]]` (§4), and the non-occurrence of `impossible` (§5, with the parenthesis-balancing argument sketched in one paragraph). `NOT FOUND IN PDF`: any induction, any proof of either claim.

## Side condition on parallel composition

**There is none.** `[[c1 ‖ c2]] = ⋃ { τ1 ‖ τ2 | τ1 ∈ [[c1]], τ2 ∈ [[c2]] }` is unconditional fair merge of trace sets (§4). Composition is always defined; interference is not *prevented* at composition time, it is *detected* at execution time, when a `start` finds its footprint missing from the available state.

**Read/read sharing: NOT allowed.** This is the sharpest point in the paper for anyone comparing against Bernstein independence. The principle in §1 is "If two overlapping operations **lookup or set** the same location ... then the meaning of program execution is wrong" — *lookup* included. Mechanically: `start(σ')` requires `σ' ⊆ σ` and then deletes `σ'` from the available state, so two concurrently-overlapping reads of the same variable make the second `start` go wrong exactly as two writes would. Reynolds names this as a limitation and future work (§6):

> "Another important direction would be permit **passivity**, i.e., to relax the assumption that overlapping operations on the same location go wrong, in order to allow the overlapping of read-only operations."

**No fractional or read permissions** anywhere in the paper.

**No ownership transfer.** Locks carry no resource invariants here; `acq`/`rel` only move a lock name in and out of `κ` and do not move state. (Contrast Brookes's and Vafeiadis's local-enabling clauses for `acq`/`rel`, which transfer a heap portion.)

### Why races abort rather than being assigned a behaviour

Two reasons, both stated explicitly.

1. **Implementation freedom.** §1: "when x = y, the semantics of the above program is simply 'wrong'. To provide any further information would make no sense at any level of abstraction above the machine-language implementation, and would unnecessarily restrict the ways in which the program could be implemented." And §5: "It also captures the notion that Wrong can be implemented arbitrarily."
2. **Because assigning a behaviour is precisely what forces a choice of grain.** The four-level enumeration in §1 is the argument: any non-`wrong` answer for `x := x × x ‖ x := x + 1` commits you to a grain, and no grain suits both the programmer and the implementor.

And it is emphatically *not* a runtime check — §1: "It must be emphasized that there is no intention of implementing wrong as a run-time error stop, which would be extremely inefficient and, in view of the nondeterminacy of concurrent computation, of little use. Instead, when the semantics of a program execution is wrong, there are no constraints on how it may be implemented." The obligation is on the programmer: "Thus it is the programmer's obligation to make a convincing argument that his program will not go wrong. We can define what that means, and we should be able to provide a logic in which such arguments can be made rigorous."

## Shared state / resources

Shared mutable state is the subject matter — all variables and addresses are shared, the state is one global `σ`. The only discipline is **locks via critical regions** (`with k do c`, `with k when b do c`), modelled by `try`/`acq`/`rel` acting on a set `κ` of closed locks (§2, §4, §5).

**Locks carry no resource invariants and transfer no state.** There is no analogue of CSL's `RI_r`; the semantics of `acq(k)` is simply `κ, σ, acq(k) τ → κ ∪ {k}, σ, τ if k ∉ κ`. Locking and unlocking are also the one exception to duration: "All operations, **except locking and unlocking**, have duration" (§1).

No CAS, no semaphores as a primitive, no ghost state. Allocation and deallocation are absent and listed as future work (§6: "It would also be useful to introduce operations for storage allocation and deallocation, perhaps similar to the `cons` and `dispose` operations of separation logic").

## What it does NOT claim

- **It proves no theorem of any kind.** There are no numbered results; the two asserted properties (totality/lock-totality; `impossible` never arises) are stated without proof.
- **It proves no equality or equivalence between a parallel program and a sequential one.** The only two-program statement in the paper is an *observation* about observational equivalence (§6): `x := x+1 ; x := x+2` and `x := x+3` are "observationally equivalent" in this semantics though distinguishable in a conventional one, because "They would both go wrong if run concurrently with any command that assigns to or evaluates x; otherwise they would both increase x by three." Note both programs there are sequential; this is not a par-vs-seq result.
- **The semantics is not fully abstract.** §6: "our trace semantics is far from fully abstract; for example, the above commands denote distinct trace sets." Study of coarser equivalences on trace sets is future work, with a stated *conjecture* (not a result): "we conjecture that every command without critical regions has a meaning that is equivalent to a set of traces whose members each have one of the forms: `start(σ) fin(σ')` where `dom σ = dom σ'`; `start(σ) ⊥`; `start(σ) wrong`."
- **No logic, no proof system, no soundness result.** §1: "Although we will not discuss separation logic further in this paper, we believe that the work described herein can provide such a semantics." §6: "Finally, we hope to use our grainless semantics to model concurrent separation logic [5], and to relate the semantics to Brookes's model [6]." Both are future work.
- **No read-only sharing (passivity)** — future work, §6.
- **No variable or lock declarations, no allocation/deallocation** — future work, §6.
- **The title says "Toward"**, and §6 is titled "Future Directions"; the paper presents itself as a proposal.

## Mechanized?
**No.** `NOT FOUND IN PDF` — no proof assistant, no tool, no mechanization is mentioned anywhere. The paper is pen-and-paper throughout, and in fact contains no proofs to mechanize.

## Quotable lines

- "If two overlapping operations lookup or set the same location, which may be either a variable or a pointer, then the meaning of program execution is wrong." — §1
- "If, from a given starting state, execution of a program can give wrong, then no other possibilities need be considered." — §1 / Abstract
- "there is no default level of atomicity that is natural for both user and implementor" — §1
- "To provide any further information would make no sense at any level of abstraction above the machine-language implementation, and would unnecessarily restrict the ways in which the program could be implemented." — §1
- "there is no intention of implementing wrong as a run-time error stop ... when the semantics of a program execution is wrong, there are no constraints on how it may be implemented." — §1
- "Another important direction would be permit passivity, i.e., to relax the assumption that overlapping operations on the same location go wrong, in order to allow the overlapping of read-only operations." — §6
- "the states in the start and finish actions have the same domain, which is the footprint of the operation, i.e., the exact set of locations that are examined or set by the operation." — §2

## Relevance to a parallel-equals-sequential equivalence theorem

- **This is the source for "races ↦ absorbing `wrong`", and the source for *why*.** `Wrong ∪ S = Wrong` (§5) is the absorbing law verbatim, and §1's four-level grain enumeration is the argument that any other treatment of races forces a commitment to an atomic grain. A project that cites grainlessness should cite the `Exec` definition and that enumeration, not just the slogan.
- **Footprints are first-class in the actions here, not derived.** `start(σ)/fin(σ')` carry "the exact set of locations that are examined or set by the operation" (§2), and overlap detection is `σ' ⊆ σ` on the *available* state. That is the closest antecedent to computing read/write footprints per operation and comparing them — but note the mechanism is subtractive (claim-and-return), not a set-intersection test.
- **Reynolds's `wrong` is strictly more aggressive than Bernstein.** Overlapping *reads* of the same location go wrong here, and §6 names fixing that ("passivity") as future work. A theorem whose independence condition is `w₁∩w₂ = w₁∩r₂ = w₂∩r₁ = ∅` with read/read sharing allowed is doing what Reynolds explicitly deferred — it is not the same condition, and claiming otherwise would be wrong. Brookes's `λ1 ♯ λ2` and Vafeiadis's `RaceDetect` are the read-sharing-permitting versions; Reynolds's is not.
- **Nothing here relates two programs.** The only equivalence discussed is observational equivalence between two *sequential* commands (§6), the semantics is conceded to be far from fully abstract, and the trace-set normal form that might narrow the gap is a conjecture. So par≡seq is entirely open territory from this paper's standpoint — but the paper supplies the outcome structure (`Exec` returning a set of terminal configurations with `wrong` absorbing) in which such an equality would be stated.
