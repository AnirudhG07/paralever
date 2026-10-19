# Reading list for Paralever

Everything worth knowing before building "independent parallel tasks ⇒ same output as sequential",
mechanized in Lean 4.

**How to use this.** Each entry says *what to take* — the specific idea, lemma, or design decision
we want from it. You do not need to read most of these end to end. Entries marked **★** are the ones
whose actual proof technique we are reproducing; read those properly. The rest are for knowing the
landscape, writing related work, and not reinventing things.

**The gap we are filling.** The clean statement *"independent footprints ⇒ `C₁ ∥ C₂` ≡ `C₁; C₂`"*,
mechanized generically and then instantiated, does not exist in any proof assistant. Brookes has the
enabling lemma but never states the corollary. Vafeiadis has the mechanization but not the corollary.
DPJ has the corollary but only on paper, for a Java-like calculus. PolCert has it only for affine
loop nests. Blom et al. have exactly our architecture but no proof assistant. Nothing exists in Lean 4.

---

## Suggested reading order

**Week 1 — the theory that is literally our theorem.**
O'Hearn (§1.1) → Brookes (§1.2) → Apt & Olderog (§1.3) → Vafeiadis (§1.4, with the Coq).
Stop here and write down the theorem statement you intend to prove.

**Week 2 — how other people packaged the same idea.**
DPJ (§2.1) → Blom et al. (§2.2) → PolCert (§2.3). These are three different answers to "what does the
user discharge per program". Decide which shape our `Indep` obligation should take.

**Week 3 — the escape hatches, in case disjointness is too strong.**
Lipton (§3.1) → CIVL reduction (§3.2) → LVars (§3.3) → Reynolds grainless (§4.2).

**Week 4 — engineering.**
iris-lean source (§7) → the algebraic branch (§5) skimmed → cost semantics (§6) skimmed.

---

## 1. Core theory — this *is* the theorem

### 1.1 O'Hearn, *Resources, Concurrency and Local Reasoning* — CONCUR'04 / TCS 375(1-3) 2007
<http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/concurrency.pdf>

The origin of CSL. Introduces the **Ownership Hypothesis**: a program component only accesses cells
it currently owns. The disjoint concurrency rule

```
{P₁} C₁ {Q₁}    {P₂} C₂ {Q₂}
─────────────────────────────────
  {P₁ ∗ P₂} C₁ ∥ C₂ {Q₁ ∗ Q₂}
```

**What to take:** `∗` *is* the independence predicate — that is the whole conceptual move. Also note
what we can drop: with no critical regions and no resource invariants, the fragment we need is just
this rule plus frame. That is why we do not need CMRAs, step-indexing, or ownership transfer.

### 1.2 ★ Brookes, *A Semantics for Concurrent Separation Logic* — CONCUR'04 / TCS 375(1-3) 2007
<https://www.cs.cmu.edu/~brookes/papers/seplogicrevisedfinal.pdf> (revised final — use this one)

**The key paper.** Trace semantics with a local enabling relation, races modelled as a distinguished
catastrophic action. Read **§5–§7**.

The load-bearing result is the **Parallel Decomposition Lemma**: if a trace of `C₁ ∥ C₂` runs from a
state split as `s₁ ∗ s₂` and the components' footprints stay separate, then that trace is an
*interleaving* of a trace of `C₁` from `s₁` and a trace of `C₂` from `s₂`, and the final states
recombine as `s₁' ∗ s₂'`.

**What to take:** this is our generic theorem in disguise. If every trace factors that way, then
*every* interleaving — including the fully sequential one — yields the same result. Brookes states
race-freedom and soundness as headline theorems; the determinacy/sequentialization corollary follows
from the decomposition lemma but **he never writes it down**. Writing it down, generically and
mechanized, is our contribution.

Companion retrospective, much shorter and worth reading first for orientation:
Brookes & O'Hearn, *Revisiting Concurrent Separation Logic* — <https://arxiv.org/pdf/1712.01631>

### 1.3 ★ Apt & Olderog, *Verification of Sequential and Concurrent Programs* — ch. on disjoint parallelism
<https://link.springer.com/chapter/10.1007/978-1-4757-4376-0_5>

Textbook, pre-separation-logic. States the **disjoint parallelism theorem**: for disjoint parallel
programs, `C₁ ∥ C₂` and `C₁; C₂` are semantically *equal*.

**What to take:** the cleanest, most directly formalizable phrasing of our target statement. Steal
the theorem statement almost verbatim. Also the historical framing — Hoare 1972 and Owicki–Gries 1976
(<https://dl.acm.org/doi/10.1145/360051.360224>) are where the disjointness side condition on the `∥`
rule comes from, i.e. Bernstein's conditions in Hoare-logic clothing. Owicki–Gries' general
interference-freedom check is the quadratic thing we are *avoiding*.

### 1.4 ★ Vafeiadis, *Concurrent Separation Logic and Operational Semantics* — MFPS 2011
Paper: <https://www.sciencedirect.com/science/article/pii/S1571066111001204/pdf>
Coq: <https://github.com/vafeiadis/cslsound> · <https://people.mpi-sws.org/~viktor/cslsound/>

**The single best artifact to imitate.** Replaces Brookes' trace model with a plain small-step
operational semantics and a safety-by-induction-on-fuel soundness proof. No traces, no domain theory,
~1500 lines of Coq. The no-ownership-transfer restriction is what is usually called **DCSL**
(Disjoint CSL) — exactly our scope.

**What to take:** the *method*. Read the Coq, not just the paper. Then add the corollary he does not
state. This is the most concrete template for `Logic/Soundness.lean`.

---

## 2. Same idea, packaged three different ways

### 2.1 ★ Bocchino, Adve et al., *A Type and Effect System for Deterministic Parallel Java* — OOPSLA 2009
<https://dl.acm.org/doi/10.1145/1640089.1640097>
Long version with the full Core DPJ metatheory (get this if you are actually formalizing):
<https://www.researchgate.net/publication/228734972>

Our goal, as a type system. The soundness theorem: *in a well-typed program, if two expressions have
non-interfering effects (region-based read/write sets that do not conflict), then either evaluation
order produces the same values, the same effects, and the same final heap.* Determinism of the whole
program then follows by structural induction over `cobegin`.

**What to take:** the *shape*. Prove the generic theorem once about the effect calculus; the
per-program work is the region annotations. This is the closest existing statement to what we want,
and the fact that it is only on paper for a Java-like calculus is a large part of our gap claim.
If our DSL carries footprint annotations, this is the design to copy.

### 2.2 Blom, Darabi, Huisman, Safari, *Correct Program Parallelisations* — STTT 23(5) 2021
<https://ris.utwente.nl/ws/files/251829479/Blom2021correct.pdf>
Earlier: *A Verification Technique for Deterministic Parallel Programs*, NFM 2017 —
<https://link.springer.com/chapter/10.1007/978-3-319-57288-8_17>
Also: *Verification of Loop Parallelisations*, FASE 2015 —
<https://link.springer.com/chapter/10.1007/978-3-662-46675-9_14>

Literally our theorem statement: a core language of parallel, vectorised and sequential basic blocks
composed by sequential, parallel and fusion composition, with the main result that **functional
correctness of the sequential program implies correctness of the parallelised program**, given
per-block contracts and iteration contracts encoding data dependences. Applied to OpenMP directives.

**What to take:** their composition algebra (sequential / parallel / fusion) is a good sanity check on
ParaLang's constructors. Crucially: this is tool-supported (VerCors/Viper), **not mechanized in a
proof assistant** — which is precisely the gap. Also the direct precedent for the OpenMP-pragma
future work.

### 2.3 ★ Li, Liang, Feng, *Verified Validation for Affine Scheduling in Polyhedral Compilation* — TASE 2024
<https://link.springer.com/chapter/10.1007/978-3-031-64626-3_17>
Coq: <https://github.com/verif-scop/PolCert>

**Bernstein's conditions, fully mechanized in Coq.** A *generic* validation framework parameterized
over the instruction language: prove once that if a candidate affine schedule respects Bernstein's
conditions (`I₁∩O₂ = I₂∩O₁ = O₁∩O₂ = ∅`, lifted to instances) then the rescheduled program is
semantically equivalent to the original; then per program a validator checks the condition.

**What to take:** the packaging — *generic theorem + per-instance decidable validator* — is exactly
our `bernsteinOK : Loop → Bool` design for the loop-parallelization example. Closest existing artifact
to our stated architecture.

Complement (the code-generation half, if we ever go further):
Courant & Leroy, *Verified Code Generation for the Polyhedral Model*, POPL 2021 —
<https://xavierleroy.org/publi/polyhedral-codegen.pdf>

---

## 3. Escape hatches if footprint disjointness proves too strong

### 3.1 Lipton, *Reduction: A Method of Proving Properties of Parallel Programs* — CACM 18(12) 1975
<https://dl.acm.org/doi/10.1145/361227.361234>

The origin of movers. Right-movers / left-movers; a block of shape `R*·A·L*` can be treated as atomic.
The algebraic core of every later sequentialization result. Short.

Modern separation-logic-flavoured descendant: *Mover Logic* — <https://arxiv.org/pdf/2407.08070>

### 3.2 *Reduction for Structured Concurrent Programs* — CIVL team, ESOP 2026
<https://arxiv.org/abs/2601.13341> · <https://civl-verifier.github.io/papers/esop2026.pdf>

Directly on point: a reduction strategy that **soundly replaces parallel composition with sequential
composition**, plus a generalization of Lipton's movers to atomic sections containing recursive calls.
Claims the first formal soundness proof of reduction theory at this generality, and identifies the
most general form of commutativity sufficient for soundness.

**What to take:** the fallback plan. If disjointness excludes programs we care about, the replacement
independence predicate is *commutativity* rather than disjointness. Read before committing to `Indep`.

### 3.3 Kuper & Newton, *LVars: Lattice-based Data Structures for Deterministic Parallelism* — FHPC 2013
<https://users.soe.ucsc.edu/~lkuper/papers/lvars-fhpc13.pdf>
Dissertation (fuller treatment): <https://users.soe.ucsc.edu/~lkuper/papers/lindsey-kuper-dissertation.pdf>
Sequel — *Freeze After Writing*, POPL 2014 (quasi-determinism).

Determinism *without* disjointness: shared state is allowed, but writes must be inflationary in a
lattice and reads are "threshold" reads. Main theorem: LVar programs are deterministic, proved by a
diamond/confluence argument on the small-step relation.

**What to take:** the **proof technique** — determinism as strong local confluence + Newman's lemma.
This is the most Lean/Mathlib-friendly route in the entire list and is our fallback for
`Core/Determinism.lean` if the footprint route gets painful.

---

## 4. Semantics design decisions

### 4.1 Hayman & Winskel, *Independence and Concurrent Separation Logic* — LICS 2006 / LMCS 4(1) 2008
<https://arxiv.org/abs/0802.0820>

Petri-net (true-concurrency) semantics for the CSL language. Proves soundness, then exploits the net's
independence relation to **characterize exactly the independence of parallel processes that CSL
enforces**, and shows this supports a refinement operation changing the granularity of atomic actions.

**What to take:** the alternative to interleaving semantics. If the interleaving proof turns into a
combinatorial swamp, a partial-order / event-structure formalization is the known way out. Theorem 5.4
(processes provable in the logic are race-free from suitable initial states) is worth reading either way.

### 4.2 ★ Reynolds, *Toward a Grainless Semantics for Shared-Variable Concurrency* — FSTTCS 2004
<https://www.cs.cmu.edu/~jcr/grainless.pdf>

Semantics where overlapping accesses to the same location yield `wrong`, and `wrong` is absorbing.
The payoff: for CSL-provable programs, **the choice of atomic grain is irrelevant**.

**What to take:** direct justification for ParaLang's race-to-absorbing-`wrong` design, and the reason
we can pick a coarse small-step granularity without weakening the theorem. Short and decisive.

Follow-up: Brookes, *Granularity and Concurrent Separation Logic*, CONCUR 2011 —
<https://link.springer.com/chapter/10.1007/978-3-642-23217-6_15>

### 4.3 Hoare, Möller, Struth, Wehrman, *Concurrent Kleene Algebra* — CONCUR 2009 / JLAP 2011
<https://link.springer.com/chapter/10.1007/978-3-642-04081-8_27>

Algebraic framing: two composition operators `·` (sequential) and `∥` (parallel) linked by the
**exchange law** `(e∥f)·(g∥h) ≤ (e·g)∥(f·h)` — precisely "sequentialization is a refinement direction".

**What to take:** a possible *presentation* of our result. Equational and first-order, so it would be a
typeclass with `parallel ≤ sequential` derived from the exchange law. Attractive for the paper's
framing even if we do not build on it. Isabelle AFP has formalizations of Kleene/CKA algebras worth
mining.

---

## 5. The "is CSL even needed?" branch — pure/algebraic parallelism

Worth knowing well: this is the cheapest path to a real theorem, and a reviewer *will* ask why we did
not just do this. The answer is that it only covers pure code with no mutable state, but we should be
able to say that crisply.

### 5.1 Gibbons, *The Third Homomorphism Theorem* — JFP 6(4) 1996
<https://www.cs.ox.ac.uk/publications/publication2365-abstract.html>

If `h` is computable both as a `foldr` and as a `foldl`, then `h` is a list homomorphism:
`h (x ++ y) = h x ⊙ h y` for some associative `⊙`.

**What to take:** the "one generic theorem, discharge per program" pattern in its purest form — the
theorem is `∀ ⊙ associative, parallel_reduce ⊙ = foldl ⊙`, and the obligation is associativity.
**Get this distinction right early:** associativity alone suffices for order-*preserving* chunked
reduction; commutativity is needed only if the schedule may permute elements.

### 5.2 Loulergue et al., *SyDPaCC* — Coq framework for correct-by-construction parallel programs
*Calculating Parallel Programs in Coq Using List Homomorphisms*, IJPP 2017 —
<https://link.springer.com/article/10.1007/s10766-016-0415-8>
*SyDPaCC: A Framework for the Development of Verified Scalable Parallel Functional Programs*, 2024 —
<https://link.springer.com/chapter/10.1007/978-3-031-75380-0_16>
All papers: <https://frederic.loulergue.eu/research/papers.html>

**The closest existing artifact to "prove `parallel = sequential` once, then instantiate."** Write a
naive sequential spec; SyDPaCC applies *verified* transformations (BMF, third homomorphism theorem,
skeletons) to yield a distributed parallel program; extraction produces runnable BSML/OCaml+MPI.

**What to take:** read this before writing Lean. It is the existence proof that the architecture works
end to end including code extraction, and it is the main related-work comparison for our library half.

### 5.3 Bird, *An Introduction to the Theory of Lists* (BMF) and Gorlatch, *Extracting and Implementing List Homomorphisms in Parallel Program Development* — SCP 1998
<https://www.sciencedirect.com/science/article/pii/S0167642397000142>

Calculational background: homomorphism lemma (`h = reduce ⊙ ∘ map f`), scan/prefix-sum derivations, and
the **almost-homomorphism / tupling trick** that makes maximum-segment-sum parallel.

**What to take:** where the per-program obligations come from in the pure setting. Useful for the
reduce example's generality.

### 5.4 Sheehan, Chen, Edelman, *Parallel Prefix Polymorphism Permits Parallelization, Presentation & Proof* — 2014
<https://arxiv.org/pdf/1410.6449>

Short and readable. A generic prefix-sum written polymorphically over any associative operator is
simultaneously the implementation and its own proof obligation.

**What to take:** good framing language for the "one theorem, many instances" pitch.

---

## 6. Verified parallel algorithms in proof assistants

### 6.1 ★ Lammich, *Refinement of Parallel Algorithms down to LLVM* — ITP 2022
<https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2022.24>
<https://www21.in.tum.de/~lammich/isabelle_llvm_par/>

Isabelle-LLVM Parallel: stepwise refinement from a nondeterministic HOL specification down to parallel
LLVM, verifying a **parallel quicksort** competitive with C++. Adds fine-grained tracking of pointer
inequalities, needed to justify parallelizing computations on disjoint memory regions.

**What to take:** the state of the art for our sort example, and a machine-checked version of the
disjointness discharge — but embedded in a refinement calculus rather than a program logic. This is
the paper to compare against for Example 2. Background: *Refinement to Imperative HOL*, JAR 2019.

### 6.2 *Verified Scalable Parallel Computing with Why3* — 2023
<https://arxiv.org/pdf/2307.16592>

WhyML formalization of algorithmic skeletons plus a verified maximum-prefix-sum.

**What to take:** a comparison point on how much automation buys you versus the interactive route.

---

## 7. Relational logics — why we are *not* using them, stated precisely

A reviewer will ask "why not just do this in ReLoC?". Know the answer.

### 7.1 Frumin, Krebbers, Birkedal, *ReLoC* / *ReLoC Reloaded* — LICS 2018 / LMCS 17(3) 2021
<https://iris-project.org/reloc/> · <https://arxiv.org/abs/2006.13635>

Relational separation logic on Iris with a first-class judgment `Δ ⊨ e₁ ≾ e₂ : τ`, sound w.r.t.
**contextual refinement**. Two flavours of points-to: `ℓ ↦ᵢ v` (implementation) and `ℓ ↦ₛ v`
(specification). Type-directed structural rules plus symbolic-execution rules so you never unfold the model.

**Why not:** it targets *fine-grained concurrency* (proving a lock-free stack refines a coarse one), not
disjoint parallelism — so its case studies are the wrong shape. And decisively: **it is Coq-only, with
no Lean port and none planned.** We would have to build it first.

**What to take:** if we ever want the theorem phrased as refinement rather than equality, this is the
template for the judgment and its soundness theorem.

### 7.2 Gäher, Sammler, Spies, Jung, Dang, Krebbers, Kang, Dreyer, *Simuliris* — POPL 2022
<https://iris-project.org/pdfs/2022-popl-simuliris.pdf>

Separation-logic framework for verifying **concurrent program optimizations**, establishing
termination-preserving refinement under a fair scheduler, *assuming data-race-freedom of the source*.
Non-step-indexed Iris variant, language-agnostic.

**What to take:** "DRF source ⇒ transformation is sound" is a generalization of our theorem, and it
shows how ownership lets you do thread-local proofs of a whole-program refinement. Also the precedent
that a **non-step-indexed** Iris variant is a sensible thing to build — relevant to our BI instance.

Predecessor, if we want two-sided equivalence (parallel terminates iff sequential does):
Tassarotti, Jung, Harper, *A Higher-Order Logic for Concurrent Termination-Preserving Refinement*,
ESOP 2017 — <https://arxiv.org/pdf/1701.05888>

---

## 8. Cost semantics — for the "same output, different work/span" story

### 8.1 Niu, Sterling, Grodin, Harper, *A Cost-Aware Logical Framework (calf)* — POPL 2022
<https://arxiv.org/pdf/2107.04663> · Agda: <https://www.cs.cmu.edu/~runmingl/calf.html>
*decalf* (directed, effectful), OOPSLA 2024 — <https://dl.acm.org/doi/pdf/10.1145/3632852>

Dependent type theory with cost as an effect and an internal **phase distinction**: *input/output
behavior cannot depend on cost*. Case studies derive tight bounds for sequential **and** parallel
merge sort in one development.

**What to take:** the principled framing of exactly our thesis — the parallel version has the same
*extension* (output) but different *intension* (work/span). The phase distinction gives
`parallel = sequential` extensionally for free while still letting you state span bounds. If we ever
add cost, this is the design. Good citation for the paper's framing regardless.

### 8.2 Blelloch & Greiner, *A Provable Time and Space Efficient Implementation of NESL* — ICFP 1996; Blelloch, Gibbons, Matias — JACM 1999
<https://www.cs.cmu.edu/~guyb/research.html>

Profiling semantics returning a work/span DAG, with theorems mapping cost measures to running time on
machine models.

**What to take:** the NESL design point — the *language* is deterministic by construction (flat data
parallelism over pure sequences), so equivalence to the sequential semantics is definitional and all
the theory goes into cost. This is the strongest argument for keeping ParaLang's parallel fragment
structured, and worth engaging with honestly in related work.

---

## 9. Context — read only if writing the related-work section

- **CompCertTSO** (Ševčík, Vafeiadis, Zappa Nardelli, Jagannathan, Sewell), JACM 60(3) 2013 —
  <https://dl.acm.org/doi/10.1145/2487241.2487248>; *Verified Compilation for Shared-Memory C*, ESOP
  2014. Verified compilation of concurrent C under x86-TSO. Relevant only if our theorem must survive
  compilation to real hardware — it tells you the DRF-SC assumption you would have to carry.
- **VerCors** (iFM 2017) and **VeyMont** (*Parallelising Verified Programs Instead of Verifying
  Parallel Programs*, FASE 2023) — <https://link.springer.com/chapter/10.1007/978-3-031-27481-7_19>.
  VeyMont's slogan is our slogan; the technique (choreographic projection) is different. Worth reading
  for framing.
- **SeLoC**, *Compositional Non-Interference for Fine-Grained Concurrent Programs* —
  <https://arxiv.org/pdf/1910.00905>. Adjacent use of separation logic for a non-interference property.

---

## 10. Source to read as code, not as papers

- **`vafeiadis/cslsound`** — <https://github.com/vafeiadis/cslsound>. ~1500 lines of Coq. The closest
  thing to a blueprint for `Logic/Soundness.lean`. **Read this properly.**
- **`verif-scop/PolCert`** — <https://github.com/verif-scop/PolCert>. Generic-framework + validator
  packaging for Bernstein conditions.
- **iris-lean** — <https://github.com/leanprover-community/iris-lean>. Note the README is badly stale;
  `master` has far more than it advertises. The parts we care about:
  - `Iris/Iris/BI/*` and `Iris/Iris/ProofMode/*` — the BI interface and the proof mode we instantiate.
    Tactic list: `Iris/tactics.md`.
  - `Iris/Iris/Algebra/{Heap, HeapView, GenMap, Frac, DFrac}.lean` — heap model, fractional/read
    permissions.
  - `Iris/Iris/HeapLang/Lib/{Par, Spawn, Quicksort}.lean` and `Iris/Tests/HeapLang/Par.lean` — read as
    *templates* for proof shape. `Quicksort.lean`'s `sortAndCheckAdequate` is a closed end-to-end proof.
  - `Iris/Iris/ProgramLogic/Adequacy.lean` — in particular `AdequateNoFork`, a Lean-only structure with
    no Coq Iris counterpart, stating "this program never forks". Prior art for phrasing "this execution
    is really sequential".
  - Porting status tracker: <https://leanprover-community.github.io/iris-lean/>
  - Zulip: <https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean>
- **Coq Iris `par` / `spawn`** — <https://plv.mpi-sws.org/coqdoc/iris/iris.heap_lang.lib.par.html>.
  The `par_spec` / `wp_par` statements, to compare against what we prove.
- **Ideas to steal without importing:**
  - `verse-lab/velvet` (`Velvet/Syntax.lean`) — how to build a Dafny-style DSL in Lean:
    `declare_syntax_cat` for `requires`/`ensures`/`invariant`, `macro_rules` for binders,
    `elab_rules : command` emitting a definition plus its VC theorem.
  - `verse-lab/veil` — the `#gen_state` / `#gen_spec` / `#check_invariants` command architecture,
    and `widget/src/traceDisplay.tsx` for how a trace is shown: cards per state, an injected
    stylesheet rather than inline styles, `--vscode-*` theme variables, and changed fields picked
    out. Followed by `Search/ExplainHtml.lean` (`docs/race-search.md`).
  - `verse-lab/splean` — the other Lean 4 separation logic; compare design choices.
  - *Yolo: Lazy Proof Automation for Separation Logic*, ITP 2026 —
    <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2026.6>. Read before designing any
    separation-logic automation.

---

## 11. Two facts about Lean worth internalizing before writing any code

Both are load-bearing for why the project is shaped the way it is.

**1. Lean's `Task` is a one-field structure with a real body** (`Init/Core.lean:626,687`):

```lean
structure Task (α : Type u) : Type u where pure :: get : α
@[noinline, extern "lean_task_spawn"]
protected def Task.spawn (fn : Unit → α) (prio := .default) : Task α := ⟨fn ()⟩
```

So `(Task.spawn f).get = f ()` holds **by `rfl`**. All parallelism is an `@[extern]` runtime override
invisible to the kernel. Verifying pure `Task` code is therefore *vacuous* as a statement about
interleaving — there is no interleaving in the model. This is why the theorem must live on ParaLang's
semantics, and simultaneously why compiling *to* `Task` is sound and nearly free.

**2. Lean's effectful task API has no semantics at all.** `BaseIO.asTask`, `mapTask`, `bindTask`,
`mapTasks`, `IO.wait` (`Init/System/IO.lean:245,258,272,300,567`) are all `opaque` + `@[extern]` with
no equations. And `IO`/`ST` are no longer `EStateM`-based, so `Std.Do` has no `WP` instance for them.
Proving anything there means *axiomatizing* the runtime, not defining it.

Together: "just verify real Lean parallel code" is either trivially true or unfoundedly axiomatic.
Hence ParaLang plus a verified compiler.

The fork-join combinator we compile to is `Task.mapList` (`Init/Task.lean`, added 2025) — there is no
`Task.zip`. It has a real body, and neither core nor Batteries nor Mathlib has a single lemma about it.
`(Task.mapList f ts).get = f (ts.map Task.get)` is a small, self-contained, upstreamable first result.
