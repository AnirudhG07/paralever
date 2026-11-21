import VersoSlides
import Verso.Doc.Concrete
import Paralever
import Lang.Core.Cost
import Examples.Programs.MatMul
import Examples.Programs.MergeSort
import Examples.Programs.SumArray
import Examples.Language.NeuralNet
import Examples.Races.Caught

set_option verso.code.warnLineLength 500
set_option verso.slides.panel false
set_option linter.unusedVariables false
set_option verso.slides.warnOnImage false

open VersoSlides
open Paralever

#doc (Slides) "Paralever — ISP" =>
# paralever




%%%
state := "title"
%%%

:::class "subheader"
Verifying that a parallel program computes what its sequential counterpart computes — in Lean 4
:::

:::class "byline"
*Anirudh Gupta*
:::

:::class "event"
IISc Bengaluru · ISP · 4th-year BTech
:::

:::class "links"
[github.com/AnirudhG07/paralever](https://github.com/AnirudhG07/paralever)
:::

# Overview

```html
<div class="figwrap">
<svg viewBox="0 0 1160 230" role="img" aria-label="the seven sections of the talk in order, with the slide each one spends">
  <g font-family="var(--sans)" font-size="13.5" text-anchor="middle">
    <rect x="18"  y="30" width="200" height="56" rx="9" fill="#f8fafc" stroke="#94a3b8"/>
    <text x="118" y="54" fill="#0f172a">1 &#183; The question</text>
    <text x="118" y="73" font-size="12" fill="#64748b">par = seq, for every schedule</text>
    <rect x="248" y="30" width="200" height="56" rx="9" fill="#f8fafc" stroke="#94a3b8"/>
    <text x="348" y="54" fill="#0f172a">2 &#183; Independence</text>
    <text x="348" y="73" font-size="12" fill="#64748b">Bernstein, not &#8727;</text>
    <rect x="478" y="30" width="200" height="56" rx="9" fill="#f8fafc" stroke="#94a3b8"/>
    <text x="578" y="54" fill="#0f172a">3 &#183; The language</text>
    <text x="578" y="73" font-size="12" fill="#64748b">one Boolean on the text</text>
    <rect x="708" y="30" width="200" height="56" rx="9" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.2"/>
    <text x="808" y="54" fill="#312e81">4 &#183; Why it holds</text>
    <text x="808" y="73" font-size="12" fill="#4f46e5">one reachable outcome</text>
    <rect x="938" y="30" width="200" height="56" rx="9" fill="#f8fafc" stroke="#94a3b8"/>
    <text x="1038" y="54" fill="#0f172a">5 &#183; Examples</text>
    <text x="1038" y="73" font-size="12" fill="#64748b">four algorithms, four proofs</text>
    <rect x="248" y="140" width="200" height="56" rx="9" fill="#f8fafc" stroke="#94a3b8"/>
    <text x="348" y="164" fill="#0f172a">6 &#183; Autoparallelization</text>
    <text x="348" y="183" font-size="12" fill="#64748b">a spine becomes forks</text>
    <rect x="478" y="140" width="200" height="56" rx="9" fill="#f8fafc" stroke="#94a3b8"/>
    <text x="578" y="164" fill="#0f172a">7 &#183; Races and MLIR</text>
    <text x="578" y="183" font-size="12" fill="#64748b">a counterexample, a front end</text>
    <rect x="708" y="140" width="200" height="56" rx="9" fill="#f8fafc" stroke="#94a3b8"/>
    <text x="808" y="164" fill="#0f172a">8 &#183; Cost and limits</text>
    <text x="808" y="183" font-size="12" fill="#64748b">what it buys, what it misses</text>
  </g>
  <g stroke="#94a3b8" stroke-width="1.5" fill="none">
    <path d="M 220 58 L 246 58"/><path d="M 450 58 L 476 58"/>
    <path d="M 680 58 L 706 58"/><path d="M 910 58 L 936 58"/>
    <path d="M 1038 88 L 1038 112 L 348 112 L 348 138"/>
    <path d="M 450 168 L 476 168"/><path d="M 680 168 L 706 168"/>
  </g>
</svg>
</div>
```

Sections 1 to 4 state and prove one theorem; 5 to 8 are what it is worth. Every program after
section 4 discharges the same decidable obligation, and none of them reasons about a schedule.

# 1 · The question

%%%
state := "section"
%%%

:::class "ahead"
* A parallel program has many runs, and the claim is about all of them.
* One shared cell turns the agreement into a refutation, in Lean.
:::

# The runs of a parallel program

```html
<div class="dgm tight">
  <div class="nd mono">[0] := 3; [1] := 4;
%0 := [0]; [2] := %0 * %0;
%1 := [1]; [3] := %1 * %1;
%2 := [2]; %3 := [3];
[4] := %2 + %3<em>sequential: one run, one heap</em></div>
  <div class="arr lbl2">&#8594;<small>parallelize</small></div>
  <div class="nd mono blue">[0] := 3; [1] := 4;
parallel { %0 := [0]; [2] := %0 * %0 }
         | { %1 := [1]; [3] := %1 * %1 };
%2 := [2]; %3 := [3];
[4] := %2 + %3<em>parallel: many schedules, one heap each</em></div>
</div>
```

```html
<div class="qask">
  <div class="qm">?</div>
  <div class="qbody">
    <div class="qhead">Does <code>par</code> <span class="eq">=</span> <code>seq</code> hold for <b>every</b></div>
    <ul class="qwhen">
      <li>interleaving</li>
      <li>starting heap</li>
      <li>register state</li>
    </ul>
  </div>
</div>
```

:::class "notation"
*`seq`* — the statements run one after another. *`par`* — the arms of a `parallel` block run at the
same time, and the block ends when every arm has.
:::

# One shared cell

```html
<div class="dgm tight">
  <div class="nd mono good">parallel { [5] := 1 }
         | { [6] := 2 }<em>writes {5} against {6} &#8212; disjoint</em></div>
  <div class="nd mono bad">parallel { [5] := 1 }
         | { [5] := 2 }<em>one character: both write cell 5</em></div>
</div>
```

```leanLibCode Examples.Races.Caught (package := paralever) (startLine := 39) (endLine := 41) -stretch
/-- **The conclusion of `par_seq_eq` is false here.** One side terminates, the other cannot. -/
theorem not_parSeqEq (σ : State) : ¬ ParSeqEq (ParM.parPair wA wB) (ParM.seqPair wA wB) σ :=
  fun h => par_no_outcome σ _ _ ((h _ _).mpr (seq_reaches σ))
```

:::class "steps"
* The hypothesis of the main theorem is load-bearing: dropped, the conclusion is refutable in Lean.
* Enumerating schedules is not a method. Two arms of `n` statements each already admit
  `(2n)! / (n!)²` interleavings; at `n = 10` that is 184 756.
:::

# 2 · Independence

%%%
state := "section"
%%%

:::class "ahead"
* Bernstein's three clauses, computed from the program text.
* Why a separating conjunction is the wrong relation for this.
* The iris-lean spike, and why no separation-logic library is used.
:::

# Bernstein's three clauses, computed from the program text

```leanLibCode Paralever.Core.Access (package := paralever) (startLine := 65) (endLine := 66) -stretch
def Indep (f₁ f₂ : Footprint) : Prop :=
  Disjoint f₁.writes f₂.writes ∧ Disjoint f₁.writes f₂.reads ∧ Disjoint f₂.writes f₁.reads
```

```html
<div class="figwrap">
<svg viewBox="0 0 860 180" role="img" aria-label="the three Bernstein clauses as crossings between two footprints">
  <g font-family="ui-monospace, monospace" font-size="14" text-anchor="middle" fill="#0f172a">
    <rect x="40"  y="22" width="130" height="34" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="105" y="44">W&#8321;</text>
    <rect x="40"  y="112" width="130" height="34" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="105" y="134">R&#8321;</text>
    <rect x="690" y="22" width="130" height="34" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="755" y="44">W&#8322;</text>
    <rect x="690" y="112" width="130" height="34" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="755" y="134">R&#8322;</text>
  </g>
  <g stroke-width="2" fill="none">
    <path d="M 172 39 L 688 39"  stroke="#dc2626"/>
    <path d="M 172 44 L 688 125" stroke="#dc2626"/>
    <path d="M 172 125 L 688 44" stroke="#dc2626"/>
    <path d="M 172 131 L 688 131" stroke="#16a34a" stroke-dasharray="6 5"/>
  </g>
  <g font-size="13.5" font-family="var(--sans)" text-anchor="middle">
    <text x="430" y="30"  fill="#dc2626">C1 &#183; W&#8321; &#8745; W&#8322; = &#8709;</text>
    <text x="430" y="72"  fill="#dc2626">C2 &#183; W&#8321; &#8745; R&#8322; = &#8709;</text>
    <text x="430" y="100" fill="#dc2626">C3 &#183; W&#8322; &#8745; R&#8321; = &#8709;</text>
    <text x="430" y="152" fill="#16a34a">no clause on R&#8321; &#8745; R&#8322; &#8212; shared reads are permitted</text>
  </g>
</svg>
</div>
```

A footprint is two lists of cells, `reads` and `writes`, read off the syntax. Independence is a
decidable `Bool` over them: three list intersections, no reasoning about interleavings.

# Separating conjunction, and Bernstein

```html
<div class="figwrap">
<svg viewBox="0 0 880 250" role="img" aria-label="matmul threads write disjoint output cells and read overlapping input rows and columns">
  <g font-family="ui-monospace, monospace" font-size="13" fill="#0f172a">
    <text x="30" y="26" font-family="var(--sans)" font-size="14" fill="#475569">thread 0 &#183; C[0,j] = &#931;&#8342; A[0,k]&#183;B[k,j]</text>
    <text x="30" y="150" font-family="var(--sans)" font-size="14" fill="#475569">thread 1 &#183; C[1,j] = &#931;&#8342; A[1,k]&#183;B[k,j]</text>

    <rect x="30"  y="38" width="120" height="30" rx="5" fill="#eff6ff" stroke="#2563eb"/><text x="54" y="58">A[0,&#183;]</text>
    <rect x="180" y="38" width="160" height="30" rx="5" fill="#eff6ff" stroke="#2563eb"/><text x="204" y="58">B[&#183;,&#183;] (all)</text>
    <rect x="380" y="38" width="120" height="30" rx="5" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.4"/><text x="404" y="58">C[0,&#183;]</text>

    <rect x="30"  y="162" width="120" height="30" rx="5" fill="#eff6ff" stroke="#2563eb"/><text x="54" y="182">A[1,&#183;]</text>
    <rect x="180" y="162" width="160" height="30" rx="5" fill="#eff6ff" stroke="#2563eb"/><text x="204" y="182">B[&#183;,&#183;] (all)</text>
    <rect x="380" y="162" width="120" height="30" rx="5" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.4"/><text x="404" y="182">C[1,&#183;]</text>
  </g>
  <g stroke="#16a34a" stroke-width="2" stroke-dasharray="6 5" fill="none">
    <path d="M 260 68 L 260 162"/>
  </g>
  <g stroke="#4f46e5" stroke-width="2" fill="none">
    <path d="M 440 68 L 440 162"/>
  </g>
  <g font-size="13" font-family="var(--sans)">
    <text x="275" y="118" fill="#16a34a">B is read by both &#8212; permitted by C1&#8211;C3, forbidden by &#8727;</text>
    <text x="455" y="118" fill="#4f46e5">C rows are disjoint &#8212; C1 holds</text>
    <text x="560" y="230" fill="#475569" text-anchor="middle">&#8727;-disjointness rejects matrix multiply; Bernstein proves it</text>
  </g>
</svg>
</div>
```

`P ∗ Q` asserts the two sides own *disjoint* heap fragments, so it cannot describe two threads
reading one cell. No separation-logic library is used; framing is plain `∧` over footprints.

# Why no separation-logic library

```html
<div class="dgm col tight">
  <div class="nd">iris-lean, added as a dependency to answer one question<em>can <code>Indep</code> be an instance of a bunched-implications <code>&#8727;</code>?</em></div>
  <div class="nd good">the BI instance costs <b>nothing</b><em>non-step-indexed, <code>&#9655; := id</code>, a discrete COFE &#183; the step-indexing risk never arrived</em></div>
  <div class="nd bad">its <code>&#8727;</code> is <b>exclusive</b> separation<em>the state splits into disjoint-domain pieces, so a shared read is not expressible</em></div>
  <div class="nd bad">its carrier is a <b>partial</b> map<em><code>Core.State</code> is total &#183; a restriction or an embedding before a triple can be stated</em></div>
</div>
```

The dependency was removed once it had answered. `Logic/Rules.lean` frames with `∧` over footprints
instead, and the parallel rule it proves is therefore fully general — shared reads included. What
would supply read-sharing inside a `∗` is a fractional-permission `∗` over `Core.State`, and nothing
available builds one off the shelf.

# 3 · The language and the theorem

%%%
state := "section"
%%%

:::class "ahead"
* `ParM`, and why `par` has to be our own constructor.
* The surface language, and the verdict the checker prints.
* `wfB s = true → ParSeqEq (execPar s) (execSeq s)`.
:::

# `par` as our own constructor

```leanLibCode Paralever.Core.ParM (package := paralever) (startLine := 82) (endLine := 89) -stretch
inductive ParM : Type → Type 1 where
  | pure  {α : Type}     : α → ParM α
  | read  {α : Type}     : Loc → (Val → ParM α) → ParM α
  | write {α : Type}     : Loc → Val → (Unit → ParM α) → ParM α
  /-- Fork every child at once, then continue with all their results. The only constructor whose
  meaning Lean does not already fix: `run` interprets it by interleaving, which is what makes the
  sequentialization theorem non-vacuous. -/
  | par   {β : Type} {αs : List Type} : Childs ParM αs → (Results αs → ParM β) → ParM β
```

```html
<div class="dgm tight">
  <div class="nd bad">Lean's <code>Task</code><em><code>(Task.spawn f).get = f ()</code> holds by <code>rfl</code> &#8212; parallel and sequential are the <i>same term</i>, so there is nothing to prove</em></div>
  <div class="nd good"><code>ParM.par</code><em>a program is data; its meaning is fixed by <code>step</code>, which interleaves. <code>Task</code> is a compilation target only</em></div>
</div>
```

`ParM` is inductive, so every program terminates: `while true` is unrepresentable, and that boundary
is fixed by Lean having no coinductive types.

# The surface language, and the verdict the checker prints

```html
<div class="dgm tight">
  <div class="nd mono">buf A[9] = 0,0,0,0,0,0,0,3,0

parallel { A[5] := 1 }
         | { %v := A[7]; A[8] := %v }<em>fig1.prl</em></div>
  <div class="arr lbl2">&#8594;<small>paralever check</small></div>
  <div class="nd mono blue">memory   A[9] @0  (9 cells)
reads    {A[7]}
writes   {A[5], A[8]}
threads  2
rounds   2 parallel, 3 sequential
verdict  every heap  Proved: Yes<em><code>wfB</code> accepts: footprints pairwise independent</em></div>
</div>
```

:::class "steps"
* `[l]` is a cell, `[A, e]` a computed cell, `%n` a register. `if`, `while … in`, `synchronize` and
  `print` are the control constructs; every one has a Lean form.
* Two interpreters, `execPar` and `execSeq`, read the same `ParProg` tree. The verdict is two-part:
  *this heap* by exact search, *any heap* by the syntactic check.
:::

# The theorem

```leanLibCode Paralever.Theory.Sequentialize (package := paralever) (startLine := 18) (endLine := 19) -stretch
def ParSeqEq {α : Type} (p q : ParM α) (σ : State) : Prop :=
  ∀ r σ', Reaches (.run p σ) (.run (.pure r) σ') ↔ Reaches (.run q σ) (.run (.pure r) σ')
```

```leanLibCode Lang.Core.Prog (package := paralever) (startLine := 674) (endLine := 675) -stretch
theorem par_seq_eq {s : ParProg} (h : wfB s = true) (ρ : Regs) (σ : State) :
    ParSeqEq (execPar s ρ) (execSeq s ρ) σ := by
```

```html
<div class="dgm tight">
  <div class="nd key"><code>wfB s = true</code><em>decided by <code>decide</code>: list intersections on footprints</em></div>
  <div class="arr">&#8594;</div>
  <div class="nd key blue">every schedule of <code>s</code> ends where <code>execSeq s</code> ends<em>stated as an <i>iff</i> on reachable outcomes</em></div>
</div>
```

Every program below discharges its obligation by `decide` or by a size-free kernel lemma. No program
carries a proof about interleavings of its own.

# 4 · Why it holds

%%%
state := "section"
%%%

:::class "ahead"
* A well-formed program has exactly one reachable outcome.
* A race has no outcome at all, which is what excludes it.
:::

# Canonical outcomes

```html
<div class="figwrap">
<svg viewBox="0 0 900 230" role="img" aria-label="the lemma chain from frame and locality up to the canonical outcome theorem">
  <defs>
    <marker id="pc" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#64748b"/>
    </marker>
  </defs>
  <g font-family="ui-monospace, monospace" font-size="12.5" text-anchor="middle" fill="#0f172a">
    <rect x="20"  y="18"  width="200" height="32" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="120" y="39">runSeq_frame</text>
    <rect x="20"  y="78"  width="200" height="32" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="120" y="99">accesses_locality</text>
    <rect x="20"  y="138" width="200" height="32" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="120" y="159">accesses_isolated</text>
    <rect x="290" y="48"  width="210" height="32" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="395" y="69">no_race_of_indep</text>
    <rect x="290" y="112" width="210" height="32" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="395" y="133">WellFormed_preserved</text>
    <rect x="570" y="80"  width="200" height="32" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="670" y="101">par_dichotomy</text>
    <rect x="330" y="186" width="430" height="34" rx="7" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.4"/><text x="545" y="208" fill="#312e81">wellFormed_canonical</text>
  </g>
  <g stroke="#64748b" stroke-width="1.4" fill="none" marker-end="url(#pc)">
    <path d="M 222 34 L 255 34 L 255 64 L 287 64"/>
    <path d="M 222 94 L 255 94 L 255 64"/>
    <path d="M 222 154 L 255 154 L 255 128 L 287 128"/>
    <path d="M 502 64  L 535 64 L 535 96 L 567 96"/>
    <path d="M 502 128 L 535 128 L 535 96"/>
    <path d="M 670 112 L 670 160 L 545 160 L 545 184"/>
  </g>
</svg>
</div>
```

```leanLibCode Paralever.Theory.WellFormedCanonical (package := paralever) (startLine := 1462) (endLine := 1464) -stretch
theorem wellFormed_canonical {τ : Type} (p : ParM τ) :
    ∀ σ r σ', WellFormed p σ → (Reaches (.run p σ) (.run (.pure r) σ') ↔ (r, σ') = runSeq p σ) :=
  wellFormed_canonical_all.1 p
```

Read as an *iff*: `→` says no schedule terminates anywhere else, `←` says that outcome is reached.
`par_seq_eq` is this theorem applied to both sides and the results compared.

# Races, and `wrong`

```html
<div class="figwrap">
<svg viewBox="0 0 880 200" role="img" aria-label="a well-formed fork reaches one outcome, a racy fork is absorbed into wrong">
  <defs>
    <marker id="dic" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#64748b"/>
    </marker>
  </defs>
  <g font-family="ui-monospace, monospace" font-size="13.5" text-anchor="middle" fill="#0f172a">
    <rect x="30"  y="36" width="180" height="32" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="120" y="57">Indep holds</text>
    <rect x="30"  y="126" width="180" height="32" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="120" y="147">Indep fails</text>
    <rect x="420" y="36" width="300" height="32" rx="6" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.2"/><text x="570" y="57" fill="#312e81">one outcome: runSeq p &#963;</text>
    <rect x="420" y="126" width="300" height="32" rx="6" fill="#fef2f2" stroke="#dc2626" stroke-width="2.2"/><text x="570" y="147" fill="#7f1d1d">wrong &#8212; terminal, absorbing</text>
  </g>
  <g stroke="#64748b" stroke-width="1.5" fill="none" marker-end="url(#dic)">
    <path d="M 212 52 L 417 52"/>
    <path d="M 212 142 L 417 142"/>
  </g>
  <g font-size="13" font-style="italic" font-family="var(--sans)" fill="#475569" text-anchor="middle">
    <text x="440" y="188">Reynolds' grainless semantics: a racy program is <i>excluded</i>, not given a behaviour</text>
  </g>
</svg>
</div>
```

:::class "steps"
* `run` returns an `Option`, and `wrong` absorbs: once a step finds two conflicting accesses ready
  at one instant, nothing recovers.
* This is why the atomic grain is irrelevant to the theorem. No result depends on how coarsely a
  write is implemented.
:::

# 5 · Examples

%%%
state := "section"
%%%

:::class "ahead"
* Matrix multiply — disjoint writes over overlapping reads.
* Merge sort — the fork is the recursion.
* A neural net — layers in sequence, threads inside each.
* Summing an array — quantified over the chunk plan.
:::

# Matrix multiply

```html
<div class="two-col wide-left">
```

```html
<div class="nd mono plain wide">const n = 2

buf A[2, 2] = 1, 2, 3, 4
buf B[2, 2] = 5, 6, 7, 8
buf C[2, 2]

parfor i in n {
  for j in n {
    %acc := 0
    for k in n {
      %x := A[i, k]
      %y := B[k, j]
      %acc := %acc + %x * %y
    }
    C[i, j] := %acc
  }
} :: "matmul 2x2"</div>
```

```leanLibCode Examples.Programs.MatMul (package := paralever) (startLine := 216) (endLine := 222) -stretch
example : ParProg.wfB (matmul 2) = true := by decide
example : ParProg.wfB (matmul 3) = true := by decide

/-- …and the equivalence follows with nothing further to supply. -/
theorem par_seq_eq_2 (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar (matmul 2) ρ) (ParProg.execSeq (matmul 2) ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ
```

```html
</div>
```

Thread `i` writes row `i` of `C` and reads row `i` of `A` and all of `B`. (C1) holds because
`i ↦ i*n + j` is injective across threads; (C2) and (C3) hold because `A` and `B` are never written.
The file above carries the same theorem as `matmul_parseqeq`, read through `prl_file`.

# Merge sort

```html
<div class="figwrap">
<svg viewBox="0 0 820 220" role="img" aria-label="merge sort recursion tree splitting a range into disjoint halves">
  <g font-family="ui-monospace, monospace" font-size="13.5" text-anchor="middle" fill="#0f172a">
    <rect x="320" y="14" width="180" height="32" rx="6" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.2"/><text x="410" y="35">sort [0, 8)</text>
    <rect x="150" y="90" width="160" height="32" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="230" y="111">sort [0, 4)</text>
    <rect x="510" y="90" width="160" height="32" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="590" y="111">sort [4, 8)</text>
    <rect x="60"  y="166" width="130" height="30" rx="5" fill="#f8fafc" stroke="#cbd5e1"/><text x="125" y="186">[0, 2)</text>
    <rect x="212" y="166" width="130" height="30" rx="5" fill="#f8fafc" stroke="#cbd5e1"/><text x="277" y="186">[2, 4)</text>
    <rect x="440" y="166" width="130" height="30" rx="5" fill="#f8fafc" stroke="#cbd5e1"/><text x="505" y="186">[4, 6)</text>
    <rect x="592" y="166" width="130" height="30" rx="5" fill="#f8fafc" stroke="#cbd5e1"/><text x="657" y="186">[6, 8)</text>
  </g>
  <g stroke="#64748b" stroke-width="1.5" fill="none">
    <path d="M 410 46 L 410 68 L 230 68 L 230 88"/>
    <path d="M 410 46 L 410 68 L 590 68 L 590 88"/>
    <path d="M 230 122 L 230 144 L 125 144 L 125 164"/>
    <path d="M 230 122 L 230 144 L 277 144 L 277 164"/>
    <path d="M 590 122 L 590 144 L 505 144 L 505 164"/>
    <path d="M 590 122 L 590 144 L 657 144 L 657 164"/>
  </g>
  <g font-size="13" font-style="italic" font-family="var(--sans)" fill="#475569" text-anchor="middle">
    <text x="410" y="214">at each level: <tspan font-family="ui-monospace, monospace">lo &#8804; mid &#8804; hi</tspan>, so <tspan font-family="ui-monospace, monospace">[lo, mid)</tspan> and <tspan font-family="ui-monospace, monospace">[mid, hi)</tspan> do not meet</text>
  </g>
</svg>
</div>
```

```leanLibCode Examples.Programs.MergeSort (package := paralever) (startLine := 474) (endLine := 475) -stretch
theorem seq_eq_par (N lo hi : Nat) (hhiN : hi ≤ N) (σ : State) :
    mergeSortPar N lo hi ∥≡ mergeSortSeq N lo hi from σ := by
```

Quantified over the array size and over every range, with no `decide`: each level's obligation is
one interval fact, and the recursion carries it down.

# Neural net

```html
<div class="figwrap">
<svg viewBox="0 0 880 180" role="img" aria-label="three layers in sequence, each forking over its own output cells">
  <defs>
    <marker id="nnar" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#64748b"/>
    </marker>
  </defs>
  <g font-family="ui-monospace, monospace" font-size="13" text-anchor="middle" fill="#0f172a">
    <rect x="20"  y="66" width="90"  height="34" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="65"  y="88">x[8]</text>
    <rect x="170" y="26" width="140" height="30" rx="6" fill="#eef2ff" stroke="#4f46e5"/><text x="240" y="46">conv1d &#215; 6</text>
    <rect x="370" y="26" width="140" height="30" rx="6" fill="#eef2ff" stroke="#4f46e5"/><text x="440" y="46">relu &#215; 6</text>
    <rect x="570" y="26" width="140" height="30" rx="6" fill="#eef2ff" stroke="#4f46e5"/><text x="640" y="46">dense &#215; 2</text>
    <rect x="770" y="66" width="90"  height="34" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="815" y="88">y[2]</text>
    <rect x="170" y="106" width="140" height="30" rx="6" fill="#f8fafc" stroke="#cbd5e1"/><text x="240" y="126">c[6]</text>
    <rect x="370" y="106" width="140" height="30" rx="6" fill="#f8fafc" stroke="#cbd5e1"/><text x="440" y="126">r[6]</text>
    <rect x="570" y="106" width="140" height="30" rx="6" fill="#f8fafc" stroke="#cbd5e1"/><text x="640" y="126">w2[2,6], b2[2]</text>
  </g>
  <g stroke="#64748b" stroke-width="1.5" fill="none" marker-end="url(#nnar)">
    <path d="M 110 83 L 140 83 L 140 41 L 167 41"/>
    <path d="M 310 41 L 367 41"/>
    <path d="M 510 41 L 567 41"/>
    <path d="M 710 41 L 740 41 L 740 83 L 767 83"/>
  </g>
  <g font-size="12.5" font-style="italic" font-family="var(--sans)" fill="#475569" text-anchor="middle">
    <text x="440" y="166">every thread of a layer reads the whole weight array; only the output cells are written</text>
  </g>
</svg>
</div>
```

```leanLibCode Examples.Language.NeuralNet (package := paralever) (startLine := 67) (endLine := 70) -stretch
theorem forward_par_seq_eq (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar forward ρ) (ParProg.execSeq forward ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ
```

The weights are shared reads, so (C2) and (C3) are free inside a layer. Between layers the
composition is sequential, and `wfB` recurses into each arm.

# Sum of an array

```html
<div class="figwrap">
<svg viewBox="0 0 860 170" role="img" aria-label="an array split into chunks, each chunk summed by one thread, the partial sums combined">
  <g font-family="ui-monospace, monospace" font-size="13" text-anchor="middle" fill="#0f172a">
    <rect x="40"  y="20" width="180" height="32" rx="5" fill="#eff6ff" stroke="#2563eb"/><text x="130" y="41">A[0, 4)</text>
    <rect x="240" y="20" width="180" height="32" rx="5" fill="#eff6ff" stroke="#2563eb"/><text x="330" y="41">A[4, 9)</text>
    <rect x="440" y="20" width="180" height="32" rx="5" fill="#eff6ff" stroke="#2563eb"/><text x="530" y="41">A[9, 13)</text>
    <rect x="640" y="20" width="180" height="32" rx="5" fill="#eff6ff" stroke="#2563eb"/><text x="730" y="41">A[13, 16)</text>

    <rect x="70"  y="90" width="120" height="30" rx="5" fill="#eef2ff" stroke="#4f46e5"/><text x="130" y="110">s&#8320;</text>
    <rect x="270" y="90" width="120" height="30" rx="5" fill="#eef2ff" stroke="#4f46e5"/><text x="330" y="110">s&#8321;</text>
    <rect x="470" y="90" width="120" height="30" rx="5" fill="#eef2ff" stroke="#4f46e5"/><text x="530" y="110">s&#8322;</text>
    <rect x="670" y="90" width="120" height="30" rx="5" fill="#eef2ff" stroke="#4f46e5"/><text x="730" y="110">s&#8323;</text>
  </g>
  <g stroke="#64748b" stroke-width="1.4" fill="none">
    <path d="M 130 52 L 130 88"/><path d="M 330 52 L 330 88"/>
    <path d="M 530 52 L 530 88"/><path d="M 730 52 L 730 88"/>
  </g>
  <g font-size="13" font-style="italic" font-family="var(--sans)" fill="#475569" text-anchor="middle">
    <text x="430" y="152">no thread writes the array, so C1&#8211;C3 hold vacuously &#8212; for <i>any</i> split</text>
  </g>
</svg>
</div>
```

```leanLibCode Examples.Programs.SumArray (package := paralever) (startLine := 106) (endLine := 108) -stretch
theorem seq_eq_par (chunks : ChunkPlan) (σ : State) :
    sumRangePar chunks ∥≡ sumRangeSeq chunks from σ :=
  parAll_par_seq_eq (chunks.map sumRange) σ (wellFormed_sumRangePar chunks σ)
```

Universally quantified over the chunk plan and the heap. This is the shape `∗`-disjointness cannot
state at all: four threads reading one array.

# 6 · Autoparallelization

%%%
state := "section"
%%%

:::class "ahead"
* A sequential program is a right-leaning spine of `seq` nodes.
* Where the parallelism is: five units, four dependences.
* The spine rebuilt as three forks, proved with no hypothesis.
:::

# The sequential spine

```html
<div class="two-col">
```

```html
<div class="nd mono plain wide">buf a[5]

a[0] := 3
a[1] := 4
%0 := a[0]
a[2] := %0 * %0
%1 := a[1]
a[3] := %1 * %1
%2 := a[2]
%3 := a[3]
a[4] := %2 + %3<em>chain.prl &#8212; ten lines, nine of them statements</em></div>
```

```html
<div class="figwrap">
<svg viewBox="0 0 520 320" role="img" aria-label="the nine statements of chain.prl as a right-leaning spine of seq nodes, one statement hanging off each">
  <g stroke="#64748b" stroke-width="1.3" fill="none">
    <path d="M 310 29 L 310 34.5 L 150 34.5 L 150 40"/>
    <path d="M 310 29 L 310 35 L 310 35 L 310 41"/>
    <path d="M 310 63 L 310 68.5 L 150 68.5 L 150 74"/>
    <path d="M 310 63 L 310 69 L 310 69 L 310 75"/>
    <path d="M 310 97 L 310 102.5 L 150 102.5 L 150 108"/>
    <path d="M 310 97 L 310 103 L 310 103 L 310 109"/>
    <path d="M 310 131 L 310 136.5 L 150 136.5 L 150 142"/>
    <path d="M 310 131 L 310 137 L 310 137 L 310 143"/>
    <path d="M 310 165 L 310 170.5 L 150 170.5 L 150 176"/>
    <path d="M 310 165 L 310 171 L 310 171 L 310 177"/>
    <path d="M 310 199 L 310 204.5 L 150 204.5 L 150 210"/>
    <path d="M 310 199 L 310 205 L 310 205 L 310 211"/>
    <path d="M 310 233 L 310 238.5 L 150 238.5 L 150 244"/>
    <path d="M 310 233 L 310 239 L 310 239 L 310 245"/>
    <path d="M 310 267 L 310 272.5 L 150 272.5 L 150 278"/>
    <path d="M 310 267 L 310 273 L 310 273 L 310 279"/>
  </g>
  <g font-family="ui-monospace, monospace" text-anchor="middle" fill="#0f172a">
    <rect x="288" y="7" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="22" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="41" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="56" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="75" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="90" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="109" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="124" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="143" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="158" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="177" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="192" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="211" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="226" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="245" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="260" font-size="12" fill="#0f172a">seq</text>
    <rect x="75" y="40" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="56" font-size="11.5">a[0] := 3</text>
    <rect x="75" y="74" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="90" font-size="11.5">a[1] := 4</text>
    <rect x="75" y="108" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="124" font-size="11.5">%0 := a[0]</text>
    <rect x="75" y="142" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="158" font-size="11.5">a[2] := %0 * %0</text>
    <rect x="75" y="176" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="192" font-size="11.5">%1 := a[1]</text>
    <rect x="75" y="210" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="226" font-size="11.5">a[3] := %1 * %1</text>
    <rect x="75" y="244" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="260" font-size="11.5">%2 := a[2]</text>
    <rect x="75" y="278" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="294" font-size="11.5">%3 := a[3]</text>
    <rect x="235" y="278" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="310" y="294" font-size="11.5">a[4] := %2 + %3</text>
  </g>
  <g font-size="12.5" font-family="var(--sans)" fill="#475569">
    <text x="345" y="92">the spine is the order</text>
    <text x="345" y="112">the text was written in;</text>
    <text x="345" y="132">depth 9, one statement</text>
    <text x="345" y="152">per round</text>
  </g>
</svg>
</div>
```

```html
</div>
```

`ParProg.block [s₀, …, s₈]` is `seq s₀ (seq s₁ (…))`, so the order the statements were written in is
the tree's right spine. The pass first cuts that spine into five register-closed units — `%0 := a[0]`
and `a[2] := %0 * %0` may not be separated, because a register is thread-private — and one scoreboard
pass reads every dependence off them: `[[], [], [0], [1], [2, 3]]`.

# The dependence DAG

```html
<div class="figwrap">
<svg viewBox="0 0 1180 376" role="img" aria-label="the ten lines bracketed into five register-closed units, and the four dependences between them laid out in three rounds">
  <rect x="548" y="50" width="500" height="72" rx="10" fill="#eef2ff" stroke="#4f46e5" stroke-width="1" stroke-dasharray="5 5"/><text x="1062" y="92" font-size="12.5" font-family="var(--sans)" fill="#4f46e5">1 round</text>
  <rect x="548" y="150" width="500" height="72" rx="10" fill="#eff6ff" stroke="#2563eb" stroke-width="1" stroke-dasharray="5 5"/><text x="1062" y="192" font-size="12.5" font-family="var(--sans)" fill="#2563eb">2 rounds</text>
  <rect x="548" y="250" width="500" height="72" rx="10" fill="#f0fdf4" stroke="#16a34a" stroke-width="1" stroke-dasharray="5 5"/><text x="1062" y="292" font-size="12.5" font-family="var(--sans)" fill="#16a34a">3 rounds</text>
  <g stroke="#94a3b8" stroke-width="1.6" fill="none" stroke-linejoin="round">
    <path d="M 680 109 L 680 135 L 680 135 L 680 161"/>
    <path d="M 900 109 L 900 135 L 900 135 L 900 161"/>
    <path d="M 680 209 L 680 235 L 790 235 L 790 261"/>
    <path d="M 900 209 L 900 235 L 790 235 L 790 261"/>
  </g>
  <g font-family="ui-monospace, monospace" font-size="13" fill="#0f172a">
    <text x="92" y="58">a[0] := 3</text>
    <text x="92" y="87">a[1] := 4</text>
    <text x="92" y="116">%0 := a[0]</text>
    <text x="92" y="145">a[2] := %0 * %0</text>
    <text x="92" y="174">%1 := a[1]</text>
    <text x="92" y="203">a[3] := %1 * %1</text>
    <text x="92" y="232">%2 := a[2]</text>
    <text x="92" y="261">%3 := a[3]</text>
    <text x="92" y="290">a[4] := %2 + %3</text>
  </g>
  <g font-family="ui-monospace, monospace">
    <rect x="64" y="43" width="7" height="22" rx="3.5" fill="#4f46e5"/><text x="52" y="58" font-size="12" fill="#4f46e5" text-anchor="end">u0</text>
    <rect x="64" y="72" width="7" height="22" rx="3.5" fill="#4f46e5"/><text x="52" y="87" font-size="12" fill="#4f46e5" text-anchor="end">u1</text>
    <rect x="64" y="101" width="7" height="51" rx="3.5" fill="#2563eb"/><text x="52" y="130.5" font-size="12" fill="#2563eb" text-anchor="end">u2</text>
    <rect x="64" y="159" width="7" height="51" rx="3.5" fill="#2563eb"/><text x="52" y="188.5" font-size="12" fill="#2563eb" text-anchor="end">u3</text>
    <rect x="64" y="217" width="7" height="80" rx="3.5" fill="#16a34a"/><text x="52" y="261" font-size="12" fill="#16a34a" text-anchor="end">u4</text>
  </g>
  <g font-family="ui-monospace, monospace" text-anchor="middle">
    <rect x="582" y="63" width="196" height="46" rx="7" fill="#ffffff" stroke="#4f46e5" stroke-width="2"/><text x="680" y="82" font-size="13" fill="#4f46e5">u0</text><text x="680" y="100" font-size="11" fill="#475569">w a[0]</text>
    <rect x="802" y="63" width="196" height="46" rx="7" fill="#ffffff" stroke="#4f46e5" stroke-width="2"/><text x="900" y="82" font-size="13" fill="#4f46e5">u1</text><text x="900" y="100" font-size="11" fill="#475569">w a[1]</text>
    <rect x="582" y="163" width="196" height="46" rx="7" fill="#ffffff" stroke="#2563eb" stroke-width="2"/><text x="680" y="182" font-size="13" fill="#2563eb">u2</text><text x="680" y="200" font-size="11" fill="#475569">r a[0] · w a[2]</text>
    <rect x="802" y="163" width="196" height="46" rx="7" fill="#ffffff" stroke="#2563eb" stroke-width="2"/><text x="900" y="182" font-size="13" fill="#2563eb">u3</text><text x="900" y="200" font-size="11" fill="#475569">r a[1] · w a[3]</text>
    <rect x="692" y="263" width="196" height="46" rx="7" fill="#ffffff" stroke="#16a34a" stroke-width="2"/><text x="790" y="282" font-size="13" fill="#16a34a">u4</text><text x="790" y="300" font-size="11" fill="#475569">r a[2],a[3] · w a[4]</text>
  </g>
  <g font-size="12.5" font-family="var(--sans)" fill="#475569">
    <text x="40" y="26">the ten lines, cut into units</text>
    <text x="548" y="26">what each unit touches, and what it must wait for</text>
    <text x="40" y="350">a unit is a run of statements no live register crosses</text>
    <text x="548" y="350">depth 6 against a sequential 9, and 6 is the lower bound</text>
  </g>
</svg>
</div>
```

A register is thread-private, so `%0 := a[0]` and `a[2] := %0 * %0` may not be separated: the unit,
not the statement, is what a thread is built from. One left-to-right scoreboard pass then reads
every dependence off the units' footprints — `[[], [], [0], [1], [2, 3]]`. Four of the ten pairs
carry one; `u0, u1` share no cell, as do `u2, u3`. That is the whole of the parallelism this program has.

# The parallel plan

```html
<div class="two-col">
```

```html
<div class="figwrap">
<svg viewBox="0 0 520 320" role="img" aria-label="the nine statements of chain.prl as a right-leaning spine of seq nodes, one statement hanging off each">
  <g stroke="#64748b" stroke-width="1.3" fill="none">
    <path d="M 310 29 L 310 34.5 L 150 34.5 L 150 40"/>
    <path d="M 310 29 L 310 35 L 310 35 L 310 41"/>
    <path d="M 310 63 L 310 68.5 L 150 68.5 L 150 74"/>
    <path d="M 310 63 L 310 69 L 310 69 L 310 75"/>
    <path d="M 310 97 L 310 102.5 L 150 102.5 L 150 108"/>
    <path d="M 310 97 L 310 103 L 310 103 L 310 109"/>
    <path d="M 310 131 L 310 136.5 L 150 136.5 L 150 142"/>
    <path d="M 310 131 L 310 137 L 310 137 L 310 143"/>
    <path d="M 310 165 L 310 170.5 L 150 170.5 L 150 176"/>
    <path d="M 310 165 L 310 171 L 310 171 L 310 177"/>
    <path d="M 310 199 L 310 204.5 L 150 204.5 L 150 210"/>
    <path d="M 310 199 L 310 205 L 310 205 L 310 211"/>
    <path d="M 310 233 L 310 238.5 L 150 238.5 L 150 244"/>
    <path d="M 310 233 L 310 239 L 310 239 L 310 245"/>
    <path d="M 310 267 L 310 272.5 L 150 272.5 L 150 278"/>
    <path d="M 310 267 L 310 273 L 310 273 L 310 279"/>
  </g>
  <g font-family="ui-monospace, monospace" text-anchor="middle" fill="#0f172a">
    <rect x="288" y="7" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="22" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="41" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="56" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="75" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="90" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="109" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="124" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="143" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="158" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="177" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="192" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="211" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="226" font-size="12" fill="#0f172a">seq</text>
    <rect x="288" y="245" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="310" y="260" font-size="12" fill="#0f172a">seq</text>
    <rect x="75" y="40" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="56" font-size="11.5">a[0] := 3</text>
    <rect x="75" y="74" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="90" font-size="11.5">a[1] := 4</text>
    <rect x="75" y="108" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="124" font-size="11.5">%0 := a[0]</text>
    <rect x="75" y="142" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="158" font-size="11.5">a[2] := %0 * %0</text>
    <rect x="75" y="176" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="192" font-size="11.5">%1 := a[1]</text>
    <rect x="75" y="210" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="226" font-size="11.5">a[3] := %1 * %1</text>
    <rect x="75" y="244" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="260" font-size="11.5">%2 := a[2]</text>
    <rect x="75" y="278" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="150" y="294" font-size="11.5">%3 := a[3]</text>
    <rect x="235" y="278" width="150" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="310" y="294" font-size="11.5">a[4] := %2 + %3</text>
  </g>
  <g font-size="12.5" font-family="var(--sans)" fill="#475569">
    <text x="345" y="92">the spine is the order</text>
    <text x="345" y="112">the text was written in;</text>
    <text x="345" y="132">depth 9, one statement</text>
    <text x="345" y="152">per round</text>
  </g>
</svg>
</div>
```

```html
<div class="figwrap">
<svg viewBox="0 0 570 292" role="img" aria-label="the same program after the rewrite: three forks in sequence, two threads then two threads then one">
  <g stroke="#64748b" stroke-width="1.3" fill="none">
    <path d="M 258 31 L 258 49 L 117.5 49 L 117.5 67"/>
    <path d="M 258 31 L 258 49 L 398.5 49 L 398.5 67"/>
    <path d="M 117.5 89 L 117.5 106.5 L 60 106.5 L 60 124"/>
    <path d="M 117.5 89 L 117.5 106.5 L 175 106.5 L 175 124"/>
    <path d="M 398.5 89 L 398.5 107 L 302 107 L 302 125"/>
    <path d="M 398.5 89 L 398.5 107 L 495 107 L 495 125"/>
    <path d="M 302 147 L 302 171.5 L 240 171.5 L 240 196"/>
    <path d="M 302 147 L 302 171.5 L 365 171.5 L 365 196"/>
    <path d="M 495 147 L 495 171.5 L 495 171.5 L 495 196"/>
  </g>
  <g font-family="ui-monospace, monospace" text-anchor="middle" fill="#0f172a">
    <rect x="236" y="9" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="258" y="24" font-size="12" fill="#0f172a">seq</text>
    <rect x="95.5" y="67" width="44" height="22" rx="5" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.2"/><text x="117.5" y="82" font-size="12" fill="#312e81">par</text>
    <rect x="376.5" y="67" width="44" height="22" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/><text x="398.5" y="82" font-size="12" fill="#0f172a">seq</text>
    <rect x="10" y="124" width="100" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="60" y="140" font-size="11.5">a[0] := 3</text>
    <rect x="125" y="124" width="100" height="24" rx="5" fill="#f8fafc" stroke="#94a3b8" stroke-width="1"/><text x="175" y="140" font-size="11.5">a[1] := 4</text>
    <rect x="280" y="125" width="44" height="22" rx="5" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.2"/><text x="302" y="140" font-size="12" fill="#312e81">par</text>
    <rect x="473" y="125" width="44" height="22" rx="5" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.2"/><text x="495" y="140" font-size="12" fill="#312e81">par</text>
    <rect x="181" y="196" width="118" height="48" rx="5" fill="#eff6ff" stroke="#2563eb" stroke-width="1.2"/><text x="240" y="214" font-size="11">%0 := a[0]</text><text x="240" y="231" font-size="11">a[2] := %0 * %0</text>
    <rect x="306" y="196" width="118" height="48" rx="5" fill="#eff6ff" stroke="#2563eb" stroke-width="1.2"/><text x="365" y="214" font-size="11">%1 := a[1]</text><text x="365" y="231" font-size="11">a[3] := %1 * %1</text>
    <rect x="436" y="196" width="118" height="65" rx="5" fill="#eff6ff" stroke="#2563eb" stroke-width="1.2"/><text x="495" y="214" font-size="11">%2 := a[2]</text><text x="495" y="231" font-size="11">%3 := a[3]</text><text x="495" y="248" font-size="11">a[4] := %2 + %3</text>
  </g>
  <g font-size="12.5" font-family="var(--sans)" fill="#475569">
    <text x="20" y="206">depth 6:</text>
    <text x="20" y="224">1 + 2 + 3</text>
    <text x="20" y="242">rounds, and</text>
    <text x="20" y="260">6 is the bound</text>
  </g>
</svg>
</div>
```

```html
</div>
```

```leanLibCode Examples.AutoPar.Pass (package := paralever) (startLine := 128) (endLine := 135) -stretch
example (ρ : Regs) (σ : State) :
    (runSeq (ParProg.execPar (rewrite p) ρ) σ).2 = (runSeq (ParProg.execSeq p ρ) σ).2 :=
  rewrite_sound p ρ σ

-- and because the rewrite stays well-formed, `par_seq_eq` lifts that from one schedule to all
example (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar (rewrite p) ρ) (ParProg.execSeq (rewrite p) ρ) σ :=
  rewrite_parSeqEq p (by decide) ρ σ
```

`rewrite` checks its own gate and hands back the program unchanged when it fails, which is why
`rewrite_sound` carries no hypothesis. Nothing is ever reordered, so no commutation lemma is needed.

# 7 · Finding races, and MLIR

%%%
state := "section"
%%%

:::class "ahead"
* What the checker returns when it refuses: the schedule that disagrees.
* A whole MLIR module in, a whole paralever program out.
:::

# What a refusal returns

```html
<div class="nd mono plain wide">2:T1         write [9] &#8592; 2  pending
2:T0         read [9]       pending
Parallel aborts at Step 2. Reason: T0, T1 access: {9}.
Parallel:   9&#8614;2, T0 reads 2
Sequential: 9&#8614;2, T0 reads 0<em>paralever race &#8212; a read-after-write race</em></div>
```

:::class "steps"
* The two heaps agree. The divergence is what `T0` *observes*, which a heap comparison would miss.
* A found schedule is replayed against the semantics and turned into a `Reaches` proof by
  `follow_sound`, so a counterexample is checked, never believed.
* The search is two-phase: scan for conflicting sites, then aim the schedule search at them.
:::

# MLIR in, paralever out

```html
<div class="two-col">
```

```html
<div class="nd mono plain wide">memref.global "private" @A : memref&lt;3xi64&gt; = dense&lt;[2, 3, 4]&gt;
func.func @main() {
  %A = memref.get_global @A : memref&lt;3xi64&gt;
  affine.parallel (%i) = (0) to (3) {
    %0 = affine.load %A[%i] : memref&lt;3xi64&gt;
    %1 = arith.muli %0, %0 : i64
    affine.store %1, %A[%i] : memref&lt;3xi64&gt;
  }
  return
}<em>square-no.mlir &#8212; the whole module</em></div>
```

```html
<div class="nd mono plain wide blue">buf A[3] = 2, 3, 4

parallel {
  %0 := A[0]
  A[0] := (%0 * %0)
} | {
  %0 := A[1]
  A[1] := (%0 * %0)
} | {
  %0 := A[2]
  A[2] := (%0 * %0)
}<em>paralever to-prl &#8212; the whole program</em></div>
```

```html
</div>
```

```leanLibCode Examples.Mlir.Files (package := paralever) (startLine := 155) (endLine := 157) -stretch
-- and the theorem the verdict stands for, on the program the deck prints
theorem square_par_seq_eq (ρ : Regs) (σ : State) :
    ParSeqEq (Lang.ParProg.execPar square.prog ρ) (Lang.ParProg.execSeq square.prog ρ) σ :=
  Lang.ParProg.par_seq_eq (by decide) ρ σ
```

A `memref.global` becomes a buffer, an `affine.map` is already a footprint function, and the three
iterations become three threads of one fork. Nine labelled pilots are `#guard`ed as a confusion
matrix — `tp = 3, fp = 0, fn = 0, tn = 4` over the seven generic-form ones — and emitting the
program back as MLIR compares memory, footprint, verdict and heap.

# 8 · Cost and limits

%%%
state := "section"
%%%

:::class "ahead"
* What parallelizing buys, and the size the check reaches.
* What the method does not cover, and what was built.
:::

# Cost and scale

```leanLibCode Lang.Core.Cost (package := paralever) (startLine := 103) (endLine := 104) -stretch
theorem time_le {s : ParProg} (h : wfB s = true) (ρ : Regs) (σ : State) :
    time (execPar s ρ) σ ≤ time (execSeq s ρ) σ := time_execPar_le_all.1 s ρ σ h
```

```html
<table class="dgmt">
<thead><tr><th>shape</th><th>points</th><th>rolled nest</th><th>written out</th></tr></thead>
<tbody>
<tr><td><code>elemwise</code> 12&#178;</td><td>144</td><td><b>0.85 s</b></td><td>6.40 s</td></tr>
<tr><td><code>elemwise</code> 20&#178;</td><td>400</td><td><b>0.85 s</b></td><td><b>49.4 s</b></td></tr>
<tr><td><code>gemm</code> 10&#179;</td><td>1 000</td><td><b>0.89 s</b></td><td>16.9 s</td></tr>
<tr class="gap"><td><code>gemm</code> 1000&#179;</td><td>10&#8313;</td><td><b>0.89 s</b></td><td>over the ceiling</td></tr>
</tbody>
</table>
```

Parallelism reorders memory operations and removes none, so `work` is identical and only `time`
falls — from the same `Bool`. Rolling a nest makes the certificate a check on three subscript maps
instead of on the iteration space: flat from 64 points to 10⁹, against 58× at the largest size both
can be measured.

# What the method does not cover

```html
<table class="dgmt">
<thead><tr><th>boundary</th><th>why</th><th>what happens instead</th></tr></thead>
<tbody>
<tr><td>non-terminating programs</td><td><code>ParM</code> is inductive; Lean has no coinductive types</td><td>unrepresentable; <code>whileAtMost</code> is the only <code>while</code></td></tr>
<tr><td>locks, atomics, <code>critical</code></td><td>no such constructor exists</td><td>out of scope by construction, and reported as such</td></tr>
<tr><td>computed addresses <code>A[B[i]]</code></td><td>the syntactic footprint must claim all of <code>A</code></td><td>refused by <code>wfB</code>; the exact per-heap check still decides it</td></tr>
<tr><td>mirror-image branches</td><td><code>ifElse</code> widens to both arms</td><td><i>inconclusive</i> after 11 probed heaps, not a false claim</td></tr>
<tr class="gap"><td>a solver's <code>unsat</code></td><td>an external solver is not the Lean kernel</td><td>reported as <i>discharged by</i> z3 or cvc5, never as proved</td></tr>
</tbody>
</table>
```

Every refusal above is a *precision* loss, never a soundness one: across 28 labelled kernels the
false-acceptance cell is zero, and that is a build-failing gate.

# What was built

:::class "steps"
* One metatheorem — Bernstein independence at every fork implies equality of reachable outcomes under
  every schedule — proved once, over a program model where `par` is a constructor and races are
  absorbing.
* Two front ends over it: a surface language with a checker, a prover and a race explainer, and an
  MLIR reader that answers on a compiler's own representation.
* Programs discharge the obligation by `decide` on footprints, by a size-free kernel lemma, or by one
  certificate over subscript maps that is flat to 10⁹ iteration points.
:::

:::class "refs"
* Bernstein, *Analysis of Programs for Parallel Processing*, IEEE TEC 1966.
* Reynolds, *Toward a Grainless Semantics for Shared-Variable Concurrency*, FSTTCS 2004.
* Brookes, *A Semantics for Concurrent Separation Logic*, CONCUR 2004.
* de Moura and Ullrich, *The Lean 4 Theorem Prover and Programming Language*, CADE 28, 2021.
:::
