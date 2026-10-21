import VersoSlides
import Verso.Doc.Concrete
import Paralever
import Examples.Programs.MatMul
import Examples.Programs.SortBatches
import Examples.Programs.RowSums

set_option verso.code.warnLineLength 500
set_option verso.slides.panel false
set_option linter.unusedVariables false
set_option verso.slides.warnOnImage false

open VersoSlides
open Paralever

/- A `timeDay` inline role: renders the wall-clock date at the moment this doc is built (elaborated),
e.g. "21 July 2026" — invoke as `{timeDay}`·``. It re-runs whenever this file is recompiled, so a
fresh `lake build` / `lake exe slides` refreshes it. -/
open Verso Doc Elab ArgParse in
open Lean Elab Widget in
open Lean.Doc.Syntax in
@[role]
meta def timeDay : RoleExpanderOf Unit
  | (), _ => do
    let out ← IO.Process.run { cmd := "date", args := #["+%d %B %Y"] }
    let html := Verso.Output.Html.text false out.trimAscii.toString
    ``(Verso.Doc.Inline.other (VersoSlides.InlineExt.ofHtml $(quote html)) #[])

#doc (Slides) "Paralever" =>

# paralever




%%%
state := "title"
%%%

:::class "subheader"
Proving output equivalence of _parallel_ programs with _sequential_ programs — in Lean 4
:::

:::class "byline"
*Anirudh Gupta*
:::

:::class "event"
IISc Bengaluru · ISP-I · 4th-year BTech
:::

:::class "links"
[github.com/AnirudhG07/paralever](https://github.com/AnirudhG07/paralever)
:::

:::class "timeDay"
{timeDay}`·`
:::


# The fundemental Question for (truly) Parallelizing programs


```html
<div class="dgm tight">
  <div class="nd mono">paralever {
  [0] := 3; [1] := 4;
  %0 := [0]; [2] := %0 * %0;
  %1 := [1]; [3] := %1 * %1;
  %2 := [2]; %3 := [3];
  [4] := %2 + %3
}<em>nine statements, one core</em></div>
  <div class="arr lbl2">&#8594;<small>parallelize</small></div>
  <div class="nd mono blue">paralever {
  [0] := 3; [1] := 4;
  parallel { %0 := [0]; [2] := %0 * %0 }
           | { %1 := [1]; [3] := %1 * %1 };
  %2 := [2]; %3 := [3];
  [4] := %2 + %3
}<em> For both codes Output State = [3,4,9,16,25].</em></div>
</div>
```

We parallelize programs for GPU/TPU, etc. targetting True Parallelism in most cases. The primary question that arises:

```html
<div style="border: 2px solid currentColor; border-radius: 12px; text-align: center;">Is par = seq <b>correct</b>?<em> under every schedule</em></div>
```



:::class "notation"
*`seq`* — the statements run one after another, on one core. *`par`* — the branches of a
`parallel` block run at the same time, and the block ends when all of them have.
:::

# Overview

1. *Background* — Hoare triples, ∗-disjointness, and what CSL's soundness theorem gives you
2. *Our claim* — independent branches can be run either way, and the answer does not change
3. *Programs as data* — one branching constructor, and a footprint computed from the syntax
4. *The proof* — four pieces, and the schedule appears in exactly one of them
5. *The language* — memory, registers, one fork, and a rejected program that explains itself
6. *Examples* — a sum, a matmul, a merge sort, a neural net — one check each
7. *Automatic parallelization* — a `;`-chain in, a proved-equivalent tree out
8. *MLIR* — a benchmark in C gets a verdict without being translated by hand

# Part 1 · Background

:::class "section-break"
Hoare triples, ∗-disjointness, and what Concurrent Separation Logic (CSL)'s soundness theorem gives you
:::


# Why Hoare triples are not enough?

Consider the below counterexample:

```html
<div class="dgm tight">
  <div class="nd mono">C&#8321; : [p] := 5; y := [p]<em>write to [p], then read it back</em></div>
  <div class="nd mono">C&#8322; : [p] := 8<em>write to the same [p]</em></div>
  <div class="nd key">Let p points at x<em>so both commands write the cell holding x</em></div>
</div>
```

```html
<div class="fan">
  <div class="nd good">{true} C&#8321; {y = 5}</div>
  <div class="nd good">{true} C&#8322; {true}</div>
  <div class="nd good">{true} C&#8321;; C&#8322; {y = 5}<em>by sequencing, y = 5</em></div>
  <div class="nd bad">{true} C&#8321; &#8741; C&#8322; {y = 5}<em>false &#183; a schedule runs C&#8322; between the write and the read, leaving y = 8</em></div>
</div>
```

:::class "steps"
* A triple `{P} C {Q}` says that if `P` holds and `C` terminates then `Q` holds. It quantifies over
  the starting state and over nothing else — in particular not over what another thread does while
  `C` runs.
* So the first triple is proved as though its command ran alone. `y := [p]` reads back the value
  the command itself wrote, which is true of every run in which nothing else touches `[p]`.
* The schedule that runs `C₂` between that write and that read does touch `[p]`, so the assumption
  the proof was built on no longer holds, and `y` ends at 8.
* A triple has no way to say *this cell is mine*, so it cannot exclude that schedule. Ownership is
  the missing notion, and it is what separation logic adds.
:::

# Separation Logic's `∗`-disjointness

```html
<div class="fan">
  <div class="nd key">l &#8614; v<em>the heap cell <em>l</em> holds v &#183; exclusive</em></div>
  <div class="nd key">P &#8727; P&#8242;<em>the heap splits into two <b>disjoint-domain</b> pieces, one satisfying each</em></div>
</div>
```

```html
<div class="rulewrap"><div class="rule">
  <div class="prem">{P} C {Q} &nbsp;&nbsp;&nbsp; {P&#8242;} C&#8242; {Q&#8242;}</div>
  <div class="bar"></div>
  <div class="conc">{P &#8727; P&#8242;} &nbsp; C &#8741; C&#8242; &nbsp; {Q &#8727; Q&#8242;}</div>
  <div class="side">C modifies no variable free in P&#8242;, C&#8242;, Q&#8242;, and conversely &#183; O'Hearn, CONCUR 2004</div>
</div></div>
```

:::class "steps"
* `l ↦ v` says the heap is exactly one cell, `l`, and it holds `v`. Holding it is exclusive: no
  other assertion standing beside this one may mention `l`.
* `P ∗ P′` says the heap splits into two pieces whose domains are disjoint, one satisfying each
  side. The existence of that split is part of the claim, not a remark about it.
* Each premise of the rule mentions one thread, and the conclusion holds for every interleaving.
  Disjointness is what pays for that step: neither thread can reach a cell the other owns, so there
  is nothing for an interleaving to disturb.
* O'Hearn states this as two hypotheses — a thread accesses only what it owns, and at every moment
  the state partitions into the parts owned by each thread and by each resource.
:::

# Sharing comes back as a loan, and the rules are sound by a trace semantics



```html
<div class="rulewrap"><div class="rule">
  <div class="prem">{(P &#8727; RI&#8323;) &#8743; B} C {Q &#8727; RI&#8323;}</div>
  <div class="bar"></div>
  <div class="conc">{P} &nbsp; <b>with</b> r <b>when</b> B <b>do</b> C &nbsp; {Q}</div>
  <div class="side">each resource name r carries an invariant RI&#8323; &#183; two <b>with</b> regions for the same r never overlap in time</div>
</div></div>
```

:::class "steps"
* `r` is a *resource*: a name for a region of the heap that no thread owns. Every `r` carries an
  invariant `RI_r`, the assertion describing the states that region is allowed to be in.
* Outside a region a thread knows nothing about those cells. `with r when B do C` lends `RI_r` to
  the thread on entry; `C` may break it while it runs, and has to restore it before the region ends.
* `RI_r` must be *precise*, meaning it pins down one sub-heap rather than any of several. Without
  that the hand-back is undefined — the thread would not know how much of the heap it is returning.
* Brookes proves both rules sound in a semantics of action traces in which a racing step is a
  catastrophic error, so a program with a race proves nothing.
:::

```html
<div class="gbox thm">
  <div class="caplabel">Parallel Decomposition &#183; Brookes, CONCUR 2004, Thm. 21</div>
  If a trace of C&#8321; &#8741; C&#8322; runs from a state split as &#963;&#8321; &#8727; &#963;&#8322; and the components' footprints stay separate, then that trace is an <b>interleaving</b> of a trace of C&#8321; from &#963;&#8321; and a trace of C&#8322; from &#963;&#8322;, and the final states recombine as &#963;&#8321;&#8242; &#8727; &#963;&#8322;&#8242;.
</div>
```

The heap splits, and that split is also the hypothesis: it must already hold of `σ`. Two threads
reading `a₀` have no such split, and `C₁; C₂` is never mentioned.

:::notes
The conclusion is about the states, not only the traces: each thread's final heap `σᵢ′` is what
that thread alone produces from its own half, and `σ′` is their disjoint union. That is what makes
the disjoint-concurrency rule sound — `Q₁` holds of `σ₁′` and `Q₂` of `σ₂′`, so `Q₁ ∗ Q₂` holds of
`σ′`. The premise is a heap already written as `σ₁ ∗ σ₂` with each thread confined to its own half,
and two threads that both read `a₀` cannot be divided that way: whichever half holds `a₀`, the
other thread's local run steps outside its heap. Our hypothesis asks for no split, only Bernstein
independence, and our conclusion is the one this lemma does not state — that `C₁ ∥ C₂` and `C₁; C₂`
reach the same outcomes, in both directions, under every schedule.
:::

# ∗ forbids a shared read that nothing can go wrong with



```html
<div class="figwrap">
<svg viewBox="0 0 760 260" role="img" aria-label="two threads reading the same two cells and writing different cells">
  <defs>
    <marker id="ah" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#334155"/>
    </marker>
  </defs>
  <g font-family="ui-monospace, monospace" font-size="17" text-anchor="middle">
    <text x="380" y="26" font-size="19" fill="#1d4ed8">&#8741;</text>
    <rect x="70"  y="52" width="240" height="40" rx="7" fill="#eff6ff" stroke="#2563eb" stroke-width="2"/>
    <text x="190" y="78" fill="#0f172a">[c&#8320;] := [a&#8320;] + [a&#8321;]</text>
    <rect x="450" y="52" width="240" height="40" rx="7" fill="#eff6ff" stroke="#2563eb" stroke-width="2"/>
    <text x="570" y="78" fill="#0f172a">[c&#8321;] := [a&#8320;] &#8722; [a&#8321;]</text>
    <rect x="70"  y="190" width="70" height="36" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="105" y="214" fill="#0f172a">c&#8320;</text>
    <rect x="320" y="190" width="70" height="36" rx="5" fill="#f1f5f9" stroke="#0d9488" stroke-width="2"/><text x="355" y="214" fill="#0f172a">a&#8320;</text>
    <rect x="410" y="190" width="70" height="36" rx="5" fill="#f1f5f9" stroke="#0d9488" stroke-width="2"/><text x="445" y="214" fill="#0f172a">a&#8321;</text>
    <rect x="620" y="190" width="70" height="36" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="655" y="214" fill="#0f172a">c&#8321;</text>
  </g>
  <g stroke="#334155" fill="none" marker-end="url(#ah)">
    <line x1="340" y1="40" x2="200" y2="48"/><line x1="420" y1="40" x2="560" y2="48"/>
    <line x1="120" y1="94" x2="105" y2="186" stroke-width="2.2"/>
    <line x1="660" y1="94" x2="655" y2="186" stroke-width="2.2"/>
  </g>
  <g stroke="#0d9488" fill="none" stroke-dasharray="5 4" marker-end="url(#ah)">
    <line x1="230" y1="94" x2="345" y2="186"/><line x1="260" y1="94" x2="432" y2="186"/>
    <line x1="530" y1="94" x2="450" y2="186"/><line x1="500" y1="94" x2="368" y2="186"/>
  </g>
  <text x="105" y="178" font-size="13" fill="#334155" text-anchor="middle" font-style="italic">W</text>
  <text x="655" y="178" font-size="13" fill="#334155" text-anchor="middle" font-style="italic">W</text>
  <text x="380" y="252" font-size="14" fill="#0d9488" text-anchor="middle" font-style="italic">both branches read a&#8320; and a&#8321; (dashed); the writes (solid) are disjoint</text>
</svg>
</div>
```

:::class "steps"
* Each side needs `a₀ ↦ u`, so the conclusion needs `(a₀ ↦ u) ∗ (a₀ ↦ u) ⇒ false`.
* A resource `r` serializes the two reads instead of allowing them.
* Fractions do allow them: `a₀ ↦_{1/2} u` each, carried through every lemma.
* Bernstein checks writes only, so read-read is no conflict.
:::

```html
<div class="pullquote">
&ldquo;there is no way to prove the obviously valid formula &#8866; {z &#8614; 1} x:=[z] &#8741; y:=[z] {x = y = 1 &#8743; z &#8614; 1}, since the logic requires both processes to &lsquo;need&rsquo; to own the heap cell denoted by z, separately. Nevertheless, the trace semantics handles this issue (and this example) correctly, so here is a place where the semantics is ahead of the logic.&rdquo;
<span class="src">Brookes, <i>A semantics for concurrent separation logic</i>, CONCUR 2004</span>
</div>
```

:::notes
To dereference `a₀` the left premise must hold `a₀ ↦ u` and the right premise the same cell, and
one cell does not split into two pieces that each contain it — so the rule does not apply, to a
program whose answer no schedule can change. Handing `a₀` to a resource takes it out of both
preconditions, but then every read sits inside `with r do …` and two such regions never overlap in
time; matmul would put each element it reads into a critical region and give up the parallelism it
was written for. Fractional permission is the real repair, and it moves the cost into the
specifications: a fraction for every shared cell, threaded through every lemma.

This is O'Hearn's own argument, used there to show that `[10]:=42 ∥ [10]:=6` has no derivable
triple; pointed at reads it rejects a deterministic program instead. The claim is not that CSL
cannot verify this — with fractions it can. The claim is about the shape of the obligation, and
matrix multiplication is this example at scale: every row of `A` is read by every thread in a row
block.
:::

# Part 2 · Our claim



:::class "section-break"
Independent branches can be run either way, and the answer does not change
:::

One theorem about two programs, with a hypothesis the kernel evaluates — rather than a bound on one
program's postcondition.

# What the literature proves, and what it leaves open




```html
<div class="lineage">
  <div class="le">
    <div class="who">O'Hearn<span>CONCUR'04</span></div>
    <div class="thm"><code>{P₁}C₁{Q₁}</code>, <code>{P₂}C₂{Q₂}</code> &rArr; <code>{P₁∗P₂} C₁∥C₂ {Q₁∗Q₂}</code></div>
    <div class="miss">a rule about <i>triples</i> &mdash; says nothing about program equality</div>
  </div>
  <div class="le">
    <div class="who">Brookes<span>CONCUR'04 §5–7</span></div>
    <div class="thm">a trace of <code>C₁∥C₂</code> from <code>σ₁∗σ₂</code> with separate footprints <b>is an interleaving</b> of traces of <code>C₁</code> and <code>C₂</code></div>
    <div class="miss">projects <i>one</i> trace &mdash; not equality of outcome <i>sets</i></div>
  </div>
  <div class="le">
    <div class="who">Apt &amp; Olderog<span>textbook</span></div>
    <div class="thm"><code>C₁</code>, <code>C₂</code> share <b>no variables</b> &rArr; <code>C₁∥C₂ = C₁;C₂</code></div>
    <div class="miss">excludes shared reads, so excludes matmul; on paper</div>
  </div>
  <div class="le ours">
    <div class="who">this work<span>Lean 4</span></div>
    <div class="thm"><code>wfB s = true</code> &rArr; <code>execPar s ∥≡ execSeq s</code> &mdash; equality of outcome sets, arbitrary programs, kernel-checked</div>
    <div class="miss">the corollary everyone uses and nobody states</div>
  </div>
</div>
```

# Independence is Bernstein, computed from the syntax




```leanLibCode Paralever.Core.Access (package := paralever) (startLine := 64) (endLine := 66) -stretch
@[simp, grind .]
def Indep (f₁ f₂ : Footprint) : Prop :=
  Disjoint f₁.writes f₂.writes ∧ Disjoint f₁.writes f₂.reads ∧ Disjoint f₂.writes f₁.reads
```

:::class "steps"
* `w₁∩w₂ = w₁∩r₂ = w₂∩r₁ = ∅` — shared *reads* are allowed
* `∗` would forbid them, and so forbid `matmul`: disjoint `C[i*n+j]`, overlapping rows
* `footprintOf` is a fold over the syntax, so the check is `decide`, not a proof
:::

```html
<div class="dgm tight">
  <div class="nd good">reads 0,1 &#183; writes 2<em>thread 1</em></div>
  <div class="nd good">reads 0,1 &#183; writes 3<em>thread 2</em></div>
  <div class="arr lbl2">&#8594;<small>indepB = true</small></div>
  <div class="nd key">accepted<em>same cells read, different cells written</em></div>
</div>
```

# `WellFormed` is that check at every `par`, along the run




```leanLibCode Paralever.Core.Access (package := paralever) (startLine := 235) (endLine := 241) -stretch
def WellFormed {τ : Type} : ParM τ → State → Prop
  | .pure _,      _ => True
  | .read l k,    σ => WellFormed (k (σ l)) σ
  | .write l v k, σ => WellFormed (k ()) (σ.update l v)
  | .par cs k,    σ =>
      let r := runChilds cs σ
      IndepAll (childFootprints cs σ) ∧ WellFormedChilds cs σ ∧ WellFormed (k r.1) r.2
```

:::class "steps"
* `accesses p σ` is the footprint of running `p` from `σ`: the cells it reads and the cells it
  writes, as two lists.
* A `par` node asks for three things — the children's own footprints are pairwise independent, each
  child is itself well-formed, and so is the continuation from the heap the children leave.
* A `read` or `write` is never a condition; it only advances the heap the next check is measured
  against. All of the content sits at `par` nodes.
* Checking the outermost `par` alone is unsound, which is why the recursion goes to the bottom of
  the tree.
:::

:::notes
`WellFormed` mentions a heap `σ`, so as stated it is a predicate about one starting state.
`wfB` is the same condition with the `σ` removed — read off the syntax — and `wfB_wellFormed`
closes that gap: `wfB s = true` gives `WellFormed (execPar s ρ) σ` for every `ρ` and every `σ`.
That is the lemma the next slide's hypothesis rests on.
:::

# Independent branches agree with `p; q` under every schedule




```leanLibCode Lang.Core.Prog (package := paralever) (startLine := 549) (endLine := 550) -stretch
theorem par_seq_eq {s : ParProg} (h : wfB s = true) (ρ : Regs) (σ : State) :
    ParSeqEq (execPar s ρ) (execSeq s ρ) σ := by
```

:::class "steps"
* `ParSeqEq p q σ` — the two reach the *same outcome set* from `σ`, not one trace
* hypothesis is a `Bool` the kernel evaluates; conclusion quantifies over schedules
* `time_le` rides along: the parallel reading never needs more rounds
:::

The schedule does not appear in the obligation. Proved once, every program afterwards pays one
`decide` on a footprint rather than a proof about interleavings.

# Part 3 · Programs as data



:::class "section-break"
One branching constructor, and a footprint computed from the syntax
:::

`ParM` is an inductive type, so a program is a tree Lean can take apart; the obligation is a `Bool`
on two lists of addresses.

# `seq` is a spine; `par` is the only node that branches




```html
<div class="figwrap">
<svg viewBox="0 0 820 352" role="img" aria-label="the chain and the forked version as two vertical flows">
  <defs>
    <marker id="sp" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#94a3b8"/>
    </marker>
    <marker id="spI" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#4f46e5"/>
    </marker>
  </defs>
  <g font-size="15" text-anchor="middle" font-style="italic" fill="#475569">
    <text x="150" y="14">the ;-chain &#183; no branch, nothing to check</text>
    <text x="590" y="14">the forked version &#183; one branching node</text>
  </g>
  <g font-family="ui-monospace, monospace" font-size="14" text-anchor="middle" fill="#0f172a">
    <rect x="45" y="28"  width="210" height="28" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="150" y="47">[0] := 3</text>
    <rect x="45" y="82"  width="210" height="28" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="150" y="101">[1] := 4</text>
    <rect x="45" y="136" width="210" height="28" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="150" y="155">%0 := [0]; [2] := %0*%0</text>
    <rect x="45" y="190" width="210" height="28" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="150" y="209">%1 := [1]; [3] := %1*%1</text>
    <rect x="45" y="244" width="210" height="28" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="150" y="263">%2 := [2]; %3 := [3]</text>
    <rect x="45" y="298" width="210" height="28" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="150" y="317">[4] := %2 + %3</text>

    <rect x="485" y="28" width="210" height="28" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="590" y="47">[0] := 3</text>
    <rect x="485" y="82" width="210" height="28" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="590" y="101">[1] := 4</text>
    <rect x="545" y="126" width="90" height="26" rx="13" fill="#eef2ff" stroke="#4f46e5" stroke-width="2"/><text x="590" y="144" fill="#312e81">par</text>
    <rect x="398" y="178" width="184" height="28" rx="5" fill="#eff6ff" stroke="#2563eb" stroke-width="2"/><text x="490" y="197" font-size="12.5">%0 := [0]; [2] := %0*%0</text>
    <rect x="598" y="178" width="184" height="28" rx="5" fill="#eff6ff" stroke="#2563eb" stroke-width="2"/><text x="690" y="197" font-size="12.5">%1 := [1]; [3] := %1*%1</text>
    <rect x="485" y="244" width="210" height="28" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="590" y="263">%2 := [2]; %3 := [3]</text>
    <rect x="485" y="298" width="210" height="28" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="590" y="317">[4] := %2 + %3</text>
  </g>
  <g stroke="#94a3b8" stroke-width="1.6" fill="none" marker-end="url(#sp)">
    <line x1="150" y1="56"  x2="150" y2="79"/>
    <line x1="150" y1="110" x2="150" y2="133"/>
    <line x1="150" y1="164" x2="150" y2="187"/>
    <line x1="150" y1="218" x2="150" y2="241"/>
    <line x1="150" y1="272" x2="150" y2="295"/>
    <line x1="590" y1="56"  x2="590" y2="79"/>
    <line x1="590" y1="110" x2="590" y2="123"/>
  </g>
  <g stroke="#4f46e5" stroke-width="1.8" fill="none">
    <path d="M 590 152 L 590 164 L 490 164 L 490 175" marker-end="url(#spI)"/>
    <path d="M 590 152 L 590 164 L 690 164 L 690 175" marker-end="url(#spI)"/>
    <path d="M 490 206 L 490 224 L 690 224 L 690 206"/>
    <path d="M 590 224 L 590 241" marker-end="url(#spI)"/>
  </g>
  <text x="590" y="238" font-size="12" text-anchor="middle" font-style="italic" fill="#4f46e5">join</text>
  <g font-size="13" fill="#2563eb" text-anchor="middle">
    <text x="490" y="221" font-size="12">writes &#123;2&#125;, reads &#123;0&#125;</text>
    <text x="690" y="221" font-size="12">writes &#123;3&#125;, reads &#123;1&#125;</text>
  </g>
</svg>
</div>
```

Same leaves, same order, one node different. `paralever { s₁; …; sₙ }` is right-nested `seq`, so
every program is a spine until a `parallel` block puts a fork in it.

:::notes
This is the slide that teaches the two constructors. `seq` threads the heap and the register file
from one child to the next; `par` hands every child the same starting state and joins. Everything
later — the check, the theorem, the rewrite — is about `par` nodes only.
:::

# Nobody states what a program touches — `footprintOf` evaluates it



```html
<div class="nd mono plain wide">#eval ParProg.footprintOf (matmul 2)

{ reads  := [0, 4, 1, 6, 0, 5, 1, 7, 2, 4, 3, 6, 2, 5, 3, 7],
  writes := [8, 9, 10, 11] }<em>two lists of addresses, obtained by reduction &#8212; not an annotation, not a lemma</em></div>
```

:::class "steps"
* `accesses p σ` is the footprint a run actually has. It depends on `σ`, so a claim about it is a
  claim about every heap.
* `footprintOf s` reads the same two lists off the syntax tree and mentions no heap at all, so
  Lean evaluates it.
* `execPar_accesses_sub` is the one thing that needed proving, and it is proved once for all
  programs: the computed lists contain the cells any run touches.
:::

```leanLibCode Lang.Core.Prog (package := paralever) (startLine := 306) (endLine := 307) -stretch
theorem execPar_accesses_sub (s : ParProg) (ρ : Regs) (σ : State) :
    (accesses (execPar s ρ) σ).Sub (footprintOf s) := execPar_accesses_sub_all.1 s ρ σ
```

:::notes
So a user's obligation is a `Bool` the kernel computes, never a lemma they write: `by decide` on
`wfB`, which runs `footprintOf` and then the pairwise independence test on the lists above.
Containment in one direction is all that is needed — an over-approximation costs precision and
never soundness. The three cases: a literal address gives an exact footprint, a computed address
`A[B[i]]` gives the whole array, and a branch gives the union of its two sides.
`Examples/Language/Scatter.lean` is where that over-approximation bites: `raceSites` finds no race and
`wfB` still refuses.
:::

# `wfB` checks every `par`, not just the top




```html
<div class="dgm col tight">
  <div class="nd mono bad wide">parallel { [0] := 1 }
         | { parallel { [1] := 2 } | { %0 := [1] } }<em>outer footprints {0} and {1} are disjoint — a top-level check passes</em></div>
  <div class="arr">&#9660;</div>
  <div class="nd key wide">the <b>inner</b> `par` writes and reads `[1]` concurrently<em>`wfB` recurses, so it rejects this</em></div>
</div>
```

```html
<div class="figwrap">
<svg viewBox="0 0 760 290" role="img" aria-label="a par whose second child is itself a racy par">
  <defs>
    <marker id="wf" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#4f46e5"/>
    </marker>
    <marker id="wfr" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#dc2626"/>
    </marker>
  </defs>
  <g font-family="ui-monospace, monospace" font-size="16" text-anchor="middle" fill="#0f172a">
    <rect x="320" y="20" width="90" height="28" rx="14" fill="#eef2ff" stroke="#4f46e5" stroke-width="2"/><text x="365" y="39" fill="#312e81">par</text>
    <rect x="80" y="110" width="170" height="30" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="165" y="130">[0] := 1</text>
    <rect x="455" y="106" width="90" height="28" rx="14" fill="#fef2f2" stroke="#dc2626" stroke-width="2.4"/><text x="500" y="125" fill="#991b1b">par</text>
    <rect x="360" y="196" width="150" height="30" rx="5" fill="#fef2f2" stroke="#dc2626" stroke-width="2"/><text x="435" y="216">[1] := 2</text>
    <rect x="550" y="196" width="150" height="30" rx="5" fill="#fef2f2" stroke="#dc2626" stroke-width="2"/><text x="625" y="216">%0 := [1]</text>
  </g>
  <g stroke="#4f46e5" stroke-width="1.8" fill="none" marker-end="url(#wf)">
    <path d="M 365 48 L 365 80 L 165 80 L 165 107"/>
    <path d="M 365 48 L 365 80 L 500 80 L 500 103"/>
  </g>
  <g stroke="#dc2626" stroke-width="1.8" fill="none" marker-end="url(#wfr)">
    <path d="M 500 134 L 500 166 L 435 166 L 435 193"/>
    <path d="M 500 134 L 500 166 L 625 166 L 625 193"/>
  </g>
  <g font-size="14" font-style="italic">
    <text x="165" y="162" text-anchor="middle" fill="#475569">writes &#123;0&#125;</text>
    <text x="640" y="95" text-anchor="middle" fill="#475569">writes and reads &#123;1&#125;</text>
    <text x="365" y="68" text-anchor="middle" fill="#0d9488" font-size="13">&#123;0&#125; and &#123;1&#125; are disjoint &#8212; a top-level check PASSES</text>
    <text x="530" y="252" text-anchor="middle" fill="#dc2626">writes &#123;1&#125; against reads &#123;1&#125; &#8212; a race, one level down</text>
  </g>
</svg>
</div>
```

```leanLibCode Lang.Core.Prog (package := paralever) (startLine := 187) (endLine := 198) -stretch
def wfB : ParProg → Bool
  | .load _ _  => true
  | .store _ _ => true
  | .set _ _   => true
  | .seq a b   => wfB a && wfB b
  | .par ss    => indepAllB (threadFootprints ss) && wfAllB ss
  | .label _ s => wfB s
  | .loadAt _ _ _  => true
  | .storeAt _ _ _ => true
  -- either branch may run, so both must be well-formed
  | .ifElse _ t e  => wfB t && wfB e
  | .synchronize         => true
```

A check that only looked at the outermost fork would be unsound, which is why `wfB` is defined by
recursion on the whole tree.

# Races stop at `wrong`, so the hypothesis is load-bearing




```html
<div class="dgm tight">
  <div class="nd mono blue">[0] := 1
 &#8741;
%0 := [0]<em>one write, one read, one cell</em></div>
  <div class="arr lbl2">&#8594;<small>run</small></div>
  <div class="nd bad">wrong<em>absorbing — Reynolds' grainless semantics</em></div>
  <div class="arr lbl2">&#8594;<small>so</small></div>
  <div class="nd key">wfB = false<em>measured, not assumed</em></div>
</div>
```

:::class "steps"
* racy programs are *excluded*, not silently assumed away — so the atomic grain is irrelevant
* standing obligation: exhibit `p`, `q` where the conclusion *fails*, so the hypothesis is not free
* the loop-carried case `A[i] := A[i-1] + 1` must stay *unprovable*
:::

# Part 4 · The proof



:::class "section-break"
Four pieces, and the schedule appears in exactly one of them
:::

Where the difficulty actually is, and the program on which this equality is false.

# The proof is four steps, and only one is about schedules




```html
<div class="figwrap">
<svg viewBox="0 0 880 400" role="img" aria-label="par_seq_eq resting on three theory modules and carrying the cost theorem">
  <defs>
    <marker id="pf" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#4f46e5"/>
    </marker>
  </defs>
  <rect x="300" y="16" width="280" height="44" rx="8" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.6"/>
  <text x="440" y="37" text-anchor="middle" font-family="ui-monospace, monospace" font-size="17" fill="#312e81">par_seq_eq</text>
  <text x="440" y="53" text-anchor="middle" font-size="12" font-style="italic" fill="#475569">Lang/Core.lean</text>

  <g font-size="13.5" text-anchor="middle">
    <rect x="30" y="128" width="250" height="110" rx="8" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/>
    <text x="155" y="150" font-family="ui-monospace, monospace" font-size="15" fill="#0f172a">Decomposition</text>
    <text x="155" y="176" fill="#334155">a <tspan font-family="ui-monospace, monospace">par</tspan> node splits into</text>
    <text x="155" y="194" fill="#334155">per-branch steps on</text>
    <text x="155" y="212" fill="#334155">disjoint cells</text>
    <text x="155" y="232" font-size="12" font-style="italic" fill="#0d9488">Brookes, CONCUR'04 §5&#8211;7</text>

    <rect x="315" y="128" width="250" height="110" rx="8" fill="#eff6ff" stroke="#2563eb" stroke-width="2.4"/>
    <text x="440" y="150" font-family="ui-monospace, monospace" font-size="15" fill="#0f172a">WellFormedCanonical</text>
    <text x="440" y="176" fill="#1e3a5f">every reachable outcome</text>
    <text x="440" y="194" fill="#1e3a5f">of a well-formed <tspan font-family="ui-monospace, monospace">par</tspan></text>
    <text x="440" y="212" fill="#1e3a5f">is ONE canonical outcome</text>
    <text x="440" y="232" font-size="12" font-style="italic" fill="#0d9488">Reynolds, grainless semantics</text>

    <rect x="600" y="128" width="250" height="110" rx="8" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/>
    <text x="725" y="150" font-family="ui-monospace, monospace" font-size="15" fill="#0f172a">Sequentialize</text>
    <text x="725" y="176" fill="#334155">that canonical outcome</text>
    <text x="725" y="194" fill="#334155">IS the one <tspan font-family="ui-monospace, monospace">p; q</tspan></text>
    <text x="725" y="212" fill="#334155">produces</text>
    <text x="725" y="232" font-size="12" font-style="italic" fill="#0d9488">Bernstein, 1966</text>
  </g>

  <text x="440" y="112" text-anchor="middle" font-size="13" font-style="italic" fill="#2563eb">the schedule appears here, and in neither of the others</text>

  <g stroke="#4f46e5" stroke-width="1.8" fill="none" marker-end="url(#pf)">
    <path d="M 440 60 L 440 84 L 155 84 L 155 125"/>
    <path d="M 440 60 L 440 125"/>
    <path d="M 440 60 L 440 84 L 725 84 L 725 125"/>
  </g>
  <g stroke="#94a3b8" stroke-width="1.6" fill="none" stroke-dasharray="5 4">
    <path d="M 155 238 L 155 284 L 440 284"/>
    <path d="M 725 238 L 725 284 L 440 284"/>
    <path d="M 440 238 L 440 300"/>
  </g>
  <rect x="245" y="306" width="390" height="64" rx="8" fill="#f1f5f9" stroke="#0d9488" stroke-width="2"/>
  <text x="440" y="328" text-anchor="middle" font-family="ui-monospace, monospace" font-size="15" fill="#0f172a">Cost &#183; Lib/Cost.lean</text>
  <text x="440" y="350" text-anchor="middle" font-size="13.5" fill="#334155">time (par ps) = foldr max &#8212; the max is DERIVED</text>
  <text x="440" y="364" text-anchor="middle" font-size="12" font-style="italic" fill="#475569">from the same independence hypothesis, not assumed</text>
</svg>
</div>
```

`ParM` is a nested inductive, so Lean's `induction` refuses it: every step runs through
`ParM.mutualInduction`, and the N-ary case is an induction on the children list.

# The difficulty, on two children



```html
<div class="dgm tight">
  <div class="nd mono">p = write 0 1
q = read 1 (&#955;v. write 2 v)<em>disjoint: p writes {0}, q reads {1} and writes {2}</em></div>
  <div class="arr lbl2">&#8594;<small>two readings</small></div>
  <div class="dgm col tight">
    <div class="nd good">runSeq measures q at &#963;[0&#8614;1]<em>after p has run</em></div>
    <div class="nd bad">a real schedule may run q at &#963;<em>before p has run</em></div>
  </div>
</div>
```

:::class "steps"
* these are *different heaps*, so the two readings of `q` are a priori different runs
* independence is what makes them agree: `q` reads `[1]`, `p` writes `[0]`, so the cell `q` looks at
  holds the same value in both
* the induction therefore carries the footprint along with the equality — one level down, the
  footprint conjunct is what pins the replayed heap to the right one
:::

The theorem is that every reachable terminal configuration of a well-formed `par` is *the same
one*, and `runSeq` names it. The schedule enters the proof here and nowhere else.

# Every configuration a schedule reaches computes the same `runSeq`




```leanLibCode Paralever.Theory.WellFormedCanonical (package := paralever) (startLine := 1462) (endLine := 1464) -stretch
theorem wellFormed_canonical {τ : Type} (p : ParM τ) :
    ∀ σ r σ', WellFormed p σ → (Reaches (.run p σ) (.run (.pure r) σ') ↔ (r, σ') = runSeq p σ) :=
  wellFormed_canonical_all.1 p
```

:::class "steps"
* One step leaves `runSeq P σ` unchanged, and can only shrink the footprint — `step_combined`.
* One step keeps `WellFormed`, whichever branch moved — `WellFormed_preserved`.
* Iterate along the whole chain: every reachable `P', σ'` has `runSeq P' σ' = runSeq P σ` —
  `runSeq_invariant_chain`.
* At a `.pure r` endpoint `runSeq` is `(r, σ')`, which gives `(r, σ') = runSeq P σ`: the `→`.
* For `←`, run child 1 to completion, then child 2, then step into the continuation —
  `reachesChilds_canonical`.
:::

:::notes
Step 1 is where independence does the work, and it is the only hard case. The branch that moves
*second* is replayed against a heap `runSeq` never measured it from. `step_locality` says a step
replays unchanged between two heaps that agree outside a set of cells; `Indep` says the branch that
moved writes nothing the other one reads or writes, so the two heaps do agree outside that set; and
pinning the replayed heap down exactly needs the footprint conjunct of this very induction, one
level down. That is why `step_combined` proves the outcome and the footprint together rather than as
two lemmas — each half needs the other.

The `←` direction needs no induction hypothesis about schedules at all: it exhibits one schedule.
Running a child to completion is this same theorem one level down, which is why the two halves are
mutually inductive.
:::

# `wfB` gives well-formedness at every heap, by one induction




```leanLibCode Lang.Core.Prog (package := paralever) (startLine := 467) (endLine := 468) -stretch
theorem wfB_wellFormed {s : ParProg} (h : wfB s = true) (ρ : Regs) (σ : State) :
    WellFormed (execPar s ρ) σ := wfB_wellFormed_all.1 s h ρ σ
```

:::class "steps"
* Induction over the syntax. `load`, `store`, `set` are `trivial` — only `par` carries a condition.
* At a `par`: `indepAllB` held of the *computed* footprints, and `Indep` is antitone, so it holds of
  the real ones at `σ` — `indepAll_childFootprints`.
* The sequential side has no `par` node, so its `WellFormed` is `True` by structure —
  `wfB_wellFormedSeq_all`.
* Hand-written `ParM` instead of a `ParProg`: `WellFormed_par_intro` asks for the same three
  obligations, proved rather than decided.
:::

:::notes
This is the only place the quantifier over heaps is discharged, and it is discharged once, in the
library: `σ` is universally quantified in the statement, so a program's own obligation never
mentions a heap. That is what makes `by decide` sufficient afterwards.

The antitonicity step is the one worth saying aloud. `execPar_accesses_sub` gives
`accesses (execPar s ρ) σ ⊆ footprintOf s`, and `Indep.mono_left`/`mono_right` say independence
survives shrinking either side — so a bound that passes the test is enough, and a data-dependent
address contributing its whole array is sound for exactly this reason.

`Examples/Programs/SharedReads.lean` is the hand-proved route: `wellFormed_minmax` discharges the three
obligations for `findMin ∥ findMax`, where both branches read all three input cells.
:::

# Where this equality is false: one shared resource



```html
<div class="dgm tight">
  <div class="nd mono bad">observer = write 1 7 (&#955;_. read 0)
mutator  = write 0 99<em>Examples/Races/Caught.lean &#183; &#963;&#8320; has cell 0 = 1</em></div>
  <div class="arr lbl2">&#8594;<small>par</small></div>
  <div class="nd bad">y = 99<em>mutator ran first &#183; <code>par_reaches</code></em></div>
  <div class="arr lbl2">&#8594;<small>seq</small></div>
  <div class="nd good">y = 1<em>only outcome &#183; <code>seq_runSeq</code></em></div>
</div>
```

:::class "steps"
* put both accesses inside `with r do …` and *CSL proves the program*, with `RI_r = ∃v. 10 ↦ v`;
  by Brookes's corollary it is race free
* race freedom is strictly weaker than determinism: the `∥` rule joins postconditions with `∗`,
  which records no ordering — *the rule is designed to forget the schedule*
* so `ParM` has no resource, no lock, and no unstructured `fork`, and the conclusion would be false
  if it had — `not_parSeqEq` proves the failure, `not_indepAll` refutes the hypothesis
:::

Both sides terminate normally here and simply disagree, which is the case a reader is entitled to
worry about.

# `max` at a fork is derived, not assumed



```leanLibCode Lang.Core.Cost (package := paralever) (startLine := 88) (endLine := 89) -stretch
theorem time_le {s : ParProg} (h : wfB s = true) (ρ : Regs) (σ : State) :
    time (execPar s ρ) σ ≤ time (execSeq s ρ) σ := time_execPar_le_all.1 s ρ σ h
```

:::class "steps"
* `work` counts memory operations and is *unchanged* by forking — `work_par_eq_seq`
* `time` counts *rounds*, where a round advances every ready child by one step
* nothing in the cost semantics stipulates `max` at a fork: it falls out of the same independence
  hypothesis, on the same `Bool` — and `time_par_lt_seq_single` makes the inequality strict when both
  branches do work
:::

Conflating work with time is the usual mistake. Parallelism buys nothing in total operations, and the
theorem says so.

# Part 5 · The language



:::class "section-break"
Memory, registers, one fork — and the check run on user code
:::

`ParProg` is the surface syntax a user writes; `wfB` is the same obligation, decided.

# The language: memory, registers, and one fork




```html
<div class="dgm col tight">
  <div class="nd mono plain wide">[l] := e        %n := [l]        %n := e
parallel { … } | { … }        if (c) { … } else { … }
for i in n { … }        parfor i in n { … }        while (c) in n { … }<em>`[` and `%` reserve no tokens — surface syntax is global in Lean</em></div>
</div>
```

```html
<div class="ladder">
  <div class="tier"><b>literal address</b> &nbsp; <code>[2] := %0</code> &nbsp;&#183;&nbsp; footprint is <i>exact</i></div>
  <div class="tier"><b>computed address</b> &nbsp; <code>A[B[i]]</code> &nbsp;&#183;&nbsp; footprint is the whole array</div>
  <div class="tier"><b>branch</b> &nbsp; <code>if c {…} else {…}</code> &nbsp;&#183;&nbsp; footprint is the branch <i>union</i></div>
</div>
```

Over-approximation costs precision, never soundness: `execPar_accesses_sub` proves the computed
footprint contains every cell actually touched, at every heap.

# Question c: a user-written `parallel` is checked, not trusted




```html
<div class="dgm tight">
  <div class="nd mono bad">parallel { [0] := 1 }
         | { %0 := [0]; [1] := %0 }<em>store x on one core, load x on another</em></div>
  <div class="arr lbl2">&#8594;<small>decide</small></div>
  <div class="nd key">wfB = false<br/><code>block [·,·]</code> = true<em>the only legal placement is in sequence</em></div>
</div>
```

:::class "steps"
* this is the configuration the whole data-race literature is about
* our rewrite can never *build* it: a RAW edge puts the two in one thread
* when the user writes it, `wfB` is the checker — and rejects
:::

# A rejected program explains itself


```html
<div class="figwrap">
<svg viewBox="0 0 800 250" role="img" aria-label="the scan proposes conflicting locations and the aimed search realizes one">
  <defs>
    <marker id="rs" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#4f46e5"/>
    </marker>
  </defs>
  <rect x="310" y="10" width="180" height="32" rx="7" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/>
  <text x="400" y="32" text-anchor="middle" font-family="ui-monospace, monospace" font-size="15" fill="#0f172a">wfB p = false</text>

  <rect x="60" y="92" width="300" height="74" rx="8" fill="#eff6ff" stroke="#2563eb" stroke-width="2.2"/>
  <text x="210" y="114" text-anchor="middle" font-family="ui-monospace, monospace" font-size="15" fill="#0f172a">phase 1 &#183; raceSites</text>
  <text x="210" y="134" text-anchor="middle" font-size="13.5" fill="#1e3a5f">walks the tree once and names</text>
  <text x="210" y="152" text-anchor="middle" font-size="13.5" fill="#1e3a5f">the conflicting locations</text>

  <rect x="440" y="92" width="300" height="74" rx="8" fill="#f1f5f9" stroke="#0d9488" stroke-width="2.2"/>
  <text x="590" y="114" text-anchor="middle" font-family="ui-monospace, monospace" font-size="15" fill="#0f172a">phase 2 &#183; findWrongGuided</text>
  <text x="590" y="134" text-anchor="middle" font-size="13.5" fill="#115e59">a bounded search, aimed at exactly</text>
  <text x="590" y="152" text-anchor="middle" font-size="13.5" fill="#115e59">those locations</text>

  <rect x="230" y="204" width="340" height="34" rx="7" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.2"/>
  <text x="400" y="226" text-anchor="middle" font-family="ui-monospace, monospace" font-size="14.5" fill="#312e81">follow_sound : Reaches c wrong</text>

  <g stroke="#4f46e5" stroke-width="1.8" fill="none" marker-end="url(#rs)">
    <path d="M 400 42 L 400 66 L 210 66 L 210 89"/>
    <path d="M 360 129 L 437 129"/>
    <path d="M 590 166 L 590 186 L 400 186 L 400 201"/>
  </g>
  <g font-size="13" font-style="italic" text-anchor="middle">
    <text x="210" y="184" fill="#2563eb">empty list &#8658; race free, by raceSites_nil_iff</text>
    <text x="398" y="120" fill="#475569" font-size="12">targets</text>
  </g>
</svg>
</div>
```

:::class "steps"
* the scan *is* the obligation, so an empty site list is the race-freedom proof — a false negative
  would be a bug in `raceSites`, not a tuning matter
* a wrong guess in phase 2 cannot produce a wrong claim: `follow_sound` turns any schedule that
  replays into a `Reaches` proof, so a bad guess merely finds nothing
* aiming is what makes it cheap — on `three 8`, three threads where the middle one is innocent,
  blind search takes *2.7 s* and the aimed search *2 ms*
:::

```html
<div class="nd mono plain wide">step:thread  action          state
0:T0         write [10] &#8592; 1  10&#8614;1, 9&#8614;0, 20&#8614;0
1:T1         write [20] &#8592; 1  10&#8614;1, 9&#8614;0, 20&#8614;1
2:T1         write [9] &#8592; 2   pending
2:T0         write [9] &#8592; 1   pending
Parallel aborts at Step 2. Reason: T0, T1 write to: &#123;9&#125;.
Parallel: 9&#8614;1          Sequential: 9&#8614;2<em>`explainProg late σ₀` &#183; the counterexample is an execution, so the report is one</em></div>
```

# A data race, and the report it produces

:::class "two-col"
```leanLibCode Examples.Races.Report (package := paralever) (startLine := 23) (endLine := 27) -stretch
def late : Prog :=
  .par (.seq (.wr 10 1) (.seq (.wr 11 1) (.wr 9 1)))
       (.seq (.wr 20 1) (.seq (.wr 21 1) (.wr 9 2)))

#eval IO.println (explainProg late σ0)
```

```html
<div class="shotbox">
  <img src="assets/race-report.png" alt="the race report as the infoview renders it"/>
  <div class="cap">assets/race-report.png</div>
</div>
```
:::

Both sides do real work before colliding on their last write, so the race is not at the first step —
which is what makes aiming the search worth having. `wellFormedB` is `false`, and the report is the
interleaving that realizes it.

# Part 6 · Examples

:::class "section-break"
Four programs, in increasing order of what they need
:::

A read-only sum, then overlapping reads, then recursion, then an in-place update — and the same two
lines discharge every one of them.

# A sum: shared reads, and nothing written twice

```leanLibCode Examples.Programs.SumArray (package := paralever) (startLine := 38) (endLine := 42) -stretch
def sumRangeSeq (chunks : ChunkPlan) : ParM (List Int) := ParM.seqAll (chunks.map sumRange)

/-! ### par -/

def sumRangePar (chunks : ChunkPlan) : ParM (List Int) := ParM.parAll (chunks.map sumRange)
```

:::class "steps"
* one thread per chunk, each folding `.read l` over its own locations — *no thread writes anything*,
  so Bernstein's three clauses are vacuous and `∗`-disjointness would still have to split the array
* `wellFormed_sumRangePar` holds for *any* `ChunkPlan`, including uneven ones, and any state — no
  `decide`, so it does not care how long the array is
* strictly fewer rounds once two chunks are nonempty (`time_lt`), at identical `work`
:::

```html
<div class="dgm tight">
  <div class="nd mono">chunks = [[0,1,2], [3], [4,5,6,7]]<em>uneven on purpose</em></div>
  <div class="arr lbl2">&#8594;<small>runSeq</small></div>
  <div class="nd good">[6, 4, 26]<em>by decide, on A = [1..8]</em></div>
</div>
```

The obligation is a `Bool` the kernel evaluates; `par_seq_eq` supplies the rest.

# A matmul: the reads overlap heavily, and that is the point

```leanLibCode Examples.Programs.MatMul (package := paralever) (startLine := 185) (endLine := 193) -stretch
def matmul (n : Nat) : ParProg :=
  ParProg.parEach (gridIdx n n) fun ij =>
    ParProg.block
      ([ paralever { %2 := 0 } ]
        ++ (List.range n).map (fun k => paralever {
              %0 := [ij.1 * n + k];
              %1 := [n * n + (k * n + ij.2)];
              %2 := %2 + %0 * %1 })
        ++ [ paralever { [n * n + n * n + (ij.1 * n + ij.2)] := %2 } ])
```

```html
<div class="nd mono plain wide">parallel {
  thread 0 { t2 := 0; t0 := M[0]; t1 := M[4]; t2 := (t2 + (t0 * t1));
                      t0 := M[1]; t1 := M[6]; t2 := (t2 + (t0 * t1)); M[8] := t2; }
  thread 1 { t2 := 0; t0 := M[0]; t1 := M[5]; t2 := (t2 + (t0 * t1));
                      t0 := M[1]; t1 := M[7]; t2 := (t2 + (t0 * t1)); M[9] := t2; }
  &#8230;
}<em>what it lowers to at n = 2 — threads 0 and 1 both read M[0] and M[1], row 0 of A</em></div>
```

The accumulator is a *register*, so a thread's whole write set is the one cell `C[i,j]`. That is what
lets different cells read overlapping rows and columns — and it is the program `∗`-disjointness
rejects outright.

```leanLibCode Examples.Programs.MatMul (package := paralever) (startLine := 216) (endLine := 222) -stretch
example : ParProg.wfB (matmul 2) = true := by decide
example : ParProg.wfB (matmul 3) = true := by decide

/-- …and the equivalence follows with nothing further to supply. -/
theorem par_seq_eq_2 (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar (matmul 2) ρ) (ParProg.execSeq (matmul 2) ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ
```

# A merge sort: the same recursion twice, `parPair` against `seqPair`

```leanLibCode Examples.Programs.MergeSort (package := paralever) (startLine := 23) (endLine := 29) -stretch
def mergeSortPure : List Int → List Int
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
      let xs := x :: y :: rest
      let mid := xs.length / 2
      mergePure (mergeSortPure (xs.take mid)) (mergeSortPure (xs.drop mid))
```

```leanLibCode Examples.Programs.MergeSort (package := paralever) (startLine := 74) (endLine := 81) -stretch
def mergeSortPar (N : Nat) : Nat → Nat → ParM Unit
  | lo, hi =>
      if _h : hi - lo ≤ 1 then .pure ()
      else
        let mid := lo + (hi - lo) / 2
        ParM.bind (ParM.parPair (mergeSortPar N lo mid) (mergeSortPar N mid hi)) (fun _ =>
          ParM.bind (mergeStep mid hi N (hi - lo) lo mid lo) (fun _ =>
            copyBack N (hi - lo) lo lo))
```

:::class "steps"
* `mergeSortSeq` is the same definition with `seqPair` for `parPair` — nothing else differs
* here the obligation cannot be `decide`d: the recursion is in `N`, `lo`, `hi`, so independence comes
  from an *interval* argument — the two halves touch `[lo,mid)` and `[mid,hi)`, which are disjoint
* `mergeSortPar_wellformed N lo hi (hi ≤ N) σ` holds for every range and every heap, and
  `seq_eq_par` follows for the whole recursion rather than the top split
:::

`#eval` on `σ₄ = [5,3,8,1]` agrees with `mergeSortPure [5,3,8,1]` — the pure function is the spec,
and the check is a `#guard` in the file.

# A neural net: layers in sequence, threads in parallel, weights updated in place

```leanLibCode Examples.Language.NeuralNet (package := paralever) (startLine := 41) (endLine := 55) -stretch
/-- Forward pass: convolution, ReLU, dense layer. -/
def forward : ParProg :=
  ParProg.block
    [ ParProg.conv1dK 6 3 X CW C
    , ParProg.mapK 6 C Rl (fun v => AExp.max v (.lit 0))
    , ParProg.denseK 2 6 W2 Rl B2 Y ]

/-- One SGD step: forward, then the error, then an in-place weight update with learning rate
`1 / lrDen`. The update's thread `(i,j)` reads and writes `W[i,j]` *in place* — admissible only
because each thread owns its own cell. -/
def trainStep (lrDen : Int) : ParProg :=
  ParProg.block
    [ forward
    , ParProg.zipK 2 Y T E (fun y t => y - t)
    , ParProg.outerUpdateK 2 6 W2 E Rl lrDen ]
```

:::class "steps"
* every `conv1dK` thread reads the whole weight array *and* its own window — two kinds of read
  sharing at once, and neither costs anything, because `Indep` constrains writes only
* the layout is *declared*, not addressed: `Layout.of` assigns the bases, so the disjointness the
  net depends on holds by construction — §5 of the file shows the bug that used to be writeable
* `trainStep`'s update thread `(i,j)` reads and writes `W[i,j]` in place, which is admissible
  exactly because each thread owns its own cell
:::

```html
<div class="stats">
  <div class="stat">82<small>memory operations, either way</small></div>
  <div class="stat">23<small>rounds, parallel</small></div>
  <div class="stat">82<small>rounds, sequential</small></div>
  <div class="stat">36<small>squared error after 4 epochs, from 1224</small></div>
</div>
```

`forward_par_seq_eq` and `forward_time_le` are both `by decide` on the same `Bool`.

# Part 7 · Automatic parallelization



:::class "section-break"
A `;`-chain in, a proved-equivalent tree out
:::

The analysis is untrusted and the gate is proved, so the pass needs no hypothesis — and the depth it
reaches is measured against the dependence DAG's own lower bound.

# Question a: dependences come from one scoreboard pass




```html
<div class="ladder">
  <div class="tier"><strong>unit i reads l</strong> edge <code>lastWriter[l] &#8594; i</code> &#183; then <code>readers[l] += i</code> &nbsp;<em>RAW &#183; W &#8745; R</em></div>
  <div class="tier"><strong>unit i writes l</strong> edge <code>lastWriter[l] &#8594; i</code> &nbsp;<em>WAW &#183; W &#8745; W</em></div>
  <div class="tier"><strong>&#8230;and</strong> edge <code>r &#8594; i</code> for every <code>r &#8712; readers[l]</code>, then <code>lastWriter[l] := i</code>, <code>readers[l] := []</code> &nbsp;<em>WAR &#183; R &#8745; W</em></div>
</div>
```

```html
<div class="figwrap">
<svg viewBox="0 0 740 180" role="img" aria-label="four units and the dependence edges one pass finds">
  <defs>
    <marker id="dg" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#2563eb"/>
    </marker>
  </defs>
  <g font-family="ui-monospace, monospace" font-size="15" text-anchor="middle" fill="#0f172a">
    <rect x="30"  y="64" width="120" height="34" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="90"  y="86">[0] := 1</text>
    <rect x="210" y="64" width="120" height="34" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="270" y="86">%0 := [0]</text>
    <rect x="390" y="64" width="120" height="34" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="450" y="86">[1] := %0</text>
    <rect x="570" y="64" width="120" height="34" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="630" y="86">[2] := 3</text>
  </g>
  <g stroke="#2563eb" stroke-width="1.8" fill="none" marker-end="url(#dg)">
    <path d="M 150 81 L 207 81"/>
    <path d="M 330 81 L 387 81"/>
  </g>
  <g font-size="13" text-anchor="middle" fill="#2563eb" font-style="italic">
    <text x="178" y="56">RAW on [0]</text>
    <text x="358" y="56">register flow</text>
    <text x="630" y="48" fill="#0d9488">no edge &#8212; nothing it touches</text>
    <text x="630" y="130" fill="#0d9488">so it may start at round 1</text>
  </g>
  <text x="370" y="166" text-anchor="middle" font-size="14" font-style="italic" fill="#475569">one pass, O(&#8721; footprints) &#8212; not the O(n&#178;) pairwise scan</text>
</svg>
</div>
```

Bernstein's three clauses *are* the three kinds of edge. The DAG's longest path (`critical`) is a
lower bound on the depth of *any* schedule, so it is what says whether a plan is optimal rather than
merely better.

The DAG's longest path (`critical`) is a lower bound on the depth of *any* schedule, so it is what
says whether a plan is optimal rather than merely better.

# A fork discards register writes, so the unit is a segment




```html
<div class="dgm col tight">
  <div class="nd mono bad wide">| .par ss, &#961; =&gt; ParM.bind (ParM.parAll (execParAll ss &#961;)) (fun _ =&gt; .pure &#961;)<em>the continuation gets the PRE-fork register file — `Lang/Core/Prog.lean`</em></div>
  <div class="arr">&#9660;</div>
  <div class="nd bad wide">a register written inside a thread is gone at the join<em>both readings agree, so it is NOT a race — `wfB` cannot see it</em></div>
  <div class="arr">&#9660;</div>
  <div class="nd key wide">the unit is a register-closed <b>segment</b>, not a statement<em>`atoms`: cut only where no register is live — `liveIn`, must-kill `regKills`</em></div>
</div>
```

Found by testing a rewrite that gave `M[12],M[13] = 0,0` where the original gave `3,4`. A load and
the store consuming its register are one segment and are never split across a fork.

# A plan is stages of threads, in program order




```html
<div class="pipewrap">
<svg viewBox="0 0 900 300" role="img" aria-label="two-level consecutive partition">
  <g font-size="16" text-anchor="middle" font-family="ui-monospace, monospace">
    <g fill="#0f172a">
      <rect x="40"  y="30" width="110" height="40" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="95"  y="55">u&#8321;</text>
      <rect x="160" y="30" width="110" height="40" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="215" y="55">u&#8322;</text>
      <rect x="290" y="30" width="110" height="40" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="345" y="55">u&#8323;</text>
      <rect x="420" y="30" width="110" height="40" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="475" y="55">u&#8324;</text>
      <rect x="550" y="30" width="110" height="40" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="605" y="55">u&#8325;</text>
      <rect x="680" y="30" width="110" height="40" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="735" y="55">u&#8326;</text>
    </g>
    <text x="820" y="55" font-size="14" font-style="italic" fill="#475569" text-anchor="start" font-family="inherit">units</text>

    <rect x="40"  y="110" width="230" height="44" rx="7" fill="#eff6ff" stroke="#2563eb" stroke-width="2"/><text x="155" y="138">t&#8321;</text>
    <rect x="290" y="110" width="110" height="44" rx="7" fill="#eff6ff" stroke="#2563eb" stroke-width="2"/><text x="345" y="138">t&#8322;</text>
    <rect x="420" y="110" width="370" height="44" rx="7" fill="#eff6ff" stroke="#2563eb" stroke-width="2"/><text x="605" y="138">t&#8323;</text>
    <text x="820" y="138" font-size="14" font-style="italic" fill="#475569" text-anchor="start" font-family="inherit">threads</text>

    <rect x="40"  y="195" width="360" height="48" rx="8" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.4"/><text x="220" y="225">par[t&#8321;, t&#8322;]</text>
    <rect x="420" y="195" width="370" height="48" rx="8" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.4"/><text x="605" y="225">par[t&#8323;]</text>
    <text x="820" y="225" font-size="14" font-style="italic" fill="#475569" text-anchor="start" font-family="inherit">stages</text>
  </g>
  <g stroke="#94a3b8" stroke-width="1.4" stroke-dasharray="4 3">
    <line x1="155" y1="72" x2="155" y2="108"/><line x1="345" y1="72" x2="345" y2="108"/>
    <line x1="605" y1="72" x2="605" y2="108"/>
    <line x1="220" y1="156" x2="220" y2="193"/><line x1="605" y1="156" x2="605" y2="193"/>
  </g>
  <text x="450" y="278" font-size="17" text-anchor="middle" font-style="italic" fill="#1d4ed8">nothing moves past anything — so the units of the plan ARE the program's statements</text>
</svg>
</div>
```

Because no unit moves, `planUnits (plan us) = us` is a *structural* theorem — proved by induction on
the pass, not checked at run time — and the soundness proof needs no commutation argument.

# The pass is one fold, and the three cases are the three dependences




```html
<div class="figwrap">
<svg viewBox="0 0 760 230" role="img" aria-label="the three-way decision the fold makes for each unit">
  <defs>
    <marker id="fd" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#64748b"/>
    </marker>
  </defs>
  <rect x="250" y="12" width="270" height="36" rx="8" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.2"/>
  <text x="385" y="36" text-anchor="middle" font-family="ui-monospace, monospace" font-size="15" fill="#312e81">next unit x</text>

  <g font-size="14" text-anchor="middle">
    <rect x="20"  y="96" width="220" height="56" rx="7" fill="#fef2f2" stroke="#dc2626" stroke-width="2"/>
    <text x="130" y="118" fill="#991b1b" font-size="13.5">conflicts with an EARLIER</text>
    <text x="130" y="135" fill="#991b1b" font-size="13.5">thread of this stage</text>
    <text x="130" y="172" fill="#334155">close the stage</text>
    <text x="130" y="190" font-size="12.5" font-style="italic" fill="#475569">only a join can order them</text>

    <rect x="270" y="96" width="220" height="56" rx="7" fill="#f1f5f9" stroke="#0d9488" stroke-width="2"/>
    <text x="380" y="118" fill="#115e59" font-size="13.5">conflicts with the thread</text>
    <text x="380" y="135" fill="#115e59" font-size="13.5">being BUILT</text>
    <text x="380" y="172" fill="#334155">extend that thread</text>
    <text x="380" y="190" font-size="12.5" font-style="italic" fill="#475569">the dependence is kept in order</text>

    <rect x="520" y="96" width="220" height="56" rx="7" fill="#eff6ff" stroke="#2563eb" stroke-width="2"/>
    <text x="630" y="118" fill="#1e3a5f" font-size="13.5">conflicts with nothing</text>
    <text x="630" y="135" fill="#1e3a5f" font-size="13.5">in the stage</text>
    <text x="630" y="172" fill="#334155">open a new thread</text>
    <text x="630" y="190" font-size="12.5" font-style="italic" fill="#475569">this is where parallelism comes from</text>
  </g>
  <g stroke="#64748b" stroke-width="1.6" fill="none" marker-end="url(#fd)">
    <path d="M 385 48 L 385 74 L 130 74 L 130 93"/>
    <path d="M 385 48 L 385 93"/>
    <path d="M 385 48 L 385 74 L 630 74 L 630 93"/>
  </g>
  <g stroke="#94a3b8" stroke-width="1.4" fill="none" marker-end="url(#fd)">
    <path d="M 130 152 L 130 160"/><path d="M 380 152 L 380 160"/><path d="M 630 152 L 630 160"/>
  </g>
</svg>
</div>
```

```html
<table class="dgmt">
<thead><tr><th colspan="3">worked on <code>[0]:=1; %0:=[0]; [1]:=%0; [2]:=3; %1:=[2]; [3]:=%1</code> &#8212; two chains written interleaved</th></tr></thead>
<tbody>
<tr><td><code>u&#8321;</code></td><td>&#8212;</td><td>new thread &#183; <code>cur = [u&#8321;]</code></td></tr>
<tr><td><code>u&#8322;</code></td><td>conflicts with <code>cur</code></td><td>extend &#183; <code>cur = [u&#8321;,u&#8322;]</code></td></tr>
<tr><td><code>u&#8323;</code></td><td>independent of everything</td><td>new thread &#183; <code>stage = [[u&#8321;,u&#8322;]]</code></td></tr>
<tr><td><code>u&#8324;</code></td><td>conflicts with <code>cur</code></td><td>extend &#183; <code>cur = [u&#8323;,u&#8324;]</code></td></tr>
<tr class="gap"><td colspan="3"><code>parallel { u&#8321;; u&#8322; } | { u&#8323;; u&#8324; }</code> &#8212; depth 3, sequential 6, bound 3</td></tr>
</tbody>
</table>
```

Greedy prefix grouping gets 5 here: one conflicting unit ends its group even when everything after
it is free.

Greedy prefix grouping gets 5 here: one conflicting unit ends its group even when everything after
it is free.

# `rewrite_sound`: seq = par for the rewrite, with no hypothesis




```leanLibCode Paralever.AutoPar.Rewrite (package := paralever) (startLine := 51) (endLine := 52) -stretch
theorem rewrite_sound (p : ParProg) (ρ : Regs) (σ : State) :
    (runSeq (execPar (rewrite p) ρ) σ).2 = (runSeq (execSeq p ρ) σ).2 := by
```

:::class "steps"
1. `execPar` and `execSeq` agree under `runSeq` — `execPar_runSeq_all`
2. `execSeq` of a `par` *restores* the register file, so a chain of forks never advances it: every
   thread of the whole plan runs at the initial registers — `stages_seqAll`
3. threads in order, each at the initial `ρ`, are the chain, when no register flows between them —
   `fork_heap`
4. a chain of blocks runs like the flat chain — `runSeq_block_map`
5. the plan's units are the program's statements — `plan_units`, `atoms_flatten`, `runSeq_flatten`
:::

Step 2 carries the proof: a fork restores `ρ`, so a chain of forks leaves the top-level plan in the
situation `fork_heap` already handles, one level up. `rewrite` checks its own plan and returns `p` unchanged if the check
fails — which is why the theorem needs no hypothesis.

# The pass on one program: the old tree and the new one

```html
<div class="figwrap">
<svg viewBox="0 0 820 330" role="img" aria-label="a six statement chain rewritten into two threads of three">
  <defs>
    <marker id="ap" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#94a3b8"/>
    </marker>
    <marker id="apI" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#4f46e5"/>
    </marker>
  </defs>
  <g font-size="14" text-anchor="middle" font-style="italic" fill="#475569">
    <text x="150" y="14">before &#183; depth 6</text>
    <text x="580" y="14">after &#183; depth 3 = the DAG's lower bound</text>
  </g>
  <g font-family="ui-monospace, monospace" font-size="14" text-anchor="middle" fill="#0f172a">
    <rect x="60" y="28"  width="180" height="26" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="150" y="46">[0] := 1</text>
    <rect x="60" y="76"  width="180" height="26" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="150" y="94">%0 := [0]</text>
    <rect x="60" y="124" width="180" height="26" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="150" y="142">[1] := %0</text>
    <rect x="60" y="172" width="180" height="26" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="150" y="190">[2] := 3</text>
    <rect x="60" y="220" width="180" height="26" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="150" y="238">%1 := [2]</text>
    <rect x="60" y="268" width="180" height="26" rx="5" fill="#f8fafc" stroke="#94a3b8"/><text x="150" y="286">[3] := %1</text>

    <rect x="535" y="28" width="90" height="26" rx="13" fill="#eef2ff" stroke="#4f46e5" stroke-width="2"/><text x="580" y="46" fill="#312e81">par</text>
    <rect x="380" y="92"  width="170" height="26" rx="5" fill="#eff6ff" stroke="#2563eb" stroke-width="1.8"/><text x="465" y="110">[0] := 1</text>
    <rect x="380" y="136" width="170" height="26" rx="5" fill="#eff6ff" stroke="#2563eb" stroke-width="1.8"/><text x="465" y="154">%0 := [0]</text>
    <rect x="380" y="180" width="170" height="26" rx="5" fill="#eff6ff" stroke="#2563eb" stroke-width="1.8"/><text x="465" y="198">[1] := %0</text>
    <rect x="610" y="92"  width="170" height="26" rx="5" fill="#f1f5f9" stroke="#0d9488" stroke-width="1.8"/><text x="695" y="110">[2] := 3</text>
    <rect x="610" y="136" width="170" height="26" rx="5" fill="#f1f5f9" stroke="#0d9488" stroke-width="1.8"/><text x="695" y="154">%1 := [2]</text>
    <rect x="610" y="180" width="170" height="26" rx="5" fill="#f1f5f9" stroke="#0d9488" stroke-width="1.8"/><text x="695" y="198">[3] := %1</text>
  </g>
  <g stroke="#94a3b8" stroke-width="1.5" fill="none" marker-end="url(#ap)">
    <line x1="150" y1="54"  x2="150" y2="73"/>
    <line x1="150" y1="102" x2="150" y2="121"/>
    <line x1="150" y1="150" x2="150" y2="169"/>
    <line x1="150" y1="198" x2="150" y2="217"/>
    <line x1="150" y1="246" x2="150" y2="265"/>
  </g>
  <g stroke="#2563eb" stroke-width="1.5" fill="none" marker-end="url(#ap)">
    <line x1="465" y1="118" x2="465" y2="133"/><line x1="465" y1="162" x2="465" y2="177"/>
  </g>
  <g stroke="#0d9488" stroke-width="1.5" fill="none" marker-end="url(#ap)">
    <line x1="695" y1="118" x2="695" y2="133"/><line x1="695" y1="162" x2="695" y2="177"/>
  </g>
  <g stroke="#4f46e5" stroke-width="1.8" fill="none">
    <path d="M 580 54 L 580 72 L 465 72 L 465 89" marker-end="url(#apI)"/>
    <path d="M 580 54 L 580 72 L 695 72 L 695 89" marker-end="url(#apI)"/>
    <path d="M 465 206 L 465 230 L 695 230 L 695 206"/>
    <path d="M 580 230 L 580 252" marker-end="url(#apI)"/>
  </g>
  <text x="580" y="270" text-anchor="middle" font-size="13" font-style="italic" fill="#4f46e5">join</text>
  <text x="310" y="170" text-anchor="middle" font-size="22" fill="#4f46e5">&#8594;</text>
  <text x="310" y="192" text-anchor="middle" font-size="12" font-style="italic" fill="#475569">rewrite</text>
</svg>
</div>
```

Two independent chains, written interleaved. The pass finds four units, one stage, two threads:
`quality ex1 = (3, 3, 6)` and `optimalB ex1` — depth 3 against a sequential 6, and 3 *is* the
dependence DAG's critical path, so this is optimal rather than merely better. Greedy prefix
grouping gets 5, because one conflicting unit ends its group even when everything after it is free.

# The round trip: `paralever` in, `paralever` out




```html
<div class="dgm col tight">
  <div class="nd mono plain wide">paralever { [0] := 1; %0 := [0]; [1] := %0; [2] := 3; %1 := [2]; [3] := %1 }<em>input — one `;`-chain</em></div>
  <div class="arr">&#9660; <small>rewrite</small></div>
  <div class="nd mono good wide">paralever {
  parallel { [0] := 1; %0 := [0]; [1] := %0 } | { [2] := 3; %1 := [2]; [3] := %1 }
}
-- units 4   stages 1   threads 2
-- depth 3  (sequential 6, lower bound 3)   optimal true   committed true<em>output — `surface` emits what `paralever { … }` parses</em></div>
</div>
```

`lang → tree → tree → lang`, closed. `evalTask (rewrite p) = evalTaskSeq p` is gated per program on
real threads, on top of the theorem.

# Measured: the pass reaches the lower bound, except where nothing can




```html
<table class="dgmt">
<thead><tr><th>program</th><th>depth</th><th>sequential</th><th>bound L</th><th>optimal</th></tr></thead>
<tbody>
<tr><td>two chains, interleaved</td><td><b>3</b></td><td>6</td><td>3</td><td>&#10003;</td></tr>
<tr><td>the N</td><td><b>8</b></td><td>12</td><td>7</td><td>&#8212;</td></tr>
<tr><td>merge sort, n = 4</td><td><b>12</b></td><td>16</td><td>12</td><td>&#10003;</td></tr>
<tr><td>loop-carried chain</td><td>6</td><td>6</td><td>6</td><td>&#10003;</td></tr>
</tbody>
</table>
```

:::class "steps"
* `L` is the dependence DAG's critical path — a bound for *any* schedule, so `✓` is a certificate
* the N's 7 needs `a₃` concurrent with `a₂`'s write of `[1]`: `wfB` of that tree is *false*
* so 8 is the floor for a race-free fork–join rewrite, and the gap is the shape, not the scheduler
:::

# Merge sort: the pass recovers a recursion tree it never saw




```html
<div class="figwrap">
<svg viewBox="0 0 800 376" role="img" aria-label="the recursion tree the pass recovers for merge sort on four elements">
  <defs>
    <marker id="ms" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#4f46e5"/>
    </marker>
  </defs>
  <rect x="300" y="14" width="200" height="34" rx="7" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/>
  <text x="400" y="37" text-anchor="middle" font-family="ui-monospace, monospace" font-size="16" fill="#0f172a">A = [3, 1, 4, 1]</text>

  <g font-family="ui-monospace, monospace" font-size="13.5" text-anchor="middle" fill="#0f172a">
    <rect x="60"  y="104" width="280" height="88" rx="7" fill="#eff6ff" stroke="#2563eb" stroke-width="2.2"/>
    <text x="200" y="124">%0 := [0];  %1 := [1]</text>
    <text x="200" y="146">[0] := min(%0, %1)</text>
    <text x="200" y="168">[1] := max(%0, %1)</text>
    <text x="200" y="186" font-size="11.5" font-style="italic" fill="#475569" font-family="inherit">compare-exchange on 0,1</text>

    <rect x="460" y="104" width="280" height="88" rx="7" fill="#eff6ff" stroke="#2563eb" stroke-width="2.2"/>
    <text x="600" y="124">%2 := [2];  %3 := [3]</text>
    <text x="600" y="146">[2] := min(%2, %3)</text>
    <text x="600" y="168">[3] := max(%2, %3)</text>
    <text x="600" y="186" font-size="11.5" font-style="italic" fill="#475569" font-family="inherit">compare-exchange on 2,3</text>

    <rect x="230" y="246" width="340" height="56" rx="7" fill="#f1f5f9" stroke="#0d9488" stroke-width="2.2"/>
    <text x="400" y="268">merge &#8212; %0..%3 stay live across all four stores</text>
    <text x="400" y="290" font-size="12" font-style="italic" fill="#115e59" font-family="inherit">so it is ONE register-closed segment, and cannot be split</text>

    <rect x="300" y="334" width="200" height="30" rx="7" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/>
    <text x="400" y="355" font-size="16">B = [1, 1, 3, 4]</text>
  </g>
  <g stroke="#4f46e5" stroke-width="1.8" fill="none" marker-end="url(#ms)">
    <path d="M 400 48 L 400 78 L 200 78 L 200 101"/>
    <path d="M 400 48 L 400 78 L 600 78 L 600 101"/>
    <path d="M 200 192 L 200 222 L 400 222 L 400 243"/>
    <path d="M 600 192 L 600 222 L 400 222"/>
    <path d="M 400 302 L 400 331"/>
  </g>
  <g font-size="13" font-style="italic" text-anchor="middle">
    <text x="400" y="96" fill="#4f46e5">par &#183; cost 4</text>
    <text x="400" y="238" fill="#4f46e5">join &#183; A = [1, 3, 1, 4]</text>
    <text x="668" y="268" fill="#0d9488">cost 8</text>
    <text x="668" y="352" fill="#0d9488">depth 12 = L</text>
  </g>
</svg>
</div>
```

:::class "steps"
* divide-and-conquer DAGs are *series-parallel* — no N — so the plan attains the bound
* `atoms` threw the recursion away with the `;`-chain: the tree comes back from footprints alone
* splitting the merge per output cell gives depth *9*, at work *16 → 24* — the trade, measured
:::

# Part 8 · MLIR



:::class "section-break"
One front end, so a benchmark is not translated by hand
:::

Hand-translating a benchmark suite is the dominant threat to validity for anything measured on one,
because the translation is part of what is measured and is itself unverified.

# MLIR as the one front end


```html
<div class="figwrap">
<svg viewBox="0 0 820 320" role="img" aria-label="three source languages reaching one converter through MLIR generic form">
  <defs>
    <marker id="ml" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#64748b"/>
    </marker>
    <marker id="mlb" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#4f46e5"/>
    </marker>
  </defs>
  <g font-family="ui-monospace, monospace" font-size="14" text-anchor="middle" fill="#0f172a">
    <rect x="30"  y="14" width="200" height="30" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="130" y="34">C / C++ &#8212; cgeist</text>
    <rect x="300" y="14" width="200" height="30" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="400" y="34">Fortran &#8212; flang</text>
    <rect x="570" y="14" width="220" height="30" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="680" y="34">a .mlir by hand</text>

    <rect x="250" y="106" width="320" height="34" rx="7" fill="#f1f5f9" stroke="#0d9488" stroke-width="2.2"/>
    <text x="410" y="129">MLIR generic form</text>

    <rect x="250" y="196" width="320" height="34" rx="7" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.4"/>
    <text x="410" y="219" fill="#312e81">Layout &#215; ParProg</text>

    <rect x="250" y="272" width="320" height="34" rx="7" fill="#eff6ff" stroke="#2563eb" stroke-width="2.2"/>
    <text x="410" y="295">wfB, raceSites, par_seq_eq</text>
  </g>
  <g stroke="#64748b" stroke-width="1.6" fill="none" marker-end="url(#ml)">
    <path d="M 130 44 L 130 80 L 410 80 L 410 103"/>
    <path d="M 400 44 L 400 80"/>
    <path d="M 680 44 L 680 80 L 410 80"/>
  </g>
  <g stroke="#4f46e5" stroke-width="1.8" fill="none" marker-end="url(#mlb)">
    <path d="M 410 140 L 410 193"/>
    <path d="M 410 230 L 410 269"/>
  </g>
  <g font-size="13" font-style="italic">
    <text x="640" y="98" fill="#475569" text-anchor="middle">stage 1 &#183; off the shelf, a text format</text>
    <text x="640" y="170" fill="#4f46e5" text-anchor="middle">stage 2 &#183; MLIR/, in Lean &#8212; one artifact to test</text>
    <text x="640" y="292" fill="#2563eb" text-anchor="middle">the verdict</text>
  </g>
</svg>
</div>
```

:::class "steps"
* N languages against one converter, instead of one front end per language — and stage 1 is
  replaceable, so a hand-written `.mlir` feeds the same interface
* *generic form, not each dialect's assembly*: `--mlir-print-op-generic` prints every op the same
  way, so one reader covers `affine`, `memref`, `arith` and `func`
* *not LLVM IR* — unstructured `br` and phi nodes have no encoding in an inductive `ParM`, and
  going through a loop structurizer destroys the affine maps the lowering depends on
:::

`MLIR.lower` is a Lean *function*, so the translation is an object we can state a theorem about.
The target is footprint preservation, which turns "trust the translator" into a proof obligation.

# An affine map is already a footprint function


```html
<div class="dgm col tight">
  <div class="nd mono plain wide">"affine.store"(%v, %A, %i, %j) &#123;map = affine_map&lt;(d0, d1) -&gt; (d0, d1)&gt;&#125;<em>the map applied to (i, j) <b>is</b> the subscript — no analysis, no inference</em></div>
  <div class="arr">&#9660;</div>
  <div class="nd mono wide">Layout.at "A" [i, j]  =  A.base + i&#183;cols + j<em>range-checked against its own buffer, because `Layout.at` is total</em></div>
  <div class="arr">&#9660;</div>
  <div class="nd key wide">wr (i, j) = [that cell]<em>which is exactly what `wfB_parFor_of_lists` asks for</em></div>
</div>
```

:::class "steps"
* loops are unrolled at lowering time, so the subscript is a literal `Nat` and the footprint stays
  *exact* — proportional to the number of accesses, not to the size of the array
* that matters for evaluability, not only precision: `indepB` is quadratic in list length, so an
  over-approximated footprint on a large array is unevaluable rather than merely imprecise
* unrolling has a ceiling — `decide` on `wfB (matmul n)` is 6.6 s at `n = 8` and 19 s at `n = 10`,
  and `native_decide` is prohibited — so about a hundred threads, and past that a kernel lemma at
  symbolic `n`
:::

`Layout.of` places buffers in consecutive ranges, so array disjointness is discharged once by the
allocator rather than once per pair.

# One pilot, end to end: `doall-no.mlir`

```html
<div class="dgm tight">
  <div class="nd mono plain">"affine.parallel"() (&#123;
^bb0(%i: index):
  %0 = "affine.load"(%A, %i) &#123;map = ...&#125;
  %1 = "affine.load"(%B, %i) &#123;map = ...&#125;
  %2 = "arith.addi"(%0, %1)
  "affine.store"(%2, %C, %i) &#123;map = ...&#125;
&#125;) &#123;upperBoundsMap = ... (8)&#125;<em>C[i] := A[i] + B[i], generic form</em></div>
  <div class="arr lbl2">&#8594;<small>MLIR.lower</small></div>
  <div class="nd mono blue">parallel &#123;
  thread 0 &#123; t0 := M[0]; t1 := M[8];  M[16] := (t0 + t1); &#125;
  thread 1 &#123; t0 := M[1]; t1 := M[9];  M[17] := (t0 + t1); &#125;
  &#8230;
  thread 7 &#123; t0 := M[7]; t1 := M[15]; M[23] := (t0 + t1); &#125;
&#125;<em>one thread per point of the index box</em></div>
</div>
```

```html
<div class="nd mono plain wide">layout      A[8]@0, B[8]@8, C[8]@16
reads       16 cells          writes      8 cells
footprint   exact             verdict     wfB true, wellFormedB true
sites       0                 values      exact in Int<em>`Lowered.report` — the whole story about one benchmark</em></div>
```

The subscript is a literal `Nat` because the loop is unrolled at lowering time, so the footprint
stays *exact* rather than becoming the whole array. `C = [11, 22, 33, 44, 55, 66, 77, 88]` on the
threaded run, and `runTask_eq` is what makes it sound to look at that heap at all.

# Two runs: the verdict over `Int`, the reference over `ℚ`


```html
<div class="dgm tight">
  <div class="nd mono blue">MLIR/Lower.lean<em>Layout × ParProg, over `Int` — the verdict</em></div>
  <div class="nd mono good">MLIR/Eval.lean<em>heap : Loc → Scalar, `Int` and `Rat` — the reference</em></div>
  <div class="arr lbl2">&#8594;<small>cell by cell</small></div>
  <div class="nd key">differential execution<em>`progCells` against `refCells`</em></div>
</div>
```

:::class "steps"
* *the verdict depends on no value*: `footprintOf` and `indepB` never inspect a `Val`, so a
  `memref<8xf64>` occupies the same eight cells as a `memref<8xi32>` and gets the same verdict
* floating point becomes `Rat`, not `Real` — every finite IEEE value *is* `m · 2ᵉ`, so `Rat` is a
  superset of the floats rather than an approximation, and it is computable, so a gate can run
* the reference interpreter is allowed to evaluate a `par` in one canonical order, and what licenses
  that is `par_seq_eq` itself
:::

```html
<table class="dgmt">
<thead><tr><th>MLIR.Corpus.summary</th><th>expressible</th><th>unsupported</th><th>confusion</th><th>over-approx</th><th>round trip</th></tr></thead>
<tbody>
<tr><td>seven labelled pilots</td><td><b>7/7</b></td><td>[]</td><td>tp=3 fp=0 fn=0 tn=4</td><td><code>indirect-yes</code></td><td>&#10003;</td></tr>
</tbody>
</table>
```

No false negatives is not luck: `raceSites_nil_iff` makes the scan complete for the obligation.
`stencil-f64-no` is the Bernstein case — neighbouring threads share two of three read cells, which
`∗` rejects outright and `Indep` accepts without a clause.

# Kernels: symbolic obligations where `decide` dies




```html
<table class="dgmt">
<thead><tr><th>surface matmul, `wfB` at n</th><th>6</th><th>8</th><th>10</th><th>12</th></tr></thead>
<tbody>
<tr><td><code>decide</code> — pairwise over n² threads</td><td>1.5 s</td><td>6.3 s</td><td>19.3 s</td><td>49.3 s</td></tr>
<tr><td><code>wfB_parFor_of_lists</code> — symbolic in n</td><td>0.16 s</td><td>0.16 s</td><td>0.16 s</td><td>0.16 s</td></tr>
</tbody>
</table>
```

:::class "steps"
* fitted exponent *5.1* — Θ(n²) threads × Θ(n) cells, pairwise
* 11 kernels have a `∀ n` obligation; each also `decide`s at a concrete `n`, so the routes are checked to agree
* the scheduler must emit *kernel shape*, not an unrolled `par` list — a `Lower` bug otherwise
:::

# Limits




:::class "steps"
* *registers cannot be renamed away — yet.* `noRegFlow` is on raw read sets, stronger than the
  liveness `atoms` establishes, so a chain reusing `%0` is declined and returned sequential
* *memory cannot be renamed at all.* A `Loc` is reached by a computed address, so the cell *is*
  the name — privatization, the commonest OpenMP clause, is out of reach
* *footprints over-approximate.* `A[B[i]]` reports the whole array; `whileAtMost` reports the
  branch union — conservative, never unsound
* *`ParM` is inductive*, so `while true` is unrepresentable; and whether order preservation itself
  costs depth is open
:::

# Conclusions




:::class "finale"
* *One theorem, then arithmetic.* `wfB s = true ⇒ execPar s ∥≡ execSeq s`, every schedule,
  arbitrary programs, kernel-checked — so each program pays `decide`, not a proof about interleavings
* *The rewrite is proved, not checked.* `rewrite_sound` has no hypothesis: the pass is untrusted,
  the gate is proved, and the plan's order preservation makes the bookkeeping structural
* *Optimal where fork–join allows.* Depth meets the DAG critical path on interleaved chains and
  on merge sort; the N's gap of 8 vs 7 is the shape, and the 7-tree is racy
:::

```html
<div class="links">534 build jobs &#183; 0 sorries &#183; <a href="https://github.com/AnirudhG07/paralever">github.com/AnirudhG07/paralever</a> &#183; contact@shemeka.in</div>
```

# References




:::class "cite"
* *Bernstein*, _Analysis of programs for parallel processing_, IEEE TEC, 1966.
* *O'Hearn*, _Resources, concurrency and local reasoning_, CONCUR 2004.
* *Brookes*, _A semantics for concurrent separation logic_, CONCUR 2004, §5–§7.
* *Reynolds*, _Toward a grainless semantics for shared-variable concurrency_, FSTTCS 2004.
* *Apt & Olderog*, _Verification of Sequential and Concurrent Programs_, Springer.
* *Valdes, Tarjan & Lawler*, _The recognition of series parallel digraphs_, SIAM J. Comput. 11(2):298–313, 1982.
* *Graham*, _Bounds on multiprocessing timing anomalies_, SIAM J. Appl. Math., 1969.
:::
