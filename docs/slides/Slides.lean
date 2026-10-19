import VersoSlides
import Verso.Doc.Concrete
import Paralever
import Examples.MatMul
import Examples.ParMapDemo
import Examples.PureToParM

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


# Three questions about one program


```html
<div class="dgm tight">
  <div class="nd mono">paralever {
  [0] := 3; [1] := 4;
  %0 := [0]; [2] := R 0 * R 0;
  %1 := [1]; [3] := R 1 * R 1;
  %2 := [2]; %3 := [3];
  [4] := R 2 + R 3
}<em>nine statements, one core</em></div>
  <div class="arr lbl2">&#8594;<small>one fork</small></div>
  <div class="nd mono blue">paralever {
  [0] := 3; [1] := 4;
  parallel { %0 := [0]; [2] := R 0 * R 0 }
           | { %1 := [1]; [3] := R 1 * R 1 };
  %2 := [2]; %3 := [3];
  [4] := R 2 + R 3
}<em>the two squares on separate cores</em></div>
</div>
```

```html
<div class="fan">
  <div class="nd key">a &#183; can the fork be <b>found</b>?<em>the program arrives as a chain</em></div>
  <div class="nd key">b &#183; is the fork <b>correct</b>?<em>par = seq, under every schedule</em></div>
  <div class="nd key">c &#183; if the <b>user</b> forked it, is it safe?<em>the same check, run the other way</em></div>
</div>
```

Nothing else changed, and both leave `M = [3,4,9,16,25]`. One check answers b and c; a is a search
whose output that check accepts or rejects.

:::class "notation"
*`seq`* — the statements run one after another, on one core. *`par`* — the branches of a
`parallel` block run at the same time, and the block ends when all of them have.
:::

:::notes
Both programs are checked: `wfB` accepts the fork, so `par_seq_eq` gives every schedule, and
`evalTaskSeq` on the chain and `evalTask` on the fork return the same five cells. On rounds the fork
is 7 against the chain's 9, for the same 9 memory operations.

a is `Paralever/AutoPar/`, b is `par_seq_eq`, c is `wfB` on user code. The talk does b first because
a and c both reduce to it. For this chain the pass does find a fork and reaches the dependence DAG's
lower bound (depth 6, bound 6, sequential 9) — the one register per segment is what lets it: the
gate refuses a chain that reuses a register across segments.
:::

# The talk in seven parts

```html
<div class="ladder">
  <div class="tier"><strong>1 &#183; Background</strong> <em>Hoare triples, &#8727;-disjointness, and what CSL's soundness theorem gives you</em></div>
  <div class="tier"><strong>2 &#183; The statement</strong> <em>what replaces &#8727;, and the equality that follows from it</em></div>
  <div class="tier"><strong>3 &#183; Programs as data</strong> <em>one branching constructor, and a footprint computed from the syntax</em></div>
  <div class="tier"><strong>4 &#183; The proof</strong> <em>four pieces, and the schedule appears in exactly one of them</em></div>
  <div class="tier"><strong>5 &#183; The language</strong> <em>memory, registers, one fork &#8212; and the check run on user code</em></div>
  <div class="tier"><strong>6 &#183; Finding the fork</strong> <em>a <code>;</code>-chain in, a proved-equivalent tree out</em></div>
  <div class="tier"><strong>7 &#183; Results</strong> <em>depth against the dependence DAG's lower bound</em></div>
</div>
```

Parts 1 and 2 are the question, 3 and 4 are the theorem, 5 to 7 are what it buys.

# Part 1 · Background

:::class "section-break"
Hoare triples, ∗-disjointness, and what CSL's soundness theorem gives you
:::

The triple that cannot be glued under ∥, the assertion that repairs it, and the shared read it
forbids on the way.

# A triple is about one program, and two of them do not glue

```html
<div class="dgm tight">
  <div class="nd mono">C&#8321; = [p] := 5; y := [p]<em>write the cell, then read it back</em></div>
  <div class="nd mono">C&#8322; = [p] := 8<em>write the same cell</em></div>
  <div class="nd key">p points at x<em>so both commands write the cell holding x</em></div>
</div>
```

```html
<div class="fan">
  <div class="nd good">{true} C&#8321; {y = 5}</div>
  <div class="nd good">{true} C&#8322; {true}</div>
  <div class="nd good">{true} C&#8321;; C&#8322; {y = 5}<em>by sequencing, with y = 5 in the middle</em></div>
  <div class="nd bad">{true} C&#8321; &#8741; C&#8322; {y = 5}<em>false &#183; a schedule runs C&#8322; between the write and the read, leaving y = 8</em></div>
</div>
```

:::class "steps"
* neither component proof is wrong — what fails is the **gluing**
* sequencing is sound because `C₁` runs to completion in a state nobody else can touch
* the hypothesis that would restore it — *the cell `p` addresses belongs to `C₁` alone* — is not a
  sentence the assertion language can write
:::

:::notes
Assertions range over variables, and the language has no notation for "the cell at the address held
by p", so the mutation rule carries a proviso the logic cannot state: {x = 5} [p]:=7 {x = 5} is valid
exactly when p does not point at x. Sequentially that is the frame problem, an inconvenience. Under
concurrency it is unsoundness.
:::

# Separation logic turns that side condition into an assertion

```html
<div class="fan">
  <div class="nd key">l &#8614; v<em>the heap <b>is</b> this one cell, and it holds v &#183; exclusive</em></div>
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
* both premises mention one thread only — **no interleaving appears in the rule**
* the `∗` is the hypothesis, not a side condition checked elsewhere: it hands the two threads
  provably non-overlapping storage
* *Ownership Hypothesis* — a fragment accesses only what it owns; *Separation Property* — at every
  moment the state partitions into the parts owned by each process and each resource
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
* read it as a loan: outside the region a process knows nothing about the resource's state; on entry
  it is handed `RI_r`, may disturb it, and must hand it back on exit
* `RI_r` must be **precise** — pinning down a unique sub-heap — which is what makes the hand-back
  well defined; the storage it describes is owned by no thread
* Brookes proves both rules sound in an action-trace semantics where a **racing step is a
  catastrophic error**
:::

```html
<div class="gbox thm">
  <div class="caplabel">Parallel Decomposition &#183; Brookes, CONCUR 2004, Thm. 21</div>
  If a trace of C&#8321; &#8741; C&#8322; runs from a state split as &#963;&#8321; &#8727; &#963;&#8322; and the components' footprints stay separate, then that trace is an <b>interleaving</b> of a trace of C&#8321; from &#963;&#8321; and a trace of C&#8322; from &#963;&#8322;, and the final states recombine as &#963;&#8321;&#8242; &#8727; &#963;&#8322;&#8242;.
</div>
```

Every quantifier there ranges over **one** trace, one heap partition, one local computation of each
component. It is a projection, in one direction, and says nothing about the two outcome *sets*.

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

To dereference `a₀` the left premise needs `a₀ ↦ u`, and so does the right one, so the conclusion's
precondition would have to be `(a₀ ↦ u) ∗ (a₀ ↦ u) ⇒ false`. The rule cannot be applied to a program
whose answer no schedule can change.

```html
<div class="pullquote">
&ldquo;there is no way to prove the obviously valid formula &#8866; {z &#8614; 1} x:=[z] &#8741; y:=[z] {x = y = 1 &#8743; z &#8614; 1}, since the logic requires both processes to &lsquo;need&rsquo; to own the heap cell denoted by z, separately. Nevertheless, the trace semantics handles this issue (and this example) correctly, so here is a place where the semantics is ahead of the logic.&rdquo;
<span class="src">Brookes, <i>A semantics for concurrent separation logic</i>, CONCUR 2004</span>
</div>
```

:::notes
This is O'Hearn's own argument, used there to show that [10]:=42 ∥ [10]:=6 has no derivable triple;
run on reads it rejects a deterministic program. The repair inside separation logic is standard —
fractional permissions, a₀ ↦_{1/2} u on each side, recombined at the join — so the claim is not that
CSL cannot verify this. The claim is about the shape of the obligation: with fractions the user picks
a fraction for every shared cell, threads it through every lemma, and discharges an entailment at the
join. Matrix multiplication is this example at scale.
:::

# Part 2 · The statement

:::class "section-break"
What replaces ∗, and the equality that follows from it
:::

Bernstein's criterion in place of ∗-disjointness, and a conclusion about two programs rather than
about one program's postcondition.

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


```leanLibCode Paralever.Core.Access (package := paralever) (startLine := 62) (endLine := 64) -stretch
@[simp, grind .]
def Indep (f₁ f₂ : Footprint) : Prop :=
  Disjoint f₁.writes f₂.writes ∧ Disjoint f₁.writes f₂.reads ∧ Disjoint f₂.writes f₁.reads
```

:::class "steps"
* `w₁∩w₂ = w₁∩r₂ = w₂∩r₁ = ∅` — shared **reads** are allowed
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

# Independent branches agree with `p; q` under every schedule


```leanLibCode Paralever.Lang.Core (package := paralever) (startLine := 533) (endLine := 534) -stretch
theorem par_seq_eq {s : ParProg} (h : wfB s = true) (ρ : Regs) (σ : State) :
    ParSeqEq (execPar s ρ) (execSeq s ρ) σ := by
```

:::class "steps"
* `ParSeqEq p q σ` — the two reach the **same outcome set** from `σ`, not one trace
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


:::class "map wide"
```
   the `;`-chain                          the forked version
   ------------------------               ------------------------
   seq                                    seq
    |- [0] := 3                            |- [0] := 3
   seq                                    seq
    |- [1] := 4                            |- [1] := 4
   seq                                    seq
    |- %0 := [0]                           |- par --+-- %0 := [0]; [2] := R0*R0
   seq                                     |        +-- %0 := [1]; [3] := R0*R0
    |- [2] := R0*R0                       seq
   seq                                     |- %0 := [2]
    |- %0 := [1]                          seq
   seq                                     |- %1 := [3]
    |- [3] := R0*R0                        +- [4] := R0+R1
   seq
    |- %0 := [2]                          ONE branching node.
   seq                                    Its two children write {2} and {3},
    |- %1 := [3]                          read {0} and {1}  ->  disjoint.
    +- [4] := R0+R1
                                          The obligation lives at that node,
   no branch, nothing to check            and nowhere else.
```
:::

Same leaves, same order, one node different. `paralever { s₁; …; sₙ }` is right-nested `seq`, so
every program is a spine until a `parallel` block puts a fork in it.

:::notes
This is the slide that teaches the two constructors. `seq` threads the heap and the register file
from one child to the next; `par` hands every child the same starting state and joins. Everything
later — the check, the theorem, the rewrite — is about `par` nodes only.
:::

# The footprint is computed from the syntax, never proved

```leanLibCode Paralever.Lang.Core (package := paralever) (startLine := 295) (endLine := 296) -stretch
theorem execPar_accesses_sub (s : ParProg) (ρ : Regs) (σ : State) :
    (accesses (execPar s ρ) σ).Sub (footprintOf s) := execPar_accesses_sub_all.1 s ρ σ
```

```html
<div class="ladder">
  <div class="tier"><strong>literal address</strong> <code>[2] := R 0</code> &#183; the footprint is <em>exact</em></div>
  <div class="tier"><strong>computed address</strong> <code>A[B[i]]</code> &#183; the footprint is the whole array</div>
  <div class="tier"><strong>branch</strong> <code>if c {…} else {…}</code> &#183; the footprint is the branch <em>union</em></div>
</div>
```

`footprintOf` is a fold over the syntax, so the obligation is `decide` rather than a proof. Where it
over-approximates it costs precision and never soundness: the computed footprint provably contains
every cell actually touched, at every heap.

# `wfB` checks every `par`, not just the top


```html
<div class="dgm col tight">
  <div class="nd mono bad wide">parallel { [0] := 1 }
         | { parallel { [1] := 2 } | { %0 := [1] } }<em>outer footprints {0} and {1} are disjoint — a top-level check passes</em></div>
  <div class="arr">&#9660;</div>
  <div class="nd key wide">the <b>inner</b> `par` writes and reads `[1]` concurrently<em>`wfB` recurses, so it rejects this</em></div>
</div>
```

:::class "map wide"
```
   par --+-- [0] := 1                     outer children:  writes {0}  vs  writes/reads {1}
         |                                                 disjoint -> a top-level check PASSES
         +-- par --+-- [1] := 2
                   |                      inner children:  writes {1}  vs  reads {1}
                   +-- %0 := [1]                           RACE
```
:::

```leanLibCode Paralever.Lang.Core (package := paralever) (startLine := 179) (endLine := 189) -stretch
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
* racy programs are **excluded**, not silently assumed away — so the atomic grain is irrelevant
* standing obligation: exhibit `p`, `q` where the conclusion *fails*, so the hypothesis is not free
* the loop-carried case `A[i] := A[i-1] + 1` must stay **unprovable**
:::

# Part 4 · The proof

:::class "section-break"
Four pieces, and the schedule appears in exactly one of them
:::

Where the difficulty actually is, and the program on which this equality is false.

# The proof is four steps, and only one is about schedules


:::class "map tall"
```
                    par_seq_eq   (Lang/Core.lean)
                         |
     +-------------------+-------------------+
     |                   |                   |
 Decomposition    WellFormedCanonical   Sequentialize
 Theory/          Theory/               Theory/
     |                   |                   |
 a `par` node       every reachable      the canonical
 splits into        outcome of a         outcome IS the
 per-branch         well-formed `par`    one `p; q`
 steps on           equals ONE           produces
 disjoint cells     canonical outcome
     |                   |                   |
 Brookes            Reynolds              Bernstein
 CONCUR'04 §5-7     grainless             1966
                    semantics
     |                   |                   |
     +-------------------+-------------------+
                         |
                   Cost (Lib/Cost.lean)
            time (par ps) = foldr max  --  the `max`
            is DERIVED from independence, not assumed
```
:::

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
* these are **different heaps**, so the two readings of `q` are a priori different runs
* independence is what makes them agree: `q` reads `[1]`, `p` writes `[0]`, so the cell `q` looks at
  holds the same value in both
* the induction therefore carries the footprint along with the equality — one level down, the
  footprint conjunct is what pins the replayed heap to the right one
:::

The theorem is that every reachable terminal configuration of a well-formed `par` is **the same
one**, and `runSeq` names it. The schedule enters the proof here and nowhere else.

# Where this equality is false: one shared resource

```html
<div class="dgm tight">
  <div class="nd mono bad">observer = write 1 7 (&#955;_. read 0)
mutator  = write 0 99<em>Examples/Racy.lean &#183; &#963;&#8320; has cell 0 = 1</em></div>
  <div class="arr lbl2">&#8594;<small>par</small></div>
  <div class="nd bad">y = 99<em>mutator ran first &#183; <code>par_reaches</code></em></div>
  <div class="arr lbl2">&#8594;<small>seq</small></div>
  <div class="nd good">y = 1<em>only outcome &#183; <code>seq_runSeq</code></em></div>
</div>
```

:::class "steps"
* put both accesses inside `with r do …` and **CSL proves the program**, with `RI_r = ∃v. 10 ↦ v`;
  by Brookes's corollary it is race free
* race freedom is strictly weaker than determinism: the `∥` rule joins postconditions with `∗`,
  which records no ordering — *the rule is designed to forget the schedule*
* so `ParM` has no resource, no lock, and no unstructured `fork`, and the conclusion would be false
  if it had — `not_parSeqEq` proves the failure, `not_indepAll` refutes the hypothesis
:::

Both sides terminate normally here and simply disagree, which is the case a reader is entitled to
worry about.

# `max` at a fork is derived, not assumed

```leanLibCode Paralever.Lang.Cost (package := paralever) (startLine := 87) (endLine := 88) -stretch
theorem time_le {s : ParProg} (h : wfB s = true) (ρ : Regs) (σ : State) :
    time (execPar s ρ) σ ≤ time (execSeq s ρ) σ := by
```

:::class "steps"
* `work` counts memory operations and is **unchanged** by forking — `work_par_eq_seq`
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
  <div class="tier"><b>literal address</b> &nbsp; <code>[2] := R 0</code> &nbsp;&#183;&nbsp; footprint is <i>exact</i></div>
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
         | { %0 := [0]; [1] := R 0 }<em>store x on one core, load x on another</em></div>
  <div class="arr lbl2">&#8594;<small>decide</small></div>
  <div class="nd key">wfB = false<br/><code>block [·,·]</code> = true<em>the only legal placement is in sequence</em></div>
</div>
```

:::class "steps"
* this is the configuration the whole data-race literature is about
* our rewrite can never *build* it: a RAW edge puts the two in one thread
* when the user writes it, `wfB` is the checker — and rejects
:::

# Part 6 · Finding the fork

:::class "section-break"
A `;`-chain in, a proved-equivalent tree out
:::

The analysis is untrusted and the gate is proved, so the pass needs no hypothesis.

# Question a: dependences come from one scoreboard pass


:::class "map wide"
```
for each unit i, with footprint f:

    for l in f.reads :   edge lastWriter[l] -> i          RAW   W n R
                         readers[l] += i
    for l in f.writes:   edge lastWriter[l] -> i          WAW   W n W
                         edge r -> i   for r in readers[l]   WAR   R n W
                         lastWriter[l] := i ;  readers[l] := []

Bernstein's THREE clauses are the THREE kinds of edge.
Cost: one pass, O(sum of footprints) -- not the O(n^2) pairwise scan.
```
:::

The DAG's longest path (`critical`) is a lower bound on the depth of *any* schedule, so it is what
says whether a plan is optimal rather than merely better.

# A fork discards register writes, so the unit is a segment


```html
<div class="dgm col tight">
  <div class="nd mono bad wide">| .par ss, &#961; =&gt; ParM.bind (ParM.parAll (execParAll ss &#961;)) (fun _ =&gt; .pure &#961;)<em>the continuation gets the PRE-fork register file — `Lang/Core.lean`</em></div>
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


:::class "map wide"
```
for each unit x:

   conflicts with an EARLIER THREAD of this stage?
       yes -> close the stage            only a join can order them
   else conflicts with the thread being BUILT?
       yes -> extend that thread
   else -> open a NEW THREAD beside it

------ worked:  [0]:=1; %0:=[0]; [1]:=R0; [2]:=3; %1:=[2]; [3]:=R1 ------

   u1                               cur = [u1]
   u2   conflicts with cur          cur = [u1,u2]
   u3   independent of everything   stage = [[u1,u2]]   cur = [u3]
   u4   conflicts with cur          cur = [u3,u4]

   ==>  parallel { u1; u2 } | { u3; u4 }      depth 3,  sequential 6,  bound 3
```
:::

Greedy prefix grouping gets 5 here: one conflicting unit ends its group even when everything after
it is free.

# `rewrite_sound`: seq = par for the rewrite, with no hypothesis


```leanLibCode Paralever.AutoPar.Rewrite (package := paralever) (startLine := 47) (endLine := 48) -stretch
theorem rewrite_sound (p : ParProg) (ρ : Regs) (σ : State) :
    (runSeq (execPar (rewrite p) ρ) σ).2 = (runSeq (execSeq p ρ) σ).2 := by
```

:::class "map wide"
```
1  execPar and execSeq agree under runSeq                 execPar_runSeq_all
2  execSeq of a `par` RESTORES the register file, so a
   CHAIN of forks never advances it: every thread of
   the whole plan runs at the initial registers           stages_seqAll
3  threads in order, each at the initial rho  =  the
   chain, when no register flows between them             fork_heap
4  a chain of blocks runs like the flat chain             runSeq_block_map
5  the plan's units are the program's statements          plan_units
                                                          atoms_flatten
                                                          runSeq_flatten
```
:::

Step 2 carries the proof: a fork restores `ρ`, so a chain of forks leaves the top-level plan in the
situation `fork_heap` already handles, one level up. `rewrite` checks its own plan and returns `p` unchanged if the check
fails — which is why the theorem needs no hypothesis.

# The round trip: `paralever` in, `paralever` out


```html
<div class="dgm col tight">
  <div class="nd mono plain wide">paralever { [0] := 1; %0 := [0]; [1] := R 0; [2] := 3; %1 := [2]; [3] := R 1 }<em>input — one `;`-chain</em></div>
  <div class="arr">&#9660; <small>rewrite</small></div>
  <div class="nd mono good wide">paralever {
  parallel { [0] := 1; %0 := [0]; [1] := R 0 } | { [2] := 3; %1 := [2]; [3] := R 1 }
}
-- units 4   stages 1   threads 2
-- depth 3  (sequential 6, lower bound 3)   optimal true   committed true<em>output — `surface` emits what `paralever { … }` parses</em></div>
</div>
```

`lang → tree → tree → lang`, closed. `evalTask (rewrite p) = evalTaskSeq p` is gated per program on
real threads, on top of the theorem.

# Part 7 · Results

:::class "section-break"
Depth against the dependence DAG's lower bound
:::

Where the pass is optimal, where the fork–join shape costs a round, and where `decide` stops scaling.

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
* the N's 7 needs `a₃` concurrent with `a₂`'s write of `[1]`: `wfB` of that tree is **false**
* so 8 is the floor for a race-free fork–join rewrite, and the gap is the shape, not the scheduler
:::

# Merge sort: the pass recovers a recursion tree it never saw


:::class "map wide"
```
                  A = [3, 1, 4, 1]
                          |
         +----------------+----------------+          par    cost 4
       ce01                               ce23
   %0:=[0] %1:=[1]                    %2:=[2] %3:=[3]
   [0]:=min(R0,R1)                    [2]:=min(R2,R3)
   [1]:=max(R0,R1)                    [3]:=max(R2,R3)
         +----------------+----------------+
                      J O I N                         A = [1, 3, 1, 4]
                          |
                        merge                         cost 8
             %0..%3 stay live across all four
             stores  ->  ONE register-closed segment
                          |
                  B = [1, 1, 3, 4]                    depth 12 = L
```
:::

:::class "steps"
* divide-and-conquer DAGs are **series-parallel** — no N — so the plan attains the bound
* `atoms` threw the recursion away with the `;`-chain: the tree comes back from footprints alone
* splitting the merge per output cell gives depth **9**, at work **16 → 24** — the trade, measured
:::

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
* fitted exponent **5.1** — Θ(n²) threads × Θ(n) cells, pairwise
* 11 kernels have a `∀ n` obligation; each also `decide`s at a concrete `n`, so the routes are checked to agree
* the scheduler must emit *kernel shape*, not an unrolled `par` list — a `Lower` bug otherwise
:::

# Limits


:::class "steps"
* **registers cannot be renamed away — yet.** `noRegFlow` is on raw read sets, stronger than the
  liveness `atoms` establishes, so a chain reusing `%0` is declined and returned sequential
* **memory cannot be renamed at all.** A `Loc` is reached by a computed address, so the cell *is*
  the name — privatization, the commonest OpenMP clause, is out of reach
* **footprints over-approximate.** `A[B[i]]` reports the whole array; `whileAtMost` reports the
  branch union — conservative, never unsound
* **`ParM` is inductive**, so `while true` is unrepresentable; and whether order preservation itself
  costs depth is open
:::

# Conclusions


:::class "finale"
* **One theorem, then arithmetic.** `wfB s = true ⇒ execPar s ∥≡ execSeq s`, every schedule,
  arbitrary programs, kernel-checked — so each program pays `decide`, not a proof about interleavings
* **The rewrite is proved, not checked.** `rewrite_sound` has no hypothesis: the pass is untrusted,
  the gate is proved, and the plan's order preservation makes the bookkeeping structural
* **Optimal where fork–join allows.** Depth meets the DAG critical path on interleaved chains and
  on merge sort; the N's gap of 8 vs 7 is the shape, and the 7-tree is racy
:::

```html
<div class="links">534 build jobs &#183; 0 sorries &#183; <a href="https://github.com/AnirudhG07/paralever">github.com/AnirudhG07/paralever</a> &#183; contact@shemeka.in</div>
```

# References


:::class "cite"
* **Bernstein**, *Analysis of programs for parallel processing*, IEEE TEC, 1966.
* **O'Hearn**, *Resources, concurrency and local reasoning*, CONCUR 2004.
* **Brookes**, *A semantics for concurrent separation logic*, CONCUR 2004, §5–§7.
* **Reynolds**, *Toward a grainless semantics for shared-variable concurrency*, FSTTCS 2004.
* **Apt & Olderog**, *Verification of Sequential and Concurrent Programs*, Springer.
* **Valdes, Tarjan & Lawler**, *The recognition of series parallel digraphs*, SIAM J. Comput. 11(2):298–313, 1982.
* **Graham**, *Bounds on multiprocessing timing anomalies*, SIAM J. Appl. Math., 1969.
:::
