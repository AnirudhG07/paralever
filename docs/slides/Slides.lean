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

# The fundamental question for (truly) parallelizing programs


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
}<em>both leave the heap [3, 4, 9, 16, 25]</em></div>
</div>
```

One run of each agrees. A parallel program has many runs, and the question is about all of them:

```html
<div class="qask">
  <div class="qm">?</div>
  <div class="qbody">
    <div class="qhead">Is <code>par</code> <span class="eq">=</span> <code>seq</code> <b>correct</b>?</div>
    <ul class="qwhen">
      <li>schedule</li>
      <li>starting heap</li>
      <li>register state</li>
    </ul>
  </div>
</div>
```

:::class "notation"
*`seq`* — the statements run one after another, on one core. *`par`* — the branches of a
`parallel` block run at the same time, and the block ends when all of them have.
:::

# Two questions, and one checker answers both


```html
<div class="dgm tight">
  <div class="nd key">1 &#183; the <code>parallel</code> you wrote &#8212; is <code>par</code> = <code>seq</code>?<em><code>par p q &#8801; seqPair p q</code>, under every schedule</em></div>
  <div class="nd key">2 &#183; the one you did not &#8212; is the program parallelizable, and is <i>that</i> fork correct?<em><code>autoPar</code> proposes it; <code>rewrite_sound</code> proves it with no hypothesis</em></div>
</div>
```

:::class "steps"
* Both questions reduce to one Boolean on the program text, `wfB`, and one theorem about it.
* `wfB s = true` is decided by `decide` — kernel-checked arithmetic on the footprints the syntax
  gives, with no proof about interleavings per program.
* When it is `false` the answer is an *interleaving*: a schedule replayed against the semantics,
  ending in a heap the sequential reading does not produce.
:::

# A Hoare triple cannot say "this cell is mine"


```html
<div class="dgm tight">
  <div class="nd mono">C&#8321; : [p] := 5; y := [p]<em>write to [p], then read it back</em></div>
  <div class="nd mono">C&#8322; : [p] := 8<em>write to the same [p]</em></div>
</div>
```

```html
<div class="fan">
  <div class="nd good">{true} C&#8321; {y = 5}</div>
  <div class="nd good">{true} C&#8322; {true}</div>
  <div class="nd bad">{true} C&#8321; &#8741; C&#8322; {y = 5}<em>false &#183; a schedule runs C&#8322; between the write and the read, leaving y = 8</em></div>
</div>
```

:::class "steps"
* A triple `{P} C {Q}` quantifies over the starting state and over nothing else — in particular not
  over what another thread does while `C` runs.
* So the first triple is proved as though its command ran alone: `y := [p]` reads back the value the
  command itself wrote, which holds of every run in which nothing else touches `[p]`.
* The schedule that runs `C₂` between that write and that read does touch `[p]`, and the
  assumption the proof rests on is gone.
* Ownership is the missing notion, and it is what separation logic adds.
:::

# `∗` forbids a shared read that nothing can go wrong with


```html
<div class="rulewrap"><div class="rule">
  <div class="prem">{P} C {Q} &nbsp;&nbsp;&nbsp; {P&#8242;} C&#8242; {Q&#8242;}</div>
  <div class="bar"></div>
  <div class="conc">{P &#8727; P&#8242;} &nbsp; C &#8741; C&#8242; &nbsp; {Q &#8727; Q&#8242;}</div>
  <div class="side">O'Hearn, CONCUR 2004 &#183; <code>P &#8727; P&#8242;</code> asserts the heap <b>splits</b> into two disjoint-domain pieces</div>
</div></div>
```

```html
<div class="dgm tight">
  <div class="nd mono">thread (i, j):
  %s := 0
  for k in n { %s += A[i,k] * B[k,j] }
  C[i,j] := %s<em>n&#178; threads of a matrix multiply</em></div>
  <div class="arr lbl2">&#8594;<small>which check?</small></div>
  <div class="dgm col tight">
    <div class="nd bad">&#8727;-disjointness &#183; <span class="vd no">REJECTS</span><em>threads (0,0) and (0,1) both read row A[0, &#183;]</em></div>
    <div class="nd good">Bernstein &#183; <span class="vd ok">ACCEPTS</span><em>the shared cells are read by both and written by neither</em></div>
  </div>
</div>
```

A separating conjunction splits the heap into disjoint *domains*, so two threads may not even name
one cell. Two threads *reading* one cell is the case every real kernel is built on, and no
interleaving of two reads can disagree. What we need is a relation that permits it.

:::class "notation"
CSL recovers sharing through a *resource* `r` with a precise invariant `RI_r`, lent to one thread at
a time by `with r when B do C`. That is mutual exclusion — the right tool for a shared counter, and
a serialization of exactly the reads a matmul wants to run at once.
:::

# Memory is a function, and one equation carries the whole proof

:::class "two-col"
```leanLibCode Paralever.Core.Semantics (package := paralever) (startLine := 17) (endLine := 17) -stretch
abbrev State := Loc → Val
```

```leanLibCode Paralever.Core.Semantics (package := paralever) (startLine := 22) (endLine := 23) -stretch
def update (σ : State) (l : Loc) (v : Val) : State :=
  fun k => if k = l then v else σ k
```
:::

```html
<div class="figwrap">
<svg viewBox="0 0 860 180" role="img" aria-label="a heap as a row of cells, and an update changing exactly one of them">
  <g font-family="ui-monospace, monospace" font-size="15" text-anchor="middle">
    <text x="36" y="46" font-size="16" fill="#0f172a">&#963;</text>
    <g fill="#0f172a">
      <rect x="60"  y="26" width="58" height="30" fill="#f8fafc" stroke="#94a3b8"/><text x="89"  y="47">3</text>
      <rect x="118" y="26" width="58" height="30" fill="#f8fafc" stroke="#94a3b8"/><text x="147" y="47">4</text>
      <rect x="176" y="26" width="58" height="30" fill="#f8fafc" stroke="#94a3b8"/><text x="205" y="47">0</text>
      <rect x="234" y="26" width="58" height="30" fill="#f8fafc" stroke="#94a3b8"/><text x="263" y="47">0</text>
      <rect x="292" y="26" width="58" height="30" fill="#f8fafc" stroke="#94a3b8"/><text x="321" y="47">0</text>
      <rect x="350" y="26" width="58" height="30" fill="#f8fafc" stroke="#94a3b8"/><text x="379" y="47">7</text>
    </g>
    <g font-size="11.5" fill="#64748b" font-family="var(--sans)">
      <text x="89" y="70">0</text><text x="147" y="70">1</text><text x="205" y="70">2</text>
      <text x="263" y="70">3</text><text x="321" y="70">4</text><text x="379" y="70">5</text>
    </g>
    <text x="440" y="70" font-size="13" fill="#64748b" font-family="var(--sans)">&#8230; total: every address holds something</text>

    <text x="24" y="136" font-size="15" fill="#0f172a" text-anchor="start">&#963;[2 &#8614; 9]</text>
    <g fill="#0f172a">
      <rect x="60"  y="116" width="58" height="30" fill="#f8fafc" stroke="#94a3b8"/><text x="89"  y="137">3</text>
      <rect x="118" y="116" width="58" height="30" fill="#f8fafc" stroke="#94a3b8"/><text x="147" y="137">4</text>
      <rect x="176" y="116" width="58" height="30" fill="#dcfce7" stroke="#16a34a" stroke-width="2.4"/><text x="205" y="137" fill="#15803d">9</text>
      <rect x="234" y="116" width="58" height="30" fill="#f8fafc" stroke="#94a3b8"/><text x="263" y="137">0</text>
      <rect x="292" y="116" width="58" height="30" fill="#f8fafc" stroke="#94a3b8"/><text x="321" y="137">0</text>
      <rect x="350" y="116" width="58" height="30" fill="#f8fafc" stroke="#94a3b8"/><text x="379" y="137">7</text>
    </g>
  </g>
  <g font-size="13.5" font-style="italic" fill="#475569" font-family="var(--sans)">
    <text x="440" y="124" text-anchor="start">one cell differs &#8212; and that is a <tspan font-weight="700" fill="#15803d">theorem</tspan>, not a convention:</text>
    <text x="440" y="146" text-anchor="start" font-family="ui-monospace, monospace" font-size="14" fill="#0f172a">k &#8800; l &#8594; &#963;[l &#8614; v] k = &#963; k</text>
  </g>
</svg>
</div>
```


:::class "steps"
* *Total* — there is no unallocated cell and no crash on a bad read, so no definedness side condition
  is ever carried. Ownership is a *footprint*, not a heap domain.
* *Addresses are numbers*, so "is `i*n + j` inside `[b, b+len)`?" is linear arithmetic and a machine
  decides it.
* `update_other` is the one load-bearing fact. Everything that follows lifts it from one cell to
  whole programs: to one program, to a program observed on two heaps, to two sibling branches, and
  finally to one step of an arbitrary interleaving.
:::

# A program is a tree, and `par` is the only node that branches

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
<div class="figwrap">
<svg viewBox="0 0 820 250" role="img" aria-label="the program tree for a fork of two branches, root at the top">
  <defs>
    <marker id="tr" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#64748b"/>
    </marker>
  </defs>
  <g font-family="ui-monospace, monospace" font-size="14" text-anchor="middle" fill="#0f172a">
    <rect x="320" y="12" width="180" height="32" rx="7" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.4"/>
    <text x="410" y="33" fill="#312e81">par &#928;[ p q ] k</text>

    <rect x="120" y="100" width="210" height="32" rx="6" fill="#f8fafc" stroke="#94a3b8"/>
    <text x="225" y="121">write 5 1</text>
    <rect x="400" y="100" width="300" height="32" rx="6" fill="#f8fafc" stroke="#94a3b8"/>
    <text x="550" y="121">read 7 (&#955;v. write 8 v)</text>

    <rect x="120" y="178" width="210" height="32" rx="6" fill="#f1f5f9" stroke="#cbd5e1"/>
    <text x="225" y="199">pure ()</text>
    <rect x="400" y="178" width="300" height="32" rx="6" fill="#f1f5f9" stroke="#cbd5e1"/>
    <text x="550" y="199">pure ()</text>
  </g>
  <g stroke="#64748b" stroke-width="1.5" fill="none" marker-end="url(#tr)">
    <path d="M 410 44 L 410 72 L 225 72 L 225 97"/>
    <path d="M 410 44 L 410 72 L 550 72 L 550 97"/>
    <path d="M 225 132 L 225 175"/>
    <path d="M 550 132 L 550 175"/>
  </g>
  <g font-size="13" font-style="italic" fill="#475569" font-family="var(--sans)">
    <text x="760" y="33" text-anchor="start">N children,</text>
    <text x="760" y="50" text-anchor="start">one continuation</text>
    <text x="80" y="121" text-anchor="end">p</text>
    <text x="760" y="121" text-anchor="start">q</text>
  </g>
</svg>
</div>
```

:::class "steps"
* A program is *data*, so "for every program `p` …" is an ordinary quantifier, and `par` is a
  constructor whose meaning Lean does not already know.
* Lean's `Task` could not host this: `(Task.spawn f).get = f ()` holds by `rfl`, so parallel and
  sequential would be the *same term* and every theorem about them vacuous.
* `par` is N-ary and heterogeneous from the start — one node with a children spine, not a nest of
  binary forks — so there is no separate metatheory for `k`-way forks.
* `ParM` is inductive, so `while true` is unrepresentable: only terminating programs exist, and that
  boundary is permanent rather than a gap.
:::

# `runSeq` walks the tree left to right, so it names exactly one answer

```leanLibCode Paralever.Core.Access (package := paralever) (startLine := 151) (endLine := 157) -stretch
def runSeq {τ : Type} : ParM τ → State → τ × State
  | .pure a,      σ => (a, σ)
  | .read l k,    σ => runSeq (k (σ l)) σ
  | .write l v k, σ => runSeq (k ()) (σ.update l v)
  | .par cs k,    σ =>
      let r := runChilds cs σ
      runSeq (k r.1) r.2
```

```html
<div class="figwrap">
<svg viewBox="0 0 880 200" role="img" aria-label="runSeq running p then q, threading the heap through three snapshots">
  <defs>
    <marker id="rq" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#2563eb"/>
    </marker>
  </defs>
  <g font-family="ui-monospace, monospace" font-size="14.5" text-anchor="middle">
    <rect x="20"  y="60" width="150" height="38" rx="7" fill="#f8fafc" stroke="#94a3b8"/>
    <text x="95" y="84" fill="#0f172a">&#963;&#8320;</text>
    <rect x="250" y="60" width="150" height="38" rx="7" fill="#f8fafc" stroke="#94a3b8"/>
    <text x="325" y="84" fill="#0f172a">&#963;&#8321; = &#963;&#8320;[5 &#8614; 1]</text>
    <rect x="480" y="60" width="210" height="38" rx="7" fill="#f8fafc" stroke="#94a3b8"/>
    <text x="585" y="84" fill="#0f172a">&#963;&#8322; = &#963;&#8321;[8 &#8614; &#963;&#8321; 7]</text>
  </g>
  <g stroke="#2563eb" stroke-width="1.8" fill="none" marker-end="url(#rq)">
    <path d="M 170 79 L 247 79"/>
    <path d="M 400 79 L 477 79"/>
  </g>
  <g font-size="13.5" fill="#1d4ed8" text-anchor="middle" font-family="ui-monospace, monospace">
    <text x="208" y="48">p</text>
    <text x="438" y="48">q</text>
  </g>
  <g font-size="13" font-style="italic" fill="#475569" font-family="var(--sans)">
    <text x="208" y="128">write 5 1</text>
    <text x="438" y="128">read 7, write 8</text>
    <text x="440" y="172" text-anchor="middle">a total function on a finite tree &#8212; no schedule, no choice, no partiality</text>
  </g>
</svg>
</div>
```

:::class "steps"
* `runSeq` is a *function*, so it returns one answer and one heap. It is the reference reading, and
  the theorem's whole job is to show the parallel machine cannot land anywhere else.
* It is defined on the same tree the parallel machine runs, not on a translation of it, so "the
  sequential reading of this program" needs no separate language.
* For a fork it runs the children left to right, threading the heap: child 2 starts where child 1
  finished.
:::

# Footprints are measured along that run — staggered, and that is the crux

:::class "two-col"
```leanLibCode Paralever.Core.Access (package := paralever) (startLine := 201) (endLine := 203) -stretch
def childFootprints {αs : List Type} : Childs ParM αs → State → List Footprint
  | .nil,       _ => []
  | .cons p ps, σ => accesses p σ :: childFootprints ps (runSeq p σ).2
```

```html
<div class="nd mono plain wide">childFootprints &#928;[ p q ] &#963;&#8320;
  = [ (reads [], writes [5]),
      (reads [7], writes [8]) ]<em>the second entry was measured at &#963;&#8321;, not at &#963;&#8320;</em></div>
```
:::

```html
<div class="figwrap">
<svg viewBox="0 0 880 210" role="img" aria-label="the reference run measures the second child after the first finished, while a real schedule may run it first">
  <defs>
    <marker id="sg" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#64748b"/>
    </marker>
  </defs>
  <g font-family="ui-monospace, monospace" font-size="14" text-anchor="middle">
    <rect x="40" y="26" width="300" height="34" rx="7" fill="#eff6ff" stroke="#2563eb" stroke-width="2.2"/>
    <text x="190" y="49" fill="#0f172a">q measured at &#963;&#8321;</text>
    <rect x="40" y="128" width="300" height="34" rx="7" fill="#fef2f2" stroke="#dc2626" stroke-width="2.2"/>
    <text x="190" y="151" fill="#0f172a">q actually runs at &#963;&#8320;</text>
  </g>
  <g font-size="13.5" font-style="italic" fill="#475569" font-family="var(--sans)" text-anchor="start">
    <text x="366" y="42" fill="#1d4ed8">the hypothesis is stated here &#8212; after p finished</text>
    <text x="366" y="60">so the value read from cell 7 is <tspan font-family="ui-monospace, monospace">&#963;&#8321; 7</tspan></text>
    <text x="366" y="144" fill="#b91c1c">the machine is free to step q first</text>
    <text x="366" y="162">so the value read from cell 7 is <tspan font-family="ui-monospace, monospace">&#963;&#8320; 7</tspan></text>
  </g>
  <g stroke="#64748b" stroke-width="1.6" fill="none" marker-end="url(#sg)" stroke-dasharray="5 4">
    <path d="M 190 60 L 190 125"/>
  </g>
  <text x="440" y="196" text-anchor="middle" font-size="15" font-style="italic" fill="#0f172a">two different heaps &#8212; and nothing so far says the two readings agree</text>
</svg>
</div>
```

This gap is the entire technical content of the theorem. It is closed once, and used in exactly one
case of one lemma.

# Independence is Bernstein, and `WellFormed` asks it at every fork

:::class "two-col"
```leanLibCode Paralever.Core.Access (package := paralever) (startLine := 65) (endLine := 66) -stretch
def Indep (f₁ f₂ : Footprint) : Prop :=
  Disjoint f₁.writes f₂.writes ∧ Disjoint f₁.writes f₂.reads ∧ Disjoint f₂.writes f₁.reads
```

```html
<div class="dgm col tight">
  <div class="nd bad">W&#8321; &#8745; W&#8322; = &#8709;<em>C1 &#183; no cell written twice</em></div>
  <div class="nd bad">W&#8321; &#8745; R&#8322; = &#8709;<em>C2 &#183; nothing written then read</em></div>
  <div class="nd bad">W&#8322; &#8745; R&#8321; = &#8709;<em>C3 &#183; nor the other way round</em></div>
  <div class="nd good">R&#8321; &#8745; R&#8322; &#183; unconstrained<em>there is no fourth clause, and that is the point</em></div>
</div>
```
:::

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
* Checking only the outermost fork is unsound — a nested fork inside a thread can race on cells the
  outer check never compares — so the obligation recurses into every `par` node.
* Each node is checked against *the heap that node sees along the canonical run*, which is what makes
  the obligation a statement about the program rather than about one heap.
* The three clauses are used exactly: two of them close the staggered-measurement gap, and all three
  are what excludes a race. Nothing in the definition is spare.
:::

# The machine: one child moves, or the fork joins, or it is `wrong`

```leanLibCode Paralever.Core.Semantics (package := paralever) (startLine := 138) (endLine := 149) -stretch
def step {α : Type} : ParM α → State → List (Conf α)
  | .pure _,      _ => []
  | .read l k,    σ => [.run (k (σ l)) σ]
  | .write l v k, σ => [.run (k ()) (σ.update l v)]
  | .par cs k,    σ =>
      if racingAll (nextAccsChilds cs) then [.wrong]
      else match allPure cs with
        | some vs => [.run (k vs) σ]
        | none    => (stepChilds cs σ).map fun r =>
            match r with
            | some x => .run (.par x.1 k) x.2
            | none   => .wrong
```

:::class "two-col"
```leanLibCode Paralever.Core.Semantics (package := paralever) (startLine := 174) (endLine := 176) -stretch
inductive Reaches {α : Type} : Conf α → Conf α → Prop where
  | refl {c} : Reaches c c
  | tail {c c' c''} : Reaches c c' → c'' ∈ stepC c' → Reaches c c''
```

```html
<div class="dgm col tight">
  <div class="nd">a `par` offers <b>every</b> ready child<em>so every interleaving is a <code>Reaches</code> path</em></div>
  <div class="nd bad">two ready accesses collide &#8594; <code>wrong</code><em>absorbing: a racy program reaches no answer at all</em></div>
</div>
```
:::

Races go to `wrong` rather than to a wrong answer, following Reynolds' grainless semantics. That is
what makes the atomic grain irrelevant: there is no "last writer wins", so no theorem here depends on
how coarsely a write is implemented.

# The theorem: a well-formed program has exactly one reachable outcome

```leanLibCode Paralever.Theory.WellFormedCanonical (package := paralever) (startLine := 1462) (endLine := 1464) -stretch
theorem wellFormed_canonical {τ : Type} (p : ParM τ) :
    ∀ σ r σ', WellFormed p σ → (Reaches (.run p σ) (.run (.pure r) σ') ↔ (r, σ') = runSeq p σ) :=
  wellFormed_canonical_all.1 p
```

```html
<div class="figwrap">
<svg viewBox="0 0 880 230" role="img" aria-label="many schedules out of one configuration, all terminating at one outcome">
  <defs>
    <marker id="cn" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#64748b"/>
    </marker>
  </defs>
  <g font-family="ui-monospace, monospace" font-size="13.5" text-anchor="middle" fill="#0f172a">
    <rect x="20"  y="92" width="140" height="34" rx="7" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.8"/>
    <text x="90" y="114">p, &#963;</text>

    <rect x="290" y="16"  width="150" height="30" rx="6" fill="#f8fafc" stroke="#cbd5e1"/><text x="365" y="37">P&#8321;, &#963;&#8321;</text>
    <rect x="290" y="62"  width="150" height="30" rx="6" fill="#f8fafc" stroke="#cbd5e1"/><text x="365" y="83">P&#8322;, &#963;&#8322;</text>
    <rect x="290" y="126" width="150" height="30" rx="6" fill="#f8fafc" stroke="#cbd5e1"/><text x="365" y="147">P&#8323;, &#963;&#8323;</text>
    <rect x="290" y="172" width="150" height="30" rx="6" fill="#f8fafc" stroke="#cbd5e1"/><text x="365" y="193">P&#8324;, &#963;&#8324;</text>

    <rect x="600" y="92" width="250" height="34" rx="7" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.6"/>
    <text x="725" y="114" fill="#312e81">pure r, &#963;&#8242;</text>
  </g>
  <g stroke="#64748b" stroke-width="1.4" fill="none" marker-end="url(#cn)">
    <path d="M 160 109 L 220 109 L 220 31 L 287 31"/>
    <path d="M 160 109 L 220 109 L 220 77 L 287 77"/>
    <path d="M 160 109 L 220 109 L 220 141 L 287 141"/>
    <path d="M 160 109 L 220 109 L 220 187 L 287 187"/>
    <path d="M 440 31 L 520 31 L 520 105 L 597 105"/>
    <path d="M 440 77 L 520 77 L 520 105"/>
    <path d="M 440 141 L 520 141 L 520 113 L 597 113"/>
    <path d="M 440 187 L 520 187 L 520 113"/>
  </g>
  <g font-size="13" font-style="italic" fill="#475569" font-family="var(--sans)" text-anchor="middle">
    <text x="365" y="214">different schedules visit different configurations</text>
    <text x="725" y="146" fill="#4f46e5">and <tspan font-family="ui-monospace, monospace">(r, &#963;&#8242;) = runSeq p &#963;</tspan></text>
  </g>
</svg>
</div>
```

:::class "steps"
* Read it as an *iff*, because both halves do work. `→` is *safety*: no schedule terminates
  anywhere else. `←` is *liveness*: that outcome is actually reached.
* Without liveness the theorem would be satisfied by a program with no terminating execution at all,
  which is how a soundness statement can be true and empty.
* Confluence and normalization, in one biconditional, for a language whose fork is N-ary.
:::

# Two ways to attack it fail, and the third is a conservation law

```html
<div class="dgm col tight">
  <div class="nd bad wide">1 &#183; induct on steps, comparing the two machines<em>false &#8212; after one step the parallel machine has done q's read and the sequential one p's write: there is no step-by-step correspondence</em></div>
  <div class="nd bad wide">2 &#183; enumerate the schedules<em>hopeless &#8212; two children of n and m steps give C(n+m, n) interleavings, and children nest</em></div>
  <div class="nd key wide">3 &#183; find a quantity that never changes<em>computable at any configuration, invariant under stepping, and equal to the answer at the end</em></div>
</div>
```

:::class "steps"
* If such a quantity exists, every terminating path must end at the same answer — the quantity was
  fixed at the start and the end merely reads it off. Whatever route a ball rolls down a hill, its
  energy at the bottom is the same, so the route need not be known.
* The candidate is already in hand: `Φ(P, σ) := runSeq P σ`. It is computable at any
  configuration — apply the function — and at `pure r, σ′` it is `(r, σ′)` by
  `runSeq`'s own first line.
* So the plan: `Φ` survives one step; `WellFormed` survives one step, so the first fact applies
  again; iterate along the path; read `Φ` off at the end.
:::

# The whole difficulty is one equation: `σ₁ 7 = σ₀ 7`

```html
<div class="dgm tight">
  <div class="nd mono plain wide">p = write 5 1 &#183;        q = read 7 (&#955;v. write 8 v)        at &#963;&#8320;<em>the tail steps first: q performs its read <b>at &#963;&#8320;</b>, so q&#8323; = write 8 (&#963;&#8320; 7)</em></div>
</div>
```

```html
<div class="figwrap">
<svg viewBox="0 0 880 215" role="img" aria-label="the two readings of the same fork, differing only in which heap cell 7 was read from">
  <g font-family="ui-monospace, monospace" font-size="14" text-anchor="start">
    <rect x="20" y="16" width="400" height="88" rx="8" fill="#fef2f2" stroke="#dc2626" stroke-width="2"/>
    <text x="38" y="40" fill="#0f172a" font-size="13">runChilds &#928;[ p q&#8323; ] &#963;&#8320;</text>
    <text x="38" y="62" fill="#334155" font-size="13">run p &#8594; &#963;&#8321;;  then q&#8323; writes <tspan fill="#b91c1c">&#963;&#8320; 7</tspan> into 8</text>
    <text x="38" y="88" fill="#0f172a" font-size="14">&#963;&#8321;[8 &#8614; <tspan fill="#b91c1c">&#963;&#8320; 7</tspan>]</text>

    <rect x="460" y="16" width="400" height="88" rx="8" fill="#eff6ff" stroke="#2563eb" stroke-width="2"/>
    <text x="478" y="40" fill="#0f172a" font-size="13">runChilds &#928;[ p q ] &#963;&#8320;</text>
    <text x="478" y="62" fill="#334155" font-size="13">run p &#8594; &#963;&#8321;;  then q reads 7 &#8212; getting <tspan fill="#1d4ed8">&#963;&#8321; 7</tspan></text>
    <text x="478" y="88" fill="#0f172a" font-size="14">&#963;&#8321;[8 &#8614; <tspan fill="#1d4ed8">&#963;&#8321; 7</tspan>]</text>
  </g>
  <text x="440" y="136" text-anchor="middle" font-size="15.5" fill="#0f172a">these agree <tspan font-weight="700">if and only if</tspan> <tspan font-family="ui-monospace, monospace">&#963;&#8321; 7 = &#963;&#8320; 7</tspan></text>
  <text x="440" y="164" text-anchor="middle" font-size="14" fill="#15803d" font-family="ui-monospace, monospace">7 &#8713; writes (accesses p &#963;&#8320;) = {5}</text>
  <text x="440" y="190" text-anchor="middle" font-size="13.5" font-style="italic" fill="#475569" font-family="var(--sans)">clause C2 of <tspan font-family="ui-monospace, monospace">Indep</tspan>, together with the frame lemma &#8212; and nothing else</text>
</svg>
</div>
```

That single equation is the entire difficulty of the theorem. Everything that follows is machinery for
saying it in general: at `N` children instead of two, and at an arbitrary depth of nesting.

# Four lemmas lift `update_other` from one cell to whole programs

```html
<div class="figwrap">
<svg viewBox="0 0 880 300" role="img" aria-label="frame, locality, isolation and no-race feeding the conservation lemma">
  <defs>
    <marker id="lm" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#4f46e5"/>
    </marker>
  </defs>
  <g font-size="13" text-anchor="middle">
    <rect x="18" y="14" width="200" height="74" rx="8" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/>
    <text x="118" y="34" font-family="ui-monospace, monospace" font-size="13.5" fill="#0f172a">runSeq_frame</text>
    <text x="118" y="56" fill="#334155">a program leaves alone</text>
    <text x="118" y="74" fill="#334155">every cell it does not write</text>

    <rect x="240" y="14" width="200" height="74" rx="8" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/>
    <text x="340" y="34" font-family="ui-monospace, monospace" font-size="13.5" fill="#0f172a">..._locality</text>
    <text x="340" y="56" fill="#334155">two heaps agreeing where</text>
    <text x="340" y="74" fill="#334155">it looks &#8658; same run</text>

    <rect x="462" y="14" width="200" height="74" rx="8" fill="#eff6ff" stroke="#2563eb" stroke-width="2.4"/>
    <text x="562" y="34" font-family="ui-monospace, monospace" font-size="13.5" fill="#0f172a">..._isolated</text>
    <text x="562" y="56" fill="#1e3a5f">q cannot tell whether</text>
    <text x="562" y="74" fill="#1e3a5f">p has already run</text>

    <rect x="684" y="14" width="180" height="74" rx="8" fill="#eff6ff" stroke="#2563eb" stroke-width="2.4"/>
    <text x="774" y="34" font-family="ui-monospace, monospace" font-size="13.5" fill="#0f172a">no_race_of_indep</text>
    <text x="774" y="56" fill="#1e3a5f">independent branches</text>
    <text x="774" y="74" fill="#1e3a5f">cannot collide</text>
  </g>
  <g stroke="#94a3b8" stroke-width="1.6" fill="none" marker-end="url(#lm)">
    <path d="M 218 51 L 237 51"/>
    <path d="M 440 51 L 459 51"/>
  </g>
  <g font-size="12.5" font-style="italic" fill="#475569" text-anchor="middle">
    <text x="118" y="110">from <tspan font-family="ui-monospace, monospace">update_other</tspan>, by induction</text>
    <text x="340" y="110">carries 3 conclusions at once</text>
    <text x="562" y="110">uses C2 and C1</text>
    <text x="774" y="110">uses C1, C2 and C3</text>
  </g>
  <g stroke="#4f46e5" stroke-width="1.8" fill="none" marker-end="url(#lm)">
    <path d="M 562 88 L 562 126 L 300 126 L 300 164"/>
    <path d="M 774 88 L 774 126 L 640 126 L 640 164"/>
  </g>
  <g font-size="13.5" text-anchor="middle">
    <rect x="170" y="168" width="260" height="56" rx="8" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.4"/>
    <text x="300" y="190" font-family="ui-monospace, monospace" font-size="14" fill="#312e81">step_combined</text>
    <text x="300" y="212" fill="#312e81">one step conserves runSeq</text>

    <rect x="520" y="168" width="240" height="56" rx="8" fill="#f1f5f9" stroke="#0d9488" stroke-width="2.2"/>
    <text x="640" y="190" font-family="ui-monospace, monospace" font-size="14" fill="#0f172a">reaches_par_of_...</text>
    <text x="640" y="212" fill="#334155">the sequential schedule is legal</text>
  </g>
  <text x="440" y="262" text-anchor="middle" font-size="13.5" font-style="italic" fill="#1d4ed8">independence enters at isolation and no-race, and nowhere else in the development</text>
  <text x="440" y="286" text-anchor="middle" font-size="13" font-style="italic" fill="#475569">the four above are about a single run; everything below is about whole interleavings</text>
</svg>
</div>
```

:::class "two-col"
```leanLibCode Paralever.Theory.WellFormedCanonical (package := paralever) (startLine := 39) (endLine := 41) -stretch
theorem runSeq_frame {τ : Type} (p : ParM τ) (σ : State) :
    ∀ l, l ∉ (accesses p σ).writes → (runSeq p σ).2 l = σ l :=
  runSeq_frame_all.1 p σ
```

```leanLibCode Paralever.Theory.WellFormedCanonical (package := paralever) (startLine := 178) (endLine := 181) -stretch
theorem accesses_runSeq_isolated {α β : Type} (p : ParM α) (q : ParM β) (σ : State)
    (h : Indep (accesses p σ) (accesses q (runSeq p σ).2)) :
    accesses q (runSeq p σ).2 = accesses q σ ∧
    (runSeq q (runSeq p σ).2).1 = (runSeq q σ).1 := by
```
:::

Isolation is proved by taking `F := writes (accesses p σ)` in locality: `q` does not touch `F` is
clauses C1 and C2 verbatim, and the two heaps agree outside `F` is the frame lemma. Two hypotheses,
both already in hand.

# Conservation: every step leaves `runSeq` exactly where it was

```leanLibCode Paralever.Theory.WellFormedCanonical (package := paralever) (startLine := 902) (endLine := 906) -stretch
theorem step_combined {τ : Type} (P : ParM τ) :
    ∀ σ, WellFormed P σ → ∀ P3 σ3, Conf.run P3 σ3 ∈ stepC (Conf.run P σ) →
      runSeq P3 σ3 = runSeq P σ ∧
      (∀ F, FDisjoint F (accesses P σ) → FDisjoint F (accesses P3 σ3)) :=
  step_combined_all.1 P
```

```html
<table class="dgmt">
<thead><tr><th>the step</th><th>what the proof does</th><th>independence?</th></tr></thead>
<tbody>
<tr><td>read l k</td><td><code>runSeq</code>'s own defining equation, read backwards — the two sides are the same term</td><td>no</td></tr>
<tr><td>write l v k</td><td>same, at the updated heap</td><td>no</td></tr>
<tr><td>par, racing</td><td>the only successor is <code>wrong</code>, so the hypothesis cannot be met</td><td>no</td></tr>
<tr><td>par, joining</td><td>every child is a leaf, so running them changes nothing</td><td>no</td></tr>
<tr><td>par, child moves</td><td>reduces to the children-level statement of this very lemma</td><td>no</td></tr>
<tr><td>children, <b>head</b> moves</td><td>the head is the child <code>runSeq</code> runs first anyway, so stepping it is what <code>runSeq</code> was going to do</td><td>no</td></tr>
<tr class="gap"><td>children, <b>tail</b> moves</td><td>the step happened at <code>σ</code>; the hypothesis is stated at <code>τ₁</code> — the three moves below</td><td><b>yes</b></td></tr>
</tbody>
</table>
```

Every row but the last is `runSeq`'s own defining equation, read in the other direction. The last row
is the theorem.

# The one case with content: a child that is not the leftmost moves

```html
<div class="figwrap">
<svg viewBox="0 0 880 250" role="img" aria-label="the three moves that close the gap between the heap the step happened at and the heap the hypothesis is stated at">
  <defs>
    <marker id="mv" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#4f46e5"/>
    </marker>
  </defs>
  <g font-family="ui-monospace, monospace" font-size="14" text-anchor="middle">
    <rect x="40" y="18" width="220" height="34" rx="7" fill="#fef2f2" stroke="#dc2626" stroke-width="2"/>
    <text x="150" y="41" fill="#0f172a">the step happened at σ</text>
    <rect x="620" y="18" width="220" height="34" rx="7" fill="#eff6ff" stroke="#2563eb" stroke-width="2"/>
    <text x="730" y="41" fill="#0f172a">the hypothesis lives at τ₁</text>
  </g>
  <g stroke="#4f46e5" stroke-width="1.8" fill="none" marker-end="url(#mv)">
    <path d="M 620 35 L 263 35"/>
    <path d="M 150 52 L 150 86"/>
    <path d="M 440 134 L 440 168"/>
  </g>
  <text x="440" y="24" text-anchor="middle" font-size="12.5" font-style="italic" fill="#4f46e5">1 · isolation carries the tail's footprint, answer and hypotheses back to σ</text>
  <g font-size="13.5" text-anchor="middle">
    <rect x="40" y="90" width="340" height="44" rx="7" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/>
    <text x="210" y="109" fill="#0f172a">2 · the head does not notice</text>
    <text x="210" y="127" font-size="12" fill="#475569">the tail wrote only inside its own footprint</text>

    <rect x="420" y="90" width="420" height="44" rx="7" fill="#f8fafc" stroke="#94a3b8" stroke-width="1.6"/>
    <text x="630" y="109" fill="#0f172a">3 · replay the tail's step where it is measured</text>
    <text x="630" y="127" font-size="12" fill="#475569">legal at σ, so available at τ₁ by move 1</text>
  </g>
  <g font-size="13.5" text-anchor="middle">
    <rect x="230" y="172" width="420" height="44" rx="8" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.4"/>
    <text x="440" y="191" font-family="ui-monospace, monospace" fill="#312e81">runChilds cs₃ σ₃ = runChilds cs σ</text>
    <text x="440" y="209" font-size="12" fill="#312e81">which is what the fork case reduced to</text>
  </g>
  <text x="440" y="240" text-anchor="middle" font-size="13" font-style="italic" fill="#475569">pinning the replayed heap to <tspan font-style="normal" font-weight="700">exactly</tspan> the right one needs the footprint conclusion, one level down</text>
</svg>
</div>
```

:::class "steps"
* Move 1 is where `Indep` is spent: the head's footprint is independent of every later child's, so
  the tail computes the same footprint and the same answer at `σ` as at `τ₁`.
* Move 2 is locality with `F` taken to be the tail's writes — the same lemma, in the other direction.
* The two conclusions cannot be separated. Proving only the `runSeq` equality leaves no way to
  re-establish the hypothesis for the next step, and move 3 needs the footprint fact at the same
  inductive depth at which it is proving the value fact.
:::

# `WellFormed` survives every step, so the invariant holds along every path

:::class "two-col"
```leanLibCode Paralever.Theory.WellFormedCanonical (package := paralever) (startLine := 1237) (endLine := 1239) -stretch
theorem WellFormed_preserved {τ : Type} (P : ParM τ) :
    ∀ σ, WellFormed P σ → ∀ P3 σ3, Conf.run P3 σ3 ∈ stepC (Conf.run P σ) → WellFormed P3 σ3 :=
  WellFormed_preserved_all.1 P
```

```leanLibCode Paralever.Theory.WellFormedCanonical (package := paralever) (startLine := 1252) (endLine := 1254) -stretch
theorem runSeq_invariant_chain {τ : Type} (P : ParM τ) (σ : State) (hwf : WellFormed P σ)
    (C : Conf τ) (h : Reaches (.run P σ) C) :
    ∀ P' σ', C = .run P' σ' → WellFormed P' σ' ∧ runSeq P' σ' = runSeq P σ := by
```
:::

```html
<div class="figwrap">
<svg viewBox="0 0 880 210" role="img" aria-label="wf holding at every configuration of two different schedules, with runSeq reading the same value at each">
  <defs>
    <marker id="iv" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M 0 0 L 10 5 L 0 10 z" fill="#64748b"/>
    </marker>
  </defs>
  <g font-family="ui-monospace, monospace" font-size="13" text-anchor="middle" fill="#0f172a">
    <rect x="20"  y="78" width="120" height="30" rx="6" fill="#f8fafc" stroke="#94a3b8"/><text x="80"  y="98">P, &#963;</text>
    <rect x="250" y="30" width="120" height="30" rx="6" fill="#f8fafc" stroke="#cbd5e1"/><text x="310" y="50">P&#8321;, &#963;&#8321;</text>
    <rect x="250" y="126" width="120" height="30" rx="6" fill="#f8fafc" stroke="#cbd5e1"/><text x="310" y="146">P&#8321;&#8242;, &#963;&#8321;&#8242;</text>
    <rect x="480" y="30" width="120" height="30" rx="6" fill="#f8fafc" stroke="#cbd5e1"/><text x="540" y="50">P&#8322;, &#963;&#8322;</text>
    <rect x="480" y="126" width="120" height="30" rx="6" fill="#f8fafc" stroke="#cbd5e1"/><text x="540" y="146">P&#8322;&#8242;, &#963;&#8322;&#8242;</text>
    <rect x="710" y="78" width="150" height="30" rx="6" fill="#eef2ff" stroke="#4f46e5" stroke-width="2.4"/><text x="785" y="98" fill="#312e81">pure r, &#963;&#8242;</text>
  </g>
  <g stroke="#64748b" stroke-width="1.4" fill="none" marker-end="url(#iv)">
    <path d="M 140 93 L 190 93 L 190 45 L 247 45"/>
    <path d="M 140 93 L 190 93 L 190 141 L 247 141"/>
    <path d="M 370 45 L 477 45"/>
    <path d="M 370 141 L 477 141"/>
    <path d="M 600 45 L 655 45 L 655 90 L 707 90"/>
    <path d="M 600 141 L 655 141 L 655 96 L 707 96"/>
  </g>
  <g font-size="12" fill="#15803d" text-anchor="middle" font-family="ui-monospace, monospace">
    <text x="80" y="124">WellFormed</text><text x="310" y="76">WellFormed</text><text x="310" y="172">WellFormed</text>
    <text x="540" y="76">WellFormed</text><text x="540" y="172">WellFormed</text><text x="785" y="124">WellFormed</text>
  </g>
  <text x="440" y="200" text-anchor="middle" font-size="13.5" font-style="italic" fill="#1d4ed8" font-family="var(--sans)">runSeq reads the same (r, &#963;&#8242;) at every one of these configurations</text>
</svg>
</div>
```

This resolves what looks like a circularity. `WellFormed` is defined by measuring footprints along
`runSeq` — a solo, left-first run — while the conclusion is about interleavings, where no such order
exists. Chaining says the hypothesis is nonetheless available at every configuration of every
schedule, because footprints only *shrink* as a program steps and independence is monotone under
shrinking either side.

# Safety is three lines; liveness exhibits one schedule

```html
<div class="dgm col tight">
  <div class="nd good wide">&#8594; &nbsp; apply chaining to the run, at <code>P&#8242; := pure r</code><em><code>runSeq (pure r) &#963;&#8242; = runSeq p &#963;</code>, and the left side is <code>(r, &#963;&#8242;)</code> by definition &#8212; so <code>(r, &#963;&#8242;) = runSeq p &#963;</code></em></div>
  <div class="nd good wide">&#8592; &nbsp; build the left-to-right schedule<em>run child 1 to completion &#8212; which is this theorem one level down &#8212; then child 2, then step through the join into the continuation</em></div>
</div>
```

:::class "steps"
* The forward direction uses *no induction on the program at all*: the induction already happened,
  inside conservation and chaining. That is the payoff of finding the right invariant.
* The backward direction is a construction, and the one thing that could go wrong is tripping the race
  test. `no_race_of_indep` rules that out — which is where Bernstein's third clause is spent.
* The children-level motive is "you can run every child to completion, left to right". It is mutual
  with the main statement because running one child to completion *is* the main statement, one level
  down.
:::

# `par ≡ seq` by unfolding — independence is not mentioned

```leanLibCode Paralever.Theory.Sequentialize (package := paralever) (startLine := 18) (endLine := 19) -stretch
def ParSeqEq {α : Type} (p q : ParM α) (σ : State) : Prop :=
  ∀ r σ', Reaches (.run p σ) (.run (.pure r) σ') ↔ Reaches (.run q σ) (.run (.pure r) σ')
```

```html
<div class="dgm col tight">
  <div class="nd mono">Reaches ⟨parAll ps, σ⟩ ⟨pure r, σ'⟩<em>what we want to relate</em></div>
  <div class="arr">⟺<small>canonical outcomes, at the hypothesis</small></div>
  <div class="nd mono">(r, σ') = runSeq (parAll ps) σ</div>
  <div class="arr">⟺<small>runSeq_parAll_eq_seqAll — pure unfolding</small></div>
  <div class="nd mono">(r, σ') = runSeq (seqAll ps) σ</div>
  <div class="arr">⟺<small>canonical outcomes again, hypothesis transferred</small></div>
  <div class="nd mono blue">Reaches ⟨seqAll ps, σ⟩ ⟨pure r, σ'⟩</div>
</div>
```

```leanLibCode Paralever.Theory.Sequentialize (package := paralever) (startLine := 172) (endLine := 177) -stretch
theorem parAll_par_seq_eq {τ : Type} (ps : List (ParM τ)) (σ : State)
    (h : WellFormed (ParM.parAll ps) σ) : ParSeqEq (ParM.parAll ps) (ParM.seqAll ps) σ := by
  intro r σ'
  rw [wellFormed_canonical _ σ r σ' h,
      wellFormed_canonical _ σ r σ' (wellFormed_of_seqAll ps σ h),
      runSeq_parAll_eq_seqAll]
```

:::class "steps"
* Both sides have *exactly one* outcome, each named by its own `runSeq`. So the two sides have the same
  outcomes as soon as they have the same `runSeq` — three rewrites, and the proof is over.
* `runSeq (parPair p q) σ = runSeq (seqPair p q) σ` is a definitional identity, true even for
  racy programs: `runSeq` is left-to-right whether the node is a fork or a bind.
* `seqAll ps` has no `par` node, so it carries no independence obligation: unfolding along `bind`
  leaves exactly the conjuncts the fork already gave.
* The N-ary form is not a corollary of the binary one. `parAll ps` is a *single* node, and the
  induction over the children list happened once, in conservation's 2-to-N step.
:::

# Drop the hypothesis and the conclusion is false

```html
<div class="dgm tight">
  <div class="nd mono bad">p = write 5 1
q&#8242; = read 5 (&#955;v. write 8 v)<em>q&#8242; reads the cell p writes &#183; W&#8321; &#8745; R&#8322; = {5}, so C2 fails</em></div>
  <div class="arr lbl2">&#8594;<small>two schedules</small></div>
  <div class="dgm col tight">
    <div class="nd bad">q&#8242; first &#183; cell 8 &#8614; &#963;&#8320; 5<em>reads the old value</em></div>
    <div class="nd bad">p first &#183; cell 8 &#8614; 1<em>reads the new one</em></div>
  </div>
</div>
```

:::class "steps"
* Two different terminal heaps from one configuration, so `wellFormed_canonical`'s conclusion is
  *false* here — and `WellFormed` is exactly what fails. The hypothesis is load-bearing, in Lean, on
  a program we exhibit.
* A second counterexample fails *differently*: a loop-carried dependence `A[i] := A[i-1] + 1` has an
  obligation that is unprovable rather than refuted, and it is kept as a test for that reason.
* `Examples/Races/` holds both, and property tests check both directions — equality on random
  independent programs, `wrong` on random racy ones.
:::

# The surface language: declared memory, registers, and one fork

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

```leanLibCode Lang.Core.Prog (package := paralever) (startLine := 261) (endLine := 273) -stretch
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
  | .print _             => true
```

Over-approximation costs precision, never soundness: `execPar_accesses_sub` proves the computed
footprint contains every cell actually touched, at every heap. `wfB s = true` implies
`WellFormed (execPar s ρ) σ`, so one `decide` discharges the metatheorem's hypothesis.

# A hand-written `parallel` is checked, not trusted

```html
<div class="dgm tight">
  <div class="nd mono bad">parallel { [0] := 1 }
         | { %0 := [0]; [1] := %0 }<em>store x on one core, load x on another</em></div>
  <div class="arr lbl2">&#8594;<small>decide</small></div>
  <div class="nd key">wfB = false<br/><code>block [·,·]</code> = true<em>the only legal placement is in sequence</em></div>
</div>
```

```html
<div class="nd mono plain wide">step:thread  action          state
0:T0         write [10] &#8592; 1  10&#8614;1, 9&#8614;0, 20&#8614;0
1:T1         write [20] &#8592; 1  10&#8614;1, 9&#8614;0, 20&#8614;1
2:T1         write [9] &#8592; 2   pending
2:T0         write [9] &#8592; 1   pending
Parallel aborts at Step 2. Reason: T0, T1 write to: &#123;9&#125;.
Parallel: 9&#8614;1          Sequential: 9&#8614;2<em>`explainProg late σ₀` &#183; the counterexample is an execution, so the report is one</em></div>
```

:::class "steps"
* This is the configuration the whole data-race literature is about — a store on one core, a load of
  the same cell on another. Our own pass can never *build* it, because a RAW edge puts the two
  statements in one thread; when the user writes it, `wfB` is the checker, and rejects.
* The rejection is not a message but an execution: phase 1 names the conflicting cells by one walk of
  the tree, phase 2 searches for a schedule aimed at exactly those cells, and `follow_sound` turns
  what it finds into a `Reaches … wrong` proof.
* So a wrong guess cannot produce a wrong claim — a bad guess merely finds nothing. Aiming is what
  makes it cheap: on three threads where the middle one is innocent, blind search takes 2.7 s and the
  aimed search 2 ms.
:::

# Four programs, four verdicts, one `decide` each

```html
<table class="dgmt">
<thead><tr><th>program</th><th>what makes it interesting</th><th>verdict</th></tr></thead>
<tbody>
<tr><td>a chunked sum</td><td>every thread <i>reads</i> the array; nobody writes, so Bernstein is vacuous and <code>∗</code> would still have to split it</td><td><span class="vd ok">proved, any plan</span></td></tr>
<tr><td>a matmul</td><td>writes disjoint <code>C[i*n+j]</code>, reads overlapping rows and columns — the case that rules out <code>∗</code></td><td><span class="vd ok">proved</span></td></tr>
<tr><td>a merge sort</td><td>the same recursion twice, <code>parPair</code> against <code>seqPair</code>, disjointness by interval arithmetic</td><td><span class="vd ok">every <code>lo</code>, <code>hi</code> and heap</span></td></tr>
<tr><td>a neural net</td><td>layers in sequence, threads inside each layer, weights updated in place between them</td><td><span class="vd ok">forward and training step</span></td></tr>
<tr class="gap"><td>a scatter <code>dst[idx[i]]</code></td><td>the address is computed, so the footprint has to claim the whole array</td><td><span class="vd no">refused by <code>wfB</code></span>, proved at this heap</td></tr>
</tbody>
</table>
```

```leanLibCode Examples.Programs.MatMul (package := paralever) (startLine := 216) (endLine := 222) -stretch
example : ParProg.wfB (matmul 2) = true := by decide
example : ParProg.wfB (matmul 3) = true := by decide

/-- …and the equivalence follows with nothing further to supply. -/
theorem par_seq_eq_2 (ρ : Regs) (σ : State) :
    ParSeqEq (ParProg.execPar (matmul 2) ρ) (ParProg.execSeq (matmul 2) ρ) σ :=
  ParProg.par_seq_eq (by decide) ρ σ
```

The sum's theorem holds for *any* chunk plan and any heap, with no `decide` — it is a kernel lemma at
symbolic size. The matmul's is `decide` on a concrete `n`, which is where the ceiling is: 6.6 s at
`n = 8`, 19 s at `n = 10`, and `native_decide` is prohibited.

# Automatic parallelization: one scoreboard pass, then a plan in program order

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

:::class "steps"
* Bernstein's three clauses *are* the three kinds of dependence edge, found in one pass over the
  statements rather than by an O(n²) pairwise scan.
* The unit is not a statement but a *register-closed segment*: a fork hands the continuation the
  pre-fork register file, so a register written inside a thread is gone at the join — both readings
  agree, so `wfB` cannot see it, and a load with the store consuming it is never split.
* Nothing is reordered. The plan's threads are a consecutive partition of the units, so
  `planUnits (plan us) = us` is structural and the soundness proof needs no commutation argument.
* The DAG's longest path is a lower bound on the depth of *any* schedule, so it is what decides
  whether a plan is optimal rather than merely better.
:::

# `rewrite_sound`: `seq = par` for the rewrite, with no hypothesis

```leanLibCode Paralever.AutoPar.Rewrite (package := paralever) (startLine := 51) (endLine := 52) -stretch
theorem rewrite_sound (p : ParProg) (ρ : Regs) (σ : State) :
    (runSeq (execPar (rewrite p) ρ) σ).2 = (runSeq (execSeq p ρ) σ).2 := by
```

```html
<table class="dgmt">
<thead><tr><th>shape</th><th>critical path</th><th>the pass</th><th></th></tr></thead>
<tbody>
<tr><td>independent chain, n = 8</td><td>1</td><td>1</td><td><span class="vd ok">optimal</span></td></tr>
<tr><td>interleaved chain</td><td>4</td><td>4</td><td><span class="vd ok">optimal</span></td></tr>
<tr><td>merge sort, 8 leaves</td><td>4</td><td>4</td><td><span class="vd ok">optimal</span></td></tr>
<tr><td>N-shape</td><td>7</td><td>8</td><td>the 7-tree is racy</td></tr>
</tbody>
</table>
```

:::class "steps"
* The theorem has *no* independence hypothesis: the pass is untrusted and the gate is proved, so a bug
  in the planner can only make the output sequential, never wrong.
* `paralever` text in, `paralever` text out: the rewritten program is re-read and round-trips, so the
  artifact the user gets is the artifact that was proved.
* Where the pass misses the lower bound it is the fork–join shape, not the analysis: the 7-deep tree
  for the N-shape has a race in it.
:::

# MLIR: one reader, and every language that targets it

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
* N languages against one converter instead of one front end per language, and stage 1 is replaceable,
  so a hand-written `.mlir` feeds the same interface.
* *Generic form, not each dialect's assembly* — `--mlir-print-op-generic` prints every op the same
  way, so one reader covers `affine`, `memref`, `arith` and `func`.
* *Not LLVM IR*: unstructured `br` and phi nodes have no encoding in an inductive `ParM`, and a loop
  structurizer destroys the affine maps the lowering depends on.
* `MLIR.lower` is a Lean *function*, so the translation is an object we can state a theorem about
  rather than a script to trust.
:::

# One file end to end, and what an affine map gives for free

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
<div class="dgm col tight">
  <div class="nd mono plain wide">"affine.store"(%v, %A, %i, %j) &#123;map = affine_map&lt;(d0, d1) -&gt; (d0, d1)&gt;&#125;<em>the map applied to (i, j) <b>is</b> the subscript — no analysis, no inference</em></div>
  <div class="arr">&#9660;</div>
  <div class="nd mono wide">Layout.at "A" [i, j]  =  A.base + i&#183;cols + j<em>range-checked against its own buffer, because `Layout.at` is total</em></div>
  <div class="arr">&#9660;</div>
  <div class="nd key wide">wr (i, j) = [that cell]<em>which is exactly what `wfB_parFor_of_lists` asks for</em></div>
</div>
```

:::class "steps"
* The map applied to the indices *is* the subscript, so the footprint is read off the source — no
  dependence analysis, no inference, nothing to be wrong about.
* Loops are unrolled at lowering, so each subscript is a literal `Nat` and the footprint stays exact:
  proportional to the number of accesses, not to the size of the array. That is what keeps `indepB`
  — quadratic in list length — evaluable at all.
* `Layout.of` places buffers in consecutive ranges, so array disjointness is discharged once by the
  allocator rather than once per pair.
* What is refused is refused *loudly*: a memory space, a dynamic dimension or a multi-block region
  gets a coded diagnostic with a position, never a silent approximation.
:::

# Limits


:::class "steps"
* *Registers cannot be renamed away — yet.* `noRegFlow` is on raw read sets, stronger than the
  liveness `atoms` establishes, so a chain reusing `%0` is declined and returned sequential.
* *Memory cannot be renamed at all.* A `Loc` is reached by a computed address, so the cell *is* the
  name — privatization, the commonest OpenMP clause, is out of reach.
* *Footprints over-approximate.* `A[B[i]]` reports the whole array and `whileAtMost` reports the branch
  union: conservative, never unsound, and the two-part verdict says which heaps the refusal covers.
* *`ParM` is inductive*, so `while true` is unrepresentable; and whether order preservation itself
  costs depth is open.
:::

# Conclusions


:::class "finale"
* *Nine lines.* A heap is a function; a program is a tree; `runSeq` reads it left to right; footprints
  are measured along that run; `Indep` is Bernstein; `wfB` asks it at every fork; a step moves one
  child, joins, or goes to `wrong`; `runSeq` is conserved by every step, so one outcome is reachable
  and reached; a fork and its sequence have the same `runSeq`.
* *One theorem, then arithmetic.* `wfB s = true ⇒ execPar s ∥≡ execSeq s`, every schedule, arbitrary
  programs, kernel-checked — so each program pays `decide`, not a proof about interleavings.
* *The one hard case.* A child that is not the leftmost takes a step, so the machine's heap and the
  reference heap disagree, and independence is what makes the disagreement invisible. Everything else
  is `runSeq`'s own defining equation, read in the other direction.
:::

```html
<div class="links">0 sorries &#183; <a href="https://github.com/AnirudhG07/paralever">github.com/AnirudhG07/paralever</a> &#183; contact@shemeka.in</div>
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
